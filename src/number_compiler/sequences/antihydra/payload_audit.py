"""Owner-local validation of retained Antihydra payloads.

Each validator is registered against one exact live root and its exact ledger
stores.  The shared resource layer sees only owner-qualified direct members;
this module owns the Antihydra arithmetic and projection invariants.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
from dataclasses import fields
from typing import TYPE_CHECKING, TypeVar, cast

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.blocks import ArithmeticCylinder, Cylinder

_Cylinder = TypeVar("_Cylinder", "Cylinder", "ArithmeticCylinder")


def _canonical_cylinder(
    value: _Cylinder,
    ledger: ResourceLedger,
    kernel: Callable[[int, int], _Cylinder],
    bit_factor: int,
    branch_counter: str,
    composition_counter: str | None = None,
) -> bool:
    width, residue = value.width, value.residue
    if type(width) is not int or not 1 <= width <= 64:
        return False
    if type(residue) is not int or not 0 <= residue < 1 << width:
        return False
    if any(
        type(getattr(value, item.name)) is not int
        or abs(getattr(value, item.name)).bit_length() > bit_factor * width + 10
        for item in fields(value)
    ):
        return False
    source, remaining = residue, width
    result: _Cylinder | None = None
    while remaining:
        size = min(8, remaining)
        leaf = kernel(source % (1 << size), size)
        source = 3**size * (source >> size) + leaf.output
        ledger.bump(branch_counter, size)
        if result is None:
            result = leaf
        else:
            result = result.then(leaf)
            if composition_counter is not None:
                ledger.bump(composition_counter)
        remaining -= size
    return value == result


def _canonical_physical_cylinder(value: object, ledger: ResourceLedger) -> bool:
    from number_compiler.sequences.antihydra.blocks import Cylinder, kernel

    return type(value) is Cylinder and _canonical_cylinder(
        value,
        ledger,
        kernel,
        4,
        "antihydra_payload_audit_branch_steps",
        "antihydra_payload_audit_compositions",
    )


def _canonical_arithmetic_cylinder(value: object, ledger: ResourceLedger) -> bool:
    from number_compiler.sequences.antihydra.blocks import (
        ArithmeticCylinder,
        arithmetic_kernel,
    )

    return type(value) is ArithmeticCylinder and _canonical_cylinder(
        value,
        ledger,
        arithmetic_kernel,
        2,
        "antihydra_payload_audit_arithmetic_branch_steps",
    )


def register_antihydra_payload_contract(root: object) -> None:
    """Register one callback for each supported exact Antihydra owner root."""
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )
    from number_compiler.sequences.antihydra.projection_core import (
        AntihydraFragmentAdapter,
    )
    from number_compiler.sequences.antihydra.projection_fragments import (
        ProjectionFragmentCache,
    )
    from number_compiler.sequences.antihydra.projection_occurrences import (
        ProjectionOccurrenceCursor,
    )
    from number_compiler.sequences.antihydra.projection_payload_audit import (
        audit_antihydra_cursor,
        audit_antihydra_fragment_adapter,
        audit_antihydra_fragment_cache,
        audit_antihydra_section_workspace,
    )
    from number_compiler.sequences.antihydra.projection_workspace import (
        SectionImageWorkspace,
    )
    from number_compiler.sequences.antihydra.runtime import (
        AntihydraArithmeticTerm,
        CylinderEngine,
    )

    ledger = getattr(root, "ledger", None)
    if type(ledger) is not ResourceLedger:
        raise TypeError("Antihydra payload roots require their ResourceLedger")
    register = ledger.register_payload_audit_contract
    bind = PayloadAuditStoreBinding
    if type(root) is AntihydraArithmeticImageWorkspace:
        stores = [
            bind(root.image_owner, "images", "arithmetic_image"),
        ]
        if root.mahler_bindings is not None:
            if root.mahler_binding_owner is None:
                raise ValueError("Antihydra Mahler bindings have no ledger owner")
            stores.append(
                bind(
                    root.mahler_binding_owner,
                    "mahler_bindings",
                    "arithmetic_source_action",
                )
            )
        register(root, "antihydra", tuple(stores), audit_antihydra_image_workspace)
    elif type(root) is CylinderEngine:
        register(
            root,
            "antihydra",
            (
                bind(root.memo.owner, "audit_memo_store", "arithmetic_cylinder"),
                bind(
                    root.arithmetic_memo.owner,
                    "audit_arithmetic_memo_store",
                    "arithmetic_cylinder",
                ),
                bind(root.workspace, "stack", "workspace"),
            ),
            audit_antihydra_engine,
        )
    elif type(root) is AntihydraArithmeticTerm:
        stores = [
            bind(
                root.segment_owner,
                "_segments",
                "arithmetic_cylinder_support",
            ),
            bind(root.result_owner, "result_publications", "arithmetic_result"),
            bind(root.physical_owner, "physical_publications", "physical_result"),
        ]
        memo = getattr(root, "mahler_window_memo", None)
        workspace = getattr(root, "mahler_workspace", None)
        window_owner = getattr(workspace, "_window_owner", None)
        if memo is not None and type(window_owner) is int:
            stores.append(
                bind(
                    window_owner,
                    "mahler_window_memo",
                    "query_memo",
                )
            )
        register(root, "antihydra", tuple(stores), audit_antihydra_term)
    elif type(root) is ProjectionFragmentCache:
        register(
            root,
            "antihydra",
            (
                bind(root.owner, "fragments", "demanded_projection"),
                bind(root.seal_owner, "seals", "projection_binding"),
            ),
            audit_antihydra_fragment_cache,
        )
    elif (
        type(root) is ProjectionOccurrenceCursor
        or type(root) is AntihydraFragmentAdapter
    ):
        register(
            root,
            "antihydra",
            tuple(
                bind(row.owner, row.attribute, row.role)
                for row in root.audit_snapshot().stores
            ),
            audit_antihydra_cursor
            if type(root) is ProjectionOccurrenceCursor
            else audit_antihydra_fragment_adapter,
        )
    elif type(root) is SectionImageWorkspace:
        register(
            root,
            "antihydra",
            (bind(root.owner, "images", "demanded_projection"),),
            audit_antihydra_section_workspace,
        )


def refresh_antihydra_payload_contract(root: object) -> None:
    """Refresh a live term contract atomically through its ledger owner."""
    ledger = getattr(root, "ledger", None)
    if type(ledger) is not ResourceLedger:
        raise TypeError("Antihydra payload roots require their ResourceLedger")
    ledger.refresh_payload_audit_contract(
        root,
        "antihydra",
        lambda: register_antihydra_payload_contract(root),
        missing_message="Antihydra term has no exact contract to refresh",
        restore_message="failed to restore the Antihydra payload contract",
    )


def owned_row_matches(
    ledger: ResourceLedger,
    owner: int,
    store: object,
    role: str,
    *,
    entries: int | None = None,
    nodes: int | None = None,
) -> bool:
    return ledger.matches_store_account(
        owner, store, role, entries=entries, nodes=nodes
    )


def approve_payload(
    approved: list[PayloadAuditEntry], owner: int, value: object
) -> None:
    approved.append(PayloadAuditEntry(owner, value))


def reject_payload(invalid: list[PayloadAuditEntry], owner: int, value: object) -> None:
    invalid.append(PayloadAuditEntry(owner, value))


def audit_antihydra_engine(ledger: object, root: object) -> PayloadAuditContribution:
    """Validate one engine and its bounded, canonical cylinder memo entries."""
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceBoundSchedulerCore,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.sequences.antihydra.projection_core import (
        AntihydraFragmentAdapter,
        AntihydraProjectionDriver,
    )
    from number_compiler.sequences.antihydra.projection_fragments import (
        ProjectionFragmentCache,
    )
    from number_compiler.sequences.antihydra.projection_workspace import (
        SectionImageWorkspace,
    )
    from number_compiler.sequences.antihydra.runtime import CylinderEngine

    if type(ledger) is not ResourceLedger or type(root) is not CylinderEngine:
        raise TypeError("Antihydra engine audit requires its exact root")
    engine = root
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    first_owner = engine.memo.owner
    structural = (
        set(vars(engine))
        == {
            "ledger",
            "memo",
            "arithmetic_memo",
            "workspace",
            "stack",
            "capacity",
            "term_serial",
            "_shared_cache",
            "projection_workspace",
            "projection_fragments",
            "projection_fragment_driver",
        }
        and engine.ledger is ledger
        and engine.memo.ledger is ledger
        and engine.arithmetic_memo.ledger is ledger
        and type(engine.projection_fragments) is ProjectionFragmentCache
        and engine.projection_fragments.ledger is ledger
        and engine.memo.nodes_per_entry == 1
        and engine.arithmetic_memo.nodes_per_entry == 1
        and type(engine.capacity) is int
        and engine.capacity >= 32
        and type(engine.shared_cache) is bool
        and type(engine.term_serial) is int
        and engine.term_serial >= 0
        and len(engine.memo) + len(engine.arithmetic_memo) <= engine.capacity
        and not engine.stack
        and owned_row_matches(
            ledger,
            engine.memo.owner,
            engine.audit_memo_store,
            "arithmetic_cylinder",
            entries=len(engine.memo),
            nodes=len(engine.memo),
        )
        and owned_row_matches(
            ledger,
            engine.arithmetic_memo.owner,
            engine.audit_arithmetic_memo_store,
            "arithmetic_cylinder",
            entries=len(engine.arithmetic_memo),
            nodes=len(engine.arithmetic_memo),
        )
        and owned_row_matches(
            ledger,
            engine.workspace,
            engine.stack,
            "workspace",
            entries=0,
            nodes=0,
        )
    )
    projection = engine.projection_workspace
    if projection is not None:
        structural &= (
            type(projection) is SectionImageWorkspace
            and projection.ledger is ledger
            and not projection.active
            and not projection.images
            and projection.area == 0
        )
    driver = engine.projection_fragment_driver
    if driver is not None:
        if type(driver) is not AntihydraProjectionDriver:
            structural = False
        else:
            adapter = driver.adapter
            core = driver.core
            scheduler = driver.scheduler
            cursor = driver.cursor
            structural &= (
                type(adapter) is AntihydraFragmentAdapter
                and type(core) is SourceBoundSchedulerCore
                and type(scheduler) is TileScheduler
                and scheduler.is_source_only
                and scheduler.ledger is ledger
                and scheduler.published_source_image_core is core
                and cursor.ledger is ledger
                and not (cursor_snapshot := cursor.audit_snapshot()).active
                and all(not row.store for row in cursor_snapshot.stores)
                and adapter.ledger is ledger
                and adapter.audit_snapshot().idle
                and len((core_snapshot := core.audit_snapshot()).adapters) == 1
                and core_snapshot.adapters.get(
                    (adapter.family, adapter.semantic_version)
                )
                is adapter
                and not core_snapshot.nodes
                and not core_snapshot.origins
                and not core_snapshot.applications
                and not core_snapshot.relative
                and not core_snapshot.projections
            )

    for physical_key, physical_value in engine.memo.items():
        valid = (
            type(physical_key) is tuple
            and len(physical_key) == 2
            and all(type(part) is int for part in physical_key)
            and _canonical_physical_cylinder(physical_value, ledger)
            and physical_key == (physical_value.width, physical_value.residue)
        )
        if valid:
            approve_payload(approved, engine.memo.owner, physical_key)
            approve_payload(approved, engine.memo.owner, physical_value)
        else:
            structural = False
            reject_payload(invalid, engine.memo.owner, physical_key)
            reject_payload(invalid, engine.memo.owner, physical_value)

    for arithmetic_key, arithmetic_value in engine.arithmetic_memo.items():
        valid = (
            type(arithmetic_key) is tuple
            and len(arithmetic_key) == 2
            and all(type(part) is int for part in arithmetic_key)
            and _canonical_arithmetic_cylinder(arithmetic_value, ledger)
            and arithmetic_key == (arithmetic_value.width, arithmetic_value.residue)
        )
        if valid:
            approve_payload(approved, engine.arithmetic_memo.owner, arithmetic_key)
            approve_payload(approved, engine.arithmetic_memo.owner, arithmetic_value)
        else:
            structural = False
            reject_payload(invalid, engine.arithmetic_memo.owner, arithmetic_key)
            reject_payload(invalid, engine.arithmetic_memo.owner, arithmetic_value)

    if not structural:
        reject_payload(invalid, first_owner, engine)
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


def audit_antihydra_image_workspace(
    ledger: object, root: object
) -> PayloadAuditContribution:
    """Validate the optional Mahler companion of an admitted arithmetic image."""
    from number_compiler.sequences.antihydra.arithmetic_images import (
        ANTIHYDRA_ARITHMETIC_LAW,
        AntihydraArithmeticImageWorkspace,
    )

    if (
        type(ledger) is not ResourceLedger
        or type(root) is not AntihydraArithmeticImageWorkspace
    ):
        raise TypeError("Antihydra image audit requires its exact workspace root")
    image = root
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    bindings = image.mahler_bindings
    owner = image.mahler_binding_owner
    valid = (
        image.ledger is ledger
        and image.seed == 8
        and image.law == ANTIHYDRA_ARITHMETIC_LAW
        and not image.mahler_consumer_active
    )
    if bindings is None:
        valid &= owner is None and image.mahler_wire is None
    else:
        valid &= (
            type(owner) is int
            and image.ledger.registered_container(owner) is bindings
            and owned_row_matches(
                ledger,
                owner,
                bindings,
                "arithmetic_source_action",
                entries=1,
                nodes=3,
            )
            and len(bindings) == 1
            and (image.root_source, image.root_action) in bindings
        )
        if type(owner) is int and len(bindings) == 1:
            key, wire = next(iter(bindings.items()))
            transfer = image.image_node(image.root_payload).summary.transfer
            valid &= (
                type(key) is tuple
                and len(key) == 2
                and key[0] == image.root_source
                and key[1] == image.root_action
                and wire is image.mahler_wire
            )
            if (
                type(wire) is tuple
                and len(wire) == 3
                and all(type(part) is int for part in wire)
            ):
                typed_wire = cast(tuple[int, int, int], wire)
                valid &= (
                    typed_wire[0] == image.steps
                    and typed_wire[1]
                    == -12 * (transfer.upper + transfer.offset - transfer.lower)
                    and typed_wire[2]
                    == (6 if image.steps == 1 else 6 * transfer.upper + typed_wire[1])
                    and typed_wire[2] < 0
                )
            else:
                valid = False
            if valid:
                approve_payload(approved, owner, key)
                approve_payload(approved, owner, wire)
            else:
                reject_payload(invalid, owner, key)
                reject_payload(invalid, owner, wire)
    if not valid:
        invalid_owner = owner if type(owner) is int else image.image_owner
        reject_payload(invalid, invalid_owner, image)
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


def audit_antihydra_term(ledger: object, root: object) -> PayloadAuditContribution:
    """Validate one total arithmetic occurrence and its optional physical result."""
    from number_compiler.arithmetic.fields.skew_transfer import (
        integer_dyadic_fiber_action,
    )
    from number_compiler.sequences.antihydra.arithmetic_images import (
        ANTIHYDRA_ARITHMETIC_LAW,
        AntihydraArithmeticImageWorkspace,
    )
    from number_compiler.sequences.antihydra.blocks import (
        ArithmeticCylinder,
        arithmetic_kernel,
        kernel,
        terminal_effect,
    )
    from number_compiler.sequences.antihydra.mahler_action import MahlerWorkspace
    from number_compiler.sequences.antihydra.runtime import (
        AntihydraArithmeticTerm,
        ArithmeticResult,
        ArithmeticSegment,
        PhysicalPublication,
        Run,
    )

    if type(ledger) is not ResourceLedger or type(root) is not AntihydraArithmeticTerm:
        raise TypeError("Antihydra term audit requires its exact term root")
    term = root
    term_snapshot = term.audit_snapshot()
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    owner = term.segment_owner
    valid = (
        set(vars(term))
        == {
            "requested",
            "_mahler_prepared",
            "_source_action_prepared",
            "max_steps",
            "max_state_bits",
            "max_cache_entries",
            "engine",
            "ledger",
            "segment_owner",
            "_segments",
            "_segments_ready",
            "result_owner",
            "result_publications",
            "physical_owner",
            "physical_publications",
            "_result",
            "arithmetic_workspace",
            "mahler_workspace",
        }
        and term.ledger is ledger
        and term.engine.ledger is ledger
        and type(term.requested) is int
        and type(term.mahler_prepared) is bool
        and type(term.source_action_prepared) is bool
        and type(term.max_steps) is int
        and type(term.max_state_bits) is int
        and 0 <= term.requested <= term.max_steps
        and 4 + term.requested <= term.max_state_bits
        and term.max_cache_entries == term.engine.capacity
        and owned_row_matches(
            ledger,
            owner,
            term_snapshot.segment_store,
            "arithmetic_cylinder_support",
            entries=len(term_snapshot.segments),
        )
        and type(term_snapshot.segments_ready) is bool
        and (term_snapshot.segments_ready or not term_snapshot.segments)
        and len(term_snapshot.segments) <= (term.requested + 63) // 64
        and owned_row_matches(
            ledger,
            term.result_owner,
            term.result_publications,
            "arithmetic_result",
            entries=len(term.result_publications),
            nodes=len(term.result_publications),
        )
        and len(term.result_publications) <= 1
        and owned_row_matches(
            ledger,
            term.physical_owner,
            term.physical_publications,
            "physical_result",
            entries=len(term.physical_publications),
            nodes=2 * len(term.physical_publications),
        )
        and len(term.physical_publications) <= 1
    )

    image = term.arithmetic_workspace
    expected_h, balance, minimum, completed = 8, 0, 0, 0
    first_failure: int | None = None
    if image is not None:
        valid &= (
            type(image) is AntihydraArithmeticImageWorkspace
            and image.ledger is ledger
            and image.seed == 8
            and image.returns == term.requested
            and image.law == ANTIHYDRA_ARITHMETIC_LAW
        )
        if type(image) is AntihydraArithmeticImageWorkspace:
            summary = image.summary()
            source = image.source_node(image.root_source)
            chart = integer_dyadic_fiber_action(
                summary.transfer, source.residue, source.precision
            )
            expected_h = chart.addend + chart.multiplier * source.lift
            balance, minimum, completed = summary.delta, summary.minimum, summary.width
            ledger.bump(
                _antihydra_keys.ANTIHYDRA_PAYLOAD_AUDIT_ENDPOINT_OPERAND_BITS,
                max(1, abs(chart.multiplier).bit_length())
                + max(1, abs(chart.addend).bit_length())
                + max(1, source.lift.bit_length()),
            )
            first_failure = image.first_failure_index()
    elif term_snapshot.result is not None or term_snapshot.segments_ready:
        valid = False

    expected_segments: Iterator[tuple[int, ArithmeticCylinder]] | None = None
    if (
        term_snapshot.segments_ready
        and type(image) is AntihydraArithmeticImageWorkspace
    ):
        # Segments are borrowed from the authenticated source image.  Their
        # validity comes from exact source/start/cylinder equality, not current
        # residence in the engine's evictable arithmetic memo.
        expected_segments = iter(image.segments())

    if term_snapshot.segments_ready:
        source_h, source_balance, source_minimum, start = 8, 0, 0, 0
        for segment in term_snapshot.segments:
            expected_segment = (
                next(expected_segments, None) if expected_segments is not None else None
            )
            if (
                type(segment) is not ArithmeticSegment
                or type(segment.start) is not int
                or segment.start != start
                or type(segment.cylinder) is not ArithmeticCylinder
            ):
                valid = False
                reject_payload(invalid, owner, segment)
                continue
            block = segment.cylinder
            segment_valid = (
                expected_segment is not None
                and expected_segment == (segment.start, block)
                and type(block.width) is int
                and 1 <= block.width <= 64
                and type(block.residue) is int
            )
            try:
                block.__post_init__()
                if segment_valid:
                    segment_valid = block.residue == source_h % (1 << block.width)
                    if segment_valid:
                        source_h, source_balance = block.advance(
                            source_h, source_balance
                        )
            except (ArithmeticError, TypeError, ValueError):
                segment_valid = False
            if not segment_valid:
                valid = False
                reject_payload(invalid, owner, segment)
                continue
            source_minimum = min(
                source_minimum, source_balance - block.delta + block.minimum
            )
            start += block.width
            approve_payload(approved, owner, segment)
        if expected_segments is not None and next(expected_segments, None) is not None:
            valid = False
        if start != term.requested:
            valid = False
        if type(image) is AntihydraArithmeticImageWorkspace and (
            source_h,
            source_balance,
            source_minimum,
        ) != (expected_h, balance, minimum):
            valid = False

    arithmetic = term_snapshot.result
    if arithmetic is not None:
        result_valid = (
            type(arithmetic) is ArithmeticResult
            and len(term.result_publications) == 1
            and term.result_publications[0] is arithmetic
            and arithmetic.source_term is term
            and arithmetic.ledger is ledger
            and arithmetic.requested == term.requested == completed
            and (arithmetic.h, arithmetic.balance, arithmetic.minimum)
            == (expected_h, balance, minimum)
            and arithmetic.first_failure_index == first_failure
            and arithmetic.h.bit_length() <= term.max_state_bits
            and arithmetic.balance.bit_length() <= term.max_state_bits
        )
        if result_valid:
            approve_payload(approved, term.result_owner, arithmetic)
        else:
            valid = False
            if len(term.result_publications) == 1:
                reject_payload(invalid, term.result_owner, term.result_publications[0])
    elif term.result_publications:
        valid = False
        for published_result in term.result_publications:
            reject_payload(invalid, term.result_owner, published_result)

    mahler = term.mahler_workspace
    if mahler is not None:
        valid &= (
            type(mahler) is MahlerWorkspace
            and arithmetic is not None
            and mahler.result is arithmetic
            and mahler.source_workspace is image
        )
        if type(mahler) is MahlerWorkspace and type(arithmetic) is ArithmeticResult:
            try:
                mahler.validate(arithmetic)
            except (TypeError, ValueError, AttributeError):
                valid = False
            else:
                window_owner = mahler.window_memo_owner
                if mahler.window_memo_container is not None:
                    if type(window_owner) is not int:
                        valid = False
                    else:
                        for key, window in mahler.window_memo_entries():
                            approve_payload(approved, window_owner, key)
                            approve_payload(approved, window_owner, window)

    physicals = term.physical_publications
    if physicals:
        physical = physicals[0]
        valid &= term_snapshot.segments_ready
        h, ledger_value = 8, 0
        left, right = 5, 6
        physical_minimum, returns, halted = 0, 0, False
        while returns < term.requested:
            leaf = arithmetic_kernel(h & 1, 1)
            if ledger_value + leaf.minimum < 0:
                dl, dr = terminal_effect(h)
                left, right = left + dl, right + dr
                ledger_value = physical_minimum = -1
                returns += 1
                halted = True
                break
            roof = kernel(h & 1, 1)
            old_ledger = ledger_value
            h, ledger_value, dl, dr = roof.apply(h, ledger_value)
            left, right = left + dl, right + dr
            physical_minimum = min(physical_minimum, old_ledger + roof.minimum)
            returns += 1
            ledger.bump(_antihydra_keys.ANTIHYDRA_PAYLOAD_AUDIT_PHYSICAL_STEPS)
        physical_valid = (
            type(physical) is PhysicalPublication
            and type(physical.run) is Run
            and physical.matches(physical.run)
            and physical.run.is_bound_to_engine(term.engine)
            and physical.run.source_term is term
            and physical.run.ledger is ledger
            and physical.run.requested == term.requested
            and (
                physical.run.h,
                physical.run.balance,
                physical.run.minimum,
                physical.run.left,
                physical.run.right,
                physical.run.returns,
                physical.run.halted,
            )
            == (h, ledger_value, physical_minimum, left, right, returns, halted)
        )
        if physical_valid:
            approve_payload(approved, term.physical_owner, physical)
        else:
            valid = False
            reject_payload(invalid, term.physical_owner, physical)

    if not valid:
        reject_payload(invalid, owner, term)
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = [
    "audit_antihydra_engine",
    "audit_antihydra_image_workspace",
    "audit_antihydra_term",
    "refresh_antihydra_payload_contract",
    "register_antihydra_payload_contract",
]
