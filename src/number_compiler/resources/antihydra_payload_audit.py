"""Independent admission of fixed-width Antihydra arithmetic cache records.

No field is reclassified as geometry. A record must equal the canonical
composition of at most 64 discovered branches, and its actual owner/storage
must reconcile. This says nothing about source-discovery complexity or the
literal TM refinement of the arithmetic law.
"""

from __future__ import annotations

from dataclasses import fields
from typing import TYPE_CHECKING, TypeVar
from collections.abc import Callable

from number_compiler.arithmetic.fields.skew_transfer import (
    integer_dyadic_fiber_action,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.blocks import Cylinder, ArithmeticCylinder
    from number_compiler.sequences.antihydra.projection_fragments import (
        ProjectionFragmentCache,
    )
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
)


_Cylinder = TypeVar("_Cylinder", "Cylinder", "ArithmeticCylinder")


def _canonical_cylinder(
    value: _Cylinder,
    ledger: ResourceLedger,
    kernel: Callable[[int, int], _Cylinder],
    bit_factor: int,
    branch_counter: str,
    composition_counter: str | None = None,
) -> bool:
    w, r = value.width, value.residue
    if type(w) is not int or not 1 <= w <= 64:
        return False
    if type(r) is not int or not 0 <= r < 1 << w:
        return False
    if any(
        type(getattr(value, item.name)) is not int
        or abs(getattr(value, item.name)).bit_length() > bit_factor * w + 10
        for item in fields(value)
    ):
        return False
    source, remaining = r, w
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


def canonical_cylinder(value: object, ledger: ResourceLedger) -> bool:
    from number_compiler.sequences.antihydra.blocks import Cylinder, kernel

    return type(value) is Cylinder and _canonical_cylinder(
        value,
        ledger,
        kernel,
        4,
        "antihydra_payload_audit_branch_steps",
        "antihydra_payload_audit_compositions",
    )


def canonical_arithmetic_cylinder(value: object, ledger: ResourceLedger) -> bool:
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


def _fragment_source_bindings(
    cache: ProjectionFragmentCache,
    terms: dict[int, AntihydraArithmeticTerm],
    ledger: ResourceLedger,
) -> set[int]:
    """Replay each demanded source prefix once, retaining only key approvals.

    Cache insertion order is unrelated to source chronology. Group at most 32
    retained keys by source and start; never retain intermediate endpoint words
    or treat a cached phase as authority for the next source occurrence.
    """
    from number_compiler.sequences.antihydra.blocks import (
        ArithmeticCylinder,
        physical_roof,
    )
    from number_compiler.sequences.antihydra.projection_fragments import (
        ProjectionFragmentKey,
    )
    from number_compiler.sequences.antihydra.runtime import ArithmeticSegment

    demanded: dict[int, dict[int, list[ProjectionFragmentKey]]] = {}
    for key in cache.fragments:
        if type(key) is not ProjectionFragmentKey:
            continue
        if any(
            type(getattr(key, field.name)) is not int
            for field in fields(key)
            if field.name != "cylinder"
        ):
            continue
        term = terms.get(key.source_owner)
        if (
            term is None
            or term.ledger is not ledger
            or term.engine.projection_fragments is not cache
            or key.requested != term.requested
            or not 0 <= key.start < key.requested
            or term._physical is None
            or term._physical.halted
            or not 1 <= key.spatial_width <= 64
            or not 1 <= key.temporal_width <= 64
            or key.spatial_sign not in (-1, 1)
            or key.temporal_sign not in (-1, 1)
            or key.modulus < 2
            or type(key.cylinder) is not tuple
            or len(key.cylinder) != 6
            or any(type(part) is not int for part in key.cylinder)
        ):
            continue
        demanded.setdefault(key.source_owner, {}).setdefault(key.start, []).append(key)

    bound: set[int] = set()
    for owner, starts in demanded.items():
        term = terms[owner]
        last = max(starts)
        h, balance, head, time, start = 8, 0, 1, 11, 0
        if not term._segments_ready:
            continue
        for segment in term._segments:
            if (
                type(segment) is not ArithmeticSegment
                or type(segment.start) is not int
                or segment.start != start
                or type(segment.cylinder) is not ArithmeticCylinder
            ):
                break
            block = segment.cylinder
            if (
                type(block.width) is not int
                or not 1 <= block.width <= 64
                or any(
                    type(getattr(block, field.name)) is not int
                    or abs(getattr(block, field.name)).bit_length()
                    > 2 * block.width + 10
                    for field in fields(block)
                )
                or block.residue != h % (1 << block.width)
                or balance + block.minimum < 0
            ):
                break
            signature = (
                block.width,
                block.residue,
                block.output,
                block.delta,
                block.minimum,
                block.parity_word,
            )
            for key in starts.get(start, ()):
                spatial_phase = key.spatial_width * (2 if key.spatial_sign == -1 else 1)
                temporal_phase = key.temporal_width * (
                    2 if key.temporal_sign == -1 else 1
                )
                if (
                    key.cylinder == signature
                    and key.head_phase == head % spatial_phase
                    and key.time_phase == time % temporal_phase
                ):
                    bound.add(id(key))
            if start >= last:
                break
            ledger.bump(
                "antihydra_payload_audit_projection_fragment_steps", block.width
            )
            ledger.bump(
                "antihydra_payload_audit_projection_fragment_operand_bits",
                h.bit_length()
                + balance.bit_length()
                + head.bit_length()
                + time.bit_length(),
            )
            h, balance, left, right = physical_roof(block).apply(h, balance)
            head += right - left
            time += right + left
            start += block.width
    return bound


def audit_antihydra_payloads(
    ledger: ResourceLedger,
    *,
    dyadic: PhysicalSupportPayloadAudit | None = None,
) -> PhysicalSupportPayloadAudit:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceBoundSchedulerCore,
    )
    from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
    from number_compiler.resources.dyadic_return_payload_audit import (
        audit_dyadic_return_payloads,
    )
    from number_compiler.sequences.antihydra.arithmetic_images import (
        AntihydraArithmeticImageWorkspace,
    )
    from number_compiler.sequences.antihydra.blocks import (
        arithmetic_kernel,
        kernel,
        terminal_effect,
    )
    from number_compiler.sequences.antihydra.mahler_action import MahlerWorkspace
    from number_compiler.sequences.antihydra.projection_core import (
        AntihydraProjectionDriver,
        _AntihydraFragmentAdapter,
    )
    from number_compiler.sequences.antihydra.projection_fragments import (
        ProjectionFragment,
        ProjectionFragmentCache,
        ProjectionFragmentKey,
    )
    from number_compiler.sequences.antihydra.projection_occurrences import (
        ProjectionOccurrenceCursor,
    )
    from number_compiler.sequences.antihydra.projection_workspace import (
        SectionImageWorkspace,
    )
    from number_compiler.sequences.antihydra.runtime import (
        AntihydraArithmeticTerm,
        ArithmeticResult,
        ArithmeticSegment,
        CylinderEngine,
        Run,
        _PhysicalPublication,
    )

    if dyadic is None:
        dyadic = audit_dyadic_return_payloads(ledger)
    approved = set(dyadic.approved)
    invalid = set(dyadic.invalid)
    containers = dict(ledger.iter_containers())
    inventory = {row.owner: row for row in ledger.inventory()}
    roots = tuple(ledger.iter_execution_roots())
    for root in roots:
        if isinstance(root, AntihydraArithmeticImageWorkspace):
            continue
        if type(root) is ProjectionOccurrenceCursor:
            owner = root._state_owner
            try:
                stores = (
                    (root._state_owner, root._states, "workspace"),
                    (root._state_seal_owner, root._state_seals, "projection_binding"),
                    (root._occurrence_owner, root._occurrences, "demanded_projection"),
                    (
                        root._occurrence_seal_owner,
                        root._occurrence_seals,
                        "projection_binding",
                    ),
                )
                valid = (
                    root.ledger is ledger
                    and root._active is False
                    and set(vars(root))
                    == {
                        "ledger",
                        "_state_owner",
                        "_state_seal_owner",
                        "_occurrence_owner",
                        "_occurrence_seal_owner",
                        "_states",
                        "_state_seals",
                        "_occurrences",
                        "_occurrence_seals",
                        "_token",
                        "_active",
                    }
                    and all(
                        not store
                        and containers.get(store_owner) is store
                        and inventory[store_owner].role == role
                        and inventory[store_owner].accounting_delta == 0
                        for store_owner, store, role in stores
                    )
                )
                if valid:
                    approved.add(id(root))
                    approved.update(id(store) for _, store, _ in stores)
                else:
                    invalid.add((owner, id(root)))
            except (AttributeError, TypeError, ValueError, KeyError):
                invalid.add((owner if type(owner) is int else -1, id(root)))
            continue
        if type(root) is ProjectionFragmentCache:
            owner = root.owner
            try:
                valid = (
                    root.ledger is ledger
                    and containers.get(owner) is root.fragments
                    and containers.get(root.seal_owner) is root.seals
                    and inventory[owner].role == "demanded_projection"
                    and inventory[root.seal_owner].role == "projection_binding"
                    and inventory[owner].accounting_delta == 0
                    and inventory[root.seal_owner].accounting_delta == 0
                    and len(root.fragments) == len(root.seals) <= 32
                )
                terms = {
                    candidate.segment_owner: candidate
                    for candidate in roots
                    if type(candidate) is AntihydraArithmeticTerm
                }
                source_bindings = (
                    _fragment_source_bindings(root, terms, ledger) if valid else set()
                )
                for fragment_key, fragment in root.fragments.items():
                    bound = (
                        id(fragment_key) in source_bindings
                        and type(fragment_key) is ProjectionFragmentKey
                        and type(fragment) is ProjectionFragment
                        and root.matches_seal(fragment_key, fragment)
                        and fragment.key == fragment_key
                    )
                    if bound:
                        try:
                            fragment.validate()
                        except ValueError:
                            bound = False
                    if bound:
                        # iter_payloads exposes each retained seal independently
                        # of its container. Admit only the exact snapshot already
                        # compared above, including its bounded cylinder fields.
                        approved.update(
                            (
                                id(fragment_key),
                                id(fragment),
                                id(root.seals[fragment_key]),
                            )
                        )
                    else:
                        valid = False
                        invalid.update(
                            ((owner, id(fragment_key)), (owner, id(fragment)))
                        )
                if valid:
                    approved.update((id(root), id(root.fragments), id(root.seals)))
                else:
                    invalid.add((owner, id(root)))
            except (AttributeError, TypeError, ValueError, KeyError):
                invalid.add((owner if type(owner) is int else -1, id(root)))
            continue
        if type(root) is AntihydraArithmeticTerm:
            owner = root.segment_owner
            try:
                valid = (
                    set(vars(root))
                    == {
                        "requested",
                        "max_steps",
                        "max_state_bits",
                        "max_cache_entries",
                        "engine",
                        "ledger",
                        "segment_owner",
                        "_segments",
                        "_segments_ready",
                        "physical_owner",
                        "physical_publications",
                        "_result",
                        "arithmetic_workspace",
                        "mahler_workspace",
                    }
                    and root.ledger is ledger
                    and root.engine.ledger is ledger
                    and type(root.requested) is int
                    and type(root.max_steps) is int
                    and type(root.max_state_bits) is int
                    and 0 <= root.requested <= root.max_steps
                    and 4 + root.requested <= root.max_state_bits
                    and root.max_cache_entries == root.engine.capacity
                    and type(owner) is int
                    and containers.get(owner) is root._segments
                    and inventory[owner].role == "arithmetic_cylinder_support"
                    and inventory[owner].accounting_delta == 0
                    and type(root._segments_ready) is bool
                    and (root._segments_ready or not root._segments)
                    and len(root._segments) <= (root.requested + 63) // 64
                    and type(root.physical_owner) is int
                    and containers.get(root.physical_owner)
                    is root.physical_publications
                    and inventory[root.physical_owner].role == "physical_result"
                    and inventory[root.physical_owner].accounting_delta == 0
                    and len(root.physical_publications) <= 1
                )
                mahler = root.mahler_workspace
                if mahler is not None:
                    arithmetic = root._result
                    if (
                        type(mahler) is not MahlerWorkspace
                        or type(arithmetic) is not ArithmeticResult
                    ):
                        valid = False
                    else:
                        mahler.validate(arithmetic)
                        approved.add(id(mahler))
                arithmetic_workspace = root.arithmetic_workspace
                if arithmetic_workspace is None:
                    expected_segments: tuple[tuple[int, ArithmeticCylinder], ...] = ()
                    h, balance, minimum, start = 8, 0, 0, 0
                    first_failure: int | None = None
                else:
                    if (
                        type(arithmetic_workspace)
                        is not AntihydraArithmeticImageWorkspace
                    ):
                        valid = False
                        expected_segments = ()
                        h, balance, minimum, start = 8, 0, 0, 0
                        first_failure = None
                    else:
                        valid &= id(arithmetic_workspace) in dyadic.approved
                        summary = arithmetic_workspace.summary()
                        expected_segments = (
                            tuple(arithmetic_workspace.segments())
                            if root._segments_ready
                            else ()
                        )
                        # Audit the sealed image directly. Calling endpoint()
                        # here would register an ordinary consumer demand and
                        # repeat its aggregate projection during a read-only
                        # payload audit.
                        source_node = arithmetic_workspace.source_node(
                            arithmetic_workspace.root_source
                        )
                        chart = integer_dyadic_fiber_action(
                            summary.transfer,
                            source_node.residue,
                            source_node.precision,
                        )
                        ledger.bump(
                            "antihydra_payload_audit_endpoint_operand_bits",
                            max(1, abs(chart.multiplier).bit_length())
                            + max(1, abs(chart.addend).bit_length())
                            + max(1, source_node.lift.bit_length()),
                        )
                        h = chart.addend + chart.multiplier * source_node.lift
                        balance, minimum, start = (
                            summary.delta,
                            summary.minimum,
                            summary.width,
                        )
                        first_failure = arithmetic_workspace.first_failure_index()
                        approved.add(id(arithmetic_workspace))
                if len(root._segments) != len(expected_segments):
                    valid = False
                for segment, expected_segment in zip(
                    root._segments, expected_segments, strict=False
                ):
                    expected_start, expected_block = expected_segment
                    bound = (
                        type(segment) is ArithmeticSegment
                        and type(segment.start) is int
                        and segment.start == expected_start
                        and segment.cylinder == expected_block
                    )
                    if not bound:
                        valid = False
                        invalid.add((owner, id(segment)))
                        continue
                    approved.update((id(segment), id(segment.cylinder)))
                result = root._result
                if result is not None:
                    valid &= (
                        type(result) is ArithmeticResult
                        and result._term is root
                        and result.ledger is ledger
                        and result.requested == root.requested == start
                        and (result.h, result.balance) == (h, balance)
                        and result.minimum == minimum
                        and result.first_failure_index == first_failure
                        and result.h.bit_length() <= root.max_state_bits
                        and result.balance.bit_length() <= root.max_state_bits
                    )
                    approved.add(id(result))
                physical = root._physical
                if physical is not None:
                    valid &= root._segments_ready
                    publication = root.physical_publications[0]
                    expected_h, expected_balance = 8, 0
                    expected_left, expected_right = 5, 6
                    expected_minimum, expected_returns = 0, 0
                    expected_halted = False
                    while expected_returns < root.requested:
                        leaf = arithmetic_kernel(expected_h & 1, 1)
                        if expected_balance + leaf.minimum < 0:
                            dl, dr = terminal_effect(expected_h)
                            expected_left += dl
                            expected_right += dr
                            expected_balance = expected_minimum = -1
                            expected_returns += 1
                            expected_halted = True
                            break
                        roof = kernel(expected_h & 1, 1)
                        old_balance = expected_balance
                        (
                            expected_h,
                            expected_balance,
                            dl,
                            dr,
                        ) = roof.apply(expected_h, expected_balance)
                        expected_left += dl
                        expected_right += dr
                        expected_minimum = min(
                            expected_minimum, old_balance + roof.minimum
                        )
                        expected_returns += 1
                        ledger.bump("antihydra_payload_audit_physical_steps")
                    valid &= (
                        type(physical) is Run
                        and type(publication) is _PhysicalPublication
                        and publication.run is physical
                        and publication.matches(physical)
                        and physical._engine is root.engine
                        and physical._term is root
                        and physical.ledger is ledger
                        and physical.requested == root.requested
                        and (
                            physical.h,
                            physical.balance,
                            physical.minimum,
                            physical.left,
                            physical.right,
                            physical.returns,
                            physical.halted,
                        )
                        == (
                            expected_h,
                            expected_balance,
                            expected_minimum,
                            expected_left,
                            expected_right,
                            expected_returns,
                            expected_halted,
                        )
                    )
                    approved.update((id(publication), id(physical)))
                if valid:
                    approved.update(
                        (id(root), id(root._segments), id(root.physical_publications))
                    )
                else:
                    invalid.add((owner, id(root)))
            except (AttributeError, TypeError, ValueError, KeyError):
                invalid.add((owner if type(owner) is int else -1, id(root)))
            continue
        if type(root) is not CylinderEngine:
            continue
        owner = getattr(getattr(root, "memo", None), "owner", -1)
        if type(owner) is not int:
            owner = -1
        try:
            valid = (
                set(vars(root))
                == {
                    "ledger",
                    "memo",
                    "arithmetic_memo",
                    "workspace",
                    "stack",
                    "capacity",
                    "term_serial",
                    "projection_workspace",
                    "projection_fragments",
                    "projection_fragment_driver",
                }
                and root.ledger is ledger
                and root.memo.ledger is ledger
                and type(root.projection_fragments) is ProjectionFragmentCache
                and root.projection_fragments.ledger is ledger
                and type(root.capacity) is int
                and root.capacity >= 32
                and type(root.term_serial) is int
                and root.term_serial >= 0
                and root.memo.nodes_per_entry == 1
                and containers.get(owner) is root.memo._data
                and inventory[owner].role == "arithmetic_cylinder"
                and inventory[owner].accounting_delta == 0
                and len(root.memo) <= root.capacity
                and containers.get(root.workspace) is root.stack
                and inventory[root.workspace].role == "workspace"
                and inventory[root.workspace].accounting_delta == 0
                and not root.stack
            )
            projection = root.projection_workspace
            if projection is not None:
                valid &= (
                    type(projection) is SectionImageWorkspace
                    and projection.ledger is ledger
                    and not projection.active
                    and not projection.images
                    and projection.area == 0
                    and containers.get(projection.owner) is projection.images
                    and inventory[projection.owner].accounting_delta == 0
                )
            driver = root.projection_fragment_driver
            if driver is not None:
                adapter = getattr(driver, "adapter", None)
                core = getattr(driver, "core", None)
                scheduler = getattr(driver, "scheduler", None)
                cursor = getattr(driver, "cursor", None)
                valid &= (
                    type(driver) is AntihydraProjectionDriver
                    and type(adapter) is _AntihydraFragmentAdapter
                    and type(core) is SourceBoundSchedulerCore
                    and type(scheduler) is TileScheduler
                    and scheduler._source_only
                    and scheduler.ledger is ledger
                    and scheduler._source_images is core
                    and type(cursor) is ProjectionOccurrenceCursor
                    and cursor.ledger is ledger
                    and not cursor._active
                    and not cursor._states
                    and not cursor._state_seals
                    and not cursor._occurrences
                    and not cursor._occurrence_seals
                    and adapter.ledger is ledger
                    and core.ledger is ledger
                    and adapter.projection is None
                    and adapter.key is None
                    and adapter.block is None
                    and adapter._cursor is None
                    and adapter._occurrence is None
                    and adapter._source_h == adapter._source_balance == 0
                    and adapter._section_capacity == 0
                    and adapter._source_token is None
                    and not adapter._records
                    and not adapter._seals
                    and not adapter._source_seals
                    and len(core._adapters) == 1
                    and core._adapters.get((adapter.family, adapter.semantic_version))
                    is adapter
                    and not core._nodes
                    and not core._origins
                    and not core._applications
                    and not core._relative
                    and not core._projections
                )
                if valid:
                    assert isinstance(adapter, _AntihydraFragmentAdapter)
                    assert isinstance(core, SourceBoundSchedulerCore)
                    approved.update(
                        (
                            id(driver),
                            id(adapter),
                            id(adapter._records),
                            id(adapter._seals),
                            id(adapter._source_seals),
                            id(core),
                            id(core._adapters),
                            id(core._nodes),
                            id(core._origins),
                            id(core._applications),
                            id(core._relative),
                            id(core._projections),
                        )
                    )
            for key, value in root.memo.items():
                bound = (
                    type(key) is tuple
                    and len(key) == 2
                    and all(type(x) is int for x in key)
                    and canonical_cylinder(value, ledger)
                    and key == (value.width, value.residue)
                )
                if bound:
                    approved.update((id(key), id(value)))
                else:
                    valid = False
                    invalid.update(((owner, id(key)), (owner, id(value))))
            arithmetic_owner = root.arithmetic_memo.owner
            valid &= (
                containers.get(arithmetic_owner) is root.arithmetic_memo._data
                and inventory[arithmetic_owner].role == "arithmetic_cylinder"
                and inventory[arithmetic_owner].accounting_delta == 0
            )
            for arithmetic_key, arithmetic_value in root.arithmetic_memo.items():
                bound = (
                    type(arithmetic_key) is tuple
                    and len(arithmetic_key) == 2
                    and all(type(item) is int for item in arithmetic_key)
                    and canonical_arithmetic_cylinder(arithmetic_value, ledger)
                    and arithmetic_key
                    == (arithmetic_value.width, arithmetic_value.residue)
                )
                if bound:
                    approved.update((id(arithmetic_key), id(arithmetic_value)))
                else:
                    valid = False
                    invalid.update(
                        (
                            (arithmetic_owner, id(arithmetic_key)),
                            (arithmetic_owner, id(arithmetic_value)),
                        )
                    )
            if valid:
                approved.update(
                    (
                        id(root),
                        id(root.memo._data),
                        id(root.arithmetic_memo._data),
                        id(root.stack),
                    )
                )
            else:
                invalid.add((owner, id(root)))
        except (AttributeError, TypeError, ValueError, KeyError):
            invalid.add((owner, id(root)))
    return PhysicalSupportPayloadAudit(frozenset(approved), frozenset(invalid))
