"""Independent admission of fixed-width Antihydra arithmetic cache records.

No field is reclassified as geometry. A record must equal the canonical
composition of at most 64 discovered branches, and its actual owner/storage
must reconcile. This says nothing about source-discovery complexity or the
literal TM refinement of the arithmetic law.
"""

from __future__ import annotations

from dataclasses import fields

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.physical_support_payload_audit import (
    PhysicalSupportPayloadAudit,
)


def canonical_cylinder(value: object, ledger: ResourceLedger) -> bool:
    from number_compiler.sequences.antihydra.blocks import Cylinder, kernel

    if type(value) is not Cylinder:
        return False
    w, r = value.width, value.residue
    if type(w) is not int or not 1 <= w <= 64:
        return False
    if type(r) is not int or not 0 <= r < 1 << w:
        return False
    # Bound malicious inputs before comparing or doing arithmetic on them.
    if any(
        type(getattr(value, f.name)) is not int
        or abs(getattr(value, f.name)).bit_length() > 4 * w + 10
        for f in fields(value)
    ):
        return False
    source, remaining = r, w
    result: Cylinder | None = None
    while remaining:
        size = min(8, remaining)
        leaf = kernel(source % (1 << size), size)
        source = 3**size * (source >> size) + leaf.output
        ledger.bump("antihydra_payload_audit_branch_steps", size)
        if result is None:
            result = leaf
        else:
            result = result.then(leaf)
            ledger.bump("antihydra_payload_audit_compositions")
        remaining -= size
    return value == result


def canonical_arithmetic_cylinder(value: object, ledger: ResourceLedger) -> bool:
    from number_compiler.sequences.antihydra.blocks import (
        ArithmeticCylinder,
        arithmetic_kernel,
    )

    if type(value) is not ArithmeticCylinder:
        return False
    w, r = value.width, value.residue
    if type(w) is not int or not 1 <= w <= 64:
        return False
    if type(r) is not int or not 0 <= r < 1 << w:
        return False
    if any(
        type(getattr(value, field.name)) is not int
        or abs(getattr(value, field.name)).bit_length() > 2 * w + 10
        for field in fields(value)
    ):
        return False
    source, remaining = r, w
    result: ArithmeticCylinder | None = None
    while remaining:
        size = min(8, remaining)
        leaf = arithmetic_kernel(source % (1 << size), size)
        source = 3**size * (source >> size) + leaf.output
        ledger.bump("antihydra_payload_audit_arithmetic_branch_steps", size)
        result = leaf if result is None else result.then(leaf)
        remaining -= size
    return value == result


def audit_antihydra_payloads(ledger: ResourceLedger) -> PhysicalSupportPayloadAudit:
    from number_compiler.hashlife.execution.source_bound_images import (
        SourceBoundSchedulerCore,
    )
    from number_compiler.sequences.antihydra.blocks import (
        arithmetic_kernel,
        kernel,
        physical_roof,
        terminal_effect,
    )
    from number_compiler.sequences.antihydra.projection_core import (
        AntihydraProjectionDriver,
        _AntihydraFragmentAdapter,
    )
    from number_compiler.sequences.antihydra.projection_fragments import (
        ProjectionFragment,
        ProjectionFragmentCache,
        ProjectionFragmentKey,
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

    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    containers = dict(ledger.iter_containers())
    inventory = {row.owner: row for row in ledger.inventory()}
    roots = tuple(ledger.iter_execution_roots())
    for root in roots:
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
                for fragment_key, fragment in root.fragments.items():
                    term = terms.get(getattr(fragment_key, "source_owner", -1))
                    segment = None
                    entering_h, entering_balance = 8, 0
                    entering_head, entering_time = 1, 11
                    if term is not None:
                        for item in term.segments:
                            if item.start == getattr(fragment_key, "start", -1):
                                segment = item
                                break
                            roof = physical_roof(item.cylinder)
                            (
                                entering_h,
                                entering_balance,
                                left,
                                right,
                            ) = roof.apply(entering_h, entering_balance)
                            entering_head += right - left
                            entering_time += right + left
                            ledger.bump(
                                "antihydra_payload_audit_projection_fragment_steps",
                                item.cylinder.width,
                            )
                    spatial_phase = (
                        fragment_key.spatial_width
                        * (2 if fragment_key.spatial_sign == -1 else 1)
                        if type(fragment_key) is ProjectionFragmentKey
                        else 0
                    )
                    temporal_phase = (
                        fragment_key.temporal_width
                        * (2 if fragment_key.temporal_sign == -1 else 1)
                        if type(fragment_key) is ProjectionFragmentKey
                        else 0
                    )
                    bound = (
                        type(fragment_key) is ProjectionFragmentKey
                        and type(fragment) is ProjectionFragment
                        and root.matches_seal(fragment_key, fragment)
                        and fragment.key == fragment_key
                        and term is not None
                        and fragment_key.requested == term.requested
                        and type(segment) is ArithmeticSegment
                        and term._physical is not None
                        and not term._physical.halted
                        and entering_balance + segment.cylinder.minimum >= 0
                        and fragment_key.head_phase == entering_head % spatial_phase
                        and fragment_key.time_phase == entering_time % temporal_phase
                        and fragment_key.cylinder
                        == (
                            segment.cylinder.width,
                            segment.cylinder.residue,
                            segment.cylinder.output,
                            segment.cylinder.delta,
                            segment.cylinder.minimum,
                            segment.cylinder.parity_word,
                        )
                        and 1 <= fragment_key.spatial_width <= 64
                        and 1 <= fragment_key.temporal_width <= 64
                        and fragment_key.spatial_sign in (-1, 1)
                        and fragment_key.temporal_sign in (-1, 1)
                        and type(fragment_key.modulus) is int
                        and fragment_key.modulus >= 2
                    )
                    if bound:
                        try:
                            fragment.validate()
                        except ValueError:
                            bound = False
                    if bound:
                        approved.update((id(fragment_key), id(fragment)))
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
                        "segments",
                        "physical_owner",
                        "physical_publications",
                        "_result",
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
                    and containers.get(owner) is root.segments
                    and inventory[owner].role == "arithmetic_cylinder_support"
                    and inventory[owner].accounting_delta == 0
                    and len(root.segments) <= (root.requested + 63) // 64
                    and type(root.physical_owner) is int
                    and containers.get(root.physical_owner)
                    is root.physical_publications
                    and inventory[root.physical_owner].role == "physical_result"
                    and inventory[root.physical_owner].accounting_delta == 0
                    and len(root.physical_publications) <= 1
                )
                h, balance, minimum, start = 8, 0, 0, 0
                first_failure: int | None = None
                for segment in root.segments:
                    bound = (
                        type(segment) is ArithmeticSegment
                        and type(segment.start) is int
                        and segment.start == start
                        and canonical_arithmetic_cylinder(segment.cylinder, ledger)
                        and segment.cylinder.residue
                        == h % (1 << segment.cylinder.width)
                    )
                    if not bound:
                        valid = False
                        invalid.add((owner, id(segment)))
                        continue
                    approved.update((id(segment), id(segment.cylinder)))
                    if first_failure is None and balance + segment.cylinder.minimum < 0:
                        local_h, local_balance = h, balance
                        for offset in range(segment.cylinder.width):
                            leaf = arithmetic_kernel(local_h & 1, 1)
                            local_h, local_balance = leaf.advance(
                                local_h, local_balance
                            )
                            ledger.bump("antihydra_payload_audit_failure_steps")
                            if local_balance < 0:
                                first_failure = start + offset
                                break
                    old_balance = balance
                    h, balance = segment.cylinder.advance(h, balance)
                    minimum = min(minimum, old_balance + segment.cylinder.minimum)
                    start += segment.cylinder.width
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
                    if valid:
                        result.require_source()
                    approved.add(id(result))
                physical = root._physical
                if physical is not None:
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
                    if valid:
                        physical.require_source()
                    approved.update((id(publication), id(physical)))
                if valid:
                    approved.update(
                        (id(root), id(root.segments), id(root.physical_publications))
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
                valid &= (
                    type(driver) is AntihydraProjectionDriver
                    and type(adapter) is _AntihydraFragmentAdapter
                    and type(core) is SourceBoundSchedulerCore
                    and adapter.ledger is ledger
                    and core.ledger is ledger
                    and adapter.projection is None
                    and adapter.key is None
                    and adapter.block is None
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
