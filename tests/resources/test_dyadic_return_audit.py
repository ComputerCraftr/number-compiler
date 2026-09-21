"""Independent ownership checks for the shared dyadic return workspace."""

from __future__ import annotations

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicCycleSummary,
    DyadicReturnCycle,
    DyadicReturnImageID,
    DyadicReturnImageWorkspace,
    DyadicReturnLaw,
)
from number_compiler.resources.dyadic_return_payload_audit import (
    audit_dyadic_return_payloads,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.antihydra.arithmetic_images import (
    ANTIHYDRA_ARITHMETIC_LAW,
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)


def _assert_clean(ledger: ResourceLedger) -> None:
    audit = audit_registered_payloads(ledger)
    assert (
        audit.forbidden_future_payloads,
        audit.unbounded_future_integers,
        audit.unknown_payloads,
    ) == (0, 0, 0)
    assert all(row.accounting_delta == 0 for row in ledger.inventory())


def _literal_weighted_cycle(
    seed: int, horizon: int
) -> tuple[int, int, int, int, int | None, tuple[int, ...]]:
    state = seed
    odd_steps = 0
    delta = 0
    minimum = 0
    first_failure: int | None = None
    bits: list[int] = []
    for index in range(horizon):
        bit = state & 1
        bits.append(bit)
        odd_steps += bit
        delta += (-1, 3)[bit]
        minimum = min(minimum, delta)
        if first_failure is None and delta < 0:
            first_failure = index
        state = state // 2 if bit == 0 else 3 * state + 1
    return state, odd_steps, delta, minimum, first_failure, tuple(bits)


def test_collatz_and_antihydra_share_one_independently_audited_schema() -> None:
    ledger = ResourceLedger()
    collatz = CollatzPhysicalImageWorkspace(ledger, 27, 129)
    antihydra = AntihydraArithmeticImageWorkspace(ledger, 129)
    result = audit_dyadic_return_payloads(ledger)
    assert not result.invalid
    assert {id(collatz), id(antihydra)} <= result.approved
    _assert_clean(ledger)


def test_audit_rejects_mutated_second_child_residue_and_stale_image() -> None:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(ledger, 27, 129)
    child = next(node for node in workspace.sources if node.side == 2)
    old_residue = child.residue
    object.__setattr__(child, "residue", old_residue ^ 1)
    try:
        result = audit_dyadic_return_payloads(ledger)
        assert (workspace.image_owner, id(workspace)) in result.invalid
        assert id(workspace) not in result.approved
        assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
    finally:
        object.__setattr__(child, "residue", old_residue)

    old_image = child.before_image
    object.__setattr__(
        child,
        "before_image",
        DyadicReturnImageID(
            workspace.owner, workspace._IMAGE_KIND, len(workspace.images)
        ),
    )
    try:
        assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
    finally:
        object.__setattr__(child, "before_image", old_image)


def test_audit_rejects_foreign_second_child_parent_authority() -> None:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(ledger, 27, 129)
    foreign = CollatzPhysicalImageWorkspace(ledger, 31, 129)
    child = next(node for node in workspace.sources if node.side == 2)
    old_parent = child.parent
    object.__setattr__(child, "parent", foreign.root_source)
    try:
        result = audit_dyadic_return_payloads(ledger)
        assert (workspace.image_owner, id(workspace)) in result.invalid
        assert id(foreign) in result.approved
    finally:
        object.__setattr__(child, "parent", old_parent)


def test_audit_reconstructs_transfer_and_rejects_law_mutation() -> None:
    ledger = ResourceLedger()
    workspace = AntihydraArithmeticImageWorkspace(ledger, 129)
    leaf = next(node for node in workspace.support if node.branch_word is not None)
    transfer = leaf.transfer
    old_offset = transfer.offset
    object.__setattr__(transfer, "offset", old_offset + 2)
    try:
        assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
    finally:
        object.__setattr__(transfer, "offset", old_offset)

    old_gains = ANTIHYDRA_ARITHMETIC_LAW.gains
    object.__setattr__(ANTIHYDRA_ARITHMETIC_LAW, "gains", (True, 3))
    try:
        result = audit_dyadic_return_payloads(ledger)
        assert (workspace.image_owner, id(workspace)) in result.invalid
    finally:
        object.__setattr__(ANTIHYDRA_ARITHMETIC_LAW, "gains", old_gains)


def test_unknown_subclass_cannot_override_validation_to_gain_approval() -> None:
    class ForgedWorkspace(CollatzPhysicalImageWorkspace):
        def validate(self) -> None:
            return

    ledger = ResourceLedger()
    workspace = ForgedWorkspace(ledger, 27, 65)
    result = audit_dyadic_return_payloads(ledger)
    assert (workspace.image_owner, id(workspace)) in result.invalid
    assert id(workspace) not in result.approved
    assert audit_registered_payloads(ledger).forbidden_future_payloads > 0


def test_audit_preserves_images_and_charges_its_bounded_recomputation() -> None:
    ledger = ResourceLedger()
    CollatzPhysicalImageWorkspace(ledger, 27, 129)
    before = dict(ledger.counters)
    inventory = ledger.inventory()
    first = audit_dyadic_return_payloads(ledger)
    middle = dict(ledger.counters)
    second = audit_registered_payloads(ledger, fresh=True)
    assert not first.invalid
    assert (
        second.forbidden_future_payloads,
        second.unbounded_future_integers,
        second.unknown_payloads,
    ) == (0, 0, 0)
    assert inventory == ledger.inventory()
    for key, value in before.items():
        assert middle[key] == ledger.counters[key] == value
    steps = middle["dyadic_payload_audit_branch_steps"]
    bits = middle["dyadic_payload_audit_operand_bits"]
    assert steps > 0 and bits > 0
    assert ledger.counters["dyadic_payload_audit_branch_steps"] == 2 * steps
    assert ledger.counters["dyadic_payload_audit_operand_bits"] == 2 * bits


def test_foreign_handle_with_equal_shape_is_not_local_authority() -> None:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(ledger, 27, 65)
    child = next(node for node in workspace.sources if node.side == 2)
    old = child.before_image
    assert old is not None
    object.__setattr__(
        child,
        "before_image",
        DyadicReturnImageID(ArenaToken("foreign"), old.kind, old.local_id),
    )
    try:
        assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
    finally:
        object.__setattr__(child, "before_image", old)


def test_cycle_compression_is_bound_to_a_reachable_exact_source() -> None:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(ledger, 27, 1_024)
    summary = workspace.summary()
    assert summary.cycle is not None
    assert summary.cycle.entry_steps > 0
    assert ledger.counters["collatz_physical_cycle_compressions"] > 0
    assert ledger.counters["collatz_physical_leaf_steps"] <= 128
    assert len(workspace.support) < 64
    _assert_clean(ledger)

    # Nine has the same low three bits as the cycle state one, but it is not
    # itself a cycle member.  Its retained image must contain a real admitted
    # prefix rather than treating the residue class as singleton authority.
    same_residue = CollatzPhysicalImageWorkspace(ledger, 9, 256)
    same_residue_cycle = same_residue.summary().cycle
    assert same_residue_cycle is not None
    assert same_residue_cycle.entry_steps > 0
    _assert_clean(ledger)


def test_cycle_compression_reconstructs_every_exact_cycle_phase() -> None:
    for phase, seed in enumerate((1, 4, 2)):
        ledger = ResourceLedger()
        workspace = CollatzPhysicalImageWorkspace(ledger, seed, 128)
        cycle = workspace.summary().cycle
        assert cycle is not None
        assert cycle.entry_steps == 0
        assert cycle.cycle_phase == phase
        assert workspace.endpoint() == (1, 4, 2)[cycle.terminal_phase]
        _assert_clean(ledger)


def test_cycle_summary_cannot_be_resealed_with_an_unreachable_phase() -> None:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(ledger, 27, 1_024)
    support_index, support = next(
        (index, record)
        for index, record in enumerate(workspace.support)
        if record.cycle is not None and record.children is None
    )
    cycle = support.cycle
    assert cycle is not None
    law_cycle = workspace.law.cycle
    assert law_cycle is not None
    old_cycle = cycle
    forged_cycle = DyadicCycleSummary(
        cycle.entry_steps,
        (cycle.cycle_phase + 1) % len(law_cycle.states),
        cycle.cycles,
        cycle.remainder,
        cycle.terminal_phase,
        cycle.odd_steps,
        cycle.delta,
        cycle.minimum,
    )
    object.__setattr__(support, "cycle", forged_cycle)
    old_snapshot = workspace.support_snapshots[support_index]
    workspace.support_snapshots[support_index] = (
        support.width,
        support.residue,
        support.transfer.upper,
        support.transfer.offset,
        support.transfer.lower,
        support.odd_steps,
        support.delta,
        support.minimum,
        support.branch_word,
        support.children,
        support.cycle,
    )
    try:
        result = audit_dyadic_return_payloads(ledger)
        assert (workspace.image_owner, id(workspace)) in result.invalid
        assert id(workspace) not in result.approved
    finally:
        object.__setattr__(support, "cycle", old_cycle)
        workspace.support_snapshots[support_index] = old_snapshot


def test_audit_rejects_a_mutated_cycle_descriptor() -> None:
    ledger = ResourceLedger()
    workspace = CollatzPhysicalImageWorkspace(ledger, 27, 256)
    cycle = workspace.law.cycle
    assert cycle is not None
    old_states = cycle.states
    object.__setattr__(cycle, "states", (1, 2, 4))
    try:
        result = audit_dyadic_return_payloads(ledger)
        assert (workspace.image_owner, id(workspace)) in result.invalid
        assert id(workspace) not in result.approved
        assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
    finally:
        object.__setattr__(cycle, "states", old_states)


def test_generic_cycle_segments_and_negative_failure_match_literal_steps() -> None:
    law = DyadicReturnLaw(
        family="test-weighted-cycle",
        semantic_version="test-weighted-cycle-v1",
        gains=(1, 6),
        offsets=(0, 2),
        weights=(-1, 3),
        cycle=DyadicReturnCycle((1, 4, 2)),
    )
    horizons = (*range(9), 128)
    for seed in (1, 4, 2):
        for horizon in horizons:
            ledger = ResourceLedger()
            workspace = DyadicReturnImageWorkspace(ledger, seed, horizon, law)
            (
                endpoint,
                odd_steps,
                delta,
                minimum,
                first_failure,
                expected_bits,
            ) = _literal_weighted_cycle(seed, horizon)
            retained_bits: list[int] = []
            expected_start = 0
            for start, width, word in workspace.branch_segments():
                assert start == expected_start
                assert 0 < width <= workspace.MAX_LEAF_STEPS
                retained_bits.extend((word >> offset) & 1 for offset in range(width))
                expected_start += width
            assert expected_start == horizon
            assert tuple(retained_bits) == expected_bits
            assert workspace.endpoint() == endpoint
            assert workspace.odd_steps() == odd_steps
            assert workspace.delta() == delta
            assert workspace.minimum() == minimum
            assert workspace.first_failure_index() == first_failure
            _assert_clean(ledger)


def test_adapter_name_spoof_does_not_authorize_a_subclass() -> None:
    forged = type(
        "CollatzPhysicalImageWorkspace",
        (CollatzPhysicalImageWorkspace,),
        {"__module__": CollatzPhysicalImageWorkspace.__module__},
    )
    ledger = ResourceLedger()
    workspace = forged(ledger, 27, 65)
    result = audit_dyadic_return_payloads(ledger)
    assert (workspace.image_owner, id(workspace)) in result.invalid
    assert id(workspace) not in result.approved


def test_audit_charges_compositions_and_cycles() -> None:
    ledger = ResourceLedger()
    CollatzPhysicalImageWorkspace(ledger, 27, 1_024)
    assert not audit_dyadic_return_payloads(ledger).invalid
    assert ledger.counters["dyadic_payload_audit_compositions"] > 0
    assert ledger.counters["dyadic_payload_audit_cycle_checks"] > 0
    assert ledger.counters["dyadic_payload_audit_operand_bits"] > 0
