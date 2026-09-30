"""Output-complete primitive quotients and certified causal symmetries."""

from __future__ import annotations

from tests.support.assertions import assert_rejected_atomically

from array import array
from collections.abc import Callable, MutableSequence
from dataclasses import dataclass, replace
from typing import cast

import pytest

from number_compiler.arithmetic.automata.symmetry_powering import ActionTransform
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
    _effect_key,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    PrimitiveKernel,
)
from number_compiler.hashlife.interfaces.primitive_behavior import (
    LocalSymmetryWitness,
    PrimitiveBehaviorQuotient,
    PrimitiveBehaviorTable,
    PrimitiveBehaviorWork,
    capture_primitive_behavior,
    certify_local_symmetry,
    identity_symmetry,
    minimize_primitive_behavior,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.resources.ownership import audit_execution_ownership
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


@dataclass(frozen=True, slots=True)
class _TinyKernel:
    left_count: int
    right_count: int
    blank: int
    distinct_output: bool = False
    occurrence_event: bool = False

    @property
    def base(self) -> int:
        return 2

    def advance(self, side: BoundarySide, state: int, symbol: int) -> int:
        del side, symbol
        return state if self.distinct_output else 0

    def emit(self, left: int, symbol: int, right: int) -> int:
        del right
        return left if self.distinct_output else symbol

    def observe(self, left: int, symbol: int, right: int) -> tuple[int, ...]:
        del symbol, right
        return int(self.occurrence_event and left == 1), 0, 0


@dataclass(frozen=True, slots=True)
class _ReorderedKernel:
    """Two states whose canonical residual order reverses source order."""

    left_count: int = 2
    right_count: int = 1
    blank: int = 1

    @property
    def base(self) -> int:
        return 2

    def advance(self, side: BoundarySide, state: int, symbol: int) -> int:
        del side, symbol
        return state

    def emit(self, left: int, symbol: int, right: int) -> int:
        del symbol, right
        return 1 - left

    def observe(self, left: int, symbol: int, right: int) -> tuple[int, ...]:
        del left, symbol, right
        return 0, 0, 0


def _identity(name: str) -> SemanticIdentity:
    return SemanticIdentity(name, ("test-primitive", name))


def test_myhill_nerode_merges_only_complete_behavior_aliases() -> None:
    merged = minimize_primitive_behavior(
        capture_primitive_behavior(
            _TinyKernel(2, 1, 1),
            _identity("merged"),
        )
    )
    assert merged.left_classes == (0, 0)
    assert merged.left_count == 1

    distinct = minimize_primitive_behavior(
        capture_primitive_behavior(
            _TinyKernel(2, 1, 1, distinct_output=True),
            _identity("distinct"),
        )
    )
    assert distinct.left_classes[0] != distinct.left_classes[1]
    assert distinct.left_count == 2
    # Both states have the same exit for symbol zero only after a local reset,
    # but exact emitted output remains part of the residual and prevents aliasing.
    assert distinct.output(0, 0, 0) != distinct.output(1, 0, 0)


def test_occurrence_cocycle_distinction_prevents_false_residual_merge() -> None:
    plain = minimize_primitive_behavior(
        capture_primitive_behavior(
            _TinyKernel(2, 1, 1),
            _identity("plain-occurrence"),
        )
    )
    assert plain.left_classes == (0, 0)

    observed = minimize_primitive_behavior(
        capture_primitive_behavior(
            _TinyKernel(2, 1, 1, occurrence_event=True),
            _identity("event-occurrence"),
        )
    )
    assert observed.left_classes[0] != observed.left_classes[1]
    assert observed.observation(observed.left_classes[0], 0, 0) == (0, 0, 0)
    assert observed.observation(observed.left_classes[1], 0, 0) == (1, 0, 0)


def test_fixed_padded_leaf_channels_are_values_not_schema_names() -> None:
    table = capture_primitive_behavior(
        _TinyKernel(2, 1, 1, distinct_output=True),
        _identity("actual-thirteen-channels"),
    )
    disappearing = table.channel_values(1, 0, 0)
    growing = table.channel_values(0, 1, 0)
    assert disappearing == (1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0)
    assert growing == (0, 0, 0, 1, 0, 0, 1, 0, 0, 2, 0, 0, 0)

    changed = list(table.channels[0])
    changed[3] ^= 1
    forged = replace(table, channels=(tuple(changed), *table.channels[1:]))
    with pytest.raises(ValueError, match="channel behavior"):
        minimize_primitive_behavior(forged)


def test_projected_channels_use_canonical_class_coordinates() -> None:
    quotient = minimize_primitive_behavior(
        capture_primitive_behavior(
            _ReorderedKernel(),
            _identity("reordered-class-coordinates"),
        )
    )
    assert quotient.left_classes == (1, 0)
    for left in range(quotient.left_count):
        for symbol in range(quotient.alphabet_size):
            channels = quotient.channel_values(left, symbol, 0)
            assert channels[:2] == (
                quotient.left_transitions[left][symbol],
                quotient.right_transitions[0][symbol],
            )


def test_real_reverse_primitive_certificate_freezes_complete_outputs() -> None:
    arena = DiamondKernelArena(ResourceLedger())
    effect = BaseBlockEffect(10)
    handle = arena.intern(effect)
    kernel = arena.kernel(handle)
    quotient = arena.behavioral_quotient(handle)

    assert quotient.source_identity.behavior[0] == (
        "primitive-behavior",
        _effect_key(effect),
    )
    assert quotient.alphabet_size == 20
    assert quotient.left_count <= kernel.left_count
    assert quotient.right_count <= kernel.right_count
    for left in range(kernel.left_count):
        for symbol in (0, 9, 10, 18, 19):
            for right in range(kernel.right_count):
                assert quotient.output(
                    quotient.left_classes[left],
                    symbol,
                    quotient.right_classes[right],
                ) == kernel.emit(left, symbol, right)
    directed = identity_symmetry(quotient)
    with pytest.raises(ValueError, match="no certified"):
        directed.require(ActionTransform.MIRROR)
    before = arena.ledger.snapshot()
    assert arena.behavioral_quotient(handle) is quotient
    assert (arena.ledger.entries, arena.ledger.nodes) == (
        before.entries,
        before.nodes,
    )
    assert not audit_execution_ownership(arena.ledger).violations
    assert collect_ledger_metrics(arena.ledger).representation_boundary_complete == 1


def test_multiround_refinement_reads_frozen_emissions_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    effect = BaseBlockEffect(10)
    left = effect.boundary_universe(BoundarySide.LEFT)
    right = effect.boundary_universe(BoundarySide.RIGHT)
    assert left is not None and right is not None
    table = capture_primitive_behavior(
        PrimitiveKernel(effect, left, right, ledger),
        _identity("decimal-multiround-emissions"),
    )
    calls = {"channels": 0, "observations": 0}
    original_channels = PrimitiveBehaviorTable.channel_values
    original_observations = PrimitiveBehaviorTable.observation

    def channel_values(
        self: PrimitiveBehaviorTable, left: int, symbol: int, right: int
    ) -> tuple[int, ...]:
        calls["channels"] += 1
        return original_channels(self, left, symbol, right)

    def observation(
        self: PrimitiveBehaviorTable, left: int, symbol: int, right: int
    ) -> tuple[int, ...]:
        calls["observations"] += 1
        return original_observations(self, left, symbol, right)

    monkeypatch.setattr(PrimitiveBehaviorTable, "channel_values", channel_values)
    monkeypatch.setattr(PrimitiveBehaviorTable, "observation", observation)
    work = PrimitiveBehaviorWork()
    quotient = minimize_primitive_behavior(table, work=work)
    primitive_rows = table.left_count * table.alphabet_size * table.right_count
    projected_rows = quotient.left_count * table.alphabet_size * quotient.right_count

    assert quotient.refinement_rounds > 1
    assert calls == {
        "channels": projected_rows,
        "observations": projected_rows,
    }
    assert work.observation_checks == 2 * primitive_rows + 3 * projected_rows
    assert (
        work.successor_checks
        == quotient.refinement_rounds
        * (table.left_count + table.right_count)
        * table.alphabet_size
    )


def test_collatz_primitive_certificate_retains_odd_event_observation() -> None:
    arena = DiamondKernelArena(ResourceLedger())
    handle = arena.intern(CollatzPhysicalBlockEffect())
    kernel = arena.kernel(handle)
    quotient = arena.behavioral_quotient(handle)
    left = kernel.initial(BoundarySide.LEFT)
    right = kernel.initial(BoundarySide.RIGHT)
    assert quotient.observation(
        quotient.left_classes[left],
        1,
        quotient.right_classes[right],
    ) == (1, 0, 0)
    assert quotient.observation(
        quotient.left_classes[left],
        0,
        quotient.right_classes[right],
    ) == (0, 0, 0)
    report = collect_ledger_metrics(arena.ledger)
    assert report.primitive_behavioral_quotient_nodes == 1
    assert report.primitive_behavioral_class_population == (
        quotient.left_count + quotient.right_count
    )
    assert report.primitive_behavior_refinement_observation_checks > 0
    assert report.primitive_behavior_refinement_successor_checks > 0


def _finite_primitive(
    initial_left: int,
    outputs: bytes = bytes((0, 0, 1, 1, 0, 0, 1, 1)),
) -> FiniteBlockEffect:
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=2,
        right_count=2,
        alphabet_size=2,
        initial_left=initial_left,
        initial_right=0,
        left_transitions=array("I", (0, 0, 1, 1)),
        right_transitions=array("I", (0, 0, 1, 1)),
        outputs=outputs,
        kernel_name="custom-primitive",
        storage_bytes=24,
        uncompressed_bytes=24,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
        blank=1,
    )


def test_custom_finite_kernel_identity_retains_initial_and_emission_semantics() -> None:
    arena = DiamondKernelArena(ResourceLedger())
    first = arena.intern(_finite_primitive(0))
    another_initial = arena.intern(_finite_primitive(1))
    another_output = arena.intern(
        _finite_primitive(0, bytes((1, 1, 0, 0, 1, 1, 0, 0))),
    )
    assert len({first, another_initial, another_output}) == 3
    assert arena.kernel(first).initial(BoundarySide.LEFT) == 0
    assert arena.kernel(another_initial).initial(BoundarySide.LEFT) == 1
    assert arena.kernel(first).emit(0, 0, 0) != arena.kernel(another_output).emit(
        0,
        0,
        0,
    )


def test_primitive_behavior_table_bound_rejects_before_retained_mutation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.interfaces.diamond_kernel as kernel_module

    arena = DiamondKernelArena(ResourceLedger())
    before = arena.ledger.snapshot()
    monkeypatch.setattr(kernel_module, "MAX_PRIMITIVE_BEHAVIOR_TABLE_ENTRIES", 1)
    with pytest.raises(ValueError, match="fixed admission bound"):
        arena.intern(_finite_primitive(0))
    assert arena.ledger.snapshot() == before


def test_behavioral_certificate_is_deeply_immutable_and_budgeted_before_capture() -> (
    None
):
    arena = DiamondKernelArena(ResourceLedger())
    handle = arena.intern(BaseBlockEffect(2))
    quotient = arena.behavioral_quotient(handle)
    with pytest.raises((AttributeError, TypeError)):
        cast(MutableSequence[int], quotient.left_classes)[0] = 1
    with pytest.raises((AttributeError, TypeError)):
        cast(MutableSequence[MutableSequence[int]], quotient.left_transitions)[0][0] = 1

    exhausted = DiamondKernelArena(ResourceLedger())
    before = exhausted.ledger.snapshot()
    exhausted.ledger.tighten_limits(before.nodes, before.entries)
    output_work = before.counters.get("primitive_output_evaluations", 0)
    with pytest.raises(BlockContextBudgetExceeded, match="exceeded"):
        exhausted.intern(BaseBlockEffect(10))
    after = exhausted.ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)
    assert after.counters.get("primitive_output_evaluations", 0) == output_work


def test_powered_proof_machine_domain_cannot_enter_runtime_quotient() -> None:
    effect = FiniteBlockEffect(
        base=2,
        exponent=2,
        left_count=1,
        right_count=1,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 4),
        right_transitions=array("I", [0] * 4),
        outputs=bytes(range(4)),
        kernel_name="proof-only",
        storage_bytes=36,
        uncompressed_bytes=36,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
    arena = DiamondKernelArena(ResourceLedger())
    handle = arena.intern(effect)
    assert_rejected_atomically(
        arena.ledger,
        lambda: arena.behavioral_quotient(handle),
        ValueError,
        match="proof-machine",
    )


def test_identity_only_certificate_rejects_uncertified_d4_and_mirror() -> None:
    quotient = minimize_primitive_behavior(
        capture_primitive_behavior(
            _TinyKernel(2, 1, 1, distinct_output=True),
            _identity("directed"),
        )
    )
    certificate = identity_symmetry(quotient)
    assert (
        certificate.require(ActionTransform.IDENTITY).transform
        is ActionTransform.IDENTITY
    )
    with pytest.raises(ValueError, match="no certified"):
        certificate.require(ActionTransform.MIRROR)
    with pytest.raises(ValueError, match="unsupported D4"):
        certificate.require(ActionTransform(4))


def test_mirror_is_admitted_only_after_complete_emission_equivariance() -> None:
    quotient = minimize_primitive_behavior(
        capture_primitive_behavior(
            _TinyKernel(2, 2, 2),
            _identity("symmetric"),
        )
    )
    identity = LocalSymmetryWitness(
        ActionTransform.IDENTITY,
        (0, 1, 2),
        (0,),
        (0,),
        (0, 1, 2),
    )
    mirror = LocalSymmetryWitness(
        ActionTransform.MIRROR,
        (0, 1, 2),
        (0,),
        (0,),
        (0, 1, 2),
    )
    certificate = certify_local_symmetry(quotient, (identity, mirror))
    assert certificate.transforms == (ActionTransform.IDENTITY, ActionTransform.MIRROR)

    wrong_output = LocalSymmetryWitness(
        ActionTransform.MIRROR,
        (0, 1, 2),
        (0,),
        (0,),
        (1, 0, 2),
    )
    with pytest.raises(ValueError, match="emission"):
        certify_local_symmetry(quotient, (identity, wrong_output))


def test_symmetry_cannot_move_blank_activity_semantics() -> None:
    quotient = minimize_primitive_behavior(
        capture_primitive_behavior(
            _TinyKernel(1, 1, 1),
            _identity("blank-preservation"),
        )
    )
    identity = LocalSymmetryWitness(
        ActionTransform.IDENTITY,
        (0, 1),
        (0,),
        (0,),
        (0, 1),
    )
    moves_blank = LocalSymmetryWitness(
        ActionTransform.CONJUGATE,
        (1, 0),
        (0,),
        (0,),
        (1, 0),
    )
    with pytest.raises(ValueError, match="blank/activity"):
        certify_local_symmetry(quotient, (identity, moves_blank))


def test_symmetry_maps_must_form_the_declared_group() -> None:
    quotient = minimize_primitive_behavior(
        capture_primitive_behavior(
            _TinyKernel(1, 1, 2),
            _identity("group"),
        )
    )
    identity = LocalSymmetryWitness(
        ActionTransform.IDENTITY,
        (0, 1, 2),
        (0,),
        (0,),
        (0, 1, 2),
    )
    conjugate = LocalSymmetryWitness(
        ActionTransform.CONJUGATE,
        (1, 0, 2),
        (0,),
        (0,),
        (1, 0, 2),
    )
    # This transform preserves the tiny transition/output law and is an
    # involution, so the two-element subgroup is accepted.
    certificate = certify_local_symmetry(quotient, (identity, conjugate))
    assert certificate.require(ActionTransform.CONJUGATE) == conjugate


@pytest.mark.parametrize("alias", (True, 1.0, -1))
def test_primitive_behavior_rejects_numeric_alias_domains(alias: object) -> None:
    kernel = _TinyKernel(cast(int, alias), 1, 1)
    with pytest.raises(ValueError):
        capture_primitive_behavior(kernel, _identity("aliases"))


def test_quotient_audit_deduplicates_references_only_within_one_snapshot(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.hashlife.interfaces.primitive_behavior as behavior
    from number_compiler.resources.payload_audit import audit_registered_payloads

    arena = DiamondKernelArena(ResourceLedger())
    handle = arena.intern(BaseBlockEffect(2))
    quotient = arena.behavioral_quotient(handle)
    validate = behavior.validate_primitive_behavior_quotient
    calls = []

    def counted(
        record: PrimitiveBehaviorQuotient,
        *,
        validate_identity: Callable[
            [SemanticIdentity], None
        ] = SemanticIdentity.validate,
    ) -> None:
        calls.append(record)
        return validate(record, validate_identity=validate_identity)

    monkeypatch.setattr(behavior, "validate_primitive_behavior_quotient", counted)
    before = arena.ledger.snapshot()
    assert audit_registered_payloads(arena.ledger).forbidden_future_payloads == 0
    assert arena.ledger.snapshot() == before
    assert len(calls) == 1 and calls[0] is quotient
    original = quotient.channels
    object.__setattr__(quotient, "channels", ())
    try:
        assert audit_registered_payloads(arena.ledger).forbidden_future_payloads > 0
        assert len(calls) == 2 and calls[1] is quotient
    finally:
        object.__setattr__(quotient, "channels", original)
