"""Successor-closed blank behavior stays narrow, scoped, and budgeted."""

from dataclasses import replace
from hashlib import sha256
from typing import Never, cast

import pytest

from devtools.proofs.immutable_artifacts import REGISTRY, ArtifactKey
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BoundarySide,
    _effect_key,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.behavior.future_behavior import (
    QUIESCENT_OBSERVATIONS,
    FutureBehaviorClassID,
    FutureBehaviorProfile,
    FutureBehaviorProfileID,
    FutureBehaviorWork,
    UnsupportedFutureBehaviorProfile,
    certify_quiescent_blank,
)
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    PrimitiveKernel,
)
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.interfaces.primitive_behavior import (
    PRIMITIVE_CHANNEL_CONTRACT,
    PRIMITIVE_OCCURRENCE_SCHEMA,
    PrimitiveBehaviorQuotient,
)
from number_compiler.resources.ledger import ResourceLedger


def _behavior(base: int) -> tuple[PrimitiveKernel, PrimitiveBehaviorQuotient]:
    effect = BaseBlockEffect(base)
    recipe = (
        _effect_key(effect),
        PRIMITIVE_CHANNEL_CONTRACT,
        PRIMITIVE_OCCURRENCE_SCHEMA,
    )
    digest = sha256(repr(recipe).encode("utf-8")).hexdigest()

    def build() -> PrimitiveBehaviorQuotient:
        kernels = DiamondKernelArena(ResourceLedger())
        handle = kernels.intern(effect)
        return kernels.behavioral_quotient(handle)

    quotient, _hit = REGISTRY.obtain(
        ArtifactKey("primitive-behavior-quotient", digest),
        build,
    )
    left = effect.boundary_universe(BoundarySide.LEFT)
    right = effect.boundary_universe(BoundarySide.RIGHT)
    assert left is not None and right is not None
    return PrimitiveKernel(effect, left, right, ResourceLedger(), quotient), quotient


@pytest.mark.parametrize("base", (2, 3, 4, 5, 10))
def test_blank_certificate_is_a_genuine_greatest_fixed_point(base: int) -> None:
    kernel, quotient = _behavior(base)
    certificate = certify_quiescent_blank(quotient)
    original_initial = kernel.initial(BoundarySide.LEFT)
    assert type(original_initial) is int
    initial = quotient.left_classes[original_initial]
    assert initial in certificate.safe_blank_left_states
    assert certificate.absorbing_blank_left_states
    for left in certificate.safe_blank_left_states:
        assert certificate.left_blank_transition[left] in (
            certificate.safe_blank_left_states
        )
        for right in range(quotient.right_count):
            assert quotient.output(left, quotient.blank, right) == quotient.blank
            assert quotient.observation(left, quotient.blank, right) == (0, 0, 0)
    for left in certificate.absorbing_blank_left_states:
        for symbol in range(quotient.alphabet_size):
            assert quotient.left_transitions[left][symbol] in (
                certificate.absorbing_blank_left_states
            )
            for right in range(quotient.right_count):
                assert quotient.output(left, symbol, right) == quotient.blank
                assert quotient.observation(left, symbol, right) == (0, 0, 0)


def test_quotient_arena_owns_one_canonical_blank_profile_and_class() -> None:
    _kernel, quotient = _behavior(10)
    ledger = ResourceLedger()
    arena = DiamondQuotientArena(SemanticFunctionArena(ledger))
    profile, behavior = arena.admit_quiescent_blank(quotient)
    assert arena.admit_quiescent_blank(quotient) == (profile, behavior)
    record = arena.resolve_future_behavior(behavior)
    declared = arena.resolve_future_profile(profile)
    assert record.profile == profile
    assert record.output_symbol == declared.blank == quotient.blank
    assert not record.active and record.termination
    assert ledger.counters["future_behavior_new_classes"] == 1
    assert ledger.counters["future_behavior_profile_early_hits"] == 1


def test_identity_digit_profile_cannot_reuse_blank_transfer_certificate() -> None:
    _kernel, quotient = _behavior(3)
    certificate = certify_quiescent_blank(quotient)
    profile = FutureBehaviorProfile(
        certificate.kernel,
        certificate.continuation,
        certificate.alphabet_size,
        certificate.blank,
        QUIESCENT_OBSERVATIONS,
        certificate.safe_blank_left_states,
        "nonempty-uniform-blank-dyadic-v1",
        "primitive-zero-occurrence-cocycle-v1",
        1,
        certificate.semantic_digest,
    )
    with pytest.raises(ValueError, match="incomplete observation"):
        replace(profile, observations=(*profile.observations, "identity-digit"))


@pytest.mark.parametrize("alias", (True, 0.0))
def test_future_behavior_numeric_aliases_reject_before_lookup(alias: object) -> None:
    _kernel, quotient = _behavior(3)
    arena = DiamondQuotientArena(SemanticFunctionArena(ResourceLedger()))
    profile, behavior = arena.admit_quiescent_blank(quotient)
    with pytest.raises((TypeError, ValueError)):
        arena.resolve_future_profile(
            FutureBehaviorProfileID(profile.owner, profile.kind, cast(int, alias))
        )
    with pytest.raises((TypeError, ValueError)):
        arena.resolve_future_behavior(
            FutureBehaviorClassID(behavior.owner, behavior.kind, cast(int, alias))
        )


def test_foreign_future_behavior_rejects_before_warm_lookup() -> None:
    _kernel, quotient = _behavior(3)
    first = DiamondQuotientArena(SemanticFunctionArena(ResourceLedger()))
    second = DiamondQuotientArena(SemanticFunctionArena(ResourceLedger()))
    profile, behavior = first.admit_quiescent_blank(quotient)
    with pytest.raises(ValueError, match="different arena"):
        second.resolve_future_profile(profile)
    with pytest.raises(ValueError, match="different arena"):
        second.resolve_future_behavior(behavior)


def test_warm_admission_skips_refinement_and_rejects_forged_tables(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _kernel, quotient = _behavior(3)
    ledger = ResourceLedger()
    arena = DiamondQuotientArena(SemanticFunctionArena(ledger))
    admitted = arena.admit_quiescent_blank(quotient)
    work = ledger.counters["future_behavior_classification_work"]

    def forbidden(_quotient: PrimitiveBehaviorQuotient) -> Never:
        raise AssertionError("warm profile admission reran refinement")

    monkeypatch.setattr(
        "number_compiler.hashlife.behavior.quiescent_admission.certify_quiescent_blank",
        forbidden,
    )
    monkeypatch.setattr(SemanticIdentity, "__post_init__", forbidden)
    assert arena.admit_quiescent_blank(quotient) == admitted
    assert ledger.counters["future_behavior_classification_work"] == work
    changed_outputs = list(quotient.outputs)
    changed_outputs[0] = (changed_outputs[0] + 1) % quotient.alphabet_size
    forged = replace(quotient, outputs=tuple(changed_outputs))
    with pytest.raises(ValueError, match="conflicts with its admitted authority"):
        arena.admit_quiescent_blank(forged)


def test_publication_snapshots_reject_numeric_and_identity_alias_mutation() -> None:
    _kernel, quotient = _behavior(3)
    arena = DiamondQuotientArena(SemanticFunctionArena(ResourceLedger()))
    profile_id, behavior_id = arena.admit_quiescent_blank(quotient)
    profile = arena.resolve_future_profile(profile_id)
    behavior = arena.resolve_future_behavior(behavior_id)

    object.__setattr__(profile, "alphabet_size", True)
    with pytest.raises(ValueError, match="profile changed"):
        arena.resolve_future_profile(profile_id)
    object.__setattr__(profile, "alphabet_size", quotient.alphabet_size)

    object.__setattr__(behavior, "output_symbol", float(quotient.blank))
    with pytest.raises(ValueError, match="class changed"):
        arena.resolve_future_behavior(behavior_id)
    object.__setattr__(behavior, "output_symbol", quotient.blank)

    original_digest = profile.kernel.digest
    object.__setattr__(profile.kernel, "digest", "0" * 64)
    with pytest.raises(ValueError, match="profile changed"):
        arena.resolve_future_profile(profile_id)
    object.__setattr__(profile.kernel, "digest", original_digest)


def test_admission_snapshot_rejects_in_place_quotient_table_replacement() -> None:
    _kernel, quotient = _behavior(3)
    arena = DiamondQuotientArena(SemanticFunctionArena(ResourceLedger()))
    arena.admit_quiescent_blank(quotient)
    original = quotient.outputs
    changed = list(original)
    changed[0] = (changed[0] + 1) % quotient.alphabet_size
    object.__setattr__(quotient, "outputs", tuple(changed))
    try:
        with pytest.raises(ValueError, match="conflicts with its admitted authority"):
            arena.admit_quiescent_blank(quotient)
    finally:
        object.__setattr__(quotient, "outputs", original)


def test_blank_behavior_budget_failure_publishes_nothing() -> None:
    _kernel, quotient = _behavior(3)
    ledger = ResourceLedger(max_cache_entries=0)
    arena = DiamondQuotientArena(SemanticFunctionArena(ledger))
    before = ledger.snapshot()
    with pytest.raises(BlockContextBudgetExceeded):
        arena.admit_quiescent_blank(quotient)
    assert not arena._future_profiles
    assert not arena._future_profile_keys
    assert not arena._future_classes
    assert not arena._future_class_keys
    after = ledger.snapshot()
    assert (after.entries, after.nodes) == (before.entries, before.nodes)


def test_failed_blank_refinement_counts_all_completed_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _kernel, quotient = _behavior(3)
    ledger = ResourceLedger()
    arena = DiamondQuotientArena(SemanticFunctionArena(ledger))

    def unsupported(
        _quotient: PrimitiveBehaviorQuotient,
        *,
        work: FutureBehaviorWork,
    ) -> None:
        work.observation_checks = 7
        work.successor_checks = 5
        work.refinement_rounds = 3
        raise UnsupportedFutureBehaviorProfile("injected unsupported profile")

    monkeypatch.setattr(
        "number_compiler.hashlife.behavior.quiescent_admission.certify_quiescent_blank",
        unsupported,
    )
    with pytest.raises(UnsupportedFutureBehaviorProfile):
        arena.admit_quiescent_blank(quotient)
    assert ledger.counters["future_behavior_refinement_observation_checks"] == 7
    assert ledger.counters["future_behavior_refinement_successor_checks"] == 5
    assert ledger.counters["future_behavior_classification_work"] == 3


def test_read_only_admission_probe_and_cross_arena_rollback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _kernel, quotient = _behavior(3)
    ledger = ResourceLedger()
    arena = DiamondQuotientArena(SemanticFunctionArena(ledger))
    assert arena.lookup_quiescent_blank(quotient) is None
    admitted = arena.admit_quiescent_blank(quotient)
    counters = dict(ledger.counters)

    def forbidden(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("read-only admission probe evaluated semantics")

    monkeypatch.setattr(SemanticIdentity, "__post_init__", forbidden)
    assert arena.lookup_quiescent_blank(quotient) == admitted
    assert ledger.counters == counters
    monkeypatch.undo()
    first_profile = admitted[0].local_id
    arena.rollback_quiescent_blank_admission(quotient, *admitted)
    assert arena.lookup_quiescent_blank(quotient) is None
    replacement = arena.admit_quiescent_blank(quotient)
    assert replacement[0].local_id > first_profile
