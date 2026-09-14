"""Proof audits distinguish transfer aliases from temporal behavior."""

from dataclasses import replace
from typing import cast

import pytest

from devtools.proofs.active_behavior_profiles import (
    BehaviorAuditWork,
    BehaviorGenerator,
    BehaviorGeneratorSort,
    FiniteBehaviorProposal,
    audit_finite_behavior_profile,
    certify_reverse_leaf_carry_consumer,
    reverse_leaf_carry_consumer_system,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.hashlife.behavior.future_behavior import (
    UnsupportedFutureBehaviorProfile,
)
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.resources.ledger import ResourceLedger
from tests.arithmetic.contracts.test_tile_kernel import _runtime, _tile


def _identity(name: str) -> SemanticIdentity:
    return SemanticIdentity("", ("active-profile-test", name))


def _aliased_system() -> FiniteBehaviorProposal:
    temporal = BehaviorGenerator(BehaviorGeneratorSort.TEMPORAL, _identity("step"))
    spatial = (
        (0, 0, 2),
        (1, 0, 2),
        (2, 2, 2),
    )
    return FiniteBehaviorProposal(
        _identity("kernel"),
        _identity("continuation"),
        ("consumer-bit",),
        ((0,), (0,), (1,)),
        (temporal,),
        ((1, 0, 2),),
        spatial,
        "synthetic-active-interval-v1",
        False,
    )


def test_active_certificate_finds_positive_alias_and_spatial_congruence() -> None:
    work = BehaviorAuditWork()
    certificate = audit_finite_behavior_profile(_aliased_system(), work=work)
    assert certificate.class_count == 2
    assert certificate.project(0) == certificate.project(1)
    assert certificate.project(0) != certificate.project(2)
    zero = certificate.project(0)
    one = certificate.project(2)
    assert certificate.successor(0, zero) == zero
    assert certificate.compose_spatial(zero, one) == one
    assert certificate.compose_spatial(one, zero) == one
    assert work.successor_checks > 0
    assert work.spatial_checks > 0


def test_identity_observing_profile_refuses_an_alias() -> None:
    with pytest.raises(UnsupportedFutureBehaviorProfile, match="cannot merge"):
        audit_finite_behavior_profile(
            replace(_aliased_system(), identity_observing=True)
        )


def test_spatial_generator_cannot_masquerade_as_temporal_closure() -> None:
    generator = BehaviorGenerator(
        BehaviorGeneratorSort.SPATIAL_PREFIX,
        _identity("prefix"),
    )
    with pytest.raises(ValueError, match="temporal generator"):
        FiniteBehaviorProposal(
            _identity("kernel"),
            _identity("continuation"),
            ("carry",),
            ((0,), (1,)),
            (generator,),
            ((0, 1),),
            ((0, 1), (1, 1)),
            "two-state-spatial-only-v1",
            False,
        )


def test_malformed_spatial_matrix_rejects_before_refinement() -> None:
    system = _aliased_system()
    assert system.spatial_composition is not None
    spatial = system.spatial_composition
    for malformed in (
        spatial[:-1],
        (*spatial[:-1], (0, 1)),
        (*spatial[:-1], (0, 1, True)),
    ):
        with pytest.raises(ValueError, match="spatial table"):
            replace(system, spatial_composition=malformed)


@pytest.mark.parametrize("base", (2, 3, 4, 5, 10))
def test_reverse_leaf_carry_aliases_are_rejected_by_temporal_successors(
    base: int,
) -> None:
    kernels = DiamondKernelArena(ResourceLedger())
    quotient = kernels.behavioral_quotient(kernels.intern(BaseBlockEffect(base)))
    system = reverse_leaf_carry_consumer_system(quotient, base)
    certificate = audit_finite_behavior_profile(system)

    # LT/EQ/GT is useful as a spatial transfer observation, but every symbol
    # becomes distinct once every exact primitive output context is admitted.
    assert certificate.class_count == quotient.alphabet_size
    assert len(set(certificate.state_classes)) == quotient.alphabet_size
    if base > 2:
        assert system.observation_values[0] == system.observation_values[1]
        assert certificate.project(0) != certificate.project(1)
        assert any(row[0] != row[1] for row in system.transitions)


def test_reverse_profile_has_real_temporal_generators_and_no_spatial_claim() -> None:
    kernels = DiamondKernelArena(ResourceLedger())
    quotient = kernels.behavioral_quotient(kernels.intern(BaseBlockEffect(3)))
    certificate = certify_reverse_leaf_carry_consumer(quotient, 3)
    assert all(
        generator.sort is BehaviorGeneratorSort.TEMPORAL
        for generator in certificate.profile.generators
    )
    assert certificate.spatial_composition is None
    with pytest.raises(ValueError, match="no certified spatial composition"):
        certificate.compose_spatial(0, 0)
    with pytest.raises(ValueError, match="certified spatial composition"):
        certificate.require_macrocell_closure()


def test_nonblank_interval_interface_alias_is_not_temporally_closed() -> None:
    """A real P2 alias splits at P4, so LocalInterfaceID is not the class."""
    _ledger, tiles, adapter, primitive, scheduler = _runtime(BaseBlockEffect(3))
    engine = CausalTileEngine(scheduler)
    words = ((0, 0, 0, 0), (0, 1, 0, 0), (3, 0, 0, 0))
    leases = [_tile(tiles, adapter, primitive, word) for word in words]
    try:
        interfaces: dict[int, list[int]] = {}
        for exponent in (2, 4):
            action = adapter.power(primitive, exponent)
            interfaces[exponent] = [
                engine.interface(
                    action,
                    lease.tile,
                    engine._initial(action, 0),
                    engine._initial(action, 1),
                ).interface.local_id
                for lease in leases
            ]
        assert len(set(interfaces[2])) == 1
        assert len(set(interfaces[4])) == len(words)
    finally:
        for lease in leases:
            lease.close()


def test_active_certificate_detects_mutated_proof_payload() -> None:
    certificate = audit_finite_behavior_profile(_aliased_system())
    with pytest.raises(ValueError, match="digest"):
        replace(certificate, transitions=((0, 0),))


@pytest.mark.parametrize("alias", (True, 0.0))
def test_active_profile_rejects_numeric_aliases(alias: object) -> None:
    system = _aliased_system()
    with pytest.raises((TypeError, ValueError)):
        replace(system, version=cast(int, alias))
