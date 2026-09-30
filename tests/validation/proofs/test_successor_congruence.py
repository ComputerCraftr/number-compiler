import pytest

from devtools.verification.collatz_spacetime import (
    CollatzCausalSpacetimeEngine,
    CollatzRadixField,
)
from number_compiler.arithmetic.contracts.successor_congruence import (
    ExactTargetCacheIdentity,
    SuccessorCongruenceAudit,
    SuccessorCongruenceViolation,
    SuccessorObservation,
)


def test_exact_target_identity_keeps_operator_and_occurrence_layers_separate() -> None:
    identity = ExactTargetCacheIdentity("action", "payload", False)
    assert identity.operator_cache_key == ("semantic-operator", "action")
    assert identity.exact_cache_key == ("exact-occurrence", "payload")

    proved = ExactTargetCacheIdentity("action", "payload", True)
    assert proved.exact_cache_key == ("proved-successor-class", "action")


def test_audit_never_promotes_sampling_to_a_global_congruence_proof() -> None:
    audit = SuccessorCongruenceAudit()
    audit.observe(SuccessorObservation("a", "x", "b", "y"))
    audit.observe(SuccessorObservation("a", "z", "b", "y"))
    assert audit.semantic_successor_closed("a")
    assert audit.exact_target_closed("a")
    with pytest.raises(SuccessorCongruenceViolation):
        audit.require_global_proof(carrier_complete=False)
    audit.require_global_proof(carrier_complete=True)


def test_collatz_carry_action_alias_is_not_a_temporal_state_quotient() -> None:
    engine = CollatzCausalSpacetimeEngine()
    three = engine.forcing_image(CollatzRadixField.from_value(3))
    eleven = engine.forcing_image(CollatzRadixField.from_value(11))
    assert three.forcing.class_id == eleven.forcing.class_id
    assert three.occurrence_key != eleven.occurrence_key
    # The bounded 3-adic observers distinguish these occurrences even though
    # the universal carry operator is shared; neither observer proves closure.
    assert three.residue3 != eleven.residue3
    assert three.forcing.canonical_key == eleven.forcing.canonical_key
    assert three.cache_identity.exact_cache_key != eleven.cache_identity.exact_cache_key

    audit = SuccessorCongruenceAudit()
    for source, value in ((three, 3), (eleven, 11)):
        target, _ = engine.advance_event_power(CollatzRadixField.from_value(value), 1)
        # Observe the explicitly requested endpoints independently. Lazy
        # production does not intern future normalized-tail occurrences.
        image = engine.forcing_image(target)
        audit.observe(
            SuccessorObservation(
                source.forcing.canonical_key,
                source.occurrence_key,
                image.forcing.canonical_key,
                image.occurrence_key,
            )
        )
    metrics = audit.metrics()
    assert metrics.successor_conflicts >= 1
    assert metrics.exact_target_conflicts >= 1
    with pytest.raises(SuccessorCongruenceViolation):
        audit.require_global_proof(carrier_complete=False)
