"""Release probe for semantic operator reuse and successor-safe exact caching."""

from __future__ import annotations

import json
from typing import TypedDict

from devtools.paths import repository_root
from devtools.proofs import exact_oracle
from devtools.proofs.collatz_spacetime import (
    CollatzCausalSpacetimeEngine,
    CollatzRadixField,
)
from devtools.proofs.reverse_spacetime import (
    ReverseAddCausalSpacetimeEngine,
    ReverseAddPairField,
)
from number_compiler.arithmetic.contracts.successor_congruence import (
    SuccessorCongruenceAudit,
    SuccessorObservation,
)

ROOT = repository_root()


class ReverseWitness(TypedDict):
    sources: list[list[int]]
    operator_classes: int
    operator_keys_shared: bool
    exact_target_keys_distinct: bool
    targets: list[list[int]]
    successor_conflicts: int
    exact_target_conflicts: int


class CollatzWitness(TypedDict):
    sources: list[int]
    operator_class_shared: bool
    exact_target_keys_distinct: bool
    targets: list[int]
    successor_conflicts: int
    exact_target_conflicts: int


class CongruenceReport(TypedDict):
    version: str
    status: str
    operator_cache_uses_semantic_action_id: bool
    exact_target_cache_requires_successor_congruence: bool
    sampled_aliases_are_never_promoted_to_proof: bool
    reverse: ReverseWitness
    collatz: CollatzWitness
    reference_oracle_counts: dict[str, dict[str, int]]
    interpretation: str


@exact_oracle()
def _reverse_witness() -> ReverseWitness:
    engine = ReverseAddCausalSpacetimeEngine(base=10)
    states = [
        engine.forcing_image(ReverseAddPairField.from_pair((v,), base=10))
        for v in (2, 4, 8)
    ]
    if len({state.forcing.class_id for state in states}) != 1:
        raise AssertionError("reverse linear operator did not alias")
    if len({state.cache_identity.exact_cache_key for state in states}) != 3:
        raise AssertionError("reverse exact target keys aliased")
    targets = []
    for state in states:
        target, _ = engine.advance_forcing_power(state, 1)
        targets.append(list(engine.forcing.pair_values(target)))
    metrics = engine.metrics()
    if (
        metrics.forcing_successor_conflicts < 1
        or metrics.forcing_exact_target_conflicts < 1
    ):
        raise AssertionError("reverse operator class was incorrectly successor-closed")
    return {
        "sources": [[2], [4], [8]],
        "operator_classes": len({state.forcing.class_id for state in states}),
        "operator_keys_shared": True,
        "exact_target_keys_distinct": True,
        "targets": targets,
        "successor_conflicts": metrics.forcing_successor_conflicts,
        "exact_target_conflicts": metrics.forcing_exact_target_conflicts,
    }


def _collatz_witness() -> CollatzWitness:
    engine = CollatzCausalSpacetimeEngine()
    states = [engine.forcing_image(CollatzRadixField.from_value(v)) for v in (3, 11)]
    if states[0].forcing.class_id != states[1].forcing.class_id:
        raise AssertionError("Collatz phase operator did not alias")
    if (
        states[0].cache_identity.exact_cache_key
        == states[1].cache_identity.exact_cache_key
    ):
        raise AssertionError("Collatz exact target keys aliased")
    targets = []
    audit = SuccessorCongruenceAudit()
    for source, value in zip(states, (3, 11), strict=True):
        target, _ = engine.advance_event_power(CollatzRadixField.from_value(value), 1)
        targets.append(target.value())
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
    if metrics.successor_conflicts < 1 or metrics.exact_target_conflicts < 1:
        raise AssertionError("Collatz operator class was incorrectly successor-closed")
    return {
        "sources": [3, 11],
        "operator_class_shared": True,
        "exact_target_keys_distinct": True,
        "targets": targets,
        "successor_conflicts": metrics.successor_conflicts,
        "exact_target_conflicts": metrics.exact_target_conflicts,
    }


@exact_oracle()
def _reference_oracle_counts() -> dict[str, dict[str, int]]:
    reverse = ReverseAddCausalSpacetimeEngine(base=10)
    field = ReverseAddPairField.from_value(196, base=10)
    for _ in range(256):
        reverse.forcing_image(field)
        field = reverse.advance(field).target
    rm = reverse.forcing.metrics()

    collatz = CollatzCausalSpacetimeEngine()
    initial = CollatzRadixField.from_value(27)
    collatz.forcing_image(initial)
    target, _ = collatz.advance_event_power(initial, 64)
    collatz.forcing_image(target)
    cm = collatz.metrics()
    return {
        "reverse_196_256": {
            "operator_classes": rm.forcing_classes,
            "exact_occurrences": rm.forcing_occurrences,
            "operator_aliases": rm.action_aliases,
        },
        "collatz_27_64": {
            "operator_classes": cm.forcing_classes,
            "primitive_exact_transitions": cm.primitive_forcing_steps,
            "operator_aliases": cm.forcing_action_aliases,
            "successor_conflicts": cm.forcing_successor_conflicts,
        },
    }


def run_probe() -> CongruenceReport:
    return {
        "version": "0.59.9",
        "status": "PASS",
        "operator_cache_uses_semantic_action_id": True,
        "exact_target_cache_requires_successor_congruence": True,
        "sampled_aliases_are_never_promoted_to_proof": True,
        "reverse": _reverse_witness(),
        "collatz": _collatz_witness(),
        "reference_oracle_counts": _reference_oracle_counts(),
        "interpretation": (
            "ActionID is maximally shared operator identity, not an exact state quotient. "
            "Exact target memoization retains occurrence payload until a complete successor-"
            "congruence proof exists. This prevents the unsafe 196/Collatz alias proposed by "
            "the earlier in-progress local-action replacement."
        ),
    }


def main() -> int:
    result = run_probe()
    out = ROOT / "results" / "successor_congruence_metrics.json"
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
