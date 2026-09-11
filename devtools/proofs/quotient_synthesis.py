"""Counterexample-guided candidate feature synthesis over finite proof domains."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Hashable, Sequence

from number_compiler.arithmetic.functions.finite_unary import (
    ObserverAnalysis,
    UnaryBehavioralBlockReport,
    UnaryImageFiltration,
    UnaryMooreMinimization,
    UnaryPowerArena,
    UnaryPowerNode,
    UnaryQuotientMachine,
    UnaryTransitionEffect,
    analyze_observer,
    minimize_unary_moore,
    partition_equivalent,
    quotient_machine_from_moore,
    unary_behavioral_block_machine,
    unary_image_filtration,
    unary_target_distance_machine,
)


@dataclass(frozen=True, slots=True)
class ObserverFeature:
    """One candidate finite quotient coordinate with explicit charged cost."""

    name: str
    values: tuple[Hashable, ...]
    cost: int = 1

    def __post_init__(self) -> None:
        if not self.name or int(self.cost) < 0:
            raise ValueError(self)
        object.__setattr__(self, "cost", int(self.cost))


@dataclass(frozen=True, slots=True)
class FiniteQuotientSynthesis:
    selected_features: tuple[str, ...]
    total_cost: int
    classes: int
    source_states: int
    target_separating: bool
    next_closed: bool
    noninjective: bool
    unresolved_counterexamples: int

    @property
    def closed(self) -> bool:
        return self.target_separating and self.next_closed


def _feature_keys(
    features: tuple[ObserverFeature, ...], selected: Sequence[int]
) -> tuple[tuple[Hashable, ...], ...]:
    return tuple(
        tuple(features[index].values[state] for index in selected)
        for state in range(len(features[0].values) if features else 0)
    )


def _counterexample_pairs(
    keys: Sequence[Hashable],
    successors: Sequence[int],
    targets: Sequence[Hashable],
) -> tuple[tuple[int, int], ...]:
    by_key: dict[Hashable, int] = {}
    pairs: list[tuple[int, int]] = []
    for state, key in enumerate(keys):
        old = by_key.get(key)
        if old is None:
            by_key[key] = state
            continue
        if (
            targets[old] != targets[state]
            or keys[successors[old]] != keys[successors[state]]
        ):
            pairs.append((old, state))
    return tuple(pairs)


def synthesize_finite_quotient(
    successors: Sequence[int],
    targets: Sequence[Hashable],
    features: Sequence[ObserverFeature],
    *,
    required_features: Sequence[str] = (),
) -> FiniteQuotientSynthesis:
    """Greedily refine a *complete finite* transition system to exact closure.

    Counterexamples drive feature selection.  At each round the candidate that
    separates the most current counterexample pairs is chosen; ties prefer the
    lower charged cost and then lexical name.  A final backward deletion pass
    removes redundant non-required features while preserving exact closure.

    This is deterministic compiler infrastructure, not a claim that a bounded
    finite proof generalizes to an unbounded sequence family.
    """
    succ = tuple(map(int, successors))
    labels = tuple(targets)
    cols = tuple(features)
    n = len(succ)
    if len(labels) != n or not cols or any(len(col.values) != n for col in cols):
        raise ValueError((n, len(labels), tuple(len(col.values) for col in cols)))
    if any(not 0 <= nxt < n for nxt in succ):
        raise ValueError("successor outside finite domain")
    names = [col.name for col in cols]
    if len(set(names)) != len(names):
        raise ValueError("duplicate feature names")
    required = tuple(required_features)
    missing = set(required) - set(names)
    if missing:
        raise ValueError(("missing-required-features", sorted(missing)))
    selected = [names.index(name) for name in required]
    unused = set(range(len(cols))) - set(selected)

    def analyze(
        indices: Sequence[int],
    ) -> tuple[
        ObserverAnalysis, tuple[tuple[Hashable, ...], ...], tuple[tuple[int, int], ...]
    ]:
        if indices:
            keys = _feature_keys(cols, indices)
        else:
            keys = ((),) * n
        next_keys = tuple(keys[succ[state]] for state in range(n))
        result = analyze_observer(keys, next_keys, labels)
        return result, keys, _counterexample_pairs(keys, succ, labels)

    analysis, keys, pairs = analyze(selected)
    while not analysis.closed and pairs:
        ranked: list[tuple[int, int, str, int]] = []
        for index in sorted(unused):
            separated = sum(
                cols[index].values[a] != cols[index].values[b] for a, b in pairs
            )
            if separated:
                ranked.append((separated, -cols[index].cost, cols[index].name, index))
        if not ranked:
            break
        _coverage, _neg_cost, _name, chosen = max(ranked)
        selected.append(chosen)
        unused.remove(chosen)
        analysis, keys, pairs = analyze(selected)

    required_indices = {names.index(name) for name in required}
    if analysis.closed:
        # Remove late refinements that became redundant after stronger features
        # were selected.  Required feature contracts are never deleted.
        for index in tuple(reversed(selected)):
            if index in required_indices:
                continue
            trial = [item for item in selected if item != index]
            trial_analysis, _trial_keys, _trial_pairs = analyze(trial)
            if trial_analysis.closed:
                selected = trial
                analysis = trial_analysis
        analysis, keys, pairs = analyze(selected)

    return FiniteQuotientSynthesis(
        tuple(cols[index].name for index in selected),
        sum(cols[index].cost for index in selected),
        analysis.classes,
        n,
        analysis.target_separating,
        analysis.next_closed,
        analysis.classes < n,
        len(pairs),
    )


@dataclass(frozen=True, slots=True)
class FiniteTargetSynthesis:
    """Cheapest selected finite feature set that separates target labels only.

    Unlike :class:`FiniteQuotientSynthesis`, this object makes no successor-
    closure claim.  It is the canonical bounded tool for powered observer
    pullbacks ``output o T**N`` where only one time-specialized target is
    requested.
    """

    selected_features: tuple[str, ...]
    total_cost: int
    classes: int
    source_states: int
    target_separating: bool
    noninjective: bool
    unresolved_counterexamples: int


def synthesize_finite_target_observer(
    targets: Sequence[Hashable],
    features: Sequence[ObserverFeature],
    *,
    required_features: Sequence[str] = (),
) -> FiniteTargetSynthesis:
    """Greedily synthesize a complete finite *target-only* observer.

    This shares the feature/cost contracts of ``synthesize_finite_quotient``
    but intentionally does not test successor closure.  The result therefore
    cannot be promoted to a self-advancing semantic state; it is valid only as
    a bounded exact pullback observer for the supplied labels.
    """
    labels = tuple(targets)
    cols = tuple(features)
    n = len(labels)
    if not cols or any(len(col.values) != n for col in cols):
        raise ValueError((n, tuple(len(col.values) for col in cols)))
    names = [col.name for col in cols]
    if len(set(names)) != len(names):
        raise ValueError("duplicate feature names")
    required = tuple(required_features)
    missing = set(required) - set(names)
    if missing:
        raise ValueError(("missing-required-features", sorted(missing)))
    selected = [names.index(name) for name in required]
    unused = set(range(len(cols))) - set(selected)

    def analyze(
        indices: Sequence[int],
    ) -> tuple[tuple[tuple[Hashable, ...], ...], tuple[tuple[int, int], ...]]:
        keys = _feature_keys(cols, indices) if indices else ((),) * n
        representative: dict[tuple[Hashable, ...], int] = {}
        pairs: list[tuple[int, int]] = []
        for state, key in enumerate(keys):
            old = representative.get(key)
            if old is None:
                representative[key] = state
            elif labels[old] != labels[state]:
                pairs.append((old, state))
        return keys, tuple(pairs)

    keys, pairs = analyze(selected)
    while pairs:
        ranked: list[tuple[int, int, str, int]] = []
        for index in sorted(unused):
            separated = sum(
                cols[index].values[a] != cols[index].values[b] for a, b in pairs
            )
            if separated:
                ranked.append((separated, -cols[index].cost, cols[index].name, index))
        if not ranked:
            break
        _coverage, _neg_cost, _name, chosen = max(ranked)
        selected.append(chosen)
        unused.remove(chosen)
        keys, pairs = analyze(selected)

    required_indices = {names.index(name) for name in required}
    if not pairs:
        for index in tuple(reversed(selected)):
            if index in required_indices:
                continue
            trial = [item for item in selected if item != index]
            trial_keys, trial_pairs = analyze(trial)
            if not trial_pairs:
                selected = trial
                keys, pairs = trial_keys, trial_pairs
        keys, pairs = analyze(selected)

    classes = len(set(keys))
    return FiniteTargetSynthesis(
        tuple(cols[index].name for index in selected),
        sum(cols[index].cost for index in selected),
        classes,
        n,
        not pairs,
        classes < n,
        len(pairs),
    )


__all__ = [
    "ObserverAnalysis",
    "UnaryImageFiltration",
    "UnaryMooreMinimization",
    "ObserverFeature",
    "FiniteQuotientSynthesis",
    "FiniteTargetSynthesis",
    "analyze_observer",
    "unary_image_filtration",
    "partition_equivalent",
    "minimize_unary_moore",
    "UnaryTransitionEffect",
    "UnaryPowerNode",
    "UnaryPowerArena",
    "UnaryQuotientMachine",
    "UnaryBehavioralBlockReport",
    "unary_behavioral_block_machine",
    "unary_target_distance_machine",
    "quotient_machine_from_moore",
    "synthesize_finite_quotient",
    "synthesize_finite_target_observer",
]
