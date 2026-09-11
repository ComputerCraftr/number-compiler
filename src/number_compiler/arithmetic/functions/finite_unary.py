"""Shared exact finite unary actions, partitions, and observer primitives.

These operations consume caller-supplied finite tables. Candidate feature search
and counterexample-guided refinement remain in proof. No trajectory is inferred.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Hashable, Sequence

from number_compiler.arithmetic.fields.morphism_core import (
    InternedEffectNode,
    binary_power,
)
from number_compiler.arithmetic.fields.radix import bit_width
from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
    partition_equivalent as partition_equivalent,
)


@dataclass(frozen=True, slots=True)
class ObserverAnalysis:
    rows: int
    classes: int
    target_conflicts: int
    successor_conflicts: int

    @property
    def target_separating(self) -> bool:
        return self.target_conflicts == 0

    @property
    def next_closed(self) -> bool:
        return self.successor_conflicts == 0

    @property
    def closed(self) -> bool:
        return self.target_separating and self.next_closed


def analyze_observer(
    keys: Sequence[Hashable],
    successor_keys: Sequence[Hashable],
    targets: Sequence[Hashable] | None = None,
) -> ObserverAnalysis:
    """Analyze an extensional observer without materializing source classes.

    Each row supplies the current observer key and the observer key after one
    semantic transition.  Optional target labels test target separation in the
    same pass.  Conflicts are counted after the first representative of a key.
    """
    current = tuple(keys)
    nxt = tuple(successor_keys)
    if len(current) != len(nxt):
        raise ValueError((len(current), len(nxt)))
    labels = None if targets is None else tuple(targets)
    if labels is not None and len(labels) != len(current):
        raise ValueError((len(labels), len(current)))
    seen_next: dict[Hashable, Hashable] = {}
    seen_target: dict[Hashable, Hashable] = {}
    next_conflicts = target_conflicts = 0
    for index, (key, next_key) in enumerate(zip(current, nxt, strict=True)):
        old_next = seen_next.setdefault(key, next_key)
        next_conflicts += int(old_next != next_key)
        if labels is not None:
            label = labels[index]
            if key in seen_target:
                target_conflicts += int(seen_target[key] != label)
            else:
                seen_target[key] = label
    return ObserverAnalysis(
        len(current),
        len(set(current)),
        target_conflicts,
        next_conflicts,
    )


@dataclass(frozen=True, slots=True)
class UnaryImageFiltration:
    """Exact nested successor-image filtration of a finite unary machine.

    ``depth_ids[state]`` is the largest strict image level containing the state.
    States in the eventual fixed image use ``-1`` because their image depth is
    unbounded.  This is a bounded exact set-morphism diagnostic; it makes no
    claim that image depth equals the target Moore partition.
    """

    ranks: tuple[int, ...]
    depth_ids: tuple[int, ...]
    stable_states: int

    @property
    def finite_depths(self) -> int:
        return max((depth for depth in self.depth_ids if depth >= 0), default=-1) + 1


def unary_image_filtration(successors: Sequence[int]) -> UnaryImageFiltration:
    """Compute ``S, T(S), T^2(S), ...`` until the image stabilizes exactly."""
    succ = tuple(map(int, successors))
    n = len(succ)
    if n <= 0 or any(not 0 <= nxt < n for nxt in succ):
        raise ValueError(succ)
    current = set(range(n))
    images: list[set[int]] = [current]
    while True:
        nxt = {succ[state] for state in current}
        images.append(nxt)
        if nxt == current:
            break
        current = nxt
        if len(images) > n + 1:
            raise AssertionError((n, len(images)))
    stable = images[-1]
    depths = [-1 if state in stable else 0 for state in range(n)]
    for level, image in enumerate(images[1:-1], start=1):
        for state in image:
            if state not in stable:
                depths[state] = level
    return UnaryImageFiltration(
        tuple(len(image) for image in images),
        tuple(depths),
        len(stable),
    )


@dataclass(frozen=True, slots=True)
class UnaryMooreMinimization:
    classes: int
    class_ids: tuple[int, ...]
    rounds: int


def minimize_unary_moore(
    successors: Sequence[int],
    outputs: Sequence[Hashable],
) -> UnaryMooreMinimization:
    """Exact Moore minimization for a finite deterministic unary transition.

    This is the canonical replacement for research-local refinement loops used
    by special-number observer probes.
    """
    succ = tuple(map(int, successors))
    labels = tuple(outputs)
    n = len(succ)
    if len(labels) != n or any(not 0 <= nxt < n for nxt in succ):
        raise ValueError((n, len(labels)))
    result = minimize_finite_observer(tuple((target,) for target in succ), labels)
    return UnaryMooreMinimization(result.classes, result.class_ids, result.rounds)


@dataclass(frozen=True, slots=True)
class UnaryTransitionEffect:
    """One extensional map on ``0..classes-1``."""

    transition: tuple[int, ...]

    def __post_init__(self) -> None:
        transition = tuple(map(int, self.transition))
        n = len(transition)
        if n <= 0 or any(not 0 <= nxt < n for nxt in transition):
            raise ValueError(transition)
        object.__setattr__(self, "transition", transition)

    @property
    def classes(self) -> int:
        return len(self.transition)

    @property
    def semantic_key(self) -> tuple[object, ...]:
        return ("unary-transition-effect", self.transition)

    @property
    def description_bits(self) -> int:
        return self.classes * max(1, bit_width(self.classes - 1))

    @classmethod
    def identity(cls, classes: int) -> "UnaryTransitionEffect":
        classes = int(classes)
        if classes <= 0:
            raise ValueError(classes)
        return cls(tuple(range(classes)))

    def then(self, other: "UnaryTransitionEffect") -> "UnaryTransitionEffect":
        """Return ``other o self``."""
        if self.classes != other.classes:
            raise ValueError((self.classes, other.classes))
        return UnaryTransitionEffect(
            tuple(other.transition[nxt] for nxt in self.transition)
        )

    def apply(self, state: int) -> int:
        state = int(state)
        if not 0 <= state < self.classes:
            raise ValueError((state, self.classes))
        return self.transition[state]


UnaryPowerNode = InternedEffectNode[UnaryTransitionEffect]


class UnaryPowerArena:
    """Early-canonical interner for extensional finite transition maps."""

    __slots__ = (
        "_nodes",
        "_by_key",
        "_identity",
        "_atom",
        "composition_operations",
        "intern_hits",
        "intern_misses",
    )

    def __init__(self, primitive: Sequence[int]) -> None:
        effect = UnaryTransitionEffect(tuple(primitive))
        self._nodes: list[UnaryPowerNode] = []
        self._by_key: dict[tuple[object, ...], UnaryPowerNode] = {}
        self.composition_operations = 0
        self.intern_hits = 0
        self.intern_misses = 0
        self._identity = self._intern(UnaryTransitionEffect.identity(effect.classes))
        self._atom = self._intern(effect)

    def _intern(self, effect: UnaryTransitionEffect) -> UnaryPowerNode:
        old = self._by_key.get(effect.semantic_key)
        if old is not None:
            self.intern_hits += 1
            return old
        node = UnaryPowerNode(len(self._nodes) + 1, effect)
        self._nodes.append(node)
        self._by_key[effect.semantic_key] = node
        self.intern_misses += 1
        return node

    @property
    def identity(self) -> UnaryPowerNode:
        return self._identity

    @property
    def atom(self) -> UnaryPowerNode:
        return self._atom

    @property
    def node_count(self) -> int:
        return len(self._nodes)

    def compose(self, first: UnaryPowerNode, second: UnaryPowerNode) -> UnaryPowerNode:
        self.composition_operations += 1
        return self._intern(first.effect.then(second.effect))

    def power(self, exponent: int) -> UnaryPowerNode:
        exponent = int(exponent)
        if exponent < 0:
            raise ValueError(exponent)
        return binary_power(
            self.atom, exponent, identity=self.identity, compose=self.compose
        ).value


@dataclass(frozen=True, slots=True)
class UnaryQuotientMachine:
    """A proved finite quotient plus exact target/output labels."""

    transition: tuple[int, ...]
    outputs: tuple[Hashable, ...]

    def __post_init__(self) -> None:
        transition = tuple(map(int, self.transition))
        outputs = tuple(self.outputs)
        n = len(transition)
        if n <= 0 or len(outputs) != n or any(not 0 <= nxt < n for nxt in transition):
            raise ValueError((transition, outputs))
        object.__setattr__(self, "transition", transition)
        object.__setattr__(self, "outputs", outputs)

    @property
    def classes(self) -> int:
        return len(self.transition)

    @property
    def state_bits(self) -> int:
        return max(1, bit_width(self.classes - 1))

    def output(self, state: int) -> Hashable:
        state = int(state)
        if not 0 <= state < self.classes:
            raise ValueError((state, self.classes))
        return self.outputs[state]

    def power_state(self, state: int, steps: int) -> tuple[int, int, int]:
        """Return powered state, composition count and arena node count."""
        arena = UnaryPowerArena(self.transition)
        node = arena.power(int(steps))
        return (
            node.effect.apply(int(state)),
            arena.composition_operations,
            arena.node_count,
        )

    def output_after(self, state: int, steps: int) -> Hashable:
        powered, _ops, _nodes = self.power_state(state, steps)
        return self.output(powered)


@dataclass(frozen=True, slots=True)
class UnaryBehavioralBlockReport:
    """Exact finite audit for one behavior-preserving unary block quotient.

    ``block_outputs`` are not sampled only at the block boundary: the quotient
    preserves the complete output trace for remainders ``0..block_size-1``.
    This is the unary analogue of a carry slab boundary.  Omitting that trace
    can create a plausible but unsound block compression which cannot answer an
    arbitrary powered projection with a final remainder.
    """

    block_size: int
    source_states: int
    one_step_classes: int
    sampled_block_classes: int
    exact_block_classes: int
    powering_compositions: int
    powering_nodes: int
    full_transition_description_bits: int
    exact_quotient_description_bits: int


def unary_behavioral_block_machine(
    successors: Sequence[int],
    outputs: Sequence[Hashable],
    block_size: int,
) -> tuple[UnaryQuotientMachine, UnaryBehavioralBlockReport]:
    """Power a complete unary machine by ``block_size`` and minimize exactly.

    The observable attached to a block state is the complete output trace
    before each of the ``block_size`` primitive transitions.  Consequently a
    caller may execute any number of whole blocks and then answer an arbitrary
    remainder without having discarded one-step semantics.

    This helper is intentionally finite/extensional.  It is reusable compiler
    infrastructure for bounded proofs, not a scalable constructor for a large
    source carrier.
    """
    succ = tuple(map(int, successors))
    labels = tuple(outputs)
    n = len(succ)
    block_size = int(block_size)
    if block_size <= 0 or len(labels) != n or n <= 0:
        raise ValueError((n, len(labels), block_size))
    if any(not 0 <= nxt < n for nxt in succ):
        raise ValueError("successor outside finite domain")

    one_step = minimize_unary_moore(succ, labels)
    arena = UnaryPowerArena(succ)
    powered = arena.power(block_size).effect

    # A sampled endpoint-only minimization is useful as an explicit negative
    # control: it may merge states which differ inside the block.
    sampled = minimize_unary_moore(powered.transition, labels)

    traces: list[tuple[Hashable, ...]] = []
    for source in range(n):
        state = source
        trace: list[Hashable] = []
        for _ in range(block_size):
            trace.append(labels[state])
            state = succ[state]
        traces.append(tuple(trace))
    exact = minimize_unary_moore(powered.transition, tuple(traces))
    machine = quotient_machine_from_moore(
        powered.transition, tuple(traces), exact.class_ids
    )
    state_bits = max(1, bit_width(machine.classes - 1))
    return machine, UnaryBehavioralBlockReport(
        block_size=block_size,
        source_states=n,
        one_step_classes=one_step.classes,
        sampled_block_classes=sampled.classes,
        exact_block_classes=exact.classes,
        powering_compositions=arena.composition_operations,
        powering_nodes=arena.node_count,
        full_transition_description_bits=powered.description_bits,
        exact_quotient_description_bits=machine.classes * state_bits,
    )


def unary_target_distance_machine(max_distance: int) -> UnaryQuotientMachine:
    """Return the canonical saturating unary target-distance machine.

    Runtime code ``0`` is the absorbing never-target class.  Code ``d+1``
    means that the unique target is exactly ``d`` transitions away.  Thus one
    transition is saturating subtraction by one, and the only target code is
    ``1``.  This is the canonical finite realization of the order/image-depth
    counters used by the special-number stack; callers should derive the
    distance theorem separately rather than materializing a source carrier.
    """
    max_distance = int(max_distance)
    if max_distance < 0:
        raise ValueError(max_distance)
    classes = max_distance + 2
    transition = (0,) + tuple(range(classes - 1))
    outputs = (False, True) + (False,) * max_distance
    return UnaryQuotientMachine(transition, outputs)


def quotient_machine_from_moore(
    transition: Sequence[int],
    outputs: Sequence[Hashable],
    class_ids: Sequence[int],
) -> UnaryQuotientMachine:
    """Quotient a complete finite unary machine by an exact Moore partition."""
    transition = tuple(map(int, transition))
    outputs = tuple(outputs)
    class_ids = tuple(map(int, class_ids))
    n = len(transition)
    if len(outputs) != n or len(class_ids) != n:
        raise ValueError((n, len(outputs), len(class_ids)))
    classes = max(class_ids, default=-1) + 1
    if classes <= 0:
        raise ValueError(classes)
    qnext: list[int | None] = [None] * classes
    qout: list[Hashable | None] = [None] * classes
    seen = [False] * classes
    for state in range(n):
        cls = class_ids[state]
        nxt = class_ids[transition[state]]
        out = outputs[state]
        if not seen[cls]:
            seen[cls] = True
            qnext[cls] = nxt
            qout[cls] = out
        elif qnext[cls] != nxt or qout[cls] != out:
            raise AssertionError(
                ("invalid-moore-partition", state, cls, qnext[cls], nxt, qout[cls], out)
            )
    if not all(seen) or any(value is None for value in qnext):
        raise AssertionError((seen, qnext))
    return UnaryQuotientMachine(
        tuple(value for value in qnext if value is not None), tuple(qout)
    )


__all__ = [
    "ObserverAnalysis",
    "UnaryImageFiltration",
    "UnaryMooreMinimization",
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
]
