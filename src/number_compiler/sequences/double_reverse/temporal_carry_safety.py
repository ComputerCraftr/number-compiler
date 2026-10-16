"""Source-derived carry-safety lifting of every 2rev10 two-cell border SCC.

For a canonical word X=a b c ... x y z, all digits MSDF, the next word's
least-significant three digits are EXACTLY

    (2*c+[b>=5])%10, (2*b+[a>=5])%10, 2*a%10.

In particular the carry entering the *following* step's second high cell is
[(2*c+[b>=5])%10 >= 5], not a new unconstrained input. A three-cell border
lift retains this connection while leaving only the fourth-from-last carry
conditional. The lift deliberately makes no claim about a shrinking frontier
whose new high cells require an arbitrarily deeper suffix.

The 2-cell graph has four cyclic SCCs. On their complete 3-cell lifts the
standard 9-edge SCC is universally closed; all three alternatives have a
DAG of *internal* transitions even when the unobserved fourth carry may be
chosen freely. This eliminates false indefinite 2-cell cycles without
assuming any special seed, empirical period, or digit-oracle table.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at

from .boundary_cycles import (
    CANDIDATE_COMPONENTS,
    Edge,
    candidate_component,
)

if TYPE_CHECKING:
    from .temporal_inward_constraints import InwardSafetySummary


def _h(digit: int) -> int:
    return int(digit >= 5)


@dataclass(frozen=True, slots=True)
class LiftedBorder:
    """Exact ordered high/low three digits, NOT just symmetric pair sums."""

    high: tuple[int, int, int]
    low: tuple[int, int, int]

    def __post_init__(self) -> None:
        for side in (self.high, self.low):
            if (
                type(side) is not tuple
                or len(side) != 3
                or any(type(x) is not int or not 0 <= x <= 9 for x in side)
            ):
                raise ValueError("lift requires two exact three-digit borders")
        if self.high[0] == 0:
            raise ValueError("leading zero is not canonical")

    @property
    def edge(self) -> Edge:
        return (self.high[0], self.high[1], self.low[1], self.low[2])

    @property
    def forced_inward_carry(self) -> int:
        """Carry used at current leading second-digit seam, when nongrowing."""
        return _h(self.low[0])

    @property
    def forced_next_inward_carry(self) -> int:
        """Two-time-step safety cone: third high digit -> next third low."""
        b, c = self.high[1:]
        return _h((2 * c + _h(b)) % 10)


def lift_from_digits(digits: str) -> LiftedBorder:
    if (
        not isinstance(digits, str)
        or len(digits) < 5
        or digits[0] == "0"
        or not (digits.isascii() and digits.isdigit())
    ):
        raise ValueError("three-cell carry safety requires >=5 canonical digits")
    return LiftedBorder(
        (int(digits[0]), int(digits[1]), int(digits[2])),
        (int(digits[-3]), int(digits[-2]), int(digits[-1])),
    )


def lift_from_slp(arena: SLPArena, root: int) -> LiftedBorder:
    if type(root) is not int or not 0 <= root < len(arena.nodes):
        raise ValueError("invalid three-cell source root")
    width = arena.nodes[root].length
    if width < 5:
        raise ValueError("three-cell carry safety requires >=5 source digits")
    return LiftedBorder(
        (
            symbol_at(arena, root, 0),
            symbol_at(arena, root, 1),
            symbol_at(arena, root, 2),
        ),
        (
            symbol_at(arena, root, width - 3),
            symbol_at(arena, root, width - 2),
            symbol_at(arena, root, width - 1),
        ),
    )


@dataclass(frozen=True, slots=True)
class LiftedSafetyStep:
    """One exact 3-cell relation; None target means a typed shrinking frontier."""

    target: LiftedBorder | None
    growth: int | None
    current_inward_carry: int
    next_inward_carry: int
    fourth_digit_carry: int

    @property
    def shrinking_frontier(self) -> bool:
        return self.target is None


def lifted_step(border: LiftedBorder, fourth_digit_carry: int) -> LiftedSafetyStep:
    """Exact width-preserving/growing relation for either *external* carry.

    Every real nonshrinking decimal transition of source width >=5 has one
    matching branch, with `fourth_digit_carry=[source[-4]>=5]`. The incoming
    carry at the second HIGH digit is NOT this free bit: it is forced by the
    retained third LOW digit. The fourth bit affects only the third high digit
    on nongrowth, and a shrinking transition is returned as an explicit
    unresolved frontier (no fabricated target or width delta).
    """
    if type(fourth_digit_carry) is not int or fourth_digit_carry not in (0, 1):
        raise ValueError("fourth-digit carry is a Boolean input")
    a, b, c = border.high
    x, y, z = border.low
    next_low = ((2 * c + _h(b)) % 10, (2 * b + _h(a)) % 10, (2 * a) % 10)
    inward = border.forced_inward_carry
    next_inward = _h(next_low[0])
    if z >= 5:
        next_high = (1, (2 * z + _h(y)) % 10, (2 * y + _h(x)) % 10)
        growth = 1
    else:
        leading = 2 * z + _h(y)
        if leading == 0:
            return LiftedSafetyStep(None, None, inward, next_inward, fourth_digit_carry)
        next_high = (leading, (2 * y + _h(x)) % 10, (2 * x + fourth_digit_carry) % 10)
        growth = 0
    return LiftedSafetyStep(
        LiftedBorder(next_high, next_low),
        growth,
        inward,
        next_inward,
        fourth_digit_carry,
    )


@dataclass(frozen=True, slots=True)
class ComponentSafetyProof:
    component: int
    lifted_states: int
    universally_closed: bool
    maximum_internal_transitions: int | None
    # Number of states admitting a path of at least i internal steps, i >= 0.
    surviving_state_counts: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class SourceCarrySafety:
    source_edge: Edge
    high3: tuple[int, int, int]
    low3: tuple[int, int, int]
    component: int | None
    current_forced_carry: int
    next_forced_carry: int
    possible_next_edges: tuple[Edge, ...]
    shrinking_frontier: bool
    source_maximum_internal_transitions: int | None
    component_maximum_internal_transitions: int | None
    universally_closed_component: bool
    exact_width_change: int | None = None
    unconditional_entry_or_shrink_bound: int | None = None


def _states_in_component(component: int) -> frozenset[LiftedBorder]:
    return frozenset(
        LiftedBorder((a, b, c), (x, y, z))
        for a, b, y, z in CANDIDATE_COMPONENTS[component]
        for c in range(10)
        for x in range(10)
    )


def _component_layers(component: int) -> tuple[frozenset[LiftedBorder], ...]:
    """Exact greatest-path survival sets under both possible fourth carries.

    This is a finite-state proof, not sampled trajectory work. Every real
    source path staying within this SCC is contained in these sets. If the
    decreasing sequence empties, all possible SCC-internal paths are finite.
    """
    if type(component) is not int or not 0 <= component < len(CANDIDATE_COMPONENTS):
        raise ValueError("unknown two-cell component")
    states = _states_in_component(component)
    layers = [states]
    while True:
        surviving = frozenset(
            state
            for state in states
            if any(lifted_step(state, bit).target in layers[-1] for bit in (0, 1))
        )
        if not surviving or surviving == layers[-1]:
            if surviving:
                return tuple(layers)  # stable infinite-path kernel
            return (*layers, surviving)
        layers.append(surviving)
        if len(layers) > len(states) + 1:
            raise AssertionError("finite carry-safety refinement did not terminate")


def component_safety_proof(component: int) -> ComponentSafetyProof:
    layers = _component_layers(component)
    return _component_safety_from_layers(component, layers)


def source_carry_safety(
    border: LiftedBorder,
) -> SourceCarrySafety:
    """Certify both initial carry bits and component-internal exit bounds.

    A finite max is an upper bound on time *inside the same candidate SCC*;
    it is not a bound on the trajectory after an exit or a certificate that an
    actual seed will choose any specific fourth-digit carry.
    """
    comp = candidate_component(border.edge)
    layers = None if comp is None else _component_layers(comp)
    return _source_carry_safety_from_layers(border, layers)


def _source_carry_safety_from_layers(
    border: LiftedBorder,
    layers: tuple[frozenset[LiftedBorder], ...] | None,
) -> SourceCarrySafety:
    """Reuse one owner-built component refinement for its exact source state."""
    steps = (lifted_step(border, 0), lifted_step(border, 1))
    next_edges = tuple(sorted({s.target.edge for s in steps if s.target is not None}))
    comp = candidate_component(border.edge)
    if layers is not None and (comp is None or layers[0] != _states_in_component(comp)):
        raise ValueError("carry-safety layers do not belong to the source component")
    proof = (
        _component_safety_from_layers(comp, layers)
        if comp is not None and layers is not None
        else None
    )
    max_source: int | None = None
    if (
        comp is not None
        and proof is not None
        and proof.maximum_internal_transitions is not None
    ):
        assert layers is not None
        max_source = max(index for index, layer in enumerate(layers) if border in layer)
    return SourceCarrySafety(
        border.edge,
        border.high,
        border.low,
        comp,
        border.forced_inward_carry,
        border.forced_next_inward_carry,
        next_edges,
        any(s.shrinking_frontier for s in steps),
        max_source,
        None if proof is None else proof.maximum_internal_transitions,
        bool(proof and proof.universally_closed),
        next(iter({s.growth for s in steps}))
        if all(s.target is not None for s in steps)
        else None,
        None,
    )


def _component_safety_from_layers(
    component: int, layers: tuple[frozenset[LiftedBorder], ...]
) -> ComponentSafetyProof:
    states = layers[0]
    universally_closed = all(
        lifted_step(state, bit).target in states for state in states for bit in (0, 1)
    )
    maximum = None if layers[-1] else len(layers) - 2
    return ComponentSafetyProof(
        component,
        len(states),
        universally_closed,
        maximum,
        tuple(len(layer) for layer in layers),
    )


@dataclass(frozen=True, slots=True)
class ConditionalCarryTrace:
    """Necessary carry ports along a separately authenticated border trace.

    `allowed_*` are exact projections of the three-cell *overapproximation*,
    not proof that the supplied border trace is a real source trajectory.
    A singleton proves that input is forced PROVIDED an independent producer
    authenticates the complete edge word. No fourth-digit choice is guessed.
    """

    edges: tuple[Edge, ...]
    allowed_inward_carries: tuple[tuple[int, ...], ...]
    allowed_fourth_carries: tuple[tuple[int, ...], ...]
    possible_final_lifts: int


def conditional_carry_trace(
    initial: LiftedBorder, edge_word: tuple[Edge, ...]
) -> ConditionalCarryTrace:
    """Forward/backward prune a source-bound exact border word.

    Each edge in `edge_word` is a separate, independently certified *claimed*
    temporal observation. The first must be the source edge. The finite
    three-cell relation enforces its own two-step high->low->carry feedback;
    a path with no compatible lift is rejected. The cycle certificate bounds
    are used to reject alternative-SCC repetition *before* any path expansion.
    """
    if (
        type(edge_word) is not tuple
        or not edge_word
        or len(edge_word) > 65
        or any(type(edge) is not tuple or len(edge) != 4 for edge in edge_word)
    ):
        raise ValueError("carry trace needs 1..65 complete two-cell edges")
    if edge_word[0] != initial.edge:
        raise ValueError("carry trace does not begin at the authenticated source")
    comp = candidate_component(initial.edge)
    if comp is not None:
        maximum = component_safety_proof(comp).maximum_internal_transitions
        if (
            maximum is not None
            and len(edge_word) - 1 > maximum
            and all(edge in CANDIDATE_COMPONENTS[comp] for edge in edge_word)
        ):
            raise ValueError("candidate cycle exceeds its proved carry-safety bound")

    layers: list[set[LiftedBorder]] = [{initial}]
    transition_rows: list[dict[LiftedBorder, set[tuple[int, LiftedBorder]]]] = []
    for requested in edge_word[1:]:
        row: dict[LiftedBorder, set[tuple[int, LiftedBorder]]] = {}
        next_states: set[LiftedBorder] = set()
        shrinking = False
        for state in layers[-1]:
            for bit in (0, 1):
                result = lifted_step(state, bit)
                if result.shrinking_frontier:
                    shrinking = True
                    continue
                assert result.target is not None
                if result.target.edge == requested:
                    row.setdefault(state, set()).add((bit, result.target))
                    next_states.add(result.target)
        if not next_states:
            if shrinking:
                raise ValueError("carry trace crosses an unresolved shrinking frontier")
            raise ValueError(
                "carry trace contradicts the forced high/low digit grammar"
            )
        transition_rows.append(row)
        layers.append(next_states)

    viable = layers[-1]
    reverse_inward: list[tuple[int, ...]] = []
    reverse_fourth: list[tuple[int, ...]] = []
    for row in reversed(transition_rows):
        survivors: set[LiftedBorder] = set()
        inwards: set[int] = set()
        fourths: set[int] = set()
        for state, transitions in row.items():
            for bit, target in transitions:
                if target in viable:
                    survivors.add(state)
                    inwards.add(state.forced_inward_carry)
                    fourths.add(bit)
        if not survivors:
            raise AssertionError("safety trace lost its certified prefix")
        viable = survivors
        reverse_inward.append(tuple(sorted(inwards)))
        reverse_fourth.append(tuple(sorted(fourths)))
    return ConditionalCarryTrace(
        edge_word,
        tuple(reversed(reverse_inward)),
        tuple(reversed(reverse_fourth)),
        len(layers[-1]),
    )


def forced_carry_prefix(border: LiftedBorder) -> tuple[int, int]:
    """First two inward carries of a real nonshrinking temporal trajectory.

    The second one is a deterministic function of the ORIGINAL high3 word;
    neither input is a guessed carry bit. A shrinking frontier must be handled
    by the exact normalization path rather than presumed nonshrinking.
    """
    if lifted_step(border, 0).shrinking_frontier:
        raise ValueError("shrinking carry-safety source needs a deeper digit halo")
    return border.forced_inward_carry, border.forced_next_inward_carry


def recursive_carry_trace(
    initial: LiftedBorder,
    edge_word: tuple[Edge, ...],
    width_word: tuple[int, ...],
    *,
    residues99: tuple[int, ...] | None = None,
) -> InwardSafetySummary:
    """Propagate an authenticated temporal border trace into BOTH interiors.

    Unlike :func:`conditional_carry_trace`, this uses the full digit-domain
    network rather than stopping at a three-digit halo. The two future-border
    orbits, actual width changes (including contractions), decimal threshold
    carries, raw reverse-innovation borrow maps and optional global mod-99
    residues all constrain one fixed-point grammar. They are NOT independent
    per-generation guesses.

    ``edge_word``, ``width_word`` and ``residues99`` must originate from an
    independently authenticated producer. Compatibility with this grammar
    does not authenticate a fabricated future trace. The output is a sound
    arc-consistent overapproximation, not a whole-root temporal closed form.
    """
    from .temporal_inward_constraints import (
        InconsistentDigitConstraints,
        InwardCarryConstraints,
    )

    if (
        type(edge_word) is not tuple
        or not edge_word
        or type(width_word) is not tuple
        or len(width_word) != len(edge_word)
        or edge_word[0] != initial.edge
    ):
        raise ValueError("inward grammar requires a source-aligned border/width trace")
    if residues99 is not None and len(residues99) != len(edge_word):
        raise ValueError("mod-99 trace must match the authenticated border trace")
    grammar = InwardCarryConstraints(width_word)
    if width_word[0] < 5:
        raise ValueError("source three-cell border is not a width<5 witness")
    high = "".join(str(d) for d in initial.high)
    low = "".join(str(d) for d in initial.low)
    grammar.constrain_prefix(0, high)
    grammar.constrain_suffix(0, low)
    for time, edge in enumerate(edge_word):
        if (
            type(edge) is not tuple
            or len(edge) != 4
            or any(type(x) is not int or not 0 <= x <= 9 for x in edge)
        ):
            raise ValueError("invalid authenticated two-cell border")
        grammar.constrain_prefix(time, f"{edge[0]}{edge[1]}")
        grammar.constrain_suffix(time, f"{edge[2]}{edge[3]}")
        if residues99 is not None:
            grammar.constrain_residue(time, 99, residues99[time])
    try:
        return grammar.propagate(direction="both")
    except InconsistentDigitConstraints as error:
        raise ValueError(
            "border/width/mod-99 trace violates temporal carry safety"
        ) from error


__all__ = [
    "ComponentSafetyProof",
    "ConditionalCarryTrace",
    "LiftedBorder",
    "LiftedSafetyStep",
    "SourceCarrySafety",
    "component_safety_proof",
    "conditional_carry_trace",
    "forced_carry_prefix",
    "lift_from_digits",
    "lift_from_slp",
    "lifted_step",
    "recursive_carry_trace",
    "source_carry_safety",
]
