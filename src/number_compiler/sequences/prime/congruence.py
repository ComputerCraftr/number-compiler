"""Prime-family congruence automata built from shared affine arithmetic."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from functools import lru_cache
from math import gcd, isqrt, prod
from typing import TypedDict

from number_compiler.arithmetic.fields.congruence_automaton import (
    FactoredAffineMorphism,
    FactoredCongruenceState,
    compile_radix_runs_morphism,
)
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    periodic_position_bases,
    symbol_runs,
)
from number_compiler.sequences.prime.wheel import (
    PackedWheelProgram,
    build_packed_wheel_program,
)


class _PrimeDecisionFrame(TypedDict):
    pos: int
    prefix: int
    state: FactoredCongruenceState
    next_digit: int
    children: list[int]
    incoming: int | None


@dataclass(frozen=True, slots=True)
class FactoredPrimeAutomaton:
    """Exact bounded primality automaton over a packed squarefree wheel."""

    wheel: PackedWheelProgram

    @classmethod
    def build(cls, limit: int, *, word_bits: int = 62) -> FactoredPrimeAutomaton:
        """Return the canonical immutable automaton for one bounded carrier.

        Sequence families previously rebuilt identical wheel/automaton objects
        independently.  The class constructor remains the single public API,
        but identical semantic keys now share one object across compiler paths.
        """
        if cls is not FactoredPrimeAutomaton:
            return cls(build_packed_wheel_program(int(limit), int(word_bits)))
        return _cached_factored_prime_automaton(int(limit), int(word_bits))

    @property
    def moduli(self) -> tuple[int, ...]:
        return self.wheel.moduli

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return (
            "factored_prime_automaton",
            self.wheel.limit,
            self.wheel.word_bits,
            self.moduli,
        )

    def zero(self) -> FactoredCongruenceState:
        return FactoredCongruenceState((0,) * len(self.moduli))

    def state_from_value(
        self, value: int, *, radix: int = 2
    ) -> tuple[FactoredCongruenceState, FactoredAffineMorphism]:
        value, radix = int(value), int(radix)
        if value < 0 or radix < 2:
            raise ValueError((value, radix))
        digits = digits_lsd(value, radix)
        morphism = compile_radix_runs_morphism(
            self.moduli, symbol_runs(tuple(reversed(digits))), radix=radix
        )
        state = morphism.apply(self.zero())
        if state.residues != tuple(value % m for m in self.moduli):
            raise AssertionError("radix morphism changed integer residue")
        return state, morphism

    def advance(
        self, state: FactoredCongruenceState, candidate_steps: int
    ) -> tuple[FactoredCongruenceState, FactoredAffineMorphism]:
        """Random-access odd-candidate advance by ``2*candidate_steps``."""
        steps = int(candidate_steps)
        if steps < 0:
            raise ValueError(steps)
        morphism = FactoredAffineMorphism.additive(self.moduli, 2).power(steps)
        return morphism.apply(state), morphism

    def classify_state(self, state: FactoredCongruenceState) -> tuple[bool, int]:
        if len(state.residues) != len(self.moduli):
            raise ValueError("state belongs to another automaton")
        calls = 0
        for residue, modulus in zip(state.residues, self.moduli):
            calls += 1
            if gcd(int(residue), modulus) > 1:
                return False, calls
        return True, calls

    def classify_value(
        self, value: int, *, radix: int = 2
    ) -> tuple[bool, int, FactoredAffineMorphism]:
        value = int(value)
        if not self.wheel.supports(value):
            raise ValueError((value, self.wheel.limit, self.wheel.exact_high))
        state, morphism = self.state_from_value(value, radix=radix)
        prime, calls = self.classify_state(state)
        return prime, calls, morphism


@lru_cache(maxsize=32)
def _cached_factored_prime_automaton(
    limit: int, word_bits: int
) -> FactoredPrimeAutomaton:
    return FactoredPrimeAutomaton(
        build_packed_wheel_program(int(limit), int(word_bits))
    )


@dataclass(frozen=True, slots=True)
class FactoredPrimeDecisionCompilation:
    """Exact prime-bit decision DAG compiled directly from congruence state."""

    start: int
    length: int
    base_period: tuple[int, ...]
    position_bases: tuple[int, ...]
    domain_size: int
    summary_count: int
    summary_first: int | None
    group_count: int
    total_group_bits: int
    decision_nodes: int
    decision_references: int
    decision_description_bits: int
    congruence_transitions: int
    gcd_calls: int
    terminal_prime_leaves: int
    terminal_composite_leaves: int
    terminal_outside_leaves: int


def compile_prime_block_factored_decision(
    start: int,
    length: int,
    *,
    base_period: Sequence[int] = (3, 5),
    word_bits: int = 62,
) -> FactoredPrimeDecisionCompilation:
    """Compile prime/composite bits without materializing a prime bitmap.

    Candidate indices ``j`` are read in an exact periodic mixed-radix system.
    If the current prefix represents ``h`` and the next lower-position digit is
    ``d`` with local base ``b``, then candidate residues transform as

        start + 2*h  ->  start + 2*(b*h+d)
        r            ->  b*r + 2*d + (1-b)*start  (mod M_i).

    Thus the same packed factor carrier is a digit automaton on the candidate
    index.  Leaves use the wheel's exact coprimality test; a third terminal is
    reserved for padding outside the requested finite block.  Internal nodes
    are hash-consed by their complete ordered child tuple, so minimization occurs
    during construction rather than after a prime bitmap exists.
    """
    start, length, word_bits = int(start), int(length), int(word_bits)
    period = tuple(map(int, base_period))
    if start < 3 or not (start & 1) or length <= 0 or word_bits < 2:
        raise ValueError((start, length, word_bits))
    bases = periodic_position_bases(length, period)
    domain = prod(bases)
    high = start + 2 * (length - 1)
    automaton = FactoredPrimeAutomaton.build(isqrt(high), word_bits=word_bits)
    if not automaton.wheel.supports(start) or not automaton.wheel.supports(high):
        raise ValueError(
            (start, high, automaton.wheel.limit, automaton.wheel.exact_high)
        )
    initial = FactoredCongruenceState(tuple(start % m for m in automaton.moduli))

    # Local IDs are scoped to this decision arena.  The interning key is the
    # complete extensional child tuple, not construction provenance.
    terminal_ids = {0: 1, 1: 2, 2: 3}  # composite, prime, outside
    next_id = 4
    by_children: dict[tuple[int, ...], int] = {}
    node_children: dict[int, tuple[int, ...]] = {}
    transitions = gcd_calls = 0
    prime_leaves = composite_leaves = outside_leaves = 0
    count = 0
    first: int | None = None

    # Explicit depth-first frames replace recursive mixed-radix descent.
    frames: list[_PrimeDecisionFrame] = [
        {
            "pos": len(bases) - 1,
            "prefix": 0,
            "state": initial,
            "next_digit": 0,
            "children": [],
            "incoming": None,
        }
    ]
    _root: int | None = None
    while frames:
        frame = frames[-1]
        pos = int(frame["pos"])
        prefix = int(frame["prefix"])
        state = frame["state"]
        match state:
            case FactoredCongruenceState():
                pass
            case _:
                raise AssertionError(state)
        if pos < 0:
            if prefix >= length:
                outside_leaves += 1
                node_id = terminal_ids[2]
            else:
                prime, calls = automaton.classify_state(state)
                gcd_calls += calls
                if prime:
                    prime_leaves += 1
                    count += 1
                    if first is None or prefix < first:
                        first = prefix
                    node_id = terminal_ids[1]
                else:
                    composite_leaves += 1
                    node_id = terminal_ids[0]
            frames.pop()
        else:
            base = bases[pos]
            next_digit = int(frame["next_digit"])
            if next_digit < base:
                digit = next_digit
                frame["next_digit"] = digit + 1
                offset = 2 * digit + (1 - base) * start
                residues = tuple(
                    (base * r + offset) % m
                    for r, m in zip(state.residues, automaton.moduli)
                )
                transitions += len(automaton.moduli)
                frames.append(
                    {
                        "pos": pos - 1,
                        "prefix": base * prefix + digit,
                        "state": FactoredCongruenceState(residues),
                        "next_digit": 0,
                        "children": [],
                        "incoming": digit,
                    }
                )
                continue
            children = tuple(frame["children"])
            got = by_children.get(children)
            if got is not None:
                node_id = got
            else:
                node_id = next_id
                next_id += 1
                by_children[children] = node_id
                node_children[node_id] = children
            frames.pop()
        if not frames:
            _root = node_id
            break
        parent_children = frames[-1]["children"]
        match parent_children:
            case list():
                pass
            case _:
                raise AssertionError(parent_children)
        parent_children.append(node_id)
    if _root is None:
        raise AssertionError("mixed-radix decision produced no root")
    # Only internally interned nodes plus the three semantic terminals are
    # retained.  Leaf occurrences are execution work, not duplicate state.
    nodes = len(node_children) + 3
    refs = sum(len(children) for children in node_children.values())
    id_bits = bit_width(max(1, nodes))
    param_bits = sum(bit_width(base - 1) for base in bases)
    description = nodes + refs * id_bits + param_bits
    return FactoredPrimeDecisionCompilation(
        start,
        length,
        period,
        bases,
        domain,
        count,
        first,
        automaton.wheel.group_count,
        automaton.wheel.total_group_bits,
        nodes,
        refs,
        description,
        transitions,
        gcd_calls,
        prime_leaves,
        composite_leaves,
        outside_leaves,
    )


__all__ = [
    "FactoredPrimeAutomaton",
    "FactoredPrimeDecisionCompilation",
    "compile_prime_block_factored_decision",
]
