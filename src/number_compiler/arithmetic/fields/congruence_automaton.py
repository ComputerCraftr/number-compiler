"""Factored affine congruence automata and radix/mixed-radix morphisms.

The prime characteristic bits are not a finite automatic sequence, but finite
primality *certificates* over a bounded interval do admit an exact automaton on
the packed factor carrier.  If ``M_i`` are the squarefree packed wheel groups,
a radix digit is the affine transition

    r_i -> base*r_i + digit (mod M_i).

These transitions compose as a monoid.  Repeated runs therefore power by
squaring, and additive candidate jumps are the same affine object with
multiplier one.  The automaton never stores a prime list or raw prime bitmap.
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from math import gcd, isqrt, prod
from typing import Iterable, Sequence, TypedDict

from number_compiler.arithmetic.automata.program_word import CanonicalWord, iter_runs
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle, binary_power
from number_compiler.arithmetic.fields.radix import (
    bit_width,
    digits_lsd,
    periodic_position_bases,
    symbol_runs,
)
from number_compiler.sequences.collatz.parity import CollatzParitySlab
from number_compiler.sequences.prime.wheel import (
    PackedWheelProgram,
    build_packed_wheel_program,
)


@dataclass(frozen=True, slots=True)
class FactoredCongruenceState:
    residues: tuple[int, ...]


@dataclass(frozen=True, slots=True)
class FactoredAffineMorphism:
    """Affine map on every component of one fixed factored modulus carrier."""

    moduli: tuple[int, ...]
    multipliers: tuple[int, ...]
    offsets: tuple[int, ...]
    symbols: int = 0
    compositions: int = 0

    def __post_init__(self) -> None:
        mods = tuple(map(int, self.moduli))
        if not mods or any(m <= 1 for m in mods):
            raise ValueError(mods)
        if len(self.multipliers) != len(mods) or len(self.offsets) != len(mods):
            raise ValueError("factored affine arity mismatch")
        object.__setattr__(self, "moduli", mods)
        object.__setattr__(
            self,
            "multipliers",
            tuple(int(a) % m for a, m in zip(self.multipliers, mods)),
        )
        object.__setattr__(
            self, "offsets", tuple(int(c) % m for c, m in zip(self.offsets, mods))
        )
        if self.symbols < 0 or self.compositions < 0:
            raise ValueError((self.symbols, self.compositions))

    @classmethod
    def identity(cls, moduli: Sequence[int]) -> "FactoredAffineMorphism":
        mods = tuple(map(int, moduli))
        return cls(mods, tuple(1 % m for m in mods), (0,) * len(mods), 0, 0)

    @classmethod
    def digit(
        cls, moduli: Sequence[int], radix: int, digit: int
    ) -> "FactoredAffineMorphism":
        mods = tuple(map(int, moduli))
        radix = int(radix)
        digit = int(digit)
        if radix < 2 or not 0 <= digit < radix:
            raise ValueError((radix, digit))
        return cls(
            mods, tuple(radix % m for m in mods), tuple(digit % m for m in mods), 1, 0
        )

    @classmethod
    def additive(cls, moduli: Sequence[int], delta: int) -> "FactoredAffineMorphism":
        mods = tuple(map(int, moduli))
        delta = int(delta)
        return cls(mods, tuple(1 for _ in mods), tuple(delta % m for m in mods), 1, 0)

    @property
    def cocycle(self) -> AffineCocycle[tuple[int, ...]]:
        return AffineCocycle(self.multipliers, self.offsets)

    def _then_raw(self, other: "FactoredAffineMorphism") -> "FactoredAffineMorphism":
        if self.moduli != other.moduli:
            raise ValueError("incompatible factored modulus carriers")

        def multiply(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
            return tuple((x * y) % m for x, y, m in zip(a, b, self.moduli))

        def add(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
            return tuple((x + y) % m for x, y, m in zip(a, b, self.moduli))

        cocycle = self.cocycle.then(other.cocycle, multiply=multiply, add=add)
        return FactoredAffineMorphism(
            self.moduli,
            cocycle.multiplier,
            cocycle.addend,
            self.symbols + other.symbols,
            0,
        )

    def then(self, other: "FactoredAffineMorphism") -> "FactoredAffineMorphism":
        out = self._then_raw(other)
        return FactoredAffineMorphism(
            out.moduli,
            out.multipliers,
            out.offsets,
            out.symbols,
            self.compositions + other.compositions + 1,
        )

    def power(self, exponent: int) -> "FactoredAffineMorphism":
        """Repeat this map through the shared binary-power kernel."""
        base = FactoredAffineMorphism(
            self.moduli, self.multipliers, self.offsets, self.symbols, 0
        )
        powered = binary_power(
            base,
            exponent,
            identity=FactoredAffineMorphism.identity(self.moduli),
            compose=FactoredAffineMorphism._then_raw,
        )
        result = powered.value
        return FactoredAffineMorphism(
            result.moduli,
            result.multipliers,
            result.offsets,
            result.symbols,
            powered.compositions,
        )

    def apply(self, state: FactoredCongruenceState) -> FactoredCongruenceState:
        if len(state.residues) != len(self.moduli):
            raise ValueError((len(state.residues), len(self.moduli)))
        return FactoredCongruenceState(
            tuple(
                (a * int(r) + c) % m
                for r, a, c, m in zip(
                    state.residues, self.multipliers, self.offsets, self.moduli
                )
            )
        )

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("factored_affine", self.moduli, self.multipliers, self.offsets)

    @property
    def description_bits(self) -> int:
        return sum(
            bit_width(m) + bit_width(a) + bit_width(c)
            for m, a, c in zip(self.moduli, self.multipliers, self.offsets)
        )


class _PrimeDecisionFrame(TypedDict):
    pos: int
    prefix: int
    state: FactoredCongruenceState
    next_digit: int
    children: list[int]
    incoming: int | None


def compile_radix_runs_morphism(
    moduli: Sequence[int], runs_msf: Iterable[tuple[int, int]], *, radix: int
) -> FactoredAffineMorphism:
    """Compile a most-significant-first RLE digit word without expanding runs."""
    result = FactoredAffineMorphism.identity(moduli)
    for digit, count in runs_msf:
        count = int(count)
        if count < 0:
            raise ValueError(count)
        if count:
            result = result.then(
                FactoredAffineMorphism.digit(moduli, radix, int(digit)).power(count)
            )
    return result


def compile_word_morphism(
    moduli: Sequence[int], word_msf: CanonicalWord, *, radix: int
) -> FactoredAffineMorphism:
    return compile_radix_runs_morphism(moduli, iter_runs(word_msf), radix=radix)


@dataclass(frozen=True, slots=True)
class FactoredPrimeAutomaton:
    """Exact bounded primality automaton over a packed squarefree wheel."""

    wheel: PackedWheelProgram

    @classmethod
    def build(cls, limit: int, *, word_bits: int = 62) -> "FactoredPrimeAutomaton":
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
        if not isinstance(state, FactoredCongruenceState):
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
        if not isinstance(parent_children, list):
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


@dataclass(frozen=True, slots=True)
class MixedRadixEncoding:
    """Exact periodic mixed-radix representation, least-significant digit first."""

    digits: tuple[int, ...]
    bases: tuple[int, ...]

    def __post_init__(self) -> None:
        if not self.digits or len(self.digits) != len(self.bases):
            raise ValueError((len(self.digits), len(self.bases)))
        if any(b < 2 or not 0 <= d < b for d, b in zip(self.digits, self.bases)):
            raise ValueError(self)

    @property
    def value(self) -> int:
        out = 0
        for digit, base in reversed(tuple(zip(self.digits, self.bases))):
            out = int(base) * out + int(digit)
        return out

    @property
    def payload_bits(self) -> int:
        return sum(max(1, (b - 1).bit_length()) for b in self.bases)


def encode_periodic_mixed_radix(value: int, bases: Sequence[int]) -> MixedRadixEncoding:
    value = int(value)
    period = tuple(map(int, bases))
    if value < 0 or not period or any(b < 2 for b in period):
        raise ValueError((value, period))
    if value == 0:
        return MixedRadixEncoding((0,), (period[0],))
    digits: list[int] = []
    used: list[int] = []
    n = value
    i = 0
    while n:
        base = period[i % len(period)]
        n, digit = divmod(n, base)
        digits.append(digit)
        used.append(base)
        i += 1
    result = MixedRadixEncoding(tuple(digits), tuple(used))
    if result.value != value:
        raise AssertionError((value, result))
    return result


def mixed_radix_morphism(
    moduli: Sequence[int], encoding: MixedRadixEncoding
) -> FactoredAffineMorphism:
    """Compile an exact mixed-radix number from MS digit to LS digit."""
    out = FactoredAffineMorphism.identity(moduli)
    for i in range(len(encoding.digits) - 1, -1, -1):
        out = out.then(
            FactoredAffineMorphism.digit(moduli, encoding.bases[i], encoding.digits[i])
        )
    return out


@dataclass(frozen=True, slots=True)
class CollatzFactoredResidueProjection:
    """Odd-modulus projection of one exact Collatz parity slab.

    The full slab keeps its exact dyadic domain.  On odd moduli, division by
    ``2**width`` is invertible, so the whole block is one factored affine map.
    ``exponent_bit_work`` charges the exponent lengths supplied to modular
    powering; it is logarithmic in the represented width/odd-count, not in the
    integer value of ``3**ones`` or ``2**width``.
    """

    morphism: FactoredAffineMorphism
    exponent_bit_work: int


def compile_collatz_slab_factored(
    slab: CollatzParitySlab, moduli: Sequence[int]
) -> CollatzFactoredResidueProjection:
    mods = tuple(map(int, moduli))
    if not mods or any(m <= 1 or m % 2 == 0 for m in mods):
        raise ValueError(mods)
    width = int(slab.width)
    ones = int(slab.ones)
    offset = int(slab.offset)
    multipliers = []
    offsets = []
    for modulus in mods:
        inv2k = pow(pow(2, width, modulus), -1, modulus)
        multipliers.append((pow(3, ones, modulus) * inv2k) % modulus)
        offsets.append((offset * inv2k) % modulus)
    morphism = FactoredAffineMorphism(
        mods, tuple(multipliers), tuple(offsets), width, 0
    )
    work = len(mods) * (bit_width(width) + bit_width(ones))
    return CollatzFactoredResidueProjection(morphism, work)


def binary_digit_reinterpretation_morphism(
    moduli: Sequence[int], value: int, target_base: int
) -> FactoredAffineMorphism:
    """Compile the binary 0/1 word of ``value`` while evaluating it in another radix.

    This is the morphism counterpart of :func:`reinterpret_binary_digits`.
    It does *not* preserve the arithmetic value unless ``target_base==2``; it
    preserves the digit language exactly and therefore exposes cyclotomic word
    identities such as Mersenne repunits and Fermat two-spike words.
    """
    value, target_base = int(value), int(target_base)
    if value < 0 or target_base < 2:
        raise ValueError((value, target_base))
    bits_msf = tuple(reversed(digits_lsd(value, 2)))
    return compile_radix_runs_morphism(moduli, symbol_runs(bits_msf), radix=target_base)


def reinterpret_binary_digits(value: int, target_base: int) -> int:
    """Interpret the *same* binary digit string as digits in ``target_base``."""
    value, target_base = int(value), int(target_base)
    if value < 0 or target_base < 2:
        raise ValueError((value, target_base))
    bits = digits_lsd(value, 2)
    return sum(int(bit) * pow(target_base, i) for i, bit in enumerate(bits))


def undo_binary_digit_reinterpretation(encoded: int, source_base: int) -> int:
    """Inverse of :func:`reinterpret_binary_digits` on its 0/1 digit image."""
    encoded, source_base = int(encoded), int(source_base)
    if encoded < 0 or source_base < 2:
        raise ValueError((encoded, source_base))
    digits = digits_lsd(encoded, source_base)
    if any(d not in (0, 1) for d in digits):
        raise ValueError("value is outside the binary-digit reinterpretation image")
    return sum(int(bit) << i for i, bit in enumerate(digits))


__all__ = [
    "FactoredCongruenceState",
    "FactoredAffineMorphism",
    "FactoredPrimeAutomaton",
    "compile_radix_runs_morphism",
    "compile_word_morphism",
    "FactoredPrimeDecisionCompilation",
    "compile_prime_block_factored_decision",
    "MixedRadixEncoding",
    "encode_periodic_mixed_radix",
    "mixed_radix_morphism",
    "CollatzFactoredResidueProjection",
    "compile_collatz_slab_factored",
    "binary_digit_reinterpretation_morphism",
    "reinterpret_binary_digits",
    "undo_binary_digit_reinterpretation",
]
