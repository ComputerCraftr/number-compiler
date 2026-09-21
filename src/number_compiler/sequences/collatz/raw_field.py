"""Carry-free raw-digit and sentinel quotients for accelerated Collatz.

For an odd source with radix-``b`` digits ``d_i``, the unnormalised odd-step
field

    r_i = 3*d_i + [i=0]

already represents the integer ``3*n+1`` exactly with the original radix
weights.  It is therefore unnecessary to retain a parallel normalised digit
word *and* carry vector merely to know the value.

A particularly strong coordinate appears when ``B = 4**m``.  Put

    D = (B-1)/3.

Then ``D`` repeated in the low radix positions is exactly the 2-adic residue
``-1/3``.  If ``q`` complete low digits equal ``D`` and the next digit is
``x != D``, then

    v2(3*n+1) = q*log2(B) + v2(3*x+1).

The residual valuation is strictly smaller than ``log2(B)``, so one first-hole
summary plus one digit determines the complete accelerated Collatz valuation.
No multiplication carry vector or divisibility-lane family is needed.

After removing the sentinel run, ``(3*m+1)/2**t`` is compiled directly from a
redundant raw field and one scalar normalisation carry.  The raw field and the
carry vector are never retained as semantic state.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from dataclasses import dataclass

from number_compiler.arithmetic.automata.program_word import CanonicalWord
from number_compiler.arithmetic.carry.carry_symmetry import (
    collatz_mul3_carry_action_arena,
    collatz_mul3_carry_word_action,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.arithmetic.formula.formula import FormulaArena, FormulaRoot


def affine_sentinel_digit(base: int) -> int:
    """Return ``D=(base-1)/3`` when the radix admits the Collatz sentinel."""
    base = int(base)
    if base < 4 or (base - 1) % 3:
        raise ValueError("Collatz sentinel requires base == 1 (mod 3)")
    return (base - 1) // 3


@dataclass(frozen=True, slots=True)
class CollatzSentinelBoundarySummary:
    """Two-sided quotient of a digit block relative to the repeated sentinel.

    ``low_first_mismatch`` and ``low_mismatch_digit`` support the valuation /
    radix-factor first-hole query. ``high_relation`` is the sign of the most
    significant non-sentinel digit versus ``D`` and therefore decides the
    width-growth threshold. Zero means every digit equals the sentinel.
    """

    length: int
    all_sentinel: bool
    low_first_mismatch: int | None
    low_mismatch_digit: int | None
    high_relation: int

    def __post_init__(self) -> None:
        if self.length < 0 or self.high_relation not in (-1, 0, 1):
            raise ValueError(self)
        if self.all_sentinel != (self.low_first_mismatch is None):
            raise ValueError(self)
        if self.all_sentinel != (self.low_mismatch_digit is None):
            raise ValueError(self)
        if self.all_sentinel != (self.high_relation == 0):
            raise ValueError(self)
        if self.low_first_mismatch is not None and not (
            0 <= self.low_first_mismatch < self.length
        ):
            raise ValueError(self)

    @staticmethod
    def identity() -> CollatzSentinelBoundarySummary:
        return CollatzSentinelBoundarySummary(0, True, None, None, 0)

    @staticmethod
    def run(digit: int, count: int, sentinel: int) -> CollatzSentinelBoundarySummary:
        digit, count, sentinel = int(digit), int(count), int(sentinel)
        if count < 0:
            raise ValueError(count)
        if count == 0:
            return CollatzSentinelBoundarySummary.identity()
        if digit == sentinel:
            return CollatzSentinelBoundarySummary(count, True, None, None, 0)
        relation = -1 if digit < sentinel else 1
        return CollatzSentinelBoundarySummary(count, False, 0, digit, relation)

    @staticmethod
    def atom(digit: int, sentinel: int) -> CollatzSentinelBoundarySummary:
        return CollatzSentinelBoundarySummary.run(digit, 1, sentinel)

    def then(
        self, other: CollatzSentinelBoundarySummary
    ) -> CollatzSentinelBoundarySummary:
        # self is the less-significant block, other the more-significant block.
        if self.low_first_mismatch is not None:
            low = self.low_first_mismatch
            low_digit = self.low_mismatch_digit
        elif other.low_first_mismatch is not None:
            low = self.length + other.low_first_mismatch
            low_digit = other.low_mismatch_digit
        else:
            low = None
            low_digit = None
        high = other.high_relation if other.high_relation else self.high_relation
        return CollatzSentinelBoundarySummary(
            self.length + other.length,
            self.all_sentinel and other.all_sentinel,
            low,
            low_digit,
            high,
        )

    @property
    def digit_growth(self) -> bool:
        # Equality is the exact threshold 3*n+1 == B**width.
        return self.high_relation >= 0

    def power4_valuation(self, *, base: int) -> int:
        bits = power4_radix_bits(base)
        if self.all_sentinel:
            return self.length * bits
        if self.low_first_mismatch is None or self.low_mismatch_digit is None:
            raise AssertionError(self)
        local = v2_positive(3 * self.low_mismatch_digit + 1)
        if local >= bits:
            raise AssertionError((base, self.low_mismatch_digit, local))
        return self.low_first_mismatch * bits + local

    def accelerated_growth_character(self, *, base: int) -> int:
        """Return the primitive modulo-four character without acquiring ``v2``.

        For a positive odd source, ``chi_4(n)=-1`` exactly when the low
        base-four residue is three, which is exactly the strict-growth branch
        ``v2(3*n+1)=1``.  A complete low sentinel has residue one modulo four,
        so any nonzero sentinel prefix is immediately nonincreasing.
        """
        power4_radix_bits(base)
        if self.all_sentinel or self.low_first_mismatch != 0:
            return 1
        digit = self.low_mismatch_digit
        if digit is None or not (digit & 1):
            raise ValueError((base, digit))
        residue = int(digit) & 3
        if residue not in (1, 3):
            raise AssertionError((base, digit, residue))
        return 1 if residue == 1 else -1

    def accelerated_increases(self, *, base: int) -> bool:
        """Strict-growth observer; deliberately does not compute the valuation."""
        return self.accelerated_growth_character(base=base) == -1

    def accelerated_nonincreasing(self, *, base: int) -> bool:
        return self.accelerated_growth_character(base=base) == 1


def summarize_collatz_sentinel_boundaries(
    digits: Sequence[int], *, base: int
) -> CollatzSentinelBoundarySummary:
    sentinel = affine_sentinel_digit(base)
    level = [CollatzSentinelBoundarySummary.atom(int(d), sentinel) for d in digits]
    if not level:
        return CollatzSentinelBoundarySummary.identity()
    while len(level) > 1:
        nxt: list[CollatzSentinelBoundarySummary] = []
        it = iter(level)
        for left in it:
            right = next(it, None)
            nxt.append(left if right is None else left.then(right))
        level = nxt
    return level[0]


def summarize_collatz_sentinel_word(
    word: CanonicalWord, *, base: int
) -> CollatzSentinelBoundarySummary:
    """Summarize a canonical RLE/SLP digit word without expanding run lengths."""
    from number_compiler.arithmetic.automata.program_word import CanonicalWord

    if not isinstance(word, CanonicalWord):
        raise TypeError(type(word))
    sentinel = affine_sentinel_digit(base)
    memo: dict[int, CollatzSentinelBoundarySummary] = {}
    stack: list[tuple[CanonicalWord, bool]] = [(word, False)]
    while stack:
        node, ready = stack.pop()
        if node.node_id in memo:
            continue
        if not node.run_count:
            memo[node.node_id] = CollatzSentinelBoundarySummary.identity()
            continue
        if node.run_count == 1:
            if node.symbol is None:
                raise AssertionError(node)
            memo[node.node_id] = CollatzSentinelBoundarySummary.run(
                int(node.symbol), int(node.run_length), sentinel
            )
            continue
        if node.left is None or node.right is None:
            raise AssertionError(node)
        if not ready:
            stack.append((node, True))
            if node.right.node_id not in memo:
                stack.append((node.right, False))
            if node.left.node_id not in memo:
                stack.append((node.left, False))
            continue
        memo[node.node_id] = memo[node.left.node_id].then(memo[node.right.node_id])
    return memo[word.node_id]


def power4_radix_bits(base: int) -> int:
    """Return ``a`` for ``base=2**a`` with even positive ``a``."""
    base = int(base)
    if base < 4 or base & (base - 1):
        raise ValueError("sentinel radix must be a power of four")
    bits = base.bit_length() - 1
    if bits & 1:
        raise ValueError("sentinel radix must be a power of four")
    return bits


def collatz_sentinel_digit(base: int) -> int:
    """The repeated radix digit representing the 2-adic integer ``-1/3``."""
    power4_radix_bits(base)
    return affine_sentinel_digit(int(base))


@dataclass(frozen=True, slots=True)
class CollatzRawDigitField:
    """Canonical redundant representation of ``3*n+1`` for one odd step.

    Only the raw coefficients are retained.  Source digits, normalised output
    digits and carry vectors are derived views and are deliberately absent.
    """

    base: int
    coefficients: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.base < 2 or not self.coefficients:
            raise ValueError((self.base, self.coefficients))
        for i, raw in enumerate(self.coefficients):
            delta = int(i == 0)
            if raw < delta or (raw - delta) % 3:
                raise ValueError((i, raw))
            digit = (raw - delta) // 3
            if not 0 <= digit < self.base:
                raise ValueError((i, raw, digit))

    @classmethod
    def from_odd_digits(
        cls, digits: Sequence[int], *, base: int
    ) -> CollatzRawDigitField:
        ds = tuple(map(int, digits))
        if not ds or any(not 0 <= d < int(base) for d in ds) or not (ds[0] & 1):
            raise ValueError((digits, base))
        return cls(int(base), tuple(3 * d + int(i == 0) for i, d in enumerate(ds)))

    @classmethod
    def from_odd_value(cls, value: int, *, base: int = 10) -> CollatzRawDigitField:
        value = int(value)
        if value <= 0 or not (value & 1):
            raise ValueError(value)
        return cls.from_odd_digits(digits_lsd(value, int(base)), base=int(base))

    @property
    def max_component(self) -> int:
        return max(self.coefficients)

    @property
    def description_bits(self) -> int:
        # Self-delimiting fixed-alphabet charge: coefficient payload plus base.
        width = max(1, (3 * self.base - 2).bit_length())
        return len(self.coefficients) * width + max(1, self.base.bit_length())

    def source_digit(self, index: int) -> int:
        raw = self.coefficients[int(index)]
        return (raw - int(index == 0)) // 3

    def source_digits(self) -> tuple[int, ...]:
        return tuple(self.source_digit(i) for i in range(len(self.coefficients)))

    def represented_value(self) -> int:
        return sum(int(r) * self.base**i for i, r in enumerate(self.coefficients))

    def source_value(self) -> int:
        raw = self.represented_value()
        if (raw - 1) % 3:
            raise AssertionError(raw)
        return (raw - 1) // 3

    def normalization_carries(self) -> tuple[int, ...]:
        """Derived carry boundaries for diagnostics; never retained as state."""
        carry = 0
        out = [0]
        for raw in self.coefficients:
            carry = (int(raw) + carry) // self.base
            out.append(carry)
        return tuple(out)

    def normalized_digits(self) -> tuple[int, ...]:
        """Project to ordinary radix digits with one scalar carry, no vector."""
        out: list[int] = []
        carry = 0
        for raw in self.coefficients:
            total = int(raw) + carry
            out.append(total % self.base)
            carry = total // self.base
        while carry:
            out.append(carry % self.base)
            carry //= self.base
        while len(out) > 1 and out[-1] == 0:
            out.pop()
        return tuple(out)

    def terminal_carry(self) -> int:
        # ``3*d_0+1`` is the ordinary multiply-by-3 carry kernel with incoming
        # carry one.  The shared oriented arena quotients mirrored/complemented
        # carry words before assigning cache identity.
        arena = collatz_mul3_carry_action_arena(self.base)
        action = collatz_mul3_carry_word_action(
            self.source_digits(),
            base=self.base,
            arena=arena,
        )
        return arena.apply(action.ref, 1)

    def boundary_summary(self) -> CollatzSentinelBoundarySummary:
        """Canonical two-sided theorem interface derived from the raw coordinate."""
        return summarize_collatz_sentinel_boundaries(
            self.source_digits(), base=self.base
        )

    @property
    def digit_growth(self) -> bool:
        """Exact width growth, synthesized from the sentinel theorem when available."""
        if self.base >= 4 and (self.base - 1) % 3 == 0:
            return self.boundary_summary().digit_growth
        return self.terminal_carry() != 0

    def sentinel_radix_factor_run(self) -> int:
        """Number of low radix factors from the canonical first-hole summary.

        If the source ends in ``q`` copies of ``D=(B-1)/3`` then
        ``3*n+1 = B**q * (3*m+1)``.  The run length is therefore a derived
        property of the same two-sided summary that also decides width growth.
        """
        summary = self.boundary_summary()
        if summary.all_sentinel:
            return summary.length
        assert summary.low_first_mismatch is not None
        return summary.low_first_mismatch

    def sentinel_valuation(self) -> int:
        """Exact ``v2(3*n+1)`` from the same power-of-four sentinel summary."""
        power4_radix_bits(self.base)
        return self.boundary_summary().power4_valuation(base=self.base)


@dataclass(frozen=True, slots=True)
class CollatzSentinelStep:
    """One exact accelerated odd step in a power-of-four radix."""

    base: int
    sentinel_digit: int
    stripped_digits: int
    local_shift: int
    valuation: int
    source_width: int
    target_digits: tuple[int, ...]
    scalar_carry_peak: int

    @property
    def target_width(self) -> int:
        return len(self.target_digits)

    @property
    def valuation_digit_checks(self) -> int:
        # One equality check per complete sentinel digit, plus the first
        # mismatch when it exists.  An all-sentinel finite word needs no
        # implicit top-digit materialization.
        return min(self.source_width, self.stripped_digits + 1)

    @property
    def increases(self) -> bool:
        return self.valuation == 1

    @property
    def nonincreasing(self) -> bool:
        return self.valuation >= 2

    @property
    def summary_description_bits(self) -> int:
        return (
            max(1, self.base.bit_length())
            + max(1, (self.stripped_digits + 1).bit_length())
            + max(1, (self.local_shift + 1).bit_length())
            + max(1, (self.scalar_carry_peak + 1).bit_length())
        )


def _canonicalize_redundant(
    coefficients: Iterable[int], base: int
) -> tuple[tuple[int, ...], int]:
    """Normalize a coefficient stream with only one live scalar carry."""
    out: list[int] = []
    carry = 0
    peak = 0
    for coefficient in coefficients:
        total = int(coefficient) + carry
        out.append(total % base)
        carry = total // base
        peak = max(peak, carry)
    while carry:
        out.append(carry % base)
        carry //= base
        peak = max(peak, carry)
    while len(out) > 1 and out[-1] == 0:
        out.pop()
    return tuple(out), peak


def _raw_divided_coefficients(
    suffix: Sequence[int], *, base: int, shift: int
) -> Iterable[int]:
    """Yield a redundant field for ``(3*m+1)/2**shift`` without carry state."""
    if shift < 0:
        raise ValueError(shift)
    factor = 1 << shift
    if base % factor:
        raise ValueError((base, shift))
    bridge = base // factor
    ds = tuple(map(int, suffix))
    for i, digit in enumerate(ds):
        raw = 3 * digit + int(i == 0)
        next_raw = 3 * ds[i + 1] if i + 1 < len(ds) else 0
        yield raw // factor + (next_raw % factor) * bridge


def accelerated_collatz_sentinel_step_digits(
    digits: Sequence[int], *, base: int = 16
) -> CollatzSentinelStep:
    """Accelerated odd Collatz using sentinel stripping + a scalar carry only.

    ``digits`` are canonical LSF radix digits of a positive odd source.  The
    function never constructs the full ``3*n+1`` carry vector.
    """
    base = int(base)
    bits = power4_radix_bits(base)
    ds = tuple(map(int, digits))
    if not ds or any(not 0 <= d < base for d in ds) or not (ds[0] & 1):
        raise ValueError((digits, base))
    if base == 64 and ds[-1] != 0:
        from number_compiler.sequences.collatz.radix64_transducer import (
            compose_radix64_events,
        )

        result = compose_radix64_events(ds)
        return CollatzSentinelStep(
            64,
            21,
            result.source_frame,
            result.source_shift,
            result.valuation,
            len(ds),
            result.target_digits,
            result.carry_peak,
        )
    sentinel = collatz_sentinel_digit(base)
    q = 0
    while q < len(ds) and ds[q] == sentinel:
        q += 1
    suffix = ds[q:]
    if suffix:
        first = suffix[0]
        local = v2_positive(3 * first + 1)
        if local >= bits:
            # ``first == sentinel`` would be the unique way to reach ``bits``.
            raise AssertionError((first, sentinel, local, bits))
        target, peak = _canonicalize_redundant(
            _raw_divided_coefficients(suffix, base=base, shift=local), base
        )
    else:
        # n=(B**q-1)/3, hence 3*n+1=B**q and the accelerated target is 1.
        local = 0
        target, peak = (1,), 0
    valuation = q * bits + local
    return CollatzSentinelStep(
        base, sentinel, q, local, valuation, len(ds), target, peak
    )


def accelerated_collatz_sentinel_step(
    value: int, *, base: int = 16
) -> CollatzSentinelStep:
    value = int(value)
    if value <= 0 or not (value & 1):
        raise ValueError(value)
    return accelerated_collatz_sentinel_step_digits(
        digits_lsd(value, int(base)), base=int(base)
    )


@dataclass(frozen=True, slots=True)
class CollatzSentinelFormulaStep:
    index: int
    valuation: int
    stripped_digits: int
    local_shift: int
    root: FormulaRoot
    formula_nodes: int
    formula_description_bits: int


def _drop_low_formula_digits(
    arena: FormulaArena, root: FormulaRoot, count: int
) -> FormulaRoot:
    from number_compiler.arithmetic.formula.formula import FormulaRoot

    count = int(count)
    if count < 0 or count >= root.width:
        raise ValueError((count, root.width))
    width = root.width - count
    return FormulaRoot(
        tuple(arena.crop(arena.shr(p, count), width) for p in root.planes)
    )


def accelerated_collatz_sentinel_formula_step(
    arena: FormulaArena, root: FormulaRoot, *, base: int = 4
) -> tuple[FormulaRoot, int, int, int]:
    """Exact accelerated odd step on a closed formula root.

    The low sentinel run is removed structurally before arithmetic.  The only
    multiplication carry machinery is the existing finite transducer monoid;
    no concrete carry vector is materialized.  The residual division is at
    most ``log2(base)-1`` local radius-1 divide-by-two maps.
    """
    from number_compiler.arithmetic.carry.prefix_monoid import (
        compile_formula_prefix_predicate,
    )
    from number_compiler.arithmetic.fields.digit_formula import (
        DigitSpec,
        closed_digit_at,
        digit_root_from_int,
        digit_value_masks,
        multiply_add_formula,
    )
    from number_compiler.sequences.collatz.radix import local_half_even_radix

    base = int(base)
    bits = power4_radix_bits(base)
    spec = DigitSpec(base)
    if root.plane_count != spec.plane_count:
        raise ValueError((root.plane_count, spec.plane_count))
    sentinel = collatz_sentinel_digit(base)
    sentinel_mask = digit_value_masks(arena, root, spec)[sentinel]
    sentinel_prefix = compile_formula_prefix_predicate(arena, sentinel_mask)
    q = sentinel_prefix.first_false(arena)
    if q == root.width:
        # Exact identity 3*((B**q-1)/3)+1=B**q.
        return digit_root_from_int(1, arena, spec), q * bits, q, 0
    first = closed_digit_at(arena, root, q)
    local = v2_positive(3 * first + 1)
    if local >= bits:
        raise AssertionError((base, q, first, local))
    suffix = root if q == 0 else _drop_low_formula_digits(arena, root, q)
    out, _compiled = multiply_add_formula(arena, suffix, spec, 3, 1)
    for _ in range(local):
        # The exact first-hole valuation proves these divisions are integral.
        # Floor division has the same result and avoids rediscovering parity.
        out = local_half_even_radix(arena, out, spec)
    return out, q * bits + local, q, local


def collatz_sentinel_orbit(
    seed: int, *, base: int = 16, max_odd_steps: int = 10000
) -> tuple[CollatzSentinelStep, ...]:
    """Forward an explicit sentinel orbit request to the proof oracle."""
    from number_compiler.projection.collatz_orbits.sentinel import (
        collatz_sentinel_orbit as lower_orbit,
    )

    return lower_orbit(
        seed,
        base=base,
        max_odd_steps=max_odd_steps,
    )


def collatz_orbit_formulas_sentinel_power4(
    seed: int,
    *,
    radix: int = 4,
    max_odd_steps: int = 10000,
    materialize_values: bool = False,
) -> tuple[FormulaArena, tuple[CollatzSentinelFormulaStep, ...]]:
    """Forward an explicit sentinel formula orbit to the proof oracle."""
    from number_compiler.projection.collatz_orbits.sentinel import (
        collatz_orbit_formulas_sentinel_power4 as lower_orbit,
    )

    return lower_orbit(
        seed,
        radix=radix,
        max_odd_steps=max_odd_steps,
        materialize_values=materialize_values,
    )


__all__ = [
    "CollatzRawDigitField",
    "CollatzSentinelBoundarySummary",
    "CollatzSentinelFormulaStep",
    "CollatzSentinelStep",
    "accelerated_collatz_sentinel_formula_step",
    "accelerated_collatz_sentinel_step",
    "accelerated_collatz_sentinel_step_digits",
    "affine_sentinel_digit",
    "collatz_orbit_formulas_sentinel_power4",
    "collatz_sentinel_digit",
    "collatz_sentinel_orbit",
    "power4_radix_bits",
    "summarize_collatz_sentinel_boundaries",
    "summarize_collatz_sentinel_word",
]
