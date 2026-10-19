"""Derived carry/event itinerary quotients for reverse-and-add.

This module is research/compiler support, not a second semantic root.  It collects
coordinates that are exact consequences of the canonical pair field:

* the three-symbol threshold itinerary whose last non-neutral symbol determines
  the forward carry;
* cyclic and negacyclic polynomial quotients used to expose annihilating /
  rank-collapsing transport factors;
* the ``(z+1)``-primary jet, where growth is literally a nilpotent shift;
* the bounded growth-run/no-growth epoch itinerary implied by the universal
  three-growth-run bound.

The raw itinerary/slab is a proof/compiler certificate, not production cache
identity.  Causal reverse/add powering quotients it through the exact forcing
epimorphism before temporal caching.
"""

from __future__ import annotations

import itertools
from collections.abc import Callable, Sequence
from dataclasses import dataclass
from math import comb, gcd

from number_compiler.arithmetic.carry.event_memory import (
    carry_field,
    event_memory_horizon,
    forcing_event_from_carry,
    pair_plane_bits,
    reconstruct_pair_from_carry_window,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.arithmetic.polynomials.cyclotomic import is_power_of_two
from number_compiler.arithmetic.polynomials.cyclotomic_transport import (
    power_two_cyclotomic_annihilated,
)
from number_compiler.arithmetic.polynomials.modular_linear import row_reduce_mod_prime

LOW = -1
NEUTRAL = 0
HIGH = 1


def carry_threshold_itinerary(
    pair: Sequence[int], *, base: int = 10
) -> tuple[int, ...]:
    """Return ``sign(S_i-(b-1))`` in ``{-1,0,+1}``.

    For the carry recurrence ``C_(i+1)=[S_i+C_i>=b]`` a LOW symbol resets the
    carry to zero, HIGH resets it to one, and NEUTRAL preserves the incoming
    carry.  Hence the carry at every boundary is the state of the last
    non-neutral event.
    """
    base = int(base)
    values = tuple(map(int, pair))
    if base < 2 or not values or any(not 0 <= v <= 2 * (base - 1) for v in values):
        raise ValueError((base, values))
    threshold = base - 1
    return tuple(
        LOW if v < threshold else HIGH if v > threshold else NEUTRAL for v in values
    )


def carry_from_threshold_itinerary(symbols: Sequence[int]) -> tuple[int, ...]:
    """Recover exact carry boundaries ``C_0..C_d`` from threshold symbols."""
    carry = 0
    out = [0]
    for symbol in map(int, symbols):
        if symbol == LOW:
            carry = 0
        elif symbol == HIGH:
            carry = 1
        elif symbol != NEUTRAL:
            raise ValueError(symbol)
        out.append(carry)
    return tuple(out)


def threshold_reset_count(symbols: Sequence[int]) -> int:
    return sum(int(s) != NEUTRAL for s in symbols)


def digit_pair_sum_fiber_size(total: int, *, base: int = 10) -> int:
    """Number of ordered radix-digit pairs ``(a,b)`` with ``a+b=total``.

    This is the additive analogue of the prime hyperbolic factor fiber.  The
    canonical reverse-and-add pair field has already quotiented these fibers:
    carry/event evolution consumes only the sum, never the individual pair.
    """
    total, base = int(total), int(base)
    if base < 2 or not 0 <= total <= 2 * (base - 1):
        raise ValueError((total, base))
    return total + 1 if total < base else 2 * base - 1 - total


def outer_digit_pair_sum_fiber_size(total: int, *, base: int = 10) -> int:
    """Fixed-width outer-pair fiber, requiring the most-significant digit nonzero."""
    total, base = int(total), int(base)
    size = digit_pair_sum_fiber_size(total, base=base)
    return size - int(total < base)  # remove the unique (MSD=0, LSD=total) choice


def pair_field_preimage_count(pair: Sequence[int], *, base: int = 10) -> int:
    """Number of fixed-width digit strings represented by one symmetric pair field."""
    values = tuple(map(int, pair))
    base = int(base)
    if not values or values != values[::-1]:
        raise ValueError("symmetric pair field required")
    count = 1
    half = len(values) // 2
    for i in range(half):
        count *= (
            outer_digit_pair_sum_fiber_size(values[i], base=base)
            if i == 0
            else digit_pair_sum_fiber_size(values[i], base=base)
        )
    if len(values) & 1:
        middle = values[len(values) // 2]
        if middle & 1 or not 0 <= middle // 2 < base:
            return 0
    return count


def _quotient_values(
    values: Sequence[int], size: int, modulus: int
) -> tuple[tuple[int, ...], int, int]:
    normalized = tuple(map(int, values))
    size, modulus = int(size), int(modulus)
    if size <= 0 or modulus <= 1:
        raise ValueError((size, modulus))
    return normalized, size, modulus


def _advance_values(
    state: Sequence[int], growth: int, modulus: int
) -> tuple[tuple[int, ...], int, int]:
    normalized = tuple(map(int, state))
    growth, modulus = int(growth), int(modulus)
    if not normalized or growth not in (0, 1) or modulus <= 1:
        raise ValueError((len(normalized), growth, modulus))
    return normalized, growth, modulus


def _doubled_event(
    state: Sequence[int], event: Sequence[int], modulus: int
) -> tuple[int, ...]:
    return tuple(
        (2 * value + forcing) % modulus
        for value, forcing in zip(state, event, strict=True)
    )


def _class_transport_kernel(
    classes: int, no_growth: int, growth: int, modulus: int, *, negacyclic: bool
) -> tuple[int, ...]:
    classes, no_growth, growth, modulus = map(
        int, (classes, no_growth, growth, modulus)
    )
    if classes <= 0 or no_growth < 0 or growth < 0 or modulus <= 1:
        raise ValueError((classes, no_growth, growth, modulus))
    scale = pow(2, no_growth, modulus)
    out = [0] * classes
    for index in range(growth + 1):
        quotient, remainder = divmod(index, classes)
        sign = -1 if negacyclic and quotient & 1 else 1
        out[remainder] = (out[remainder] + sign * scale * comb(growth, index)) % modulus
    return tuple(out)


def _adaptive_memory_horizon(
    growth_bits: Sequence[int],
    endpoint: int,
    size: int,
    bits: int,
    annihilated: Callable[..., bool],
    *,
    primary: bool = False,
) -> int | None:
    gs = tuple(map(int, growth_bits))
    endpoint, size, bits = int(endpoint), int(size), int(bits)
    if (
        not 0 <= endpoint <= len(gs)
        or size <= 0
        or bits <= 0
        or any(g not in (0, 1) for g in gs)
    ):
        raise ValueError((endpoint, size, bits))
    kwargs = {"bits": bits} if primary else {"modulus": 1 << bits}
    no_growth = growth = 0
    for length in range(1, endpoint + 1):
        bit = gs[endpoint - length]
        growth += bit
        no_growth += 1 - bit
        if annihilated(size, no_growth, growth, **kwargs):
            return length
    return None


def cyclic_class_sums(
    values: Sequence[int], classes: int, modulus: int
) -> tuple[int, ...]:
    """Coefficient vector of ``sum values[i] z**i`` modulo ``z**classes-1``."""
    values, classes, modulus = _quotient_values(values, classes, modulus)
    out = [0] * classes
    for i, value in enumerate(values):
        out[i % classes] = (out[i % classes] + value) % modulus
    return tuple(out)


def cyclic_pair_advance(
    state: Sequence[int], event: Sequence[int], growth: int, *, modulus: int
) -> tuple[int, ...]:
    """Advance an exact cyclic quotient under ``S' = A_g S + E``.

    ``growth=0`` uses ``A_0=2``.  ``growth=1`` uses ``A_1=1+z`` with cyclic
    indexing.  The event may be the full event row or an already-quotiented
    vector of the same class count.
    """
    state, growth, modulus = _advance_values(state, growth, modulus)
    classes = len(state)
    if len(event) == classes:
        ev = tuple(int(x) % modulus for x in event)
    else:
        ev = cyclic_class_sums(event, classes, modulus)
    if growth == 0:
        return _doubled_event(state, ev, modulus)
    return tuple(
        (state[i] + state[(i - 1) % classes] + ev[i]) % modulus for i in range(classes)
    )


def cyclic_transport_kernel(
    classes: int, no_growth: int, growth: int, *, modulus: int
) -> tuple[int, ...]:
    """Kernel of ``2**q (1+z)**r`` in ``Z/modulus[z]/(z**m-1)``."""
    return _class_transport_kernel(
        classes, no_growth, growth, modulus, negacyclic=False
    )


def cyclic_transport_annihilated(
    classes: int, no_growth: int, growth: int, *, modulus: int
) -> bool:
    return not any(cyclic_transport_kernel(classes, no_growth, growth, modulus=modulus))


def negacyclic_class_sums(
    values: Sequence[int], classes: int, modulus: int
) -> tuple[int, ...]:
    """Coefficient vector modulo ``z**classes+1``.

    A coefficient at index ``q*classes+r`` folds into class ``r`` with sign
    ``(-1)**q``.  At integer radix ``b`` this is the polynomial interface behind
    residues modulo ``b**classes+1`` (for example decimal mod 101 at classes=2).
    """
    values, classes, modulus = _quotient_values(values, classes, modulus)
    out = [0] * classes
    for i, value in enumerate(values):
        q, r = divmod(i, classes)
        sign = -1 if q & 1 else 1
        out[r] = (out[r] + sign * value) % modulus
    return tuple(out)


def negacyclic_pair_advance(
    state: Sequence[int], event: Sequence[int], growth: int, *, modulus: int
) -> tuple[int, ...]:
    """Advance ``S' = A_g S + E`` in ``Z/modulus[z]/(z**m+1)``."""
    state, growth, modulus = _advance_values(state, growth, modulus)
    classes = len(state)
    # ``len(event)==classes`` is ambiguous (a raw event can have exactly m
    # digits), so the public primitive always treats ``event`` as raw values.
    ev = negacyclic_class_sums(event, classes, modulus)
    if growth == 0:
        return _doubled_event(state, ev, modulus)
    out: list[int] = []
    for i in range(classes):
        shifted = -state[-1] if i == 0 else state[i - 1]
        out.append((state[i] + shifted + ev[i]) % modulus)
    return tuple(out)


def negacyclic_transport_kernel(
    classes: int, no_growth: int, growth: int, *, modulus: int
) -> tuple[int, ...]:
    """Kernel of ``2**q(1+z)**r`` modulo ``(z**m+1, modulus)``."""
    return _class_transport_kernel(classes, no_growth, growth, modulus, negacyclic=True)


def negacyclic_transport_annihilated(
    classes: int, no_growth: int, growth: int, *, modulus: int
) -> bool:
    classes, no_growth, growth, modulus = map(
        int, (classes, no_growth, growth, modulus)
    )
    # For the power-of-two cyclotomic family Phi_(2m)=z**m+1 over a 2-power
    # coefficient modulus, use the closed valuation theorem rather than
    # expanding the binomial kernel.  The expanded kernel remains available as
    # an independent differential/proof path.
    if is_power_of_two(classes) and is_power_of_two(modulus):
        bits = modulus.bit_length() - 1
        return power_two_cyclotomic_annihilated(classes, no_growth, growth, bits=bits)
    return not any(
        negacyclic_transport_kernel(classes, no_growth, growth, modulus=modulus)
    )


def adaptive_negacyclic_memory_horizon(
    growth_bits: Sequence[int], endpoint: int, *, classes: int, bits: int
) -> int | None:
    """Exact old-state dependency horizon in a negacyclic ``2**bits`` quotient."""
    return _adaptive_memory_horizon(
        growth_bits,
        endpoint,
        classes,
        bits,
        negacyclic_transport_annihilated,
        primary=False,
    )


def zplus1_jet(values: Sequence[int], degree: int, modulus: int) -> tuple[int, ...]:
    """Return ``S(z)`` modulo ``((z+1)**degree, modulus)`` in ``y=z+1`` coordinates.

    With ``z=y-1``, ``z**i = sum_j C(i,j)(-1)**(i-j)y**j``.  The resulting
    jet is an exact polynomial quotient; no point evaluation or digit materialization
    is hidden behind the representation.
    """
    values, degree, modulus = _quotient_values(values, degree, modulus)
    out = [0] * degree
    for i, value in enumerate(values):
        for j in range(min(i, degree - 1) + 1):
            sign = -1 if (i - j) & 1 else 1
            out[j] = (out[j] + sign * value * comb(i, j)) % modulus
    return tuple(out)


def zplus1_jet_advance(
    state: Sequence[int], event: Sequence[int], growth: int, *, modulus: int
) -> tuple[int, ...]:
    """Advance a ``(z+1)``-primary jet.

    In ``y=z+1`` coordinates, ``A_0=2`` and ``A_1=y``.  Thus growth is a
    literal one-place nilpotent shift; this is the strongest polynomial
    conjugacy found by the residue audit.
    """
    state, growth, modulus = _advance_values(state, growth, modulus)
    degree = len(state)
    # As above, raw width can equal the quotient degree.  Never infer an
    # already-projected event from length alone.
    ev = zplus1_jet(event, degree, modulus)
    if growth == 0:
        return _doubled_event(state, ev, modulus)
    return tuple((ev[j] + (state[j - 1] if j else 0)) % modulus for j in range(degree))


def zplus1_transport_annihilated(
    degree: int, no_growth: int, growth: int, *, bits: int
) -> bool:
    """Whether ``2**q y**r`` is zero in ``Z/2**bits[y]/y**degree``."""
    degree, no_growth, growth, bits = map(int, (degree, no_growth, growth, bits))
    if degree <= 0 or no_growth < 0 or growth < 0 or bits <= 0:
        raise ValueError((degree, no_growth, growth, bits))
    return no_growth >= bits or growth >= degree


def adaptive_zplus1_memory_horizon(
    growth_bits: Sequence[int], endpoint: int, *, degree: int, bits: int
) -> int | None:
    """Exact dependency horizon in the primary jet quotient."""
    return _adaptive_memory_horizon(
        growth_bits, endpoint, degree, bits, zplus1_transport_annihilated, primary=True
    )


def adaptive_cyclic_memory_horizon(
    growth_bits: Sequence[int], endpoint: int, *, classes: int, bits: int
) -> int | None:
    """Smallest recent interval whose transport annihilates all older state.

    ``endpoint`` counts transitions, so the inspected operators are
    ``growth_bits[endpoint-k:endpoint]``.  ``None`` means the supplied prefix is
    too short to prove annihilation.
    """
    return _adaptive_memory_horizon(
        growth_bits,
        endpoint,
        classes,
        bits,
        cyclic_transport_annihilated,
        primary=False,
    )


def growth_run_itinerary(
    growth_bits: Sequence[int], *, include_trailing: bool = False
) -> tuple[int, ...]:
    """Run lengths of growth steps immediately preceding each no-growth step.

    Reverse-and-add has the proved universal bound ``run<=3``.  Keeping this
    function generic lets tests reject an invalid stream instead of silently
    truncating it.
    """
    runs: list[int] = []
    run = 0
    for g in map(int, growth_bits):
        if g == 1:
            run += 1
        elif g == 0:
            runs.append(run)
            run = 0
        else:
            raise ValueError(g)
    if include_trailing and run:
        runs.append(run)
    return tuple(runs)


def live_event_suffix_start(events: Sequence[Sequence[int]], *, base: int = 10) -> int:
    """First event row whose contribution can still survive modulo ``2**w``.

    The input is ordinarily the proved fixed-H event window.  Event row ``j``
    is multiplied by one factor 2 for every *later* no-growth transition.  Once
    that count reaches ``w=pair_plane_bits(base)``, the whole transported row is
    zero modulo ``2**w`` and every still older row is dead as well.
    """
    rows = tuple(tuple(map(int, row)) for row in events)
    if not rows or any(not row for row in rows):
        raise ValueError("nonempty event rows required")
    widths = tuple(len(row) for row in rows)
    later_growths = tuple(b - a for a, b in itertools.pairwise(widths))
    if any(g not in (0, 1) for g in later_growths):
        raise ValueError("event widths do not encode a valid growth itinerary")
    bits = pair_plane_bits(base)
    q = 0
    # Walk backward.  For row j, q counts no-growth transitions among j+1..last.
    start = len(rows) - 1
    for j in range(len(rows) - 1, -1, -1):
        if q >= bits:
            return j + 1
        start = j
        if j > 0:
            g = later_growths[j - 1]
            q += 1 - g
    return start


def live_event_suffix_length(events: Sequence[Sequence[int]], *, base: int = 10) -> int:
    rows = tuple(events)
    return len(rows) - live_event_suffix_start(rows, base=base)


def reconstruct_pair_from_live_event_suffix(
    events: Sequence[Sequence[int]],
    *,
    base: int = 10,
    record_updates: Callable[[int], None] | None = None,
) -> tuple[int, ...]:
    """Reconstruct an endpoint from a *certified* live event suffix.

    Unlike ``reconstruct_pair_from_event_window`` this accepts fewer than H
    rows.  Its precondition is semantic: every omitted older event/source
    contribution has already been proved dead modulo ``2**w``.  The
    ``LiveCarryItinerary`` constructor below establishes that certificate from
    one ordinary H-row seed and preserves it under every advance.
    """
    rows = tuple(tuple(map(int, row)) for row in events)
    if not rows or any(not row for row in rows):
        raise ValueError("nonempty certified event suffix required")
    widths = tuple(len(row) for row in rows)
    growths = tuple(b - a for a, b in itertools.pairwise(widths))
    if any(g not in (0, 1) for g in growths):
        raise ValueError("invalid event-width schedule")
    modulus = 1 << pair_plane_bits(base)
    target_width = widths[-1]
    out = [0] * target_width
    updates = 0
    try:
        for j, event in enumerate(rows):
            tail = growths[j:]
            r = sum(tail)
            q = len(tail) - r
            scale = pow(2, q, modulus)
            for i, value in enumerate(event):
                for k in range(r + 1):
                    out[i + k] = (out[i + k] + value * scale * comb(r, k)) % modulus
                    updates += 1
    finally:
        if record_updates is not None:
            record_updates(updates)
    pair_max = 2 * (int(base) - 1)
    result = tuple(out)
    if any(not 0 <= value <= pair_max for value in result) or result != result[::-1]:
        raise ValueError("suffix is not a valid certified pair itinerary")
    return result


@dataclass(frozen=True, slots=True)
class LiveCarryItinerary:
    """Self-pruning exact carry-history certificate.

    This is research/compiler data, never a second semantic root.  It exists to
    test whether the fixed H-row theorem can be represented by its actually
    live temporal suffix.  ``seed`` needs one ordinary H-row carry window;
    ``advance`` then maintains the certificate without recovering discarded
    rows.
    """

    base: int
    carries: tuple[tuple[int, ...], ...]
    dropped_rows: int = 0

    def __post_init__(self) -> None:
        if self.base < 3 or not self.carries:
            raise ValueError((self.base, len(self.carries)))
        if any(
            not row or row[0] != 0 or any(v not in (0, 1) for v in row)
            for row in self.carries
        ):
            raise ValueError("invalid carry suffix")

    @classmethod
    def seed(
        cls, carries: Sequence[Sequence[int]], *, base: int = 10
    ) -> LiveCarryItinerary:
        rows = tuple(tuple(map(int, row)) for row in carries)
        horizon = event_memory_horizon(base)
        if len(rows) != horizon:
            raise ValueError(f"seed requires exactly {horizon} carry rows")
        full_pair = reconstruct_pair_from_carry_window(rows, base=base)
        events = tuple(forcing_event_from_carry(row, base=base) for row in rows)
        start = live_event_suffix_start(events, base=base)
        live = rows[start:]
        obj = cls(int(base), live, start)
        if obj.pair != full_pair:
            raise AssertionError("live suffix failed seed equivalence")
        return obj

    @property
    def events(self) -> tuple[tuple[int, ...], ...]:
        return tuple(
            forcing_event_from_carry(row, base=self.base) for row in self.carries
        )

    @property
    def pair(self) -> tuple[int, ...]:
        return reconstruct_pair_from_live_event_suffix(self.events, base=self.base)

    @property
    def row_count(self) -> int:
        return len(self.carries)

    @property
    def charged_carry_bits(self) -> int:
        return sum(len(row) for row in self.carries)

    def advance(self) -> LiveCarryItinerary:
        next_carry = carry_field(self.pair, base=self.base)
        rows = self.carries + (next_carry,)
        events = tuple(forcing_event_from_carry(row, base=self.base) for row in rows)
        start = live_event_suffix_start(events, base=self.base)
        return LiveCarryItinerary(self.base, rows[start:], self.dropped_rows + start)


@dataclass(frozen=True, slots=True)
class PairParityChannels:
    """The ``z**2=1`` cyclic quotient of a pair/event field."""

    modulus: int
    even: int
    odd: int

    def __post_init__(self) -> None:
        if self.modulus <= 1:
            raise ValueError(self.modulus)
        object.__setattr__(self, "even", int(self.even) % self.modulus)
        object.__setattr__(self, "odd", int(self.odd) % self.modulus)

    @classmethod
    def from_values(cls, values: Sequence[int], *, modulus: int) -> PairParityChannels:
        even, odd = cyclic_class_sums(values, 2, modulus)
        return cls(int(modulus), even, odd)

    @property
    def total(self) -> int:
        return (self.even + self.odd) % self.modulus

    @property
    def alternating(self) -> int:
        return (self.even - self.odd) % self.modulus

    def advance(self, event: Sequence[int], growth: int) -> PairParityChannels:
        e, o = cyclic_pair_advance(
            (self.even, self.odd), event, growth, modulus=self.modulus
        )
        return PairParityChannels(self.modulus, e, o)


def reverse_add_base_pm_residues(
    value: int, width: int, *, base: int = 10
) -> tuple[int, int]:
    """Return residues modulo ``b-1`` and ``b+1`` for one integer state."""
    value, width, base = int(value), int(width), int(base)
    if value < 0 or width <= 0 or base < 2:
        raise ValueError((value, width, base))
    return value % (base - 1), value % (base + 1)


def reverse_add_base_pm_advance(
    minus_residue: int, plus_residue: int, width: int, *, base: int = 10
) -> tuple[int, int]:
    """Exact residue transition for ``n -> n + reverse_b(n)``.

    Modulo ``b-1`` reversal is identity.  Modulo ``b+1`` it is ``(-1)**(d-1)``
    on a ``d``-digit number, so every even-width source sends the ``b+1``
    channel to zero; zero is then absorbing.
    """
    base, width = int(base), int(width)
    if base < 2 or width <= 0:
        raise ValueError((base, width))
    m0, m1 = base - 1, base + 1
    a = (2 * int(minus_residue)) % m0
    b = 0 if width % 2 == 0 else (2 * int(plus_residue)) % m1
    return a, b


def crt_coprime(a: int, ma: int, b: int, mb: int) -> int:
    a, ma, b, mb = map(int, (a, ma, b, mb))
    if ma <= 0 or mb <= 0 or gcd(ma, mb) != 1:
        raise ValueError((ma, mb))
    t = ((b - a) * pow(ma, -1, mb)) % mb
    return (a + ma * t) % (ma * mb)


def reverse_add_base_squared_minus_one_residue(
    minus_residue: int, plus_residue: int, *, base: int = 10
) -> int:
    """CRT reconstruction modulo ``b**2-1`` for even ``base`` (e.g. mod 99)."""
    base = int(base)
    if base < 2 or base & 1:
        raise ValueError("coprime (b-1,b+1) reconstruction requires even base")
    return crt_coprime(minus_residue, base - 1, plus_residue, base + 1)


def _matrix_mul(
    a: Sequence[Sequence[int]], b: Sequence[Sequence[int]], modulus: int
) -> tuple[tuple[int, ...], ...]:
    n = len(a)
    m = len(b[0])
    k = len(b)
    return tuple(
        tuple(sum(a[i][t] * b[t][j] for t in range(k)) % modulus for j in range(m))
        for i in range(n)
    )


def _matrix_pow(
    a: Sequence[Sequence[int]], exponent: int, modulus: int
) -> tuple[tuple[int, ...], ...]:
    n = len(a)
    identity = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
    base = tuple(tuple(int(x) % modulus for x in row) for row in a)
    return binary_power(
        base,
        exponent,
        identity=identity,
        compose=lambda first, second: _matrix_mul(second, first, modulus),
    ).value


def _rank_mod_prime(matrix: Sequence[Sequence[int]], prime: int) -> int:
    p = int(prime)
    if p < 2:
        raise ValueError(p)
    _rows, pivots = row_reduce_mod_prime(matrix, p)
    return len(pivots)


def cyclic_growth_operator_rank(classes: int, prime: int, *, power: int = 1) -> int:
    """Rank of ``(I+shift)**power`` on ``F_p[z]/(z**classes-1)``."""
    classes, prime, power = int(classes), int(prime), int(power)
    if classes <= 0 or power < 0 or prime < 2:
        raise ValueError((classes, prime, power))
    a = [[0] * classes for _ in range(classes)]
    for i in range(classes):
        a[i][i] = 1
        a[(i + 1) % classes][i] = (a[(i + 1) % classes][i] + 1) % prime
    return _rank_mod_prime(_matrix_pow(a, power, prime), prime)


def polynomial_growth_operator_rank(
    modulus_polynomial: Sequence[int], prime: int, *, power: int = 1
) -> int:
    """Rank of multiplication by ``(1+z)**power`` modulo a monic polynomial.

    Coefficients are low-to-high.  This directly audits the user's
    ``prime-polynomial`` suggestion: for irreducible ``f != z+1``, ``1+z`` is a
    unit in ``F_p[z]/(f)``, hence this rank is full.  Rank loss requires a
    ``z+1`` factor; powers of that factor give the useful nilpotent primary
    quotients above.
    """
    coeffs = tuple(int(x) % int(prime) for x in modulus_polynomial)
    prime, power = int(prime), int(power)
    if prime < 2 or power < 0 or len(coeffs) < 2 or coeffs[-1] != 1:
        raise ValueError((coeffs, prime, power))
    degree = len(coeffs) - 1
    z = [[0] * degree for _ in range(degree)]
    for j in range(degree):
        if j + 1 < degree:
            z[j + 1][j] = 1
        else:
            for i in range(degree):
                z[i][j] = (-coeffs[i]) % prime
    a = [[z[i][j] for j in range(degree)] for i in range(degree)]
    for i in range(degree):
        a[i][i] = (a[i][i] + 1) % prime
    return _rank_mod_prime(_matrix_pow(a, power, prime), prime)


def even_width_palindrome_has_z_plus_one_factor(values: Sequence[int]) -> bool:
    """Exact palindromic-polynomial check behind the ``b+1`` residue reset."""
    values = tuple(map(int, values))
    if not values or values != values[::-1] or len(values) % 2:
        return False
    return sum((-value if i & 1 else value) for i, value in enumerate(values)) == 0


__all__ = [
    "HIGH",
    "LOW",
    "NEUTRAL",
    "LiveCarryItinerary",
    "PairParityChannels",
    "adaptive_cyclic_memory_horizon",
    "adaptive_negacyclic_memory_horizon",
    "adaptive_zplus1_memory_horizon",
    "carry_from_threshold_itinerary",
    "carry_threshold_itinerary",
    "crt_coprime",
    "cyclic_class_sums",
    "cyclic_growth_operator_rank",
    "cyclic_pair_advance",
    "cyclic_transport_annihilated",
    "cyclic_transport_kernel",
    "digit_pair_sum_fiber_size",
    "even_width_palindrome_has_z_plus_one_factor",
    "growth_run_itinerary",
    "live_event_suffix_length",
    "live_event_suffix_start",
    "negacyclic_class_sums",
    "negacyclic_pair_advance",
    "negacyclic_transport_annihilated",
    "negacyclic_transport_kernel",
    "outer_digit_pair_sum_fiber_size",
    "pair_field_preimage_count",
    "polynomial_growth_operator_rank",
    "reconstruct_pair_from_live_event_suffix",
    "reverse_add_base_pm_advance",
    "reverse_add_base_pm_residues",
    "reverse_add_base_squared_minus_one_residue",
    "threshold_reset_count",
    "zplus1_jet",
    "zplus1_jet_advance",
    "zplus1_transport_annihilated",
]
