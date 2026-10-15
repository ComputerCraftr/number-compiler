"""Exact parity-radix coordinate for powered Collatz dynamics.

Let

    H(n) = n/2                 when n is even
           (3*n+1)/2           when n is odd.

For a nonnegative integer ``n`` define the finite parity prefix

    Q_k(n) = sum_{j=0}^{k-1} (H**j(n) mod 2) * 2**j.

The 2-adic continuation ``Q`` conjugates ``H`` to the right shift.  This module
uses only finite prefixes, so no convergence assumptions are required.

The original unaccelerated Collatz map is a two-phase suspension of that shift:
a zero parity symbol consumes one physical step; a one parity symbol consumes
two (the odd ``3*n+1`` step followed by its forced even division).  Hence a
powered physical-time query is a weighted rank/select operation on parity bits,
not an enumeration of the Fibonacci family of legal E/O branch words.
"""

from __future__ import annotations

from bisect import bisect_right
from collections.abc import Iterable
from dataclasses import dataclass, field
from functools import lru_cache
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import (
    normalized_integer_pair,
)
from number_compiler.arithmetic.fields.adic_morphism import PadicAffineMorphism
from number_compiler.arithmetic.fields.morphism_core import DyadicAffineCocycle
from number_compiler.arithmetic.fields.two_adic import inverse_dyadic_parity_word
from number_compiler.arithmetic.polynomials.binomial_pow2 import (
    scaled_binomial_mod_pow2,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys

if TYPE_CHECKING:
    from number_compiler.arithmetic.fields.congruence_automaton import (
        FactoredAffineMorphism,
    )


def normalized_collatz(n: int) -> int:
    n = int(n)
    if n < 0:
        raise ValueError(n)
    return (3 * n + 1) // 2 if n & 1 else n // 2


def physical_collatz(n: int) -> int:
    n = int(n)
    if n < 0:
        raise ValueError(n)
    return 3 * n + 1 if n & 1 else n // 2


def collatz_parity_word(seed: int, width: int) -> int:
    """Return the low ``width`` bits of the exact parity coordinate ``Q(seed)``."""
    seed, width = int(seed), int(width)
    if seed < 0 or width < 0:
        raise ValueError((seed, width))
    value = seed
    word = 0
    for j in range(width):
        bit = value & 1
        word |= bit << j
        value = normalized_collatz(value)
    return word


def collatz_parity_word_from_valuations(
    seed: int, valuations: Iterable[int], width: int
) -> int:
    """Reconstruct a normalized Collatz parity prefix from accelerated valuations.

    If an odd accelerated step has ``k=v2(3*n+1)``, the normalized map emits
    one odd bit followed by ``k-1`` forced even bits before the next odd state.
    Initial factors of two contribute the leading zero run.  Thus an already
    computed valuation itinerary is a lossless run encoding of the parity word;
    rebuilding it must not replay the Collatz orbit.
    """
    seed, width = int(seed), int(width)
    if seed <= 0 or width < 0:
        raise ValueError((seed, width))
    vals = tuple(map(int, valuations))
    if any(k <= 0 for k in vals):
        raise ValueError(vals)
    pos = 0
    value = seed
    while pos < width and value > 1 and not (value & 1):
        value >>= 1
        pos += 1
    word = 0
    for k in vals:
        if pos >= width:
            break
        word |= 1 << pos
        pos += 1
        pos += min(k - 1, width - pos)
    if pos < width:
        raise ValueError("valuation itinerary does not cover requested parity width")
    return word


def pow3_mod_pow2_binomial(exponent: int, bits: int, *, inverse: bool = False) -> int:
    """Compute ``3**(+/-exponent) mod 2**bits`` by the exact binomial series.

    ``3 = 1+2``.  Positive powers use the ordinary finite binomial expansion.
    Negative powers use

        (1+2)^(-s) = sum_r (-1)^r binom(s+r-1,r) 2^r,

    where terms ``r >= bits`` vanish modulo ``2**bits``.  This deliberately
    reuses the same 2-adic binomial transport primitive as reverse-and-add.
    """
    exponent, bits = normalized_integer_pair(exponent, bits, second_minimum=1)
    modulus = 1 << bits
    if exponent == 0:
        return 1 % modulus
    out = 0
    if inverse:
        for r in range(bits):
            term = scaled_binomial_mod_pow2(exponent + r - 1, r, r, bits)
            out = (out - term) % modulus if r & 1 else (out + term) % modulus
        return out
    for r in range(min(exponent, bits - 1) + 1):
        out = (out + scaled_binomial_mod_pow2(exponent, r, r, bits)) % modulus
    return out


def collatz_parity_inverse_residue(word: int, width: int) -> int:
    """Return the unique ``n mod 2**width`` with parity prefix ``word``.

    If the one bits of ``word`` occur at positions ``d_0 < d_1 < ...``, then

        n == -sum_m 2**d_m / 3**(m+1)        (mod 2**width).
    """
    word, width = int(word), int(width)
    if width < 0 or word < 0 or word.bit_length() > width:
        raise ValueError((word, width))
    return inverse_dyadic_parity_word(word, width, gains=(1, 3), offsets=(0, 1))


def collatz_parity_inverse_residue_binomial(word: int, width: int) -> int:
    """Independent binomial implementation of :func:`collatz_parity_inverse_residue`."""
    word, width = int(word), int(width)
    if width < 0 or word < 0 or word >= (1 << width):
        raise ValueError((word, width))
    if width == 0:
        return 0
    modulus = 1 << width
    residue = 0
    ones = 0
    for j in range(width):
        if not ((word >> j) & 1):
            continue
        ones += 1
        # Shifting by j means only width-j low bits of 3**(-ones) matter.
        inv = pow3_mod_pow2_binomial(ones, width - j, inverse=True)
        residue = (residue - (inv << j)) % modulus
    return residue


@dataclass(frozen=True, slots=True)
class CollatzParityInformationBound:
    """Exact information bound for a finite unknown parity itinerary.

    The finite parity coordinate is a bijection on residues modulo ``2**width``.
    Therefore a representation that must distinguish *all* unknown parity
    prefixes of this width has exactly ``2**width`` semantic cases and needs at
    least ``width`` bits.  This is a bound on carrying/accepting an arbitrary
    itinerary, not a lower bound against a future source-specific theorem that
    computes an endpoint without materializing that itinerary.
    """

    width: int
    semantic_cases: int
    minimum_itinerary_bits: int

    @property
    def itinerary_is_polylogarithmic_in_width(self) -> bool:
        # The exact lower bound is width bits, so the itinerary itself cannot be
        # an O(log width)-bit hidden state as width grows.
        return self.width <= 1


def collatz_parity_information_bound(width: int) -> CollatzParityInformationBound:
    width = int(width)
    if width < 0:
        raise ValueError(width)
    return CollatzParityInformationBound(
        width=width,
        semantic_cases=1 << width,
        minimum_itinerary_bits=width,
    )


@dataclass(frozen=True, slots=True)
class CollatzInverseStreamingProgram:
    """Uniform arithmetic transducer for the *full* finite inverse parity map.

    The earlier shared radix decision DAG measures a ROBDD representation of
    ``Q_k^-1`` and can have ``O(sqrt(k) 2^(k/2))`` states.  That is not a lower
    bound for general arithmetic circuits.  This streaming program consumes the
    ``k`` parity symbols once while retaining only two ``k``-bit arithmetic
    registers: the current ``3^-popcount`` and the inverse residue.

    Per symbol, a one bit multiplies the first register by the single constant
    ``3^-1 mod 2^k`` and conditionally subtracts its position-shifted value.
    Thus the representation is linear in independent input symbols and
    ``O(k)`` state bits, rather than subexponential decision states.  It cannot
    be logarithmic for an arbitrary unknown parity word because those ``k``
    independent input bits still have to enter the projection.
    """

    width: int
    inv3: int

    def __post_init__(self) -> None:
        if self.width < 0:
            raise ValueError(self.width)
        modulus = 1 << self.width if self.width else 1
        if self.inv3 != (pow(3, -1, modulus) if self.width else 0):
            raise ValueError("noncanonical inverse-three constant")

    @classmethod
    def build(cls, width: int) -> CollatzInverseStreamingProgram:
        width = int(width)
        if width < 0:
            raise ValueError(width)
        return cls(width, pow(3, -1, 1 << width) if width else 0)

    @property
    def canonical_key(self) -> tuple[object, ...]:
        return ("collatz-inverse-stream", int(self.width), int(self.inv3))

    @property
    def state_bits(self) -> int:
        # inverse power + residue; the position is the stream cursor, not a
        # second semantic word.
        return 2 * self.width

    @property
    def program_description_bits(self) -> int:
        # One fixed transition schema plus the sole width-bit constant inv3.
        return max(1, self.width.bit_length()) + max(1, self.inv3.bit_length()) + 3

    @property
    def symbol_steps(self) -> int:
        return self.width

    def apply(self, word: int) -> int:
        word = int(word)
        if self.width < 0 or word < 0 or word >= (1 << self.width):
            raise ValueError((word, self.width))
        if self.width == 0:
            return 0
        mask = (1 << self.width) - 1
        inv_power = 1
        residue = 0
        for j in range(self.width):
            if (word >> j) & 1:
                inv_power = (inv_power * self.inv3) & mask
                residue = (residue - (inv_power << j)) & mask
        return residue


@dataclass(frozen=True, slots=True)
class CollatzParitySlab:
    """Exact native block action for a normalized-Collatz parity word.

    A block with ``width=k`` and ``ones=s`` acts as

        H**k(x) = (3**s*x + offset) / 2**k

    on the unique residue class that realizes the represented parity word.
    Composition is closed and does not retain the word's construction tree.
    """

    width: int
    ones: int
    offset: int

    def __post_init__(self) -> None:
        if self.width < 0 or not 0 <= self.ones <= self.width or self.offset < 0:
            raise ValueError(self)
        if self.width == 0 and (self.ones or self.offset):
            raise ValueError("empty parity slab must be the identity")

    @property
    def cocycle(self) -> DyadicAffineCocycle:
        return DyadicAffineCocycle(pow(3, self.ones), self.offset, self.width)

    @classmethod
    def identity(cls) -> CollatzParitySlab:
        return cls(0, 0, 0)

    @classmethod
    def symbol(cls, bit: int) -> CollatzParitySlab:
        bit = int(bit)
        if bit not in (0, 1):
            raise ValueError(bit)
        return cls(1, bit, bit)

    def then(self, other: CollatzParitySlab) -> CollatzParitySlab:
        """Apply ``self`` first and ``other`` second through the shared cocycle."""
        cocycle = self.cocycle.then(other.cocycle)
        expected_multiplier = pow(3, self.ones + other.ones)
        if cocycle.multiplier != expected_multiplier:
            raise AssertionError((cocycle.multiplier, expected_multiplier))
        return CollatzParitySlab(
            cocycle.shift,
            self.ones + other.ones,
            cocycle.addend,
        )

    @property
    def domain_residue(self) -> int:
        if self.width == 0:
            return 0
        modulus = 1 << self.width
        return (-self.offset * pow(3, -self.ones, modulus)) % modulus

    @property
    def description_bits(self) -> int:
        """Fail-honest charge for retained integer payload, excluding object tags."""
        return (
            max(1, self.width.bit_length())
            + max(1, self.ones.bit_length())
            + max(1, self.offset.bit_length())
        )

    def apply(self, seed: int) -> int:
        seed = int(seed)
        if seed < 0:
            raise ValueError(seed)
        if self.width == 0:
            return seed
        if seed % (1 << self.width) != self.domain_residue:
            raise ValueError("seed does not realize this parity slab")
        try:
            return self.cocycle.apply_exact(seed)
        except ValueError as exc:
            raise AssertionError((self, seed)) from exc


def collatz_parity_slab(word: int, width: int) -> CollatzParitySlab:
    """Build the exact slab for ``word`` by balanced native composition."""
    word, width = int(word), int(width)
    if width < 0 or word < 0 or word >= (1 << width):
        raise ValueError((word, width))
    memo: dict[tuple[int, int], CollatzParitySlab] = {}
    stack: list[tuple[int, int, bool]] = [(word, width, False)]
    while stack:
        current_word, current_width, ready = stack.pop()
        key = (current_word, current_width)
        if key in memo:
            continue
        if current_width == 0:
            memo[key] = CollatzParitySlab.identity()
            continue
        if current_width == 1:
            memo[key] = CollatzParitySlab.symbol(current_word)
            continue
        split = current_width // 2
        low_key = (current_word & ((1 << split) - 1), split)
        high_key = (current_word >> split, current_width - split)
        if not ready:
            stack.append((current_word, current_width, True))
            if high_key not in memo:
                stack.append((*high_key, False))
            if low_key not in memo:
                stack.append((*low_key, False))
            continue
        memo[key] = memo[low_key].then(memo[high_key])
    return memo[(word, width)]


@dataclass(frozen=True, slots=True)
class ParityDurationSummary:
    """Associative summary of one parity block for physical Collatz time."""

    length: int
    ones: int

    def __post_init__(self) -> None:
        if self.length < 0 or not 0 <= self.ones <= self.length:
            raise ValueError(self)

    @property
    def physical_steps(self) -> int:
        return self.length + self.ones

    def then(self, other: ParityDurationSummary) -> ParityDurationSummary:
        return ParityDurationSummary(self.length + other.length, self.ones + other.ones)

    @classmethod
    def valuation_event(cls, valuation: int) -> ParityDurationSummary:
        """Summary of ``1,0**(k-1)`` without materializing those bits."""
        k = int(valuation)
        if k <= 0:
            raise ValueError(valuation)
        return cls(k, 1)


def summarize_parity_word(word: int, width: int) -> ParityDurationSummary:
    word, width = int(word), int(width)
    if width < 0 or word < 0 or word >= (1 << width):
        raise ValueError((word, width))
    return ParityDurationSummary(width, word.bit_count())


@dataclass(frozen=True, slots=True)
class CollatzParityPrefixIndex:
    """Block-prefix monoid index for an explicit finite parity coordinate.

    Construction is linear only in the *explicit input word size* (64-bit
    blocks).  Once built, weighted physical-time prefix selection is logarithmic
    in the number of blocks and inspects at most one 64-bit leaf.  Compressed
    accelerated-valuation inputs should still use :class:`CollatzValuationSchedule`,
    which avoids constructing the explicit parity word entirely.
    """

    word: int
    width: int
    block_bits: int = 64
    _blocks: tuple[ParityDurationSummary, ...] = field(
        init=False, repr=False, compare=False
    )
    _physical_prefix: tuple[int, ...] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        word, width, block_bits = int(self.word), int(self.width), int(self.block_bits)
        if width < 0 or word < 0 or word >= (1 << width) or block_bits <= 0:
            raise ValueError((word, width, block_bits))
        blocks = []
        physical = [0]
        for start in range(0, width, block_bits):
            length = min(block_bits, width - start)
            mask = (1 << length) - 1
            value = (word >> start) & mask
            summary = ParityDurationSummary(length, value.bit_count())
            blocks.append(summary)
            physical.append(physical[-1] + summary.physical_steps)
        object.__setattr__(self, "word", word)
        object.__setattr__(self, "width", width)
        object.__setattr__(self, "block_bits", block_bits)
        object.__setattr__(self, "_blocks", tuple(blocks))
        object.__setattr__(self, "_physical_prefix", tuple(physical))

    @property
    def physical_steps(self) -> int:
        return self._physical_prefix[-1]

    @property
    def block_count(self) -> int:
        return len(self._blocks)

    def select_complete_symbols(
        self, physical_budget: int
    ) -> tuple[int, int, int, int]:
        """Return ``(symbols, used_steps, summary_queries, leaf_bits_examined)``.

        ``symbols`` is the longest complete normalized-parity prefix whose
        weighted physical duration is at most ``physical_budget``.
        """
        budget = int(physical_budget)
        if budget < 0:
            raise ValueError(budget)
        if not self._blocks or budget <= 0:
            return 0, 0, 0, 0
        # Largest complete block prefix fitting the budget.  bisect is a binary
        # search over monoid prefix summaries, not over the parity bits.
        block = bisect_right(self._physical_prefix, budget) - 1
        block = min(block, self.block_count)
        queries = (self.block_count - 1).bit_length() if self.block_count > 1 else 0
        symbols = min(self.width, block * self.block_bits)
        if block >= self.block_count:
            return symbols, self._physical_prefix[block], queries, 0

        remaining = budget - self._physical_prefix[block]
        summary = self._blocks[block]
        start = block * self.block_bits
        value = (self.word >> start) & ((1 << summary.length) - 1)
        lo, hi = 0, summary.length
        local_queries = 0
        while lo < hi:
            mid = (lo + hi + 1) // 2
            local_queries += 1
            duration = mid + (value & ((1 << mid) - 1)).bit_count()
            if duration <= remaining:
                lo = mid
            else:
                hi = mid - 1
        local_used = lo + (value & ((1 << lo) - 1)).bit_count()
        return (
            symbols + lo,
            self._physical_prefix[block] + local_used,
            queries + local_queries,
            summary.length,
        )


@lru_cache(maxsize=128)
def collatz_parity_prefix_index(word: int, width: int) -> CollatzParityPrefixIndex:
    return CollatzParityPrefixIndex(int(word), int(width))


@dataclass(frozen=True, slots=True)
class CollatzValuationSchedule:
    """Run-compressed parity/physical-time schedule from accelerated events.

    ``initial_zeros`` represents an initial even run.  Each positive valuation
    ``k`` then represents the normalized-parity run ``1,0**(k-1)`` and the
    physical branch event ``O,E**k``.  Prefix tables have one entry per odd
    event, never one entry per forced division/parity bit.
    """

    initial_zeros: int
    valuations: tuple[int, ...]
    _physical_prefix: tuple[int, ...] = field(init=False, repr=False, compare=False)
    _symbol_prefix: tuple[int, ...] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        initial = int(self.initial_zeros)
        vals = tuple(map(int, self.valuations))
        if initial < 0 or any(k <= 0 for k in vals):
            raise ValueError((initial, vals))
        physical = [initial]
        symbols = [initial]
        for k in vals:
            physical.append(physical[-1] + k + 1)
            symbols.append(symbols[-1] + k)
        object.__setattr__(self, "initial_zeros", initial)
        object.__setattr__(self, "valuations", vals)
        object.__setattr__(self, "_physical_prefix", tuple(physical))
        object.__setattr__(self, "_symbol_prefix", tuple(symbols))

    @property
    def physical_steps(self) -> int:
        return self._physical_prefix[-1]

    @property
    def normalized_symbols(self) -> int:
        return self._symbol_prefix[-1]

    @property
    def event_count(self) -> int:
        return len(self.valuations)

    @property
    def description_bits(self) -> int:
        return max(1, self.initial_zeros.bit_length()) + sum(
            max(1, k.bit_length()) for k in self.valuations
        )

    def locate(self, physical_offset: int) -> CollatzValuationPosition:
        offset = int(physical_offset)
        if not 0 <= offset <= self.physical_steps:
            raise ValueError((offset, self.physical_steps))
        if offset < self.initial_zeros:
            return CollatzValuationPosition(
                offset,
                0,
                0,
                offset,
                0,
                False,
            )
        if offset == self.physical_steps:
            return CollatzValuationPosition(
                offset,
                self.event_count,
                0,
                self.normalized_symbols,
                0,
                True,
            )
        # _physical_prefix[i] is the start of event i after leading zeroes.
        event = bisect_right(self._physical_prefix, offset) - 1
        if event < 0 or event >= self.event_count:
            raise AssertionError((offset, event, self._physical_prefix))
        event_offset = offset - self._physical_prefix[event]
        k = self.valuations[event]
        if not 0 <= event_offset < k + 1:
            raise AssertionError((event, event_offset, k))
        before = self._symbol_prefix[event]
        if event_offset == 0:
            consumed = before
            phase = 0
        elif event_offset == 1:
            consumed = before
            phase = 1
        else:
            consumed = before + event_offset - 1
            phase = 0
        return CollatzValuationPosition(
            offset,
            event,
            event_offset,
            consumed,
            phase,
            False,
        )


@dataclass(frozen=True, slots=True)
class CollatzValuationPosition:
    physical_offset: int
    event_index: int
    event_offset: int
    consumed_normalized_symbols: int
    phase: int
    exhausted: bool


@dataclass(frozen=True, slots=True)
class CollatzValuationCursor:
    """Persistent cursor over a run-compressed valuation schedule."""

    schedule: CollatzValuationSchedule
    physical_offset: int = 0

    def __post_init__(self) -> None:
        if not isinstance(self.schedule, CollatzValuationSchedule):
            raise TypeError(type(self.schedule))
        if not 0 <= int(self.physical_offset) <= self.schedule.physical_steps:
            raise ValueError(self.physical_offset)
        object.__setattr__(self, "physical_offset", int(self.physical_offset))

    @property
    def position(self) -> CollatzValuationPosition:
        return self.schedule.locate(self.physical_offset)


@dataclass(frozen=True, slots=True)
class CollatzValuationAdvance:
    cursor: CollatzValuationCursor
    position: CollatzValuationPosition
    event_binary_search_bound: int


def advance_collatz_valuations(
    cursor: CollatzValuationCursor,
    physical_steps: int,
) -> CollatzValuationAdvance:
    """Advance physical time without rebuilding a parity integer/bitstream."""
    ticks = int(physical_steps)
    if ticks < 0:
        raise ValueError(ticks)
    target = cursor.physical_offset + ticks
    if target > cursor.schedule.physical_steps:
        raise ValueError("valuation schedule exhausted inside powered Collatz query")
    out = CollatzValuationCursor(cursor.schedule, target)
    queries = (
        max(1, cursor.schedule.event_count.bit_length())
        if cursor.schedule.event_count
        else 0
    )
    return CollatzValuationAdvance(out, out.position, queries)


@dataclass(frozen=True, slots=True)
class CollatzParityCursor:
    """Finite parity-stream state for the two-phase physical Collatz suspension.

    ``phase=0`` means the next parity symbol has not started. ``phase=1`` means
    that symbol is necessarily one and its odd ``3*n+1`` half has occurred; one
    more physical step consumes the symbol and shifts the parity coordinate.
    """

    word: int
    width: int
    phase: int = 0

    def __post_init__(self) -> None:
        if any(type(value) is not int for value in (self.word, self.width, self.phase)):
            raise TypeError("parity cursor fields must be exact integers")
        if self.width < 0 or self.word < 0 or self.word.bit_length() > self.width:
            raise ValueError(self)
        if self.phase not in (0, 1):
            raise ValueError(self.phase)
        if self.phase and (self.width == 0 or (self.word & 1) == 0):
            raise ValueError("phase 1 requires a pending odd parity symbol")


def collatz_shifted_parity_residue(
    cursor: CollatzParityCursor, precision: int, *, ledger: ResourceLedger
) -> int:
    """Read a low state residue from an already admitted shifted-Q cursor.

    Phase zero is the normalized state ``Q^-1(W)``. Phase one is the even
    intermediate ``3*n+1`` after the odd physical tick, so the pending one
    symbol is discarded and the inverse of the remaining word is doubled.
    This finite arithmetic does not construct ``W``, certify its source or
    decide whether a requested digit lies beyond the integer's high end.
    """
    if type(cursor) is not CollatzParityCursor:
        raise TypeError("shifted parity germ requires a finite cursor")
    # Frozen dataclasses can still be forged with object.__setattr__. Validate
    # at the arithmetic boundary before shifting or trusting a phase claim.
    if any(
        type(value) is not int for value in (cursor.word, cursor.width, cursor.phase)
    ):
        raise TypeError("shifted parity cursor fields must be exact integers")
    if (
        cursor.word < 0
        or cursor.width < 0
        or cursor.word.bit_length() > cursor.width
        or cursor.phase not in (0, 1)
        or cursor.phase == 1
        and (cursor.width == 0 or not cursor.word & 1)
    ):
        raise ValueError("shifted parity cursor is not canonical")
    if type(precision) is not int or precision < 0:
        raise ValueError("shifted parity germ precision must be natural")
    if type(ledger) is not ResourceLedger:
        raise TypeError("shifted parity germ requires a resource ledger")
    if precision > cursor.width:
        raise ValueError("shifted parity cursor lacks demanded precision")
    ledger.bump(_collatz_keys.COLLATZ_SHIFTED_PARITY_GERM_DEMANDS)
    if precision == 0:
        # The pending odd symbol was checked even though the requested output
        # contains no bits; charge that admission read.
        if cursor.phase:
            ledger.bump(_collatz_keys.COLLATZ_SHIFTED_PARITY_GERM_SYMBOL_READS)
            ledger.bump(_collatz_keys.COLLATZ_SHIFTED_PARITY_GERM_OPERAND_BITS)
        return 0
    inverse_width = precision - cursor.phase
    # Mask first: shifting the entire supplied Q word would allocate a copy
    # proportional to its temporal horizon for a one-bit point demand.
    word = (cursor.word & ((1 << precision) - 1)) >> cursor.phase
    ones = word.bit_count()
    # The inverse routine performs at most one inverse-three setup and one
    # modular contribution per one symbol. Account for the precision
    # of those operands as well as the bits selected from the cursor.
    ledger.bump(_collatz_keys.COLLATZ_SHIFTED_PARITY_GERM_SYMBOL_READS, precision)
    ledger.bump(
        _collatz_keys.COLLATZ_SHIFTED_PARITY_GERM_INVERSE_SETUPS,
        int(inverse_width > 0),
    )
    ledger.bump(_collatz_keys.COLLATZ_SHIFTED_PARITY_GERM_MODULAR_TERMS, ones)
    ledger.bump(
        _collatz_keys.COLLATZ_SHIFTED_PARITY_GERM_OPERAND_BITS,
        max(1, precision) + inverse_width * (2 * ones + 1),
    )
    residue = collatz_parity_inverse_residue(word, inverse_width)
    return (residue << cursor.phase) & ((1 << precision) - 1)


@dataclass(frozen=True, slots=True)
class CollatzParityAdvance:
    cursor: CollatzParityCursor
    consumed_symbols: int
    rank_queries: int
    rank_bits_scanned: int


@dataclass(frozen=True, slots=True)
class CollatzParityTimeOperator:
    """Source-independent powered physical-time action in parity coordinates."""

    steps: int = 0

    def __post_init__(self) -> None:
        if self.steps < 0:
            raise ValueError(self.steps)

    def then(self, other: CollatzParityTimeOperator) -> CollatzParityTimeOperator:
        return CollatzParityTimeOperator(self.steps + other.steps)

    def power(self, exponent: int) -> CollatzParityTimeOperator:
        exponent = int(exponent)
        if exponent < 0:
            raise ValueError(exponent)
        return CollatzParityTimeOperator(self.steps * exponent)

    @property
    def operator_nodes(self) -> int:
        return 1

    @property
    def description_bits(self) -> int:
        return max(1, self.steps.bit_length())

    def apply(self, cursor: CollatzParityCursor) -> CollatzParityAdvance:
        return advance_collatz_parity(cursor, self.steps)

    def apply_valuations(
        self, cursor: CollatzValuationCursor
    ) -> CollatzValuationAdvance:
        """Apply directly to compressed accelerated-valuation events."""
        return advance_collatz_valuations(cursor, self.steps)


def _prefix_duration(word: int, symbols: int) -> int:
    """Reference scalar duration helper retained for bounded differential tests."""
    if symbols <= 0:
        return 0
    return symbols + (word & ((1 << symbols) - 1)).bit_count()


def advance_collatz_parity(
    cursor: CollatzParityCursor, physical_steps: int
) -> CollatzParityAdvance:
    """Advance physical Collatz time by weighted rank/select on a parity prefix.

    The query uses binary search over the associative ``(length,ones)`` summary.
    It never enumerates legal E/O branch programs.  The supplied finite parity
    prefix must contain every complete symbol needed by the request and, when
    the result stops in phase 1, the pending one symbol.
    """
    ticks = int(physical_steps)
    if ticks < 0:
        raise ValueError(ticks)
    word, width, phase = cursor.word, cursor.width, cursor.phase
    consumed = 0
    queries = 0
    bits_scanned = 0
    if ticks == 0:
        return CollatzParityAdvance(cursor, 0, 0, 0)

    if phase:
        # Complete the forced division following an odd 3*n+1 step.
        ticks -= 1
        word >>= 1
        width -= 1
        consumed += 1
        phase = 0
        if ticks == 0:
            return CollatzParityAdvance(
                CollatzParityCursor(word, width, 0), consumed, queries, bits_scanned
            )

    # Find the longest complete prefix from cached associative block summaries.
    # No repeated scan of increasingly large integer prefixes occurs here.
    prefix_index = collatz_parity_prefix_index(word, width)
    complete, used, prefix_queries, leaf_bits = prefix_index.select_complete_symbols(
        ticks
    )
    queries += prefix_queries
    bits_scanned += leaf_bits
    ticks -= used
    word >>= complete
    width -= complete
    consumed += complete

    if ticks == 0:
        return CollatzParityAdvance(
            CollatzParityCursor(word, width, 0), consumed, queries, bits_scanned
        )
    if ticks != 1:
        raise AssertionError((ticks, word, width))
    if width == 0:
        raise ValueError("parity prefix exhausted inside powered Collatz query")
    if (word & 1) == 0:
        # A zero symbol costs only one tick, so maximality would have consumed it.
        raise AssertionError(
            "weighted prefix select stopped before a complete zero symbol"
        )
    return CollatzParityAdvance(
        CollatzParityCursor(word, width, 1), consumed, queries, bits_scanned
    )


def valid_physical_branch_count(steps: int) -> int:
    """Number of length-``steps`` E/O words with no consecutive odd branches."""
    steps = int(steps)
    if steps < 0:
        raise ValueError(steps)
    # F_{steps+2}, with F_0=0, F_1=1.
    a, b = 0, 1
    for _ in range(steps + 2):
        a, b = b, a + b
    return a


@dataclass(frozen=True, slots=True)
class CollatzFactoredResidueProjection:
    """Odd-modulus projection of one exact Collatz parity slab."""

    morphism: FactoredAffineMorphism
    exponent_bit_work: int


def compile_collatz_slab_factored(
    slab: CollatzParitySlab, moduli: Iterable[int]
) -> CollatzFactoredResidueProjection:
    """Compile a parity slab as one exact affine map over odd moduli."""
    from number_compiler.arithmetic.fields.congruence_automaton import (
        FactoredAffineMorphism,
    )

    mods = tuple(map(int, moduli))
    if not mods or any(modulus <= 1 or modulus % 2 == 0 for modulus in mods):
        raise ValueError(mods)
    width = int(slab.width)
    ones = int(slab.ones)
    offset = int(slab.offset)
    multipliers: list[int] = []
    offsets: list[int] = []
    for modulus in mods:
        inverse = pow(pow(2, width, modulus), -1, modulus)
        multipliers.append((pow(3, ones, modulus) * inverse) % modulus)
        offsets.append((offset * inverse) % modulus)
    morphism = FactoredAffineMorphism(
        mods, tuple(multipliers), tuple(offsets), width, 0
    )
    work = len(mods) * (max(1, width.bit_length()) + max(1, ones.bit_length()))
    return CollatzFactoredResidueProjection(morphism, work)


def collatz_slab_padic3(
    slab: CollatzParitySlab, precision: int = 8
) -> PadicAffineMorphism:
    """Exact normalized Collatz slab modulo ``3**precision``."""
    if type(precision) is not int:
        raise TypeError("p-adic precision must be an exact integer")
    modulus = 3**precision
    width = int(slab.width)
    ones = int(slab.ones)
    offset = int(slab.offset)
    inverse = pow(pow(2, width, modulus), -1, modulus)
    return PadicAffineMorphism(
        3,
        precision,
        (pow(3, ones, modulus) * inverse) % modulus,
        (offset * inverse) % modulus,
        width,
        0,
    )


__all__ = [
    "CollatzFactoredResidueProjection",
    "CollatzInverseStreamingProgram",
    "CollatzParityAdvance",
    "CollatzParityCursor",
    "CollatzParityInformationBound",
    "CollatzParityPrefixIndex",
    "CollatzParitySlab",
    "CollatzParityTimeOperator",
    "CollatzValuationAdvance",
    "CollatzValuationCursor",
    "CollatzValuationPosition",
    "CollatzValuationSchedule",
    "ParityDurationSummary",
    "advance_collatz_parity",
    "advance_collatz_valuations",
    "collatz_parity_information_bound",
    "collatz_parity_inverse_residue",
    "collatz_parity_inverse_residue_binomial",
    "collatz_parity_prefix_index",
    "collatz_parity_slab",
    "collatz_parity_word",
    "collatz_parity_word_from_valuations",
    "collatz_slab_padic3",
    "compile_collatz_slab_factored",
    "normalized_collatz",
    "physical_collatz",
    "pow3_mod_pow2_binomial",
    "summarize_parity_word",
    "valid_physical_branch_count",
]
