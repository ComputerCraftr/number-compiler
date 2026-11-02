"""The autonomous, source-anchored mod-99 reverse/add accumulator quotient.

At physical generation n set u_n=z_n (n even), u_n=reverse(z_n) (n
odd). Start A_0=seed, B_0=0; put u_(n+1)-u_n into B at even n
and into A at odd n. Hence u=A+B.

Once z is divisible by 11, every subsequent z is divisible by 11, and
reverse(z) == z (mod 99), for *either* decimal width parity. Therefore
there is a genuine autonomous output-right-congruence on the alternating
(A,B) mod 99 state plus parity:

 even -> odd: (A,B) -> (A, A+2B)
 odd -> even: (A,B) -> (2A+B, B).

The two-step even -> even matrix is N=[[3,2],[1,2]], with
(N-I)^2 = 3*(N-I). Its power is I+h*(N-I), h=(4**k-1)//3.

This quotient is exact for *accumulator residues*, and does not authorize
Q19 word, physical carry or exact-integer powering. No occurrence IDs,
width histories or future port guesses participate in its state.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
from typing import Final

from number_compiler.resources.ledger import ResourceLedger, ResourceScope
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys

from .temporal_residue99 import reverse_decimal_and_width

_MOD = 99
_MAX_SOURCE_DIGITS: Final[int] = 4096
_MAX_SOURCE_VALUE: Final[int] = 10**_MAX_SOURCE_DIGITS
_BOOTSTRAP_INTEGER_SLOTS: Final[int] = 12
_BOOTSTRAP_GROWTH_BITS: Final[int] = 28

_BeforeDigit = Callable[[int, int], None]
_BeforeArithmetic = Callable[[int, int, int], None]


@dataclass(frozen=True, slots=True)
class AccumulatorStateKey99:
    """Canonical typed identity inside the finite mod-99 accumulator owner."""

    phase: int
    first: int
    second: int

    def __post_init__(self) -> None:
        if type(self.phase) is not int or self.phase not in (0, 1):
            raise ValueError("invalid accumulator key phase")
        if type(self.first) is not int or not 0 <= self.first < _MOD:
            raise ValueError("invalid first accumulator key residue")
        if type(self.second) is not int or not 0 <= self.second < _MOD:
            raise ValueError("invalid second accumulator key residue")

    def packet(self) -> tuple[int, int, int]:
        """Retain the existing compact wire representation."""
        return self.phase, self.first, self.second


@dataclass(frozen=True, slots=True)
class RankOneAccumulatorAction99:
    """Even-to-even mod-99 matrix, (S,D) -> (a*S, D+h*S)."""

    multiplier: int
    coupling: int

    def __post_init__(self) -> None:
        if type(self.multiplier) is not int or not 0 <= self.multiplier < _MOD:
            raise ValueError("invalid modulo-99 multiplier")
        if type(self.coupling) is not int or not 0 <= self.coupling < _MOD:
            raise ValueError("invalid modulo-99 coupling")
        if (self.multiplier - (1 + 3 * self.coupling)) % _MOD:
            raise ValueError("rank-one matrix identity violated")

    @classmethod
    def identity(cls) -> RankOneAccumulatorAction99:
        return cls(1, 0)

    @classmethod
    def two_steps(cls) -> RankOneAccumulatorAction99:
        return cls(4, 1)

    def then(self, later: RankOneAccumulatorAction99) -> RankOneAccumulatorAction99:
        if type(later) is not RankOneAccumulatorAction99:
            raise TypeError("accumulator composition requires same quotient type")
        return RankOneAccumulatorAction99(
            (later.multiplier * self.multiplier) % _MOD,
            (self.coupling + later.coupling * self.multiplier) % _MOD,
        )

    def square(self) -> RankOneAccumulatorAction99:
        return self.then(self)

    def power(self, copies: int) -> RankOneAccumulatorAction99:
        """Exact logarithmic matrix power; not a physical carry-word power."""
        if type(copies) is not int or copies < 0:
            raise ValueError("block exponent must be a nonnegative integer")
        powered: int = pow(1 + 3 * self.coupling, copies, 3 * _MOD)
        coupling = (powered - 1) // 3
        return RankOneAccumulatorAction99((1 + 3 * coupling) % _MOD, coupling)

    @property
    def matrix_ab(self) -> tuple[tuple[int, int], tuple[int, int]]:
        h = self.coupling
        return ((1 + 2 * h) % _MOD, 2 * h % _MOD), (h, (1 + h) % _MOD)

    def apply(self, state: AccumulatorMooreState99) -> AccumulatorMooreState99:
        if type(state) is not AccumulatorMooreState99 or state.phase != 0:
            raise ValueError("rank-one block requires even-generation state")
        h = self.coupling
        s = state.sum_mod99
        return AccumulatorMooreState99(
            0, (state.a + 2 * h * s) % _MOD, (state.b + h * s) % _MOD
        )


@dataclass(frozen=True, slots=True)
class AccumulatorMooreState99:
    """Exact output-right-congruence for all future mod-99 accumulator pairs.

    The state is authorized *only after 11 divides the physical source*.
    The quotient is not a source equivalence for full integer/digit outputs.
    """

    phase: int  # n mod 2; mandatory for successor closure
    a: int
    b: int

    def __post_init__(self) -> None:
        if type(self.phase) is not int or self.phase not in (0, 1):
            raise ValueError("invalid accumulator orientation")
        if type(self.a) is not int or not 0 <= self.a < _MOD:
            raise ValueError("invalid first accumulator residue")
        if type(self.b) is not int or not 0 <= self.b < _MOD:
            raise ValueError("invalid second accumulator residue")

    @property
    def semantic_id(self) -> AccumulatorStateKey99:
        return AccumulatorStateKey99(self.phase, self.a, self.b)

    @property
    def future_class_id(self) -> AccumulatorStateKey99:
        """Moore-minimal over formal residue states with (A,B) outputs.

        Phase is distinguishable by the next accumulator output unless the
        sum vanishes. At S=0 both physical phases emit the same constant
        accumulator pair forever, so their phase tags must be merged.
        """
        return AccumulatorStateKey99(
            self.phase if self.sum_mod99 else 0, self.a, self.b
        )

    @property
    def sum_mod99(self) -> int:
        return (self.a + self.b) % _MOD

    @property
    def difference_mod99(self) -> int:
        return (self.a - self.b) % _MOD

    def successor(self) -> AccumulatorMooreState99:
        """One *physical* tick, no external carry inputs."""
        if self.phase == 0:
            return AccumulatorMooreState99(1, self.a, (self.a + 2 * self.b) % _MOD)
        return AccumulatorMooreState99(0, (2 * self.a + self.b) % _MOD, self.b)


@dataclass(frozen=True, slots=True)
class PoweredAccumulator99:
    """Pointed source-to-class transport and powered, residue-only output."""

    generation: int
    bootstrap_generation: int
    state: AccumulatorMooreState99
    integer_mod99: int
    reverse_mod99: int
    absorbed_mod11: bool
    even_blocks_powered: int
    action: RankOneAccumulatorAction99
    source_mod99: int
    generation_mod99: int
    source_certified: bool = True
    complete_integer_certified: bool = False
    source_reverse_mod99: int | None = None

    @property
    def first_accumulator_mod99(self) -> int:
        return self.state.a

    @property
    def second_accumulator_mod99(self) -> int:
        return self.state.b

    @property
    def sum_mod99(self) -> int:
        return self.state.sum_mod99

    @property
    def difference_mod99(self) -> int:
        return self.state.difference_mod99

    def packet(self) -> dict[str, object]:
        return {
            "generation": self.generation,
            "bootstrap_generation": self.bootstrap_generation,
            "state_phase": self.state.phase,
            "semantic_id": self.state.semantic_id.packet(),
            "future_moore_class_id": self.state.future_class_id.packet(),
            "formal_moore_class_count": 19503,
            "mod11_absorbed_formal_class_count": 1683,
            "first_accumulator_mod99": self.state.a,
            "second_accumulator_mod99": self.state.b,
            "sum_mod99": self.sum_mod99,
            "difference_mod99": self.difference_mod99,
            "integer_mod99": self.integer_mod99,
            "reverse_mod99": self.reverse_mod99,
            "absorbed_mod11": self.absorbed_mod11,
            "even_blocks_powered": self.even_blocks_powered,
            "rank_one_matrix": self.action.matrix_ab,
            "source_certified": self.source_certified,
            "complete_integer_certified": self.complete_integer_certified,
            "scope": "autonomous mod-99 accumulator Moore quotient; not a whole-Q19 successor",
        }


def _from_seed(
    seed: int,
    generation: int,
    *,
    before_digit: _BeforeDigit | None = None,
    before_arithmetic: _BeforeArithmetic | None = None,
    include_source_reverse: bool = False,
) -> PoweredAccumulator99:
    """Shared exact bootstrap; callers choose pure or ledger-accounted work."""
    if type(seed) is not int or seed < 0:
        raise ValueError("reverse/add source must be a nonnegative integer")
    if type(generation) is not int or generation < 0:
        raise ValueError("generation must be a nonnegative integer")
    x = u = a = seed
    b = 0
    n = 0
    source_reverse_mod99: int | None = None

    def reduce_operand(value: int, modulus: int) -> int:
        if before_arithmetic is not None:
            operand_bits = modulus.bit_length()
            before_arithmetic(value.bit_length(), operand_bits, operand_bits)
        return value % modulus

    source_mod99 = reduce_operand(seed, _MOD)
    generation_mod99 = reduce_operand(generation, _MOD)

    absorbed = False
    while n < generation:
        if n % 2 == 0 and reduce_operand(x, 11) == 0:
            absorbed = True
            break
        if n >= 6:
            raise AssertionError("universal six-tick mod-11 bootstrap failed")
        reverse, _ = reverse_decimal_and_width(x, before_digit=before_digit)
        if n == 0 and include_source_reverse:
            source_reverse_mod99 = reduce_operand(reverse, _MOD)
        if before_arithmetic is not None:
            before_arithmetic(
                x.bit_length(),
                reverse.bit_length(),
                max(x.bit_length(), reverse.bit_length()) + 1,
            )
        nxt = x + reverse
        next_u = (
            nxt
            if (n + 1) % 2 == 0
            else reverse_decimal_and_width(nxt, before_digit=before_digit)[0]
        )
        if before_arithmetic is not None:
            before_arithmetic(
                next_u.bit_length(),
                u.bit_length(),
                max(next_u.bit_length(), u.bit_length()) + 1,
            )
        delta = next_u - u
        if before_arithmetic is not None:
            previous = a if n & 1 else b
            before_arithmetic(
                previous.bit_length(),
                delta.bit_length(),
                max(previous.bit_length(), delta.bit_length()) + 1,
            )
            del previous
        if n & 1:
            a += delta
        else:
            b += delta
        x, u = nxt, next_u
        n += 1
        del reverse, nxt, next_u, delta

    if include_source_reverse and source_reverse_mod99 is None:
        source_reverse_mod99 = reduce_operand(
            reverse_decimal_and_width(seed, before_digit=before_digit)[0],
            _MOD,
        )

    if not absorbed and n % 2 == 0:
        absorbed = reduce_operand(x, 11) == 0
    action = RankOneAccumulatorAction99.identity()
    even_blocks = 0
    state = AccumulatorMooreState99(
        n % 2,
        reduce_operand(a, _MOD),
        reduce_operand(b, _MOD),
    )
    if absorbed and generation > n:
        if before_arithmetic is not None:
            before_arithmetic(
                generation.bit_length(), n.bit_length(), generation.bit_length() + 1
            )
        remaining = generation - n
        if before_arithmetic is not None:
            before_arithmetic(remaining.bit_length(), 1, remaining.bit_length())
        even_blocks, extra_tick = divmod(remaining, 2)
        action = RankOneAccumulatorAction99.two_steps().power(even_blocks)
        state = action.apply(state)
        if extra_tick:
            state = state.successor()
        # Reversal of any integer divisible by 11 is identical modulo 99.
        integer_mod99 = reverse_mod99 = state.sum_mod99
    else:
        integer_mod99 = reduce_operand(x, _MOD)
        if generation == 0 and source_reverse_mod99 is not None:
            reverse_mod99 = source_reverse_mod99
        else:
            reverse_mod99 = reduce_operand(
                reverse_decimal_and_width(x, before_digit=before_digit)[0],
                _MOD,
            )
    return PoweredAccumulator99(
        generation,
        n,
        state,
        integer_mod99,
        reverse_mod99,
        absorbed,
        even_blocks,
        action,
        source_mod99,
        generation_mod99,
        source_reverse_mod99=source_reverse_mod99,
    )


def from_seed(seed: int, generation: int) -> PoweredAccumulator99:
    """O(log generation) after at most six literal bootstrap iterations.

    Detect a *real* even-generation 11-multiple before invoking the
    autonomous matrices. No future carry or width control is hypothesized.
    """
    return _from_seed(seed, generation)


def from_seed_guarded(
    seed: int,
    generation: int,
    *,
    ledger: ResourceLedger,
    include_source_reverse: bool = False,
) -> PoweredAccumulator99:
    """Run the bounded literal source prefix under an existing ledger owner.

    The generation remains arbitrary precision: only the at-most-six-step
    source bootstrap is bounded. Source length is admitted before a decimal
    scan, and integer scratch is reserved before any reversal is constructed.
    """
    if type(seed) is not int or seed < 0:
        raise ValueError("reverse/add source must be a nonnegative integer")
    if type(generation) is not int or generation < 0:
        raise ValueError("generation must be a nonnegative integer")
    if type(ledger) is not ResourceLedger:
        raise TypeError("guarded accumulator needs its exact resource ledger")
    if type(include_source_reverse) is not bool:
        raise TypeError("source reverse demand must be Boolean")
    try:
        if seed >= _MAX_SOURCE_VALUE:
            raise ValueError(
                f"mod-99 accumulator source exceeds {_MAX_SOURCE_DIGITS} digits"
            )
        # For a positive d-digit x, reverse(x) < 10^d <= 10*x, hence each
        # source step is < 11*x and x after six steps is < 11^6*seed. A
        # reversed endpoint is < 10 times that; each of the two sums adds at
        # most three endpoint-sized deltas. Thus source, pair, sums, reversal
        # intermediates and temporaries are below 31*11^6*seed < 2^28*seed.
        # Twelve scratch slots cover x/u/a/b, reverse/nxt/next_u/delta,
        # reversal accumulator/quotient, an arithmetic transient, and the
        # generation subtraction temporary. Caller-owned seed/generation
        # inputs are included in the bit bound but are not recharged as new
        # scratch allocations.
        # Include generation arithmetic too: powering still accepts arbitrary
        # generation integers, and its temporary exponent is not source-sized.
        source_bits = seed.bit_length()
        maximum_bits = max(
            source_bits + _BOOTSTRAP_GROWTH_BITS,
            generation.bit_length() + 1,
        )
        integer_limbs = max(1, (maximum_bits + 29) // 30)
        scratch_owner = ledger.register(
            "reverse-accumulator99-bootstrap-scratch",
            "temporary_work",
            scope=ResourceScope.INDEX_OWNED,
        )
        with ledger.reservation(
            scratch_owner,
            entries=_BOOTSTRAP_INTEGER_SLOTS,
            nodes=_BOOTSTRAP_INTEGER_SLOTS * integer_limbs,
        ):

            def charge_digit(input_bits: int, output_bits: int) -> None:
                ledger.bump(
                    _reverse_add_keys.REVERSE_ACCUMULATOR99_BOOTSTRAP_DIGIT_STEPS
                )
                ledger.bump(
                    _reverse_add_keys.REVERSE_ACCUMULATOR99_BOOTSTRAP_OPERAND_BITS,
                    input_bits + output_bits,
                )

            def charge_arithmetic(
                left_bits: int, right_bits: int, result_bits: int
            ) -> None:
                ledger.bump(
                    _reverse_add_keys.REVERSE_ACCUMULATOR99_BOOTSTRAP_OPERAND_BITS,
                    left_bits + right_bits + result_bits,
                )

            return _from_seed(
                seed,
                generation,
                before_digit=charge_digit,
                before_arithmetic=charge_arithmetic,
                include_source_reverse=include_source_reverse,
            )
    except BaseException:
        ledger.bump(_reverse_add_keys.REVERSE_ACCUMULATOR99_BOOTSTRAP_FAILED_WORK)
        raise


def source_reverse_mod99_guarded(seed: int, *, ledger: ResourceLedger) -> int:
    """Demand only the bounded source-reversal coordinate of a cached action."""
    if type(seed) is not int or seed < 0:
        raise ValueError("reverse/add source must be a nonnegative integer")
    if type(ledger) is not ResourceLedger:
        raise TypeError("source reversal needs its exact resource ledger")
    try:
        if seed >= _MAX_SOURCE_VALUE:
            raise ValueError(
                f"mod-99 accumulator source exceeds {_MAX_SOURCE_DIGITS} digits"
            )
        maximum_bits = seed.bit_length() + 4
        integer_limbs = max(1, (maximum_bits + 29) // 30)
        scratch_owner = ledger.register(
            "reverse-accumulator99-source-reversal-scratch",
            "temporary_work",
            scope=ResourceScope.INDEX_OWNED,
        )
        with ledger.reservation(
            scratch_owner,
            entries=6,
            nodes=6 * integer_limbs,
        ):

            def charge_digit(input_bits: int, output_bits: int) -> None:
                ledger.bump(
                    _reverse_add_keys.REVERSE_ACCUMULATOR99_BOOTSTRAP_DIGIT_STEPS
                )
                ledger.bump(
                    _reverse_add_keys.REVERSE_ACCUMULATOR99_BOOTSTRAP_OPERAND_BITS,
                    input_bits + output_bits,
                )

            reversed_seed, _width = reverse_decimal_and_width(
                seed, before_digit=charge_digit
            )
            ledger.bump(
                _reverse_add_keys.REVERSE_ACCUMULATOR99_BOOTSTRAP_OPERAND_BITS,
                seed.bit_length() + reversed_seed.bit_length() + _MOD.bit_length(),
            )
            return reversed_seed % _MOD
    except BaseException:
        ledger.bump(_reverse_add_keys.REVERSE_ACCUMULATOR99_BOOTSTRAP_FAILED_WORK)
        raise


__all__ = [
    "AccumulatorStateKey99",
    "AccumulatorMooreState99",
    "PoweredAccumulator99",
    "RankOneAccumulatorAction99",
    "from_seed",
    "from_seed_guarded",
    "source_reverse_mod99_guarded",
]
