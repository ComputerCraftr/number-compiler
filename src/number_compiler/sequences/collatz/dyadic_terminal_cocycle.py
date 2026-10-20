"""Exact affine endpoint and successor-sum actions on certified dyadic blocks.

For a normalized parity block of length ``k``, the endpoint and sum of the
next ``k`` states are affine functions with common denominator ``2**k``.
Actions compose from authenticated run formulas or a checked finite prefix row;
they do not store a parity itinerary or an absolute accumulator value.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from itertools import pairwise

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.morphism_core import binary_power

_FIELD_ACTION_ISSUER = object()


def _quotient_residue(numerator: int, steps: int, modulus: int) -> int:
    denominator = 1 << steps
    quotient, remainder = divmod(numerator, denominator)
    if remainder:
        raise ValueError("dyadic source does not match its parity cylinder")
    return quotient % modulus


@dataclass(frozen=True, slots=True, init=False)
class DyadicTerminalFieldAction:
    """Affine endpoint, predecessor and prefix-sum action for one parity word."""

    steps: int
    gain: int
    offset: int
    sum_gain: int
    sum_offset: int
    previous_gain: int
    previous_offset: int
    _issuer: object = field(default=None, init=False, repr=False, compare=False)
    _issued_coefficients: tuple[int, ...] = field(
        default=(), init=False, repr=False, compare=False
    )

    def __init__(
        self,
        steps: int,
        gain: int,
        offset: int,
        sum_gain: int,
        sum_offset: int,
        previous_gain: int,
        previous_offset: int,
        *,
        _issuer: object | None = None,
    ) -> None:
        if _issuer is not _FIELD_ACTION_ISSUER:
            raise TypeError("dyadic field actions must come from a checked producer")
        for name, value in (
            ("steps", steps),
            ("gain", gain),
            ("offset", offset),
            ("sum_gain", sum_gain),
            ("sum_offset", sum_offset),
            ("previous_gain", previous_gain),
            ("previous_offset", previous_offset),
        ):
            object.__setattr__(self, name, value)
        object.__setattr__(self, "_issuer", _FIELD_ACTION_ISSUER)
        object.__setattr__(
            self,
            "_issued_coefficients",
            (
                steps,
                gain,
                offset,
                sum_gain,
                sum_offset,
                previous_gain,
                previous_offset,
            ),
        )
        self.__post_init__()

    @classmethod
    def _create(
        cls,
        steps: int,
        gain: int,
        offset: int,
        sum_gain: int,
        sum_offset: int,
        previous_gain: int,
        previous_offset: int,
    ) -> DyadicTerminalFieldAction:
        return cls(
            steps,
            gain,
            offset,
            sum_gain,
            sum_offset,
            previous_gain,
            previous_offset,
            _issuer=_FIELD_ACTION_ISSUER,
        )

    @classmethod
    def restore_cache_payload(
        cls, steps: int, coefficients: tuple[int, ...]
    ) -> DyadicTerminalFieldAction:
        """Restore an exact coefficient record after its cache owner check."""
        if type(coefficients) is not tuple or len(coefficients) != 6:
            raise ValueError("issued dyadic field payload is malformed")
        if any(type(value) is not int for value in coefficients):
            raise ValueError("issued dyadic field payload is malformed")
        return cls._create(steps, *coefficients)

    @property
    def producer_issued(self) -> bool:
        return (
            self._issuer is _FIELD_ACTION_ISSUER
            and self._issued_coefficients == self.coefficient_snapshot()
        )

    def coefficient_snapshot(self) -> tuple[int, ...]:
        """Return the exact affine fields for an outer publication seal."""
        return (
            self.steps,
            self.gain,
            self.offset,
            self.sum_gain,
            self.sum_offset,
            self.previous_gain,
            self.previous_offset,
        )

    def __post_init__(self) -> None:
        values = (
            self.steps,
            self.gain,
            self.offset,
            self.sum_gain,
            self.sum_offset,
            self.previous_gain,
            self.previous_offset,
        )
        if any(type(value) is not int for value in values):
            raise TypeError("dyadic field coefficients require exact integers")
        if self.steps < 0 or self.gain <= 0:
            raise ValueError("dyadic field action has an invalid extent or gain")
        if (
            min(
                self.offset,
                self.sum_gain,
                self.sum_offset,
                self.previous_gain,
                self.previous_offset,
            )
            < 0
        ):
            raise ValueError(
                "normalized Collatz field coefficients must be nonnegative"
            )
        if self.steps == 0 and values != (0, 1, 0, 0, 0, 0, 0):
            raise ValueError("zero-step field action must be the identity")
        if self.steps and self.gain % 2 == 0:
            raise ValueError("normalized Collatz gain must be odd")
        if self.steps and self.previous_gain <= 0:
            raise ValueError("nonempty block needs an exact predecessor action")

    @classmethod
    def identity(cls) -> DyadicTerminalFieldAction:
        return cls._create(0, 1, 0, 0, 0, 0, 0)

    @classmethod
    def zero_run(cls, length: int) -> DyadicTerminalFieldAction:
        length = require_integer(length, "zero-run length", 0)
        if length == 0:
            return cls.identity()
        denominator = 1 << length
        return cls._create(length, 1, 0, denominator - 1, 0, 1, 0)

    @classmethod
    def one_run(cls, length: int) -> DyadicTerminalFieldAction:
        length = require_integer(length, "one-run length", 0)
        if length == 0:
            return cls.identity()
        power_two = 1 << length
        power_three = 3**length
        difference = power_three - power_two
        return cls._create(
            length,
            power_three,
            difference,
            3 * difference,
            3 * difference - length * power_two,
            power_three // 3,
            power_three // 3 - power_two // 2,
        )

    @classmethod
    def from_prefixes(
        cls, prefixes: tuple[tuple[int, int], ...]
    ) -> DyadicTerminalFieldAction:
        """Project an already authenticated affine prefix table.

        Prefix ``j`` represents ``(g_j*x+c_j)/2**j``. The caller must obtain
        this table from the source-owned D8 producer, not from a sampled label.
        """
        if type(prefixes) is not tuple or not prefixes or prefixes[0] != (1, 0):
            raise ValueError("authenticated affine prefix row is malformed")
        for row in prefixes:
            if (
                type(row) is not tuple
                or len(row) != 2
                or any(type(value) is not int for value in row)
                or row[0] <= 0
            ):
                raise ValueError("authenticated affine prefix row is malformed")
        steps = len(prefixes) - 1
        if steps == 0:
            return cls.identity()
        if any(gain % 2 == 0 for gain, _ in prefixes):
            raise ValueError("normalized Collatz prefix gain must be odd")
        for index, ((gain, offset), following) in enumerate(pairwise(prefixes)):
            if following not in (
                (gain, offset),
                (3 * gain, 3 * offset + (1 << index)),
            ):
                raise ValueError("affine prefix row violates normalized Collatz")
        sum_gain = sum(
            gain << (steps - index) for index, (gain, _) in enumerate(prefixes) if index
        )
        sum_offset = sum(
            offset << (steps - index)
            for index, (_, offset) in enumerate(prefixes)
            if index
        )
        return cls._create(
            steps,
            *prefixes[-1],
            sum_gain,
            sum_offset,
            *prefixes[-2],
        )

    def then(self, after: DyadicTerminalFieldAction) -> DyadicTerminalFieldAction:
        """Compose chronologically: apply ``self``, then ``after``."""
        if (
            type(self) is not DyadicTerminalFieldAction
            or not self.producer_issued
            or type(after) is not DyadicTerminalFieldAction
            or not after.producer_issued
        ):
            raise TypeError("dyadic field composition requires a matching action")
        if self.steps == 0:
            return after
        if after.steps == 0:
            return self
        left_denominator = 1 << self.steps
        right_denominator = 1 << after.steps
        previous_gain = (
            self.gain if after.steps == 1 else after.previous_gain * self.gain
        )
        previous_offset = (
            self.offset
            if after.steps == 1
            else after.previous_gain * self.offset
            + left_denominator * after.previous_offset
        )
        return self._create(
            self.steps + after.steps,
            after.gain * self.gain,
            after.gain * self.offset + left_denominator * after.offset,
            right_denominator * self.sum_gain + after.sum_gain * self.gain,
            right_denominator * self.sum_offset
            + after.sum_gain * self.offset
            + left_denominator * after.sum_offset,
            previous_gain,
            previous_offset,
        )

    def power(
        self,
        count: int,
        *,
        on_compose: Callable[
            [DyadicTerminalFieldAction, DyadicTerminalFieldAction], None
        ]
        | None = None,
    ) -> DyadicTerminalFieldAction:
        """Repeat this block chronologically by exponentiation by squaring."""
        count = require_integer(count, "dyadic action repetition", 0)

        def compose(
            first: DyadicTerminalFieldAction, second: DyadicTerminalFieldAction
        ) -> DyadicTerminalFieldAction:
            if on_compose is not None and first.steps and second.steps:
                on_compose(first, second)
            return first.then(second)

        powered = binary_power(
            self,
            count,
            identity=self.identity(),
            compose=compose,
        )
        return powered.value

    @property
    def source_modulus(self) -> int:
        return 1 << self.steps

    @property
    def source_residue(self) -> int:
        if self.steps == 0:
            return 0
        modulus = self.source_modulus
        return (-self.offset * pow(self.gain, -1, modulus)) % modulus

    def certifies(self, source: int) -> bool:
        return (
            type(source) is int
            and source > 0
            and (self.gain * (source % self.source_modulus) + self.offset)
            % self.source_modulus
            == 0
        )

    def endpoint(self, source: int) -> int:
        self._require_source(source)
        if self.steps == 0:
            return source
        numerator = self.gain * source + self.offset
        endpoint, remainder = divmod(numerator, self.source_modulus)
        if remainder:
            raise ValueError("certified endpoint is not integral")
        return endpoint

    def sum_mod(self, source: int, modulus: int) -> int:
        self._require_source(source)
        modulus = require_integer(modulus, "field modulus", 2)
        if self.steps == 0:
            return 0
        return _quotient_residue(
            self.sum_gain * source + self.sum_offset, self.steps, modulus
        )

    def _require_source(self, source: int) -> None:
        source = require_integer(source, "terminal source", 1)
        if not self.certifies(source):
            raise ValueError("source is outside the certified dyadic block")


__all__ = ["DyadicTerminalFieldAction"]
