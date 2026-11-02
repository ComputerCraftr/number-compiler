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
from typing import Final, NamedTuple

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.arithmetic.fields.morphism_core import binary_power

MAX_DYADIC_SOURCE_WINDOW_STEPS: Final = 512

_FIELD_ACTION_ISSUER = object()
_FIELD_WORD_ISSUER = object()


def _quotient_residue(numerator: int, steps: int, modulus: int) -> int:
    denominator = 1 << steps
    quotient, remainder = divmod(numerator, denominator)
    if remainder:
        raise ValueError("dyadic source does not match its parity cylinder")
    return quotient % modulus


def _dyadic_source_modulus(steps: int) -> int:
    return 1 << steps


def _dyadic_source_residue(steps: int, gain: int, offset: int) -> int:
    if steps == 0:
        return 0
    modulus = _dyadic_source_modulus(steps)
    return (-offset * pow(gain, -1, modulus)) % modulus


def _dyadic_action_certifies(
    steps: int, gain: int, offset: int, source: object
) -> bool:
    modulus = _dyadic_source_modulus(steps)
    return (
        type(source) is int
        and source > 0
        and (gain * (source % modulus) + offset) % modulus == 0
    )


def _require_dyadic_source(
    steps: int,
    gain: int,
    offset: int,
    source: int,
    *,
    producer_issued: bool,
    authority_error: str,
) -> int:
    if not producer_issued:
        raise ValueError(authority_error)
    source = require_integer(source, "terminal source", 1)
    if not _dyadic_action_certifies(steps, gain, offset, source):
        raise ValueError("source is outside the certified dyadic block")
    return source


def _apply_dyadic_endpoint(
    steps: int,
    gain: int,
    offset: int,
    source: int,
    *,
    producer_issued: bool,
    authority_error: str,
) -> int:
    source = _require_dyadic_source(
        steps,
        gain,
        offset,
        source,
        producer_issued=producer_issued,
        authority_error=authority_error,
    )
    if steps == 0:
        return source
    endpoint, remainder = divmod(gain * source + offset, _dyadic_source_modulus(steps))
    if remainder:
        raise ValueError("certified endpoint is not integral")
    return endpoint


@dataclass(frozen=True, slots=True, init=False)
class DyadicTerminalEndpointAction:
    """Authenticated endpoint-only projection of one produced parity word."""

    steps: int
    gain: int
    offset: int
    _issuer: object = field(default=None, init=False, repr=False, compare=False)
    _issued_coefficients: tuple[int, ...] = field(
        default=(), init=False, repr=False, compare=False
    )
    _word_issuer: object = field(default=None, init=False, repr=False, compare=False)

    def __init__(
        self,
        steps: int,
        gain: int,
        offset: int,
        *,
        _issuer: object | None = None,
        _word_issuer: object | None = None,
    ) -> None:
        if _issuer is not _FIELD_ACTION_ISSUER:
            raise TypeError("dyadic endpoint actions must come from a checked producer")
        object.__setattr__(self, "steps", steps)
        object.__setattr__(self, "gain", gain)
        object.__setattr__(self, "offset", offset)
        object.__setattr__(self, "_issuer", _FIELD_ACTION_ISSUER)
        object.__setattr__(self, "_word_issuer", _word_issuer)
        object.__setattr__(self, "_issued_coefficients", (steps, gain, offset))
        self.__post_init__()

    @property
    def producer_issued(self) -> bool:
        return (
            self._issuer is _FIELD_ACTION_ISSUER
            and self._word_issuer is _FIELD_WORD_ISSUER
            and self._issued_coefficients == self.coefficient_snapshot()
        )

    def coefficient_snapshot(self) -> tuple[int, ...]:
        return self.steps, self.gain, self.offset

    def __post_init__(self) -> None:
        if any(type(value) is not int for value in self.coefficient_snapshot()):
            raise TypeError("dyadic endpoint coefficients require exact integers")
        if self.steps < 0 or self.gain <= 0 or self.offset < 0:
            raise ValueError("dyadic endpoint action has invalid coefficients")
        if self.steps == 0 and self.coefficient_snapshot() != (0, 1, 0):
            raise ValueError("zero-step endpoint action must be the identity")
        if self.steps and self.gain % 2 == 0:
            raise ValueError("normalized Collatz gain must be odd")

    @property
    def source_modulus(self) -> int:
        return _dyadic_source_modulus(self.steps)

    @property
    def source_residue(self) -> int:
        return _dyadic_source_residue(
            self.steps,
            self.gain,
            self.offset,
        )

    def certifies(self, source: int) -> bool:
        return _dyadic_action_certifies(
            self.steps,
            self.gain,
            self.offset,
            source,
        )

    def endpoint(self, source: int) -> int:
        return _apply_dyadic_endpoint(
            self.steps,
            self.gain,
            self.offset,
            source,
            producer_issued=self.producer_issued,
            authority_error="untrusted endpoint coefficients cannot be applied",
        )


class _EndpointWindowPrefixState(NamedTuple):
    steps: int
    gain: int
    offset: int
    odd_symbols: int


class _FieldWindowPrefixState(NamedTuple):
    steps: int
    gain: int
    offset: int
    sum_gain: int
    sum_offset: int
    previous_gain: int
    previous_offset: int
    odd_symbols: int


@dataclass(slots=True)
class _WindowFieldAccumulator:
    sum_gain: int = 0
    sum_offset: int = 0
    previous_gain: int = 0
    previous_offset: int = 0

    def advance(
        self,
        previous_gain: int,
        previous_offset: int,
        gain: int,
        offset: int,
    ) -> int:
        old_values = (
            self.sum_gain,
            self.sum_offset,
            self.previous_gain,
            self.previous_offset,
        )
        self.previous_gain = previous_gain
        self.previous_offset = previous_offset
        self.sum_gain = (self.sum_gain << 1) + gain
        self.sum_offset = (self.sum_offset << 1) + offset
        return sum(value.bit_length() for value in old_values) + sum(
            value.bit_length()
            for value in (
                self.sum_gain,
                self.sum_offset,
                self.previous_gain,
                self.previous_offset,
            )
        )

    def prefix_state(
        self, steps: int, gain: int, offset: int, odd_symbols: int
    ) -> _FieldWindowPrefixState:
        return _FieldWindowPrefixState(
            steps,
            gain,
            offset,
            self.sum_gain,
            self.sum_offset,
            self.previous_gain,
            self.previous_offset,
            odd_symbols,
        )


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
    _word_issuer: object = field(default=None, init=False, repr=False, compare=False)

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
        _word_issuer: object | None = None,
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
        object.__setattr__(self, "_word_issuer", _word_issuer)
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
            _word_issuer=_FIELD_WORD_ISSUER,
        )

    @classmethod
    def restore_untrusted_cache_payload(
        cls, steps: int, coefficients: tuple[int, ...]
    ) -> DyadicTerminalFieldAction:
        """Decode coefficients without granting source-word authority.

        Persistent cache wire records contain integers, not the producer's
        proof that its carry and sum fields came from the same parity word.
        Owners that retain these actions must keep the typed action itself or
        establish a separate checked admission before using weighted fields.
        """
        if type(coefficients) is not tuple or len(coefficients) != 6:
            raise ValueError("issued dyadic field payload is malformed")
        if any(type(value) is not int for value in coefficients):
            raise ValueError("issued dyadic field payload is malformed")
        return cls(
            steps,
            *coefficients,
            _issuer=_FIELD_ACTION_ISSUER,
        )

    @classmethod
    def authenticate_cache_payload_for_source(
        cls,
        steps: int,
        coefficients: tuple[int, ...],
        source: int,
        *,
        preflight: Callable[[int], None],
        on_work: Callable[[int], None],
    ) -> DyadicTerminalFieldAction:
        """Promote one bounded primitive cache record into a typed action.

        This is a cold cache-admission path, not the weighted binding path.
        The source and horizon are already bounded by the cache owner; the
        complete emitted action is checked once before it enters that owner's
        typed local memo. Later local hits reuse the returned action directly.
        """
        steps = require_integer(steps, "cached field steps", 0)
        source = require_integer(source, "cached field source", 1)
        if (
            type(coefficients) is not tuple
            or len(coefficients) != 6
            or any(type(value) is not int for value in coefficients)
        ):
            raise ValueError("issued dyadic field payload is malformed")
        if not callable(preflight) or not callable(on_work):
            raise TypeError("cache action admission requires a budget owner")
        coefficient_bits = sum(
            max(1, abs(value).bit_length()) for value in coefficients
        )
        preflight(8 * (source.bit_length() + 4 * steps + coefficient_bits + 32))
        candidate = cls.restore_untrusted_cache_payload(steps, coefficients)
        if not candidate.certifies(source):
            raise ValueError("cached field action does not admit its source")
        expected = cls.identity()
        current = source
        even = cls.zero_run(1)
        odd = cls.one_run(1)
        for _ in range(steps):
            coefficient_bits = sum(
                max(1, abs(value).bit_length())
                for value in expected.coefficient_snapshot()
            )
            on_work(source.bit_length() + current.bit_length() + 4 * coefficient_bits)
            if current & 1:
                expected = expected.then(odd)
                current = (3 * current + 1) // 2
            else:
                expected = expected.then(even)
                current //= 2
        if expected.coefficient_snapshot() != candidate.coefficient_snapshot():
            raise ValueError("cached field coefficients differ from source word")
        return expected

    @property
    def producer_issued(self) -> bool:
        return (
            self._issuer is _FIELD_ACTION_ISSUER
            and self._word_issuer is _FIELD_WORD_ISSUER
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
        return _dyadic_source_modulus(self.steps)

    @property
    def source_residue(self) -> int:
        return _dyadic_source_residue(
            self.steps,
            self.gain,
            self.offset,
        )

    def certifies(self, source: int) -> bool:
        return _dyadic_action_certifies(
            self.steps,
            self.gain,
            self.offset,
            source,
        )

    def endpoint(self, source: int) -> int:
        return _apply_dyadic_endpoint(
            self.steps,
            self.gain,
            self.offset,
            source,
            producer_issued=self.producer_issued,
            authority_error="untrusted field coefficients cannot produce an endpoint",
        )

    def sum_mod(self, source: int, modulus: int) -> int:
        self._require_source(source)
        modulus = require_integer(modulus, "field modulus", 2)
        if self.steps == 0:
            return 0
        return _quotient_residue(
            self.sum_gain * source + self.sum_offset, self.steps, modulus
        )

    def _require_source(self, source: int) -> None:
        _require_dyadic_source(
            self.steps,
            self.gain,
            self.offset,
            source,
            producer_issued=self.producer_issued,
            authority_error="untrusted field coefficients cannot produce an endpoint",
        )

    @classmethod
    def issue_source_window(
        cls,
        source: int,
        physical_budget: int,
        *,
        max_normalized: int = 256,
        retain_parity_mask: bool = False,
        retain_field_action: bool = True,
        prefix_steps: tuple[int, ...] = (),
        record_step: Callable[[], None],
        reserve_bits: Callable[[int], None],
        record_work: Callable[[int], None],
    ) -> DyadicSourceWindowAction:
        """Produce one source-guarded action, its clocks, and same-pass prefixes.

        Only the bounded source scan can call the coefficient constructors here.
        Endpoint coefficients are always retained; successor-sum/predecessor
        fields, the parity mask, and requested prefixes are captured during that
        same scan only when demanded. This factory accepts no supplied coefficients.
        """
        source = require_integer(source, "diagonal source", 1)
        physical_budget = require_integer(physical_budget, "physical budget", 0)
        max_normalized = require_integer(
            max_normalized,
            "diagonal window symbols",
            1,
            MAX_DYADIC_SOURCE_WINDOW_STEPS,
        )
        if type(retain_parity_mask) is not bool:
            raise TypeError("diagonal optional output demand must be Boolean")
        if type(retain_field_action) is not bool:
            raise TypeError("diagonal field-action demand must be Boolean")
        if (
            type(prefix_steps) is not tuple
            or any(
                type(prefix_step) is not int
                or prefix_step <= 0
                or prefix_step > max_normalized
                for prefix_step in prefix_steps
            )
            or any(left >= right for left, right in pairwise(prefix_steps))
        ):
            raise ValueError("source-window prefix schedule is malformed")
        if (
            not callable(reserve_bits)
            or not callable(record_step)
            or not callable(record_work)
        ):
            raise TypeError("source-window issuance requires resource and work owners")
        k_limit = min(max_normalized, physical_budget)
        prefix_capacity = len(prefix_steps)
        reserve_bits(
            8
            * (
                source.bit_length()
                + (10 if retain_field_action else 4) * k_limit
                + physical_budget.bit_length()
                + 96
                + prefix_capacity * (source.bit_length() + 512)
            )
        )

        low = source & ((1 << k_limit) - 1) if k_limit else 0
        gain, offset = 1, 0
        field_accumulator = _WindowFieldAccumulator() if retain_field_action else None
        denominator = 1
        steps = odd_symbols = spent = parity_mask = 0
        prefix_states: list[_EndpointWindowPrefixState | _FieldWindowPrefixState] = []
        next_prefix = 0
        while steps < k_limit:
            odd = low & 1
            cost = 1 + odd
            if spent + cost > physical_budget:
                break
            old_low = low
            old_gain = gain
            old_offset = offset
            old_denominator = denominator
            parity_work = 0
            if odd:
                gain *= 3
                offset = 3 * offset + denominator
                low = (3 * low + 1) >> 1
                odd_symbols += 1
                if retain_parity_mask:
                    shifted_bit = 1 << steps
                    updated_mask = parity_mask | shifted_bit
                    parity_work = (
                        1
                        + steps.bit_length()
                        + parity_mask.bit_length()
                        + shifted_bit.bit_length()
                        + updated_mask.bit_length()
                    )
                    parity_mask = updated_mask
            else:
                low >>= 1
            denominator <<= 1
            field_work = (
                0
                if field_accumulator is None
                else field_accumulator.advance(old_gain, old_offset, gain, offset)
            )
            record_work(
                old_low.bit_length()
                + old_gain.bit_length()
                + old_offset.bit_length()
                + old_denominator.bit_length()
                + gain.bit_length()
                + offset.bit_length()
                + field_work
                + parity_work
                + 12
            )
            spent += cost
            steps += 1
            record_step()
            if next_prefix < len(prefix_steps) and steps == prefix_steps[next_prefix]:
                if field_accumulator is not None:
                    prefix_states.append(
                        field_accumulator.prefix_state(
                            steps,
                            gain,
                            offset,
                            odd_symbols,
                        )
                    )
                else:
                    prefix_states.append(
                        _EndpointWindowPrefixState(
                            steps,
                            gain,
                            offset,
                            odd_symbols,
                        )
                    )
                next_prefix += 1

        action: DyadicTerminalEndpointAction | DyadicTerminalFieldAction
        if field_accumulator is not None:
            action = cls._create(
                steps,
                gain,
                offset,
                field_accumulator.sum_gain,
                field_accumulator.sum_offset,
                field_accumulator.previous_gain,
                field_accumulator.previous_offset,
            )
        else:
            action = DyadicTerminalEndpointAction(
                steps,
                gain,
                offset,
                _issuer=_FIELD_ACTION_ISSUER,
                _word_issuer=_FIELD_WORD_ISSUER,
            )
        normalized_endpoint = action.endpoint(source)
        record_work(
            2 * source.bit_length()
            + sum(
                max(1, abs(coefficient).bit_length())
                for coefficient in action.coefficient_snapshot()
            )
            + 2 * steps
            + 16
        )
        phase = int(
            spent < physical_budget
            and physical_budget - spent == 1
            and normalized_endpoint % 2 == 1
        )
        physical_ticks = spent + phase
        physical_endpoint = (
            3 * normalized_endpoint + 1 if phase else normalized_endpoint
        )
        prefixes: list[DyadicSourceWindowPrefix] = []
        for prefix_state in prefix_states:
            prefix_action: DyadicTerminalEndpointAction | DyadicTerminalFieldAction
            if type(prefix_state) is _FieldWindowPrefixState:
                prefix_width = prefix_state.steps
                prefix_odd_symbols = prefix_state.odd_symbols
                prefix_action = cls._create(
                    prefix_width,
                    prefix_state.gain,
                    prefix_state.offset,
                    prefix_state.sum_gain,
                    prefix_state.sum_offset,
                    prefix_state.previous_gain,
                    prefix_state.previous_offset,
                )
            elif type(prefix_state) is _EndpointWindowPrefixState:
                prefix_width = prefix_state.steps
                prefix_odd_symbols = prefix_state.odd_symbols
                prefix_action = DyadicTerminalEndpointAction(
                    prefix_width,
                    prefix_state.gain,
                    prefix_state.offset,
                    _issuer=_FIELD_ACTION_ISSUER,
                    _word_issuer=_FIELD_WORD_ISSUER,
                )
            else:
                raise TypeError("source-window prefix state is malformed")
            normalized_prefix_endpoint = prefix_action.endpoint(source)
            prefixes.append(
                DyadicSourceWindowPrefix(
                    prefix_action,
                    prefix_odd_symbols,
                    normalized_prefix_endpoint,
                )
            )
            record_work(
                2 * source.bit_length()
                + sum(
                    max(1, abs(coefficient).bit_length())
                    for coefficient in prefix_action.coefficient_snapshot()
                )
                + 2 * prefix_width
                + 16
            )
        return DyadicSourceWindowAction(
            action,
            source,
            odd_symbols,
            physical_ticks,
            phase,
            normalized_endpoint,
            physical_endpoint,
            parity_mask if retain_parity_mask else None,
            tuple(prefixes),
        )


class DyadicSourceWindowPrefix(NamedTuple):
    """One same-pass source prefix used to form an aligned cache interval."""

    action: DyadicTerminalEndpointAction | DyadicTerminalFieldAction
    odd_symbols: int
    normalized_endpoint: int


class DyadicSourceWindowAction(NamedTuple):
    """One action and clocks issued by the bounded low-bit source producer."""

    action: DyadicTerminalEndpointAction | DyadicTerminalFieldAction
    source: int
    odd_symbols: int
    physical_ticks: int
    phase: int
    normalized_endpoint: int
    physical_endpoint: int
    parity_mask: int | None
    prefixes: tuple[DyadicSourceWindowPrefix, ...]


__all__ = [
    "DyadicSourceWindowAction",
    "DyadicSourceWindowPrefix",
    "DyadicTerminalEndpointAction",
    "DyadicTerminalFieldAction",
    "MAX_DYADIC_SOURCE_WINDOW_STEPS",
]
