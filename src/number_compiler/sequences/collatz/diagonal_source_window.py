"""Bounded source-certified normalized Collatz windows.

The low-bit source action is produced by the canonical dyadic action owner.
This module retains the optional same-pass parity word and its finite source
occurrence seal, without loading the larger spatial/Laurent observation code.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, TypeGuard

from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    MAX_DYADIC_SOURCE_WINDOW_STEPS,
    DyadicSourceWindowPrefix,
    DyadicTerminalEndpointAction,
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.mahler_joint_carry import (
        MahlerFutureCarryPort,
    )

_DIAGONAL_WINDOW_ISSUER = object()


def _is_source_window_action(
    value: object,
) -> TypeGuard[DyadicTerminalEndpointAction | DyadicTerminalFieldAction]:
    return type(value) in (DyadicTerminalEndpointAction, DyadicTerminalFieldAction)


@dataclass(frozen=True, slots=True)
class _DiagonalWindowCertificate:
    """Independent immutable evidence retained by a source-window value."""

    action_kind: type[object]
    action_coefficients: tuple[int, ...]
    source: int
    odd_symbols: int
    physical_ticks: int
    phase: int
    normalized_endpoint: int
    physical_endpoint: int
    parity_mask: int | None
    prefixes: tuple[tuple[type[object], tuple[int, ...], int, int], ...]
    issuer: object


@dataclass(frozen=True, slots=True, init=False)
class CollatzDiagonalWindow:
    """One exact finite source cylinder issued by the bounded low-bit producer.

    A window is neither a cache entry nor a repeatable semantic class.  Its
    optional parity mask is present only for an explicitly requested grammar.
    """

    action: DyadicTerminalEndpointAction | DyadicTerminalFieldAction
    source: int
    odd_symbols: int
    physical_ticks: int
    phase: int
    normalized_endpoint: int
    physical_endpoint: int
    _parity_mask: int | None = field(repr=False, compare=False)
    prefixes: tuple[DyadicSourceWindowPrefix, ...]
    _issuer: object = field(repr=False, compare=False)
    _issued_certificate: _DiagonalWindowCertificate = field(repr=False, compare=False)

    def __init__(self, *_args: object, **_kwargs: object) -> None:
        raise TypeError("diagonal windows must be issued by their bounded producer")

    @classmethod
    def from_source_window(
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
    ) -> CollatzDiagonalWindow:
        """Issue and seal one exact source window through its owning classes."""
        issued = DyadicTerminalFieldAction.issue_source_window(
            source,
            physical_budget,
            max_normalized=max_normalized,
            retain_parity_mask=retain_parity_mask,
            retain_field_action=retain_field_action,
            prefix_steps=prefix_steps,
            record_step=record_step,
            reserve_bits=reserve_bits,
            record_work=record_work,
        )
        return cls._issue(
            issued.action,
            issued.source,
            issued.odd_symbols,
            issued.physical_ticks,
            issued.phase,
            issued.normalized_endpoint,
            issued.physical_endpoint,
            issued.parity_mask,
            issued.prefixes,
            record_work,
        )

    @classmethod
    def _issue(
        cls,
        action: DyadicTerminalEndpointAction | DyadicTerminalFieldAction,
        source: int,
        odd_symbols: int,
        physical_ticks: int,
        phase: int,
        normalized_endpoint: int,
        physical_endpoint: int,
        parity_mask: int | None,
        prefixes: tuple[DyadicSourceWindowPrefix, ...],
        record_work: Callable[[int], None],
    ) -> CollatzDiagonalWindow:
        if not _is_source_window_action(action):
            raise TypeError("diagonal source action has a foreign type")
        result = object.__new__(cls)
        values: tuple[object, ...] = (
            action,
            source,
            odd_symbols,
            physical_ticks,
            phase,
            normalized_endpoint,
            physical_endpoint,
            parity_mask,
            prefixes,
        )
        for name, value in zip(
            (
                "action",
                "source",
                "odd_symbols",
                "physical_ticks",
                "phase",
                "normalized_endpoint",
                "physical_endpoint",
                "_parity_mask",
                "prefixes",
            ),
            values,
            strict=True,
        ):
            object.__setattr__(result, name, value)
        if type(prefixes) is not tuple or any(
            type(prefix) is not DyadicSourceWindowPrefix
            or not _is_source_window_action(prefix.action)
            or type(prefix.action) is not type(action)
            for prefix in prefixes
        ):
            raise TypeError("diagonal reusable prefixes are malformed")
        certificate = _DiagonalWindowCertificate(
            type(action),
            action.coefficient_snapshot(),
            source,
            odd_symbols,
            physical_ticks,
            phase,
            normalized_endpoint,
            physical_endpoint,
            parity_mask,
            tuple(
                (
                    type(prefix.action),
                    prefix.action.coefficient_snapshot(),
                    prefix.odd_symbols,
                    prefix.normalized_endpoint,
                )
                for prefix in prefixes
            ),
            _DIAGONAL_WINDOW_ISSUER,
        )
        object.__setattr__(result, "_issuer", _DIAGONAL_WINDOW_ISSUER)
        object.__setattr__(result, "_issued_certificate", certificate)
        result.require_issued()
        if (
            action.endpoint(source) != normalized_endpoint
            or physical_ticks != action.steps + odd_symbols + phase
            or phase not in (0, 1)
            or physical_endpoint
            != (normalized_endpoint if phase == 0 else 3 * normalized_endpoint + 1)
            or (phase == 1 and normalized_endpoint % 2 != 1)
        ):
            raise ValueError("diagonal window producer supplied a false endpoint")
        record_work(
            2 * source.bit_length()
            + 2 * action.gain.bit_length()
            + action.offset.bit_length()
            + 2 * action.steps
            + 16
        )
        previous_steps = 0
        previous_ones = 0
        for prefix in prefixes:
            if (
                not prefix.action.producer_issued
                or type(prefix.action) is not type(action)
                or prefix.action.steps <= previous_steps
                or prefix.action.steps > action.steps
                or type(prefix.odd_symbols) is not int
                or not previous_ones <= prefix.odd_symbols <= prefix.action.steps
                or prefix.odd_symbols > odd_symbols
                or type(prefix.normalized_endpoint) is not int
                or prefix.normalized_endpoint <= 0
            ):
                raise ValueError("diagonal window has an invalid reusable prefix")
            if prefix.action.endpoint(source) != prefix.normalized_endpoint:
                raise ValueError("diagonal window prefix has an invalid endpoint")
            record_work(
                2 * source.bit_length()
                + 2 * prefix.action.gain.bit_length()
                + prefix.action.offset.bit_length()
                + 2 * prefix.action.steps
                + 16
            )
            previous_steps = prefix.action.steps
            previous_ones = prefix.odd_symbols
        return result

    @property
    def parity_mask(self) -> int | None:
        """Return the producer-retained compact word, if it was demanded."""
        self.require_issued()
        return self._parity_mask

    def require_field_action(self) -> DyadicTerminalFieldAction:
        """Return the full affine field only when its arithmetic was demanded."""
        self.require_issued()
        action = self.action
        if type(action) is not DyadicTerminalFieldAction:
            raise ValueError("diagonal source window retained endpoint arithmetic only")
        return action

    def mahler_future_carry_port(self) -> MahlerFutureCarryPort:
        """View this issued endpoint as the next 6305 source seam."""
        from number_compiler.sequences.collatz.mahler_joint_carry import (
            MahlerFutureCarryPort,
        )

        return MahlerFutureCarryPort.from_issued_window(self)

    @property
    def producer_issued(self) -> bool:
        """Check the producer seal without rebuilding powers or the parity word."""
        certificate = self._issued_certificate
        return (
            self._issuer is _DIAGONAL_WINDOW_ISSUER
            and type(certificate) is _DiagonalWindowCertificate
            and certificate.issuer is _DIAGONAL_WINDOW_ISSUER
            and _is_source_window_action(self.action)
            and self.action.producer_issued
            and certificate.action_kind is type(self.action)
            and certificate.action_coefficients == self.action.coefficient_snapshot()
            and certificate.source == self.source
            and certificate.odd_symbols == self.odd_symbols
            and certificate.physical_ticks == self.physical_ticks
            and certificate.phase == self.phase
            and certificate.normalized_endpoint == self.normalized_endpoint
            and certificate.physical_endpoint == self.physical_endpoint
            and certificate.parity_mask == self._parity_mask
            and type(self.prefixes) is tuple
            and certificate.prefixes
            == tuple(
                (
                    type(prefix.action),
                    prefix.action.coefficient_snapshot(),
                    prefix.odd_symbols,
                    prefix.normalized_endpoint,
                )
                for prefix in self.prefixes
                if type(prefix) is DyadicSourceWindowPrefix
                and _is_source_window_action(prefix.action)
            )
            and all(
                type(prefix) is DyadicSourceWindowPrefix
                and _is_source_window_action(prefix.action)
                for prefix in self.prefixes
            )
        )

    def require_issued(self) -> None:
        if not self.producer_issued:
            raise ValueError("diagonal source window changed after issuance")
        if (
            type(self.source) is not int
            or self.source <= 0
            or type(self.odd_symbols) is not int
            or not 0 <= self.odd_symbols <= self.action.steps
            or type(self.physical_ticks) is not int
            or self.physical_ticks < 0
            or type(self.phase) is not int
            or self.phase not in (0, 1)
            or type(self.normalized_endpoint) is not int
            or self.normalized_endpoint <= 0
            or type(self.physical_endpoint) is not int
            or self.physical_endpoint <= 0
            or self.action.steps + self.odd_symbols + self.phase != self.physical_ticks
            or self.physical_endpoint
            != (
                self.normalized_endpoint
                if self.phase == 0
                else 3 * self.normalized_endpoint + 1
            )
            or (self.phase == 1 and self.normalized_endpoint % 2 != 1)
        ):
            raise ValueError("diagonal source window has invalid issued coordinates")
        if self._parity_mask is not None and (
            type(self._parity_mask) is not int
            or self._parity_mask < 0
            or self._parity_mask.bit_length() > self.action.steps
            or self._parity_mask.bit_count() != self.odd_symbols
        ):
            raise ValueError("diagonal source window parity mask was changed")
        previous_steps = 0
        previous_ones = 0
        for prefix in self.prefixes:
            if (
                not prefix.action.producer_issued
                or type(prefix.action) is not type(self.action)
                or prefix.action.steps <= previous_steps
                or prefix.action.steps > self.action.steps
                or not previous_ones <= prefix.odd_symbols <= prefix.action.steps
                or prefix.odd_symbols > self.odd_symbols
                or prefix.normalized_endpoint <= 0
            ):
                raise ValueError("diagonal reusable prefix coordinates were changed")
            previous_steps = prefix.action.steps
            previous_ones = prefix.odd_symbols

    def parity_factor(
        self,
        *,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> tuple[int, ...]:
        """Materialize the demanded finite parity motif after reserving memory."""
        self.require_issued()
        max_width = require_integer(max_width, "parity motif width", 1, 4096)
        reserve_bits = _require_reservation_callback(reserve_bits)
        mask = self._parity_mask
        if mask is None:
            raise ValueError("diagonal source window has no demanded parity grammar")
        steps = self.action.steps
        if steps > max_width:
            raise ValueError("diagonal parity motif exceeds its requested width")
        reserve_bits(8 * (self.source.bit_length() + 2 * steps + 64))
        return tuple((mask >> index) & 1 for index in range(steps))


def source_window_checkpoint_steps(
    normalized_offset: int, max_normalized: int
) -> tuple[int, ...]:
    """Partition a bounded source window at offset-aligned dyadic boundaries."""
    normalized_offset = require_integer(
        normalized_offset, "normalized source offset", 0
    )
    max_normalized = require_integer(
        max_normalized,
        "diagonal window symbols",
        1,
        MAX_DYADIC_SOURCE_WINDOW_STEPS,
    )
    offset = normalized_offset
    local = 0
    boundaries: list[int] = []
    while local < max_normalized:
        remaining = max_normalized - local
        low_bit = offset & -offset
        if offset % 8:
            width = min(8 - offset % 8, remaining)
        elif offset == 0:
            width = min(8, remaining)
        else:
            width = min(low_bit, 1 << (remaining.bit_length() - 1))
        local += width
        offset += width
        boundaries.append(local)
    return tuple(boundaries)


def _require_reservation_callback(
    reserve_bits: Callable[[int], None],
) -> Callable[[int], None]:
    if not callable(reserve_bits):
        raise TypeError("diagonal work requires the active resource reservation")
    return reserve_bits


__all__ = [
    "CollatzDiagonalWindow",
    "source_window_checkpoint_steps",
]
