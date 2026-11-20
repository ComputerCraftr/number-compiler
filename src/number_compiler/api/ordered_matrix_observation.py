"""Demanded ordered outputs selected through existing family source owners."""

from __future__ import annotations

from dataclasses import asdict
from typing import TYPE_CHECKING, Protocol

from number_compiler.api.matrix_contracts import MatrixKind, OrderedMatrixRequest
from number_compiler.api.reverse_payloads import (
    DoubleReverseTermPayload,
    PoweredReverseAddTermPayload,
)

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.arithmetic.contracts.ordered_output import OrderedBandOutput


class _OrderedDigitOwner(Protocol):
    def ordered_digit_band(
        self,
        steps: int,
        width: int,
        modulus: int,
        /,
        *,
        coefficients: tuple[int, ...] | None = None,
        trace: bool = False,
    ) -> OrderedBandOutput: ...


def _digit_packet(
    term: _OrderedDigitOwner, request: OrderedMatrixRequest
) -> dict[str, object]:
    if request.kind is not MatrixKind.DIGIT_BAND:
        raise ValueError("this source owner has no admitted bit-fibre carry output")
    return asdict(
        term.ordered_digit_band(
            request.steps,
            request.band_width,
            request.modulus,
            coefficients=request.coefficients,
            trace=request.trace,
        )
    )


def double_ordered(
    context: QueryContext, request: OrderedMatrixRequest
) -> dict[str, object]:
    payload = context.term.payload
    if not isinstance(payload, DoubleReverseTermPayload):
        raise TypeError("2rev10 ordered matrix requires its issued source owner")
    return _digit_packet(payload.term, request)


def reverse_ordered(
    context: QueryContext, request: OrderedMatrixRequest
) -> dict[str, object]:
    payload = context.term.payload
    if not isinstance(payload, PoweredReverseAddTermPayload):
        raise TypeError("reverse ordered matrix requires its issued source owner")
    return _digit_packet(payload.term, request)
