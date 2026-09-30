"""Exact original-source carry pullback for the same-carry no-growth chamber."""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import closing
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.formula.skew_residue_laws import (
    pair_no_growth,
    skew_normalized_digit,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_ports import SourceCarryPorts


class SameCarryChamberRejected(ValueError):
    """The requested power leaves the bounded same-carry chamber."""


@dataclass(frozen=True, slots=True)
class SameCarryChamberCertificate:
    steps: int
    width: int
    all_slopes_zero: bool


def _endpoint_pair(pair: int, beta: int, exponent: int, pair_max: int) -> int:
    slope = pair + beta
    if slope == 0:
        endpoint = -beta
    else:
        maximum_scale = (pair_max + beta) // slope if slope > 0 else (-beta) // (-slope)
        if maximum_scale < 1 or exponent >= maximum_scale.bit_length():
            raise SameCarryChamberRejected(
                "powered pair leaves the same-carry radix chamber"
            )
        endpoint = (1 << exponent) * slope - beta
    if not 0 <= endpoint <= pair_max:
        raise SameCarryChamberRejected(
            "powered pair leaves the same-carry radix chamber"
        )
    return endpoint


def validate_same_carry_chamber(
    source: ExactSource,
    steps: int,
    ledger: ResourceLedger,
    *,
    ports: SourceCarryPorts | None = None,
) -> SameCarryChamberCertificate:
    """Validate the complete powered pair field before publication."""
    if type(steps) is not int or steps < 3:
        raise ValueError("same-carry powered chamber requires at least three steps")
    owned = ports is None
    ports = SourceCarryPorts(source, ledger) if ports is None else ports
    ports.check_source(source)
    try:
        return _validate_ports(ports, steps)
    finally:
        if owned:
            ports.dispose()


def _validate_ports(ports: SourceCarryPorts, steps: int) -> SameCarryChamberCertificate:
    source, ledger = ports.source, ports.ledger
    if ports.terminal:
        ledger.bump("reverse_source_chamber_rejections")
        raise SameCarryChamberRejected("original source leaves the no-growth chamber")
    exponent = steps - 1
    all_zero = True
    with (
        closing(ports.iter_first_ports()) as forward,
        closing(ports.iter_first_ports(reflected=True)) as reflected,
    ):
        for position, (left, right) in enumerate(zip(forward, reflected, strict=True)):
            pair = ports.pair(position)
            left_in, left_out = left
            right_in, right_out = right
            beta = pair_no_growth(
                0, left_in, left_out, right_in, right_out, source.base
            )
            try:
                endpoint = _endpoint_pair(pair, beta, exponent, 2 * source.base - 2)
            except SameCarryChamberRejected:
                ledger.bump("reverse_source_chamber_rejections")
                raise
            all_zero &= pair + beta == 0
            if int(endpoint + left_in >= source.base) != left_out:
                ledger.bump("reverse_source_chamber_rejections")
                raise SameCarryChamberRejected(
                    "powered pair changes an original source carry port"
                )
            ledger.bump("reverse_source_chamber_guard_coordinates")
    ledger.bump("reverse_source_chamber_admissions")
    return SameCarryChamberCertificate(steps, ports.width, all_zero)


def same_carry_digit(ports: SourceCarryPorts, steps: int, position: int) -> int:
    """Consume a previously admitted chamber at one coordinate, without replay."""
    return _same_carry_digit(
        ports,
        steps,
        position,
        (ports.carry(position), ports.carry(position + 1)),
        (ports.carry(ports.width - 1 - position), ports.carry(ports.width - position)),
    )


def _same_carry_digit(
    ports: SourceCarryPorts,
    steps: int,
    position: int,
    left: tuple[int, int],
    right: tuple[int, int],
) -> int:
    source, ledger = ports.source, ports.ledger
    pair = ports.pair(position)
    left_in, left_out = left
    right_in, right_out = right
    beta = pair_no_growth(0, left_in, left_out, right_in, right_out, source.base)
    endpoint = _endpoint_pair(pair, beta, steps - 1, 2 * source.base - 2)
    if source.base == 10:
        domain = int(endpoint >= 9) + int(endpoint > 9)
        digit = skew_normalized_digit(domain, endpoint % 9, left_in)
        ledger.bump("reverse_source_mod9_digit_reconstructions")
    else:
        digit = endpoint + left_in - source.base * left_out
        ledger.bump("reverse_source_radix_digit_reconstructions")
    if not 0 <= digit < source.base:
        raise ValueError("same-carry chamber emitted a non-radix digit")
    ledger.bump("reverse_source_chamber_projection_coordinates")
    return digit


def iter_admitted_same_carry_digits(
    ports: SourceCarryPorts, steps: int
) -> Iterator[int]:
    """Consume admitted output with shared regional carry contexts."""
    forward = ports.iter_first_ports()
    reflected = ports.iter_first_ports(reflected=True)
    try:
        for position, (left, right) in enumerate(zip(forward, reflected, strict=True)):
            yield _same_carry_digit(ports, steps, position, left, right)
    finally:
        forward.close()
        reflected.close()


def iter_same_carry_digits(
    source: ExactSource, steps: int, ledger: ResourceLedger
) -> Iterator[int]:
    """Validate first, then stream the powered output without a temporal loop."""
    ports = SourceCarryPorts(source, ledger)
    try:
        validate_same_carry_chamber(source, steps, ledger, ports=ports)
        yield from iter_admitted_same_carry_digits(ports, steps)
    finally:
        ports.dispose()


__all__ = [
    "SameCarryChamberCertificate",
    "SameCarryChamberRejected",
    "iter_same_carry_digits",
    "same_carry_digit",
    "validate_same_carry_chamber",
]
