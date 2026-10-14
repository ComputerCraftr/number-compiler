"""Total physical decimal boundary controller with an explicit inward port.

The port is the parity of the higher decimal quotient. It is source input,
not a prediction made from the current digit or an innovation observation.
Distinct present-digit outputs already distinguish all ten Moore states.
"""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.resources.ledger import ResourceLedger


def physical_digit_successor(digit: int, inward: int) -> int:
    """Apply one physical step to an admitted decimal digit and inward bit."""
    if type(digit) is not int or not 0 <= digit < 10:
        raise ValueError("physical boundary digit must be in 0..9")
    if type(inward) is not int or inward not in (0, 1):
        raise ValueError("physical boundary inward port must be a bit")
    return (3 * digit + 1) % 10 if digit & 1 else digit // 2 + 5 * inward


@dataclass(frozen=True, slots=True)
class DecimalBoundaryEdge:
    """A source-qualified edge, with occurrence residue separate from control."""

    residue20: int
    source_digit: int
    target_digit: int
    inward_bit: int


def physical_boundary_edge(source: int) -> DecimalBoundaryEdge:
    if type(source) is not int or source <= 0:
        raise ValueError("physical boundary source must be a positive integer")
    residue = source % 20
    digit = residue % 10
    inward = residue // 10
    return DecimalBoundaryEdge(
        residue, digit, physical_digit_successor(digit, inward), inward
    )


def physical_boundary_packet(source: int, ledger: ResourceLedger) -> dict[str, object]:
    """Observe the initial exact source without discovering its future inputs."""
    edge = physical_boundary_edge(source)
    ledger.bump("collatz_decimal_boundary_source_classifications")
    ledger.bump("collatz_decimal_boundary_operand_bits", source.bit_length())
    return {
        "source_residue": edge.residue20,
        "source_modulus": 20,
        "source_digit": edge.source_digit,
        "target_digit": edge.target_digit,
        "inward_bit": edge.inward_bit,
        "scope": "one physical step; higher-quotient parity is authenticated source input",
    }
