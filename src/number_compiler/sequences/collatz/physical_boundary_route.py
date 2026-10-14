"""Exact low-cylinder guards for Collatz physical boundary routes."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicReturnImageWorkspace,
    _SourceNode,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.temporal_dyadic import (
    D8TemporalTable,
    bounded_run_length,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.dyadic_return_runs import (
        RunArithmeticWorkspace,
    )


_MAX_BOUNDARY_ROUTE_TAIL = DyadicReturnImageWorkspace.MAX_LEAF_STEPS


def _source_modulo(source: _SourceNode, modulus: int) -> int:
    """Read a small exact-source residue without assembling its full value."""
    return (
        source.residue % modulus
        + (source.lift % modulus) * pow(2, source.precision, modulus)
    ) % modulus


def leading_homogeneous_run(source: int, remaining: int) -> tuple[int, int, int]:
    """Return the low byte, exact run length, and requested normalized prefix."""
    low = source & 255
    available = bounded_run_length(low)
    if low in (0, 255):
        available = v2_positive(source + 1 if low == 255 else source)
    normalized = min(available, remaining // 2 if low & 1 else remaining)
    return low, available, normalized


def exact_source_bit_length(source: _SourceNode) -> int:
    """Compute an exact cylinder source width without assembling its value."""
    if type(source) is not _SourceNode or not source.exact:
        raise ValueError("source width requires an exact admitted cylinder")
    return max(
        1,
        source.residue.bit_length(),
        source.lift.bit_length() + source.precision if source.lift else 0,
    )


def _affine_power_guard(
    source: _SourceNode,
    coefficient: int,
    offset: int,
    exponent: int,
    *,
    source_bits: int,
    ledger: ResourceLedger | None,
    scratch: RunArithmeticWorkspace | None,
) -> bool:
    """Certify affine divisibility with progressively widened low residues."""
    if exponent > source_bits + max(2, coefficient.bit_length()):
        if ledger is not None:
            ledger.bump("collatz_boundary_route_extent_impossible_checks")
        return False
    checked = 1
    while True:
        checked = min(exponent, checked)
        if scratch is not None:
            scratch.require_bits(8 * (source_bits + checked + 17))
        modulus = 1 << checked
        if ledger is not None:
            ledger.bump("collatz_boundary_route_extent_residue_checks")
            ledger.bump(
                "collatz_boundary_route_extent_operand_bits",
                source_bits + modulus.bit_length(),
            )
        if (coefficient * _source_modulo(source, modulus) + offset) % modulus:
            return False
        if checked == exponent:
            return True
        checked = min(exponent, checked * 2)


def _quotient_power_guard(
    source: _SourceNode,
    divisor: int,
    base: int,
    exponent: int,
    *,
    source_bits: int,
    ledger: ResourceLedger | None,
    scratch: RunArithmeticWorkspace | None,
) -> bool:
    """Certify a quotient-based 2-adic guard without constructing the quotient."""
    if exponent > source_bits + divisor.bit_length() + 2:
        if ledger is not None:
            ledger.bump("collatz_boundary_route_extent_impossible_checks")
        return False
    checked = 1
    while True:
        checked = min(exponent, checked)
        if scratch is not None:
            scratch.require_bits(
                8 * (source_bits + divisor.bit_length() + checked + 16)
            )
        power = 1 << checked
        modulus = divisor * power
        if ledger is not None:
            ledger.bump("collatz_boundary_route_extent_residue_checks")
            ledger.bump(
                "collatz_boundary_route_extent_operand_bits",
                source_bits + modulus.bit_length(),
            )
        residue = _source_modulo(source, modulus)
        quotient_numerator = residue - base
        if quotient_numerator % divisor:
            return False
        quotient = quotient_numerator // divisor
        if (3 * quotient + 1) % power:
            return False
        if checked == exponent:
            return True
        checked = min(exponent, checked * 2)


def _needed_repetitions(width: int, stride: int, terminal_ticks: int) -> int:
    useful_ticks = max(0, width - _MAX_BOUNDARY_ROUTE_TAIL)
    return max(1, (useful_ticks - terminal_ticks + stride - 1) // stride)


def _has_useful_boundary_extent(
    source: _SourceNode,
    width: int,
    family: str,
    phase: int | None,
    *,
    ledger: ResourceLedger | None,
    scratch: RunArithmeticWorkspace | None,
) -> bool:
    """Require a source-certified macro prefix plus a bounded exact tail."""
    if width <= _MAX_BOUNDARY_ROUTE_TAIL:
        return True
    source_bits = exact_source_bit_length(source)
    if family in ("421", "4721", "0563"):
        stride, terminal = (3, 1) if family == "421" else (4, 1)
        repetitions = _needed_repetitions(width, stride, terminal)
        offset = -4 if family == "421" else 2
        return _affine_power_guard(
            source,
            1,
            offset,
            2 * repetitions + 1,
            source_bits=source_bits,
            ledger=ledger,
            scratch=scratch,
        )
    if phase is not None:
        repetitions = _needed_repetitions(width, 5, 1 - phase)
        return _affine_power_guard(
            source,
            13,
            -(1 << (4 - phase)),
            4 * repetitions - phase + 1,
            source_bits=source_bits,
            ledger=ledger,
            scratch=scratch,
        )
    if family == "630":
        repetitions = _needed_repetitions(width, 1, 3)
        return _quotient_power_guard(
            source,
            20,
            6,
            repetitions,
            source_bits=source_bits,
            ledger=ledger,
            scratch=scratch,
        )
    if family == "305":
        repetitions = _needed_repetitions(width, 1, 2)
        return _quotient_power_guard(
            source,
            10,
            3,
            repetitions,
            source_bits=source_bits,
            ledger=ledger,
            scratch=scratch,
        )
    if family == "989":
        repetitions = _needed_repetitions(width, 2, 0)
        return _affine_power_guard(
            source,
            1,
            1,
            repetitions,
            source_bits=source_bits,
            ledger=ledger,
            scratch=scratch,
        )
    return False


def has_admitted_boundary_macro(
    source: _SourceNode,
    width: int,
    *,
    include_innovation_tape: bool,
    include_joint_cocycle: bool,
    allow_border_return: bool = True,
    ledger: ResourceLedger | None = None,
    scratch: RunArithmeticWorkspace | None = None,
) -> bool:
    """Select a guarded macro only when it leaves a bounded exact tail."""
    if type(source) is not _SourceNode or not source.exact:
        return False
    if type(allow_border_return) is not bool:
        raise TypeError("border-return admission choice must be Boolean")
    if ledger is not None:
        ledger.bump("collatz_physical_boundary_macro_plan_checks")
        ledger.bump(
            "collatz_physical_boundary_macro_plan_operand_bits",
            source.residue.bit_length() + source.lift.bit_length() + width.bit_length(),
        )
    if (
        width >= 7
        and _source_modulo(source, 160) == 4
        and exact_source_bit_length(source) > 3
    ):
        return _has_useful_boundary_extent(
            source, width, "421", None, ledger=ledger, scratch=scratch
        )
    if width >= 9 and _source_modulo(source, 160) == 94:
        return _has_useful_boundary_extent(
            source, width, "4721", None, ledger=ledger, scratch=scratch
        )
    if width >= 5 and _source_modulo(source, 40) == 30:
        return _has_useful_boundary_extent(
            source, width, "0563", None, ledger=ledger, scratch=scratch
        )
    if width >= 7 and _source_modulo(source, 160) == 112:
        return _has_useful_boundary_extent(
            source, width, "26847", 0, ledger=ledger, scratch=scratch
        )
    if width >= 6 and _source_modulo(source, 80) == 56:
        return _has_useful_boundary_extent(
            source, width, "26847P1", 1, ledger=ledger, scratch=scratch
        )
    if width >= 5 and _source_modulo(source, 40) == 28:
        return _has_useful_boundary_extent(
            source, width, "26847P2", 2, ledger=ledger, scratch=scratch
        )
    if width >= 4 and _source_modulo(source, 20) == 14:
        family, phase = (
            ("4721", None) if _source_modulo(source, 40) == 14 else ("26847P3", 3)
        )
        return _has_useful_boundary_extent(
            source, width, family, phase, ledger=ledger, scratch=scratch
        )
    if width >= 3 and _source_modulo(source, 10) == 7:
        return _has_useful_boundary_extent(
            source, width, "26847P4", 4, ledger=ledger, scratch=scratch
        )
    if allow_border_return and width >= 6 and _source_modulo(source, 10) == 3:
        return _has_useful_boundary_extent(
            source, width, "305", None, ledger=ledger, scratch=scratch
        )
    if allow_border_return and width >= 5 and _source_modulo(source, 80) == 26:
        return _has_useful_boundary_extent(
            source, width, "630", None, ledger=ledger, scratch=scratch
        )
    if (
        (include_innovation_tape or include_joint_cocycle)
        and width >= 4
        and _source_modulo(source, 20) == 19
        and _source_modulo(source, 4) == 3
    ):
        return _has_useful_boundary_extent(
            source, width, "989", None, ledger=ledger, scratch=scratch
        )
    return False


def release_d8_rows_if_unleased(
    ledger: ResourceLedger, workspace_type: type[object]
) -> None:
    """Release D8 ledger rows after the last live workspace lease closes."""
    has_live_workspace = any(
        isinstance(root, workspace_type)
        and getattr(root, "ledger", None) is ledger
        and getattr(root, "_closed", True) is False
        for root in ledger.iter_execution_roots()
    )
    D8TemporalTable.release_if_unleased(
        ledger, has_live_collatz_workspace=has_live_workspace
    )
