"""Lazy spatial and Laurent projections of an issued Collatz action.

This module is imported only for a demanded diagonal observation. The ordinary
scheduler and bounded source-window producer do not load these projections.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from fractions import Fraction
from itertools import pairwise
from typing import TYPE_CHECKING
from weakref import ReferenceType, ref

from number_compiler.arithmetic.carry.carry_normalization import (
    linear_normalization_fields,
)
from number_compiler.arithmetic.contracts.input_validation import require_integer
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.joint_temporal_action import (
        CollatzJointRunAction,
    )
    from number_compiler.sequences.collatz.physical_images import (
        CollatzPhysicalImageWorkspace,
    )
    from number_compiler.sequences.collatz.weighted_right_congruence import (
        CollatzDoubleWeight,
    )

_DIAGONAL_SEAM_ISSUER = object()
_MAX_DIAGONAL_QUERY_EVENTS = 4096


@dataclass(frozen=True, slots=True)
class CollatzDiagonalField:
    """A bounded, LSB-first endpoint field and its two carry views."""

    width: int
    digits: tuple[int, ...]
    multiply_carries: tuple[int, ...]
    addition_carries: tuple[int, ...]
    active_multiply_carries: tuple[int, ...]
    next_parity: int

    def __post_init__(self) -> None:
        if (
            type(self.width) is not int
            or self.width <= 0
            or any(
                type(row) is not tuple or len(row) != self.width
                for row in (
                    self.digits,
                    self.multiply_carries,
                    self.addition_carries,
                    self.active_multiply_carries,
                )
            )
            or any(type(bit) is not int or bit not in (0, 1) for bit in self.digits)
            or any(
                type(carry) is not int or carry not in (0, 1, 2)
                for carry in self.multiply_carries
            )
            or any(
                type(carry) is not int or carry not in (0, 1)
                for carry in self.addition_carries
            )
            or any(
                type(carry) is not int or carry not in (0, 1, 2)
                for carry in self.active_multiply_carries
            )
            or type(self.next_parity) is not int
            or self.next_parity not in (0, 1)
            or self.next_parity != self.digits[0]
            or self.active_multiply_carries
            != tuple(self.next_parity * carry for carry in self.multiply_carries)
        ):
            raise ValueError("diagonal field has malformed bounded carry rows")


@dataclass(frozen=True, slots=True)
class CollatzWeightedLaurentDefect:
    """Aggregate exact A/B normalization defect and sparse moving-cut views.

    This is the Laurent defect of the complete ledgers, not the sum of the
    historical per-step carry words.
    """

    moving_cut: int
    endpoint_defect: tuple[int, ...]
    carry_coefficients: tuple[int, ...]
    symmetric: tuple[tuple[int, int], ...]
    antisymmetric: tuple[tuple[int, int], ...]

    def __post_init__(self) -> None:
        if (
            type(self.moving_cut) is not int
            or self.moving_cut < 0
            or type(self.endpoint_defect) is not tuple
            or any(type(value) is not int for value in self.endpoint_defect)
            or type(self.carry_coefficients) is not tuple
            or any(type(value) is not int for value in self.carry_coefficients)
            or type(self.symmetric) is not tuple
            or type(self.antisymmetric) is not tuple
            or any(
                type(row) is not tuple
                or len(row) != 2
                or type(row[0]) is not int
                or type(row[1]) is not int
                or row[1] == 0
                for row in (*self.symmetric, *self.antisymmetric)
            )
            or tuple(sorted(self.symmetric)) != self.symmetric
            or tuple(sorted(self.antisymmetric)) != self.antisymmetric
            or any(
                before[0] >= after[0]
                for rows in (self.symmetric, self.antisymmetric)
                for before, after in pairwise(rows)
            )
        ):
            raise ValueError("weighted Laurent defect has malformed coefficients")


@dataclass(frozen=True, slots=True)
class _DiagonalSeamCertificate:
    """Immutable occurrence evidence pinned to one live image generation."""

    workspace_owner: object
    workspace_binding: tuple[object, ...]
    joint_payload: tuple[int, ...]
    action_coefficients: tuple[int, ...]
    source: int
    normalized_endpoint: int
    physical_endpoint: int
    physical_ticks: int
    normalized_steps: int
    odd_symbols: int
    phase: int
    issuer: object


@dataclass(frozen=True, slots=True, init=False)
class CollatzDiagonalSeam:
    """Lazy spatial view pinned to one authenticated joint run action."""

    _action: DyadicTerminalFieldAction = field(repr=False, compare=False)
    _joint_action: CollatzJointRunAction = field(repr=False, compare=False)
    _workspace_ref: ReferenceType[CollatzPhysicalImageWorkspace] = field(
        repr=False, compare=False
    )
    _issued_certificate: _DiagonalSeamCertificate = field(repr=False, compare=False)
    source: int
    normalized_endpoint: int
    physical_endpoint: int
    physical_ticks: int
    normalized_steps: int
    odd_symbols: int
    phase: int

    def __init__(self, *_args: object, **_kwargs: object) -> None:
        raise TypeError("diagonal seams must come from an admitted Collatz term")

    @classmethod
    def from_issued_joint(
        cls,
        workspace: CollatzPhysicalImageWorkspace,
    ) -> CollatzDiagonalSeam:
        from number_compiler.sequences.collatz.joint_temporal_action import (
            CollatzJointRunAction,
        )
        from number_compiler.sequences.collatz.physical_images import (
            CollatzPhysicalImageWorkspace,
        )

        if type(workspace) is not CollatzPhysicalImageWorkspace or workspace.closed:
            raise TypeError("diagonal seam requires its live source-image workspace")
        if not workspace.demand_configuration[1]:
            raise ValueError("diagonal seam requires a demanded joint action")
        action: CollatzJointRunAction
        if workspace.steps == 0:
            # A zero-span request has no execution port to look up. Its exact
            # source-bound identity is the mathematical empty action, anchored
            # to this live workspace's registered source and action handles.
            workspace.validate_source(workspace.root_source)
            workspace.validate_action(workspace.root_action)
            source = workspace.seed
            fields = DyadicTerminalFieldAction.identity()
            action = CollatzJointRunAction(
                source,
                source,
                source,
                0,
                0,
                0,
                0,
                fields,
            )
        else:
            candidate = workspace.joint_action
            if candidate is None:
                raise ValueError("diagonal seam requires the admitted joint run action")
            action = candidate
        if type(action) is not CollatzJointRunAction:
            raise ValueError("diagonal seam requires the admitted joint run action")
        if action.source != workspace.seed or action.physical_ticks != workspace.steps:
            raise ValueError("joint run action belongs to another source extent")
        if not action.fields.producer_issued:
            raise ValueError("joint run action lost its issued dyadic fields")
        result = object.__new__(cls)
        workspace_binding: tuple[object, ...] = (
            workspace.root_source,
            workspace.root_action,
            workspace.root_payload,
            workspace.demand_configuration,
        )
        joint_payload = action.root_port_payload()
        certificate = _DiagonalSeamCertificate(
            workspace.owner,
            workspace_binding,
            joint_payload,
            action.fields.coefficient_snapshot(),
            action.source,
            action.normalized_endpoint,
            action.endpoint,
            action.physical_ticks,
            action.normalized_steps,
            action.odd_symbols,
            action.phase,
            _DIAGONAL_SEAM_ISSUER,
        )
        values: tuple[object, ...] = (
            action.fields,
            action,
            ref(workspace),
            certificate,
            action.source,
            action.normalized_endpoint,
            action.endpoint,
            action.physical_ticks,
            action.normalized_steps,
            action.odd_symbols,
            action.phase,
        )
        for name, value in zip(
            (
                "_action",
                "_joint_action",
                "_workspace_ref",
                "_issued_certificate",
                "source",
                "normalized_endpoint",
                "physical_endpoint",
                "physical_ticks",
                "normalized_steps",
                "odd_symbols",
                "phase",
            ),
            values,
            strict=True,
        ):
            object.__setattr__(result, name, value)
        result.require_issued()
        return result

    def require_issued(self) -> None:
        from number_compiler.sequences.collatz.joint_temporal_action import (
            CollatzJointRunAction,
        )

        workspace = self._workspace_ref()
        certificate = self._issued_certificate
        if (
            type(certificate) is not _DiagonalSeamCertificate
            or certificate.issuer is not _DIAGONAL_SEAM_ISSUER
        ):
            raise ValueError("diagonal seam lost its issued certificate")
        workspace_is_live = False
        if (
            workspace is not None
            and not workspace.closed
            and workspace.owner is certificate.workspace_owner
            and certificate.workspace_binding
            == (
                workspace.root_source,
                workspace.root_action,
                workspace.root_payload,
                workspace.demand_configuration,
            )
            and workspace.demand_configuration[1]
        ):
            if self._joint_action.physical_ticks == 0:
                try:
                    workspace.validate_source(workspace.root_source)
                    workspace.validate_action(workspace.root_action)
                    workspace_is_live = (
                        workspace.steps == 0
                        and workspace.seed == self.source
                        and self._joint_action.source == self.source
                        and self._joint_action.endpoint == self.source
                        and self._joint_action.normalized_endpoint == self.source
                        and self._joint_action.fields.coefficient_snapshot()
                        == (0, 1, 0, 0, 0, 0, 0)
                    )
                except (ArithmeticError, TypeError, ValueError):
                    workspace_is_live = False
            else:
                workspace_is_live = workspace.joint_action is self._joint_action
        if (
            not workspace_is_live
            or type(self._joint_action) is not CollatzJointRunAction
            or self._joint_action.root_port_payload() != certificate.joint_payload
            or type(self._action) is not DyadicTerminalFieldAction
            or not self._action.producer_issued
            or self._action.coefficient_snapshot() != certificate.action_coefficients
            or self._action.coefficient_snapshot()
            != (self.normalized_steps, *certificate.joint_payload[7:])
            or type(self.source) is not int
            or self.source <= 0
            or type(self.normalized_endpoint) is not int
            or self.normalized_endpoint <= 0
            or type(self.physical_endpoint) is not int
            or self.physical_endpoint <= 0
            or type(self.physical_ticks) is not int
            or self.physical_ticks < 0
            or type(self.normalized_steps) is not int
            or self.normalized_steps != self._action.steps
            or type(self.odd_symbols) is not int
            or not 0 <= self.odd_symbols <= self.normalized_steps
            or type(self.phase) is not int
            or self.phase not in (0, 1)
            or certificate.joint_payload
            != (
                self.source,
                self.physical_endpoint,
                self.normalized_endpoint,
                self.physical_ticks,
                self.normalized_steps,
                self.odd_symbols,
                self.phase,
                *self._action.coefficient_snapshot()[1:],
            )
        ):
            raise ValueError("diagonal seam has stale or altered source authority")

    @property
    def endpoint(self) -> int:
        self.require_issued()
        return self.physical_endpoint

    @property
    def required_field_width(self) -> int:
        """A conservative endpoint field width from retained endpoint metadata."""
        self.require_issued()
        return self.normalized_endpoint.bit_length() + 2

    @property
    def required_macro_width(self) -> int:
        """A safe full-width bound without forming ``gain * source``."""
        self.require_issued()
        return max(
            self.source.bit_length() + self._action.gain.bit_length() + 1,
            self._action.offset.bit_length(),
            self.normalized_steps + self.normalized_endpoint.bit_length(),
        )

    def endpoint_residue(
        self,
        bits: int,
        *,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> int:
        self.require_issued()
        bits = require_integer(bits, "endpoint suffix bits", 0)
        _validate_query_width(max_width)
        if bits > max_width:
            raise ValueError("endpoint suffix exceeds its requested width")
        if bits == 0:
            return 0
        span = self._action.steps + bits
        _validate_event_span(span)
        reserve_bits(
            8
            * (
                self.source.bit_length()
                + self._action.gain.bit_length()
                + self._action.offset.bit_length()
                + 3 * span
                + 64
            )
        )
        return self._endpoint_residue_reserved(bits)

    def phase_fraction(
        self,
        offset: int,
        *,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> Fraction:
        self.require_issued()
        offset = require_integer(offset, "diagonal offset")
        _validate_query_width(max_width)
        if offset <= 0:
            return Fraction(0)
        if offset > max_width:
            raise ValueError("diagonal phase fraction exceeds its requested width")
        return Fraction(
            self.endpoint_residue(
                offset, reserve_bits=reserve_bits, max_width=max_width
            ),
            1 << offset,
        )

    def field(
        self,
        width: int,
        *,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> CollatzDiagonalField:
        """Materialize bounded endpoint digits and carry columns on demand."""
        self.require_issued()
        width = require_integer(width, "diagonal field width", 1)
        _validate_query_width(max_width)
        if width > max_width:
            raise ValueError("diagonal field exceeds its requested width")
        _validate_event_span(self._action.steps + width)
        reserve_bits(
            8
            * (
                self.source.bit_length()
                + self._action.gain.bit_length()
                + self._action.offset.bit_length()
                + 3 * (self._action.steps + width)
                + 64 * width
                + 96
            )
        )
        value = self._endpoint_residue_reserved(width)
        digits = tuple((value >> position) & 1 for position in range(width))
        multiply_coefficients = tuple(
            3 * bit + int(position == 0) for position, bit in enumerate(digits)
        )
        _, multiply_boundaries = linear_normalization_fields(
            multiply_coefficients, base=2
        )
        addition_coefficients: list[int] = []
        increment_carry = 1
        for position, bit in enumerate(digits):
            plus_bit = (bit + increment_carry) & 1
            increment_carry = (bit + increment_carry) >> 1
            shifted_source_bit = 0 if position == 0 else digits[position - 1]
            addition_coefficients.append(shifted_source_bit + plus_bit)
        _, addition_boundaries = linear_normalization_fields(
            addition_coefficients, base=2
        )
        carries = multiply_boundaries[1:]
        additions = addition_boundaries[1:]
        parity = digits[0]
        return CollatzDiagonalField(
            width,
            digits,
            carries,
            additions,
            tuple(parity * carry for carry in carries),
            parity,
        )

    def prospective_multiply_carry(
        self,
        boundary: int,
        *,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> int:
        boundary = require_integer(boundary, "multiplication boundary", 1)
        _validate_query_width(max_width)
        if boundary > max_width:
            raise ValueError("multiplication boundary exceeds its requested width")
        low = self.endpoint_residue(
            boundary, reserve_bits=reserve_bits, max_width=max_width
        )
        return (3 * low + 1) >> boundary

    def prospective_addition_carry(
        self,
        boundary: int,
        *,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> int:
        boundary = require_integer(boundary, "addition boundary", 1)
        _validate_query_width(max_width)
        if boundary > max_width:
            raise ValueError("addition boundary exceeds its requested width")
        low = self.endpoint_residue(
            boundary, reserve_bits=reserve_bits, max_width=max_width
        )
        power = 1 << boundary
        carry = (3 * low + 1) // power - (2 * low) // power - (low + 1) // power
        if carry not in (0, 1):
            raise AssertionError("Collatz addition carry must be binary")
        return carry

    def macro_carries(
        self,
        width: int,
        *,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> tuple[int, ...]:
        """Return bounded carries for the raw affine numerator columns."""
        self.require_issued()
        width = require_integer(width, "macro carry width", 0)
        _validate_query_width(max_width)
        if width > max_width:
            raise ValueError("macro carry width exceeds its requested width")
        reserve_bits(
            8
            * (
                self.source.bit_length()
                + self._action.gain.bit_length()
                + self._action.offset.bit_length()
                + width * (self._action.gain.bit_length() + 64)
                + 64
            )
        )
        coefficients = tuple(
            self._action.gain * ((self.source >> position) & 1)
            + ((self._action.offset >> position) & 1)
            for position in range(width)
        )
        _, carry_boundaries = linear_normalization_fields(coefficients, base=2)
        return carry_boundaries[1:]

    def macro_laurent_defect(
        self,
        width: int,
        *,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> tuple[int, ...]:
        carries = self.macro_carries(
            width, reserve_bits=reserve_bits, max_width=max_width
        )
        return self.macro_laurent_defect_from_carries(carries, max_width=max_width)

    def macro_laurent_defect_from_carries(
        self,
        carries: tuple[int, ...],
        *,
        max_width: int,
    ) -> tuple[int, ...]:
        """Trim a previously produced carry row without recomputing columns."""
        self.require_issued()
        _validate_query_width(max_width)
        if (
            type(carries) is not tuple
            or len(carries) > max_width
            or any(type(carry) is not int or carry < 0 for carry in carries)
        ):
            raise ValueError("macro carry row is malformed or over budget")
        last = len(carries)
        while last and carries[last - 1] == 0:
            last -= 1
        # The published identity is ``z^k P_endpoint - N = (z - 2) Γ``.
        # For least-significant-first coefficients, the usual outgoing carry
        # C[j+1] is exactly Γ[j].
        return carries[:last]

    def double_accumulators(
        self,
        *,
        phase: int,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> CollatzDoubleWeight:
        self.require_issued()
        phase = require_integer(phase, "physical half-step phase", 0, 1)
        if phase != self.phase:
            raise ValueError("accumulator phase differs from the issued run")
        _validate_query_width(max_width)
        _validate_event_span(self._action.steps)
        reserve_bits(
            8
            * (
                self.source.bit_length()
                + self._action.gain.bit_length()
                + self._action.offset.bit_length()
                + self._action.sum_gain.bit_length()
                + self._action.sum_offset.bit_length()
                + 4 * self._action.steps
                + 128
            )
        )
        upper_result_bits = self.source.bit_length() + 2 * self.physical_ticks + 8
        if upper_result_bits > max_width:
            raise ValueError("double accumulators exceed their requested width")
        from number_compiler.sequences.collatz.weighted_right_congruence import (
            exact_double_weight,
        )

        result = exact_double_weight(self._action, self.source, phase=phase)
        if (
            result.normalized_endpoint != self.normalized_endpoint
            or result.physical_endpoint != self.physical_endpoint
        ):
            raise ValueError("diagonal accumulator differs from the issued endpoint")
        return result

    def weighted_laurent_defect(
        self,
        *,
        moving_cut: int,
        reserve_bits: Callable[[int], None],
        max_width: int,
    ) -> CollatzWeightedLaurentDefect:
        """Derive the aggregate A/B Laurent defect without a historical replay."""
        self.require_issued()
        moving_cut = require_integer(moving_cut, "Laurent moving cut", 0)
        _validate_query_width(max_width)
        if moving_cut > max_width:
            raise ValueError("Laurent moving cut exceeds its requested width")
        size_bound = self.source.bit_length() + 2 * self.physical_ticks + 8
        if size_bound > max_width:
            raise ValueError("aggregate Laurent support exceeds its requested width")
        reserve_bits(
            8
            * (
                self.source.bit_length()
                + self._action.gain.bit_length()
                + self._action.sum_gain.bit_length()
                + 6 * size_bound
                + 128
            )
        )
        weight = self.double_accumulators(
            phase=self.phase,
            reserve_bits=reserve_bits,
            max_width=max_width,
        )
        size = max(
            self.source.bit_length(),
            weight.physical_endpoint.bit_length(),
            weight.added.bit_length(),
            weight.subtracted.bit_length(),
        )
        if size > max_width:
            raise ValueError("aggregate Laurent support exceeds its requested width")
        reserve_bits(
            8
            * (
                self.source.bit_length()
                + weight.physical_endpoint.bit_length()
                + weight.added.bit_length()
                + weight.subtracted.bit_length()
                + 64 * size
                + 128
            )
        )
        defect = tuple(
            ((weight.physical_endpoint >> position) & 1)
            - ((self.source >> position) & 1)
            - ((weight.added >> position) & 1)
            + ((weight.subtracted >> position) & 1)
            for position in range(size)
        )
        from number_compiler.arithmetic.polynomials.polynomial import (
            laurent_reflection_projections,
            polynomial_divide_exact,
        )

        quotient = polynomial_divide_exact(defect, (-2, 1))
        if quotient is None:
            raise AssertionError("aggregate A/B Laurent defect is not divisible by z-2")
        symmetric, antisymmetric = laurent_reflection_projections(quotient, moving_cut)
        return CollatzWeightedLaurentDefect(
            moving_cut, defect, quotient, symmetric, antisymmetric
        )

    def _endpoint_residue_reserved(self, bits: int) -> int:
        span = self._action.steps + bits
        modulus = 1 << span
        numerator = (
            self._action.gain * (self.source % modulus) + self._action.offset
        ) % modulus
        divisor = 1 << self._action.steps
        if numerator % divisor:
            raise ValueError("diagonal seam lost its exact source cylinder")
        return numerator >> self._action.steps


def _validate_query_width(max_width: int) -> None:
    require_integer(max_width, "maximum diagonal width", 1, 4096)


def _validate_event_span(span: int) -> None:
    if type(span) is not int or span < 0 or span > 2 * _MAX_DIAGONAL_QUERY_EVENTS:
        raise ValueError("diagonal action exceeds the bounded event horizon")


__all__ = [
    "CollatzDiagonalField",
    "CollatzDiagonalSeam",
    "CollatzWeightedLaurentDefect",
]
