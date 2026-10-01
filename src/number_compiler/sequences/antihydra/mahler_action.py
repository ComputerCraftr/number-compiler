"""Finite Mahler safety pulled from Antihydra's admitted dyadic source image.

The associated min-plus action is a demanded projection of the same composed
source cylinder that supplies the arithmetic endpoint and ledger safety. Its
threshold is a consumer; neither it nor the ledger authorizes another source.
"""

from __future__ import annotations

from dataclasses import asdict
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    GuardedAffineAction,
    HalfOpenInterval,
    SaturatingAffineAction,
    ThresholdDemand,
)
from number_compiler.arithmetic.fields.homogeneous_growth import HomogeneousGrowthScale
from number_compiler.arithmetic.fields.mechanical_readout import (
    homogeneous_growth_packet,
)
from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.runtime import authenticated_arithmetic_result

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.runtime import ArithmeticResult, Run


_MAHLER_DEMAND = SourceImageDemand("mahler-associated-action")


def rational_packet(value: ExactRational | None) -> dict[str, int] | None:
    if value is None:
        return None
    return {"numerator": value.numerator, "denominator": value.denominator}


def _action_packet(
    result: ArithmeticResult,
    semantic: SaturatingAffineAction,
    first_failure: int | None,
) -> dict[str, object]:
    # The authenticated centered source is 7, whose first two bits are 11.
    # Their exact theta guards are [2/3,1) then empty. The root chart uses
    # r^2=theta=2t, while the existing margin action has offset -3*C.
    root_offset = ExactRational(2, 3) * semantic.offset
    root = GuardedAffineAction(
        SaturatingAffineAction(semantic.scale, root_offset),
        HalfOpenInterval(
            ExactRational(0) if result.returns != 1 else ExactRational(2, 3),
            ExactRational(1) if result.returns < 2 else ExactRational(0),
        ),
    )
    result.ledger.bump("mahler_root_shell_projections")
    result.ledger.bump(
        "mahler_root_shell_operand_bits",
        sum(
            abs(value.numerator).bit_length() + value.denominator.bit_length()
            for value in (
                root.action.scale,
                root_offset,
                root.domain.lower,
                root.domain.upper,
            )
        ),
    )
    workspace = result._term.arithmetic_workspace
    if type(workspace) is not AntihydraArithmeticImageWorkspace:
        raise ValueError("Mahler residual lost its admitted arithmetic image")
    # The scheduler projection has already authenticated the complete source
    # image and read its saturated summary.  Serialize the same published
    # transfer directly; a second aggregate projection duplicates work and
    # cannot strengthen the source binding checked at this demand boundary.
    transfer = workspace.summary().transfer
    carry = transfer.upper + transfer.offset - transfer.lower
    result.ledger.bump("mahler_temporal_residual_projections")
    result.ledger.bump(
        "mahler_temporal_residual_operand_bits",
        transfer.upper.bit_length()
        + transfer.lower.bit_length()
        + abs(transfer.offset).bit_length()
        + carry.bit_length(),
    )
    # The centered source and the real w=4t action consume this identical carry.
    # The admitted public source is D=7. Its 11 prefix makes the real domain
    # empty at return two, independently of the Antihydra ledger.
    residual = {
        "Q": result.returns,
        "C": carry,
        "R": 7 if result.returns >= 3 else 7 % (1 << result.returns),
        "source_modulus_exponent": result.returns,
        "real_coordinate": "w=4*fractional_offset",
        "rho": rational_packet(ExactRational(transfer.lower, transfer.upper)),
        "h": rational_packet(ExactRational(4 * carry, transfer.upper)),
        "L": rational_packet(ExactRational(2) * root.domain.lower),
        "U": rational_packet(ExactRational(2) * root.domain.upper),
        "delta": result.balance,
        "minimum": result.minimum,
    }
    demand = semantic.pullback(ThresholdDemand())
    return {
        "source_binding": result.source_binding,
        "extent": result.returns,
        "homogeneous_growth": asdict(
            homogeneous_growth_packet(
                HomogeneousGrowthScale(result.returns, result.returns), result.ledger
            )
        ),
        "bit_convention": "parity_of_centered_D_equals_a_minus_one",
        "scale": rational_packet(semantic.scale),
        "offset": rational_packet(semantic.offset),
        "cap": rational_packet(semantic.cap),
        "initial_margin": "positive_infinity",
        "pulled_threshold": {
            "possible": demand.possible,
            "strict": demand.strict,
            "threshold": rational_packet(demand.threshold),
        },
        "first_failure": first_failure,
        "first_failure_index_unit": "one_based_macro_return",
        "predicate": "Mahler_strict_margin_positivity",
        "temporal_run_residual": residual,
        "root_shell": {
            "coordinate": "r_squared=theta=2*fractional_offset",
            "radicand_scale": rational_packet(root.action.scale),
            "radicand_offset": rational_packet(root_offset),
            "guard_squared": {
                "lower": rational_packet(root.domain.lower),
                "upper": rational_packet(root.domain.upper),
                "lower_closed": True,
                "upper_closed": False,
                "empty": root.domain.empty,
            },
        },
        "all_time_claim": False,
    }


class MahlerWorkspace:
    """Demand one finite consumer from the source scheduler's published image."""

    def __init__(self, result: ArithmeticResult) -> None:
        workspace = result._term.arithmetic_workspace
        if type(workspace) is not AntihydraArithmeticImageWorkspace:
            raise ValueError("Mahler source lost its admitted arithmetic image")
        self.result = result
        self.source_workspace = workspace

    def _validate_binding(self, result: ArithmeticResult) -> None:
        if (
            result is not self.result
            or type(self.source_workspace) is not AntihydraArithmeticImageWorkspace
            or self.source_workspace is not result._term.arithmetic_workspace
            or self.source_workspace.ledger is not result.ledger
        ):
            raise ValueError("Mahler consumer belongs to another source occurrence")
        result.ledger.bump(
            "mahler_source_validation_operand_bits", result.h.bit_length()
        )

    def validate(self, result: ArithmeticResult) -> None:
        self._validate_binding(result)
        self.source_workspace.validate()

    def packet(self, result: ArithmeticResult) -> dict[str, object]:
        result.require_source()
        return self._packet_authenticated(result)

    def _packet_authenticated(self, result: ArithmeticResult) -> dict[str, object]:
        # Call only after ``require_source`` (directly or through the public
        # source adapter), which validates the complete dyadic image once.
        self._validate_binding(result)
        workspace = self.source_workspace
        try:
            projected = workspace.scheduler.source_projection(
                workspace, workspace.root_image, _MAHLER_DEMAND
            ).value
        except BaseException:
            result.ledger.bump("mahler_associated_publication_rollbacks")
            raise
        if type(projected) is not SaturatingAffineAction:
            raise TypeError("Mahler source projected another action sort")
        # The authenticated h=8 source has centered prefix 11. The first
        # margin cap is 3/4 and the second is -3/8; later increasing actions
        # cannot repair that first failure.
        failure = 2 if result.returns >= 2 else None
        if (projected.cap is not None and projected.cap <= ExactRational(0)) != (
            failure is not None
        ):
            raise ArithmeticError("Mahler source projection lost first failure")
        result.ledger.bump("mahler_associated_action_demands")
        return _action_packet(result, projected, failure)


def associated_action(result: Run | ArithmeticResult) -> dict[str, object]:
    arithmetic = authenticated_arithmetic_result(result)
    source_binding = result.source_binding
    workspace = arithmetic._term.mahler_workspace
    if workspace is None:
        workspace = MahlerWorkspace(arithmetic)
        packet = workspace._packet_authenticated(arithmetic)
        arithmetic._term.mahler_workspace = workspace
    else:
        packet = workspace._packet_authenticated(arithmetic)
    packet["source_binding"] = source_binding
    return packet
