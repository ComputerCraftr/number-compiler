"""Finite Mahler safety pulled from Antihydra's admitted dyadic source image.

The associated min-plus action is a demanded projection of the same composed
source cylinder that supplies the arithmetic endpoint and ledger safety. Its
threshold is a consumer; neither it nor the ledger authorizes another source.
"""

from __future__ import annotations

from dataclasses import asdict
from typing import TYPE_CHECKING

from number_compiler.arithmetic.fields.affine_high_digits import (
    affine_high_digit_transport,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational,
    GuardedAffineAction,
    HalfOpenInterval,
    SaturatingAffineAction,
    ThresholdDemand,
)
from number_compiler.arithmetic.fields.homogeneous_growth import (
    GrowthArithmeticEvaluator,
    HomogeneousGrowthScale,
)
from number_compiler.arithmetic.fields.mechanical_readout import (
    homogeneous_growth_packet,
)
from number_compiler.arithmetic.fields.radial_sturmian import RadialSturmianClock
from number_compiler.hashlife.execution.source_bound_images import SourceImageDemand
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
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
    *,
    include_radix_ports: bool = False,
) -> dict[str, object]:
    if result.returns == 0 and semantic != SaturatingAffineAction.identity():
        raise ValueError(
            "zero-extent Mahler source must have the uncapped identity action"
        )
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
    result.ledger.bump(_antihydra_keys.MAHLER_ROOT_SHELL_PROJECTIONS)
    result.ledger.bump(
        _antihydra_keys.MAHLER_ROOT_SHELL_OPERAND_BITS,
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
    if semantic.scale != ExactRational(transfer.upper, transfer.lower):
        raise ValueError("Mahler radial scale is detached from the admitted source")
    carry = transfer.upper + transfer.offset - transfer.lower
    result.ledger.bump(_antihydra_keys.MAHLER_TEMPORAL_RESIDUAL_PROJECTIONS)
    result.ledger.bump(
        _antihydra_keys.MAHLER_TEMPORAL_RESIDUAL_OPERAND_BITS,
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
    # The return extent already supplies the ordinary radial clock. Construct
    # and cross-check the richer source-bound action only for an explicit port
    # consumer, so a warm associated-action read does not rebuild it eagerly.
    radial_clock = RadialSturmianClock(
        HomogeneousGrowthScale(result.returns, result.returns)
    )
    demanded_tripling: dict[str, object] | None = None
    radial_affine_packet: dict[str, object] | None = None
    if include_radix_ports and result.returns > 0:
        source_form = workspace.mahler_root_wire()
        if source_form is None:
            offset_hat = -12 * carry
            source_form = (
                result.returns,
                offset_hat,
                6 if result.returns == 1 else 6 * transfer.upper + offset_hat,
            )
        from number_compiler.sequences.antihydra.mahler_source_actions import (
            MahlerSourceBoundSafetyAction,
        )

        bound_action = MahlerSourceBoundSafetyAction(*source_form)
        cap_denominator = 1 << (result.returns + 2)
        bound_offset = ExactRational(bound_action.offset_hat, cap_denominator)
        bound_cap = (
            None
            if bound_action.cap_hat is None
            else ExactRational(bound_action.cap_hat, cap_denominator)
        )
        if (
            bound_action.extent != result.returns
            or semantic.scale != ExactRational(transfer.upper, transfer.lower)
            or semantic.offset != bound_offset
            or semantic.cap != bound_cap
        ):
            raise ValueError(
                "Mahler radial/cap action differs from its admitted source"
            )
        demanded_tripling = bound_action.demanded_tripling_ports(
            base=6, places=4, ledger=result.ledger
        )
    with GrowthArithmeticEvaluator(result.ledger) as radial_evaluator:
        radial_packet = asdict(radial_clock.leading_binary(radial_evaluator))
        growth_packet = asdict(
            homogeneous_growth_packet(
                radial_clock.scale, result.ledger, evaluator=radial_evaluator
            )
        )
        source_operand_bits = (
            transfer.upper.bit_length()
            + workspace.seed.bit_length()
            + abs(transfer.offset).bit_length()
            + transfer.lower.bit_length()
            + result.h.bit_length()
        )
        result.ledger.bump(
            _antihydra_keys.MAHLER_RADIAL_AFFINE_OPERAND_BITS, source_operand_bits
        )
        work_units = max(1, transfer.upper.bit_length() * workspace.seed.bit_length())
        with radial_evaluator._charge_work(
            work_units,
            0,
            source_operand_bits,
            storage_bits=2 * source_operand_bits + 16,
        ):
            if (
                workspace.seed != 8
                or transfer.lower.bit_length() != result.returns + 1
                or transfer.lower.bit_count() != 1
            ):
                raise ValueError("Mahler high-digit source/denominator is detached")
            numerator = transfer.upper * workspace.seed + transfer.offset
            endpoint, remainder = divmod(numerator, transfer.lower)
            if remainder or endpoint != result.h:
                raise ValueError("Mahler source transfer lost its integer endpoint")
            arithmetic_high = affine_high_digit_transport(
                result.h, transfer.offset, result.returns, 8
            )
            pure_h = (transfer.upper * workspace.seed) >> result.returns
            if result.h != pure_h + arithmetic_high.offset_quotient:
                raise ValueError("Mahler affine high-digit correction is detached")
    if include_radix_ports:
        radial_affine_packet = {
            "source": workspace.seed,
            "endpoint_h": result.h,
            "homogeneous_high_binary": arithmetic_high.homogeneous_high_binary,
            "endpoint_high_binary": arithmetic_high.endpoint_high_binary,
            "high_xor_binary": arithmetic_high.high_xor_binary,
            "high_digit_transport": asdict(arithmetic_high),
            "scope": (
                "authenticated finite h image; not the capped Mahler margin "
                "or a Turing-machine successor"
            ),
        }
    demand = semantic.pullback(ThresholdDemand())
    return {
        "source_binding": result.source_binding,
        "extent": result.returns,
        "homogeneous_growth": growth_packet,
        "radial_sturmian": radial_packet,
        **(
            {"source_bound_radix6_difference": demanded_tripling}
            if include_radix_ports
            else {}
        ),
        **(
            {"radial_affine_arithmetic": radial_affine_packet}
            if radial_affine_packet is not None
            else {}
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
            _antihydra_keys.MAHLER_SOURCE_VALIDATION_OPERAND_BITS,
            result.h.bit_length(),
        )

    def validate(self, result: ArithmeticResult) -> None:
        self._validate_binding(result)
        self.source_workspace.validate()

    def packet(
        self, result: ArithmeticResult, *, include_radix_ports: bool = False
    ) -> dict[str, object]:
        result.require_source()
        return self._packet_authenticated(
            result, include_radix_ports=include_radix_ports
        )

    def _packet_authenticated(
        self, result: ArithmeticResult, *, include_radix_ports: bool = False
    ) -> dict[str, object]:
        # Call only after ``require_source`` (directly or through the public
        # source adapter), which validates the complete dyadic image once.
        self._validate_binding(result)
        workspace = self.source_workspace
        projected: object
        try:
            if result.returns == 1:
                # Source validation above authenticates the pinned seed and
                # return extent. Its only centered bit is (8 - 1) mod 2 = 1,
                # so construct this leaf directly in the shared source-action
                # normal form instead of requesting a second projection.
                from number_compiler.sequences.antihydra.mahler_source_actions import (
                    MahlerSourceBoundSafetyAction,
                )

                if workspace.seed != 8 or workspace.returns != result.returns:
                    raise ValueError("Mahler one-bit leaf has another admitted source")
                first_bit = (workspace.seed - 1) & 1
                projected = MahlerSourceBoundSafetyAction.one_bit(first_bit).to_action()
            else:
                projected = workspace.scheduler.source_projection(
                    workspace, workspace.root_image, _MAHLER_DEMAND
                ).value
        except BaseException:
            result.ledger.bump(_antihydra_keys.MAHLER_ASSOCIATED_PUBLICATION_ROLLBACKS)
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
        result.ledger.bump(_antihydra_keys.MAHLER_ASSOCIATED_ACTION_DEMANDS)
        return _action_packet(
            result,
            projected,
            failure,
            include_radix_ports=include_radix_ports,
        )


def associated_action(
    result: Run | ArithmeticResult, *, include_radix_ports: bool = False
) -> dict[str, object]:
    if type(include_radix_ports) is not bool:
        raise TypeError("radix-port demand must be Boolean")
    arithmetic = authenticated_arithmetic_result(result)
    source_binding = result.source_binding
    workspace = arithmetic._term.mahler_workspace
    if workspace is None:
        workspace = MahlerWorkspace(arithmetic)
        packet = workspace._packet_authenticated(
            arithmetic, include_radix_ports=include_radix_ports
        )
        arithmetic._term.mahler_workspace = workspace
    else:
        packet = workspace._packet_authenticated(
            arithmetic, include_radix_ports=include_radix_ports
        )
    packet["source_binding"] = source_binding
    return packet
