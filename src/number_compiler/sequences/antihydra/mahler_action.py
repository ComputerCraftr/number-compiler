"""Finite Mahler safety pulled from Antihydra's admitted dyadic source image.

The associated min-plus action is a demanded projection of the same composed
source cylinder that supplies the arithmetic endpoint and ledger safety. Its
threshold is a consumer; neither it nor the ledger authorizes another source.
"""

from __future__ import annotations

from dataclasses import asdict
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
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
from number_compiler.hashlife.execution.source_image_inventory import SourceImageDemand
from number_compiler.hashlife.execution.source_image_seals import typed_payload_equal
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.runtime import authenticated_arithmetic_result

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.mahler_joint_future import (
        MahlerJointInteriorWindow,
    )
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
    include_source_cylinder: bool = False,
    window_memo: OwnedMemo[tuple[object, ...], MahlerJointInteriorWindow] | None = None,
) -> dict[str, object]:
    if result.returns == 0 and semantic != SaturatingAffineAction.identity():
        raise ValueError(
            "zero-extent Mahler source must have the uncapped identity action"
        )
    if type(include_source_cylinder) is not bool:
        raise TypeError("two-sided source-cylinder demand must be Boolean")
    if include_source_cylinder and not include_radix_ports:
        raise ValueError("source cylinders require the detailed Mahler port demand")
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
    workspace = result.source_term.arithmetic_workspace
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
    odd_macro_packet: dict[str, object] | None = None
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
            base=6,
            places=4,
            ledger=result.ledger,
            source=workspace.seed - 1,
            endpoint_h=result.h,
            binary_places=16,
            decimal_places=4,
            _workspace=workspace,
            _workspace_transfer=transfer,
            _window_memo=window_memo,
        )
        joint_successor = demanded_tripling.pop("joint_source_successor", None)
    else:
        joint_successor = None
    if include_radix_ports:
        # The admitted arithmetic image supplies this exact endpoint. A point
        # observer is issued only when its centered value is a positive odd
        # source; it never discovers another source window or execution step.
        centered_source = result.h - 1
        if centered_source > 0 and centered_source & 1:
            odd_index = result.odd_events
            if (
                workspace.seed != 8
                or odd_index < 0
                or result.balance != 3 * odd_index - result.returns
                or (
                    result.returns == 0
                    and (centered_source != 7 or result.balance != 0)
                )
            ):
                raise ValueError("Mahler pointed odd-event source lost its authority")
            from number_compiler.sequences.antihydra.mahler_odd_macro import (
                odd_seam_pointwise_packet,
                odd_seam_step,
            )

            seam = odd_seam_step(
                centered_source, odd_index, result.returns, result.balance
            )
            if result.returns == 0:
                # Retain the previously published, fully detailed root packet.
                from number_compiler.sequences.antihydra.mahler_odd_macro import (
                    odd_seam_packet,
                )

                odd_macro_packet = odd_seam_packet(
                    seam,
                    bits=16,
                    decimal_places=4,
                    walsh=False,
                    include_mixed_ring=True,
                )
            else:
                odd_macro_packet = odd_seam_pointwise_packet(seam, places=4)
    source_cylinder_packet: dict[str, object] | None = None
    if include_source_cylinder:
        centered_source = result.h - 1
        if centered_source <= 0 or not centered_source & 1:
            source_cylinder_packet = {
                "status": "unavailable",
                "reason": "current centered source is not positive and odd",
            }
        else:
            from number_compiler.sequences.antihydra.mahler_two_sided_cylinder import (
                MahlerGuardedSourceFiber,
                MahlerTwoSidedCylinder,
            )

            cylinder = MahlerTwoSidedCylinder.from_pointed_source(
                centered_source,
                binary_bits=8,
                five_places=1,
                leading_bits=min(8, centered_source.bit_length()),
                ledger=result.ledger,
            )
            initial_fiber = MahlerGuardedSourceFiber(
                cylinder, HalfOpenInterval(), result.balance
            )
            powered, terminal_fiber, accepted_events, stop_reason = (
                initial_fiber.forced_future(
                    max_events=16,
                    max_extent=128,
                    ledger=result.ledger,
                )
            )
            source_cylinder_packet = {
                "initial": cylinder.summary(
                    upper_bits=min(8, centered_source.bit_length()),
                    low_bits=8,
                    five_places=1,
                    ledger=result.ledger,
                ),
                "accepted_odd_events": accepted_events,
                "accepted_extent": powered.extent,
                "stop_reason": stop_reason,
                "terminal": {
                    "integer_fiber": terminal_fiber.integers.summary(
                        upper_bits=min(8, terminal_fiber.integers.first.bit_length()),
                        low_bits=8,
                        five_places=1,
                        ledger=result.ledger,
                    ),
                    "fractional_guard": {
                        "lower": rational_packet(terminal_fiber.fractional_guard.lower),
                        "upper": rational_packet(terminal_fiber.fractional_guard.upper),
                        "empty": terminal_fiber.fractional_guard.empty,
                    },
                    "ledger_balance": terminal_fiber.ledger_balance,
                },
                "composed_action": {
                    "source_residue": powered.source_residue,
                    "source_modulus": powered.source_modulus,
                    "gain": powered.joint.gain,
                    "innovation": powered.joint.innovation,
                    "guard": {
                        "lower": rational_packet(powered.joint.guard.lower),
                        "upper": rational_packet(powered.joint.guard.upper),
                        "empty": powered.joint.guard.empty,
                    },
                    "ledger_delta": powered.delta,
                    "ledger_minimum": powered.minimum,
                },
                "scope": (
                    "finite source/fraction/ledger product; no all-time or "
                    "Antihydra future-safety claim"
                ),
            }
    with GrowthArithmeticEvaluator(result.ledger) as radial_evaluator:
        radial_packet = asdict(radial_clock.leading_binary(radial_evaluator))
        growth_packet = asdict(
            homogeneous_growth_packet(
                radial_clock.scale, result.ledger, evaluator=radial_evaluator
            )
        )
        if include_radix_ports:
            source_operand_bits = (
                transfer.upper.bit_length()
                + workspace.seed.bit_length()
                + abs(transfer.offset).bit_length()
                + transfer.lower.bit_length()
                + result.h.bit_length()
            )
            result.ledger.bump(
                _antihydra_keys.MAHLER_RADIAL_AFFINE_OPERAND_BITS,
                source_operand_bits,
            )
            work_units = max(
                1, transfer.upper.bit_length() * workspace.seed.bit_length()
            )
            with radial_evaluator.charge_work(
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
            {"source_bound_joint_successor": joint_successor}
            if joint_successor is not None
            else {}
        ),
        **(
            {"source_bound_odd_to_odd": odd_macro_packet}
            if odd_macro_packet is not None
            else {}
        ),
        **(
            {"source_cylinder": source_cylinder_packet}
            if source_cylinder_packet is not None
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
        workspace = result.source_term.arithmetic_workspace
        if type(workspace) is not AntihydraArithmeticImageWorkspace:
            raise ValueError("Mahler source lost its admitted arithmetic image")
        self.result = result
        self.source_workspace = workspace
        self._window_owner: int | None = None
        self._window_memo: (
            OwnedMemo[tuple[object, ...], MahlerJointInteriorWindow] | None
        ) = None
        self._window_contract_registered = False

    @property
    def window_memo_container(self) -> object | None:
        """Exact registered container for a fresh audit, including closed state."""
        memo = self._window_memo
        return None if memo is None else memo.audit_snapshot().container

    @property
    def window_memo_owner(self) -> int | None:
        """Registered owner for the optional precision memo."""
        return self._window_owner

    @property
    def window_contract_registered(self) -> bool:
        """Whether the live memo is bound into the source payload contract."""
        return self._window_contract_registered

    def mark_window_contract_registered(self) -> None:
        """Record that the exact current memo has a refreshed source contract."""
        if self._window_memo is None:
            raise ValueError("cannot register a Mahler contract without its memo")
        self._window_contract_registered = True

    def window_memo_entries(
        self,
    ) -> tuple[tuple[tuple[object, ...], MahlerJointInteriorWindow], ...]:
        """Return the bounded entries needed by the read-only payload auditor."""
        memo = self._window_memo
        return () if memo is None else tuple(memo.items())

    def _validate_binding(self, result: ArithmeticResult) -> None:
        if (
            result is not self.result
            or type(self.source_workspace) is not AntihydraArithmeticImageWorkspace
            or self.source_workspace is not result.source_term.arithmetic_workspace
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
        memo = self._window_memo
        owner = self._window_owner
        if memo is None:
            if owner is not None:
                raise ValueError("Mahler window owner lost its memo")
        elif (
            type(owner) is not int
            or type(memo.owner) is not int
            or memo.ledger is not result.ledger
            or memo.owner != owner
            or memo.nodes_per_entry != 64
            or result.ledger.registered_container(owner)
            is not memo.audit_snapshot().container
        ):
            raise ValueError("Mahler precision memo is detached from its owner")
        if memo is not None:
            self._validate_window_payloads(result, memo)

    def _validate_window_payloads(
        self,
        result: ArithmeticResult,
        memo: OwnedMemo[tuple[object, ...], MahlerJointInteriorWindow],
    ) -> None:
        """Audit the one demanded window against the admitted root source."""
        from number_compiler.sequences.antihydra.mahler_joint_future import (
            MAHLER_JOINT_FUTURE_KIND,
            MahlerJointInteriorWindow,
        )

        if len(memo) > 1:
            raise ValueError("Mahler precision memo exceeded its one-entry bound")
        if not memo:
            return
        from number_compiler.arithmetic.fields.consumer_pullback import (
            ExactRational as Q,
        )
        from number_compiler.arithmetic.fields.consumer_pullback import (
            HalfOpenInterval,
        )
        from number_compiler.sequences.antihydra.mahler_source_actions import (
            MahlerSourceBoundSafetyAction,
        )

        transfer = self.source_workspace.image_node(
            self.source_workspace.root_payload
        ).summary.transfer
        extent = self.source_workspace.returns
        modulus = 1 << extent
        gain = transfer.upper
        innovation = gain + transfer.offset - modulus
        offset_hat = -12 * innovation
        safety = MahlerSourceBoundSafetyAction(
            extent,
            offset_hat,
            6 if extent == 1 else 6 * gain + offset_hat,
        )
        guard = (
            HalfOpenInterval()
            if extent == 0
            else HalfOpenInterval(Q(1, 3), Q(1, 2))
            if extent == 1
            else HalfOpenInterval(Q(0), Q(0))
        )
        semantic_id = (
            MAHLER_JOINT_FUTURE_KIND,
            extent,
            7 % modulus,
            innovation,
            guard,
            safety,
            gain,
        )
        for key, window in memo.items():
            if type(key) is not tuple or len(key) != 4:
                raise ValueError("Mahler window memo key has another shape")
            if type(window) is not MahlerJointInteriorWindow:
                raise ValueError("Mahler precision memo contains another payload")
            window.verify_issued()
            if (
                not is_exact_object_tuple(key[0])
                or not typed_payload_equal(key[0], semantic_id)
                or key[1] != 7
                or key[2] != window.bits
                or key[3] != window.decimal_places
                or type(key[1]) is not int
                or type(key[2]) is not int
                or type(key[3]) is not int
                or type(window.bits) is not int
                or type(window.decimal_places) is not int
                or window.source != 7
                or window.source_endpoint != result.h - 1
            ):
                raise ValueError("Mahler interior window lost its source payload")

    def _demand_window_memo(
        self, result: ArithmeticResult
    ) -> OwnedMemo[tuple[object, ...], MahlerJointInteriorWindow]:
        from number_compiler.sequences.antihydra.mahler_joint_future import (
            MahlerJointInteriorWindow,
        )

        if (
            result is not self.result
            or self.source_workspace is not result.source_term.arithmetic_workspace
            or self.source_workspace.ledger is not result.ledger
        ):
            raise ValueError("Mahler window memo belongs to another source")
        memo = self._window_memo
        if memo is None:
            owner = result.ledger.register(
                f"mahler-joint-window-{len(result.ledger.inventory())}",
                "query_memo",
            )
            memo = OwnedMemo[tuple[object, ...], MahlerJointInteriorWindow](
                result.ledger,
                owner,
                nodes_per_entry=64,
                evictable=True,
            )
            self._window_owner = owner
            self._window_memo = memo
        elif (
            self._window_owner != memo.owner
            or type(memo.owner) is not int
            or memo.ledger is not result.ledger
            or result.ledger.registered_container(memo.owner)
            is not memo.audit_snapshot().container
        ):
            raise ValueError("Mahler precision memo has another source owner")
        return memo

    def dispose(self) -> None:
        memo = self._window_memo
        self._window_memo = None
        self._window_owner = None
        self._window_contract_registered = False
        if memo is not None:
            memo.dispose()

    def packet(
        self,
        result: ArithmeticResult,
        *,
        include_radix_ports: bool = False,
        include_source_cylinder: bool = False,
    ) -> dict[str, object]:
        result.require_source()
        return self.packet_after_source_validation(
            result,
            include_radix_ports=include_radix_ports,
            include_source_cylinder=include_source_cylinder,
        )

    def packet_after_source_validation(
        self,
        result: ArithmeticResult,
        *,
        include_radix_ports: bool = False,
        include_source_cylinder: bool = False,
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
            include_source_cylinder=include_source_cylinder,
            window_memo=(
                self._demand_window_memo(result)
                if include_radix_ports and result.returns > 0
                else None
            ),
        )


def associated_action(
    result: Run | ArithmeticResult,
    *,
    include_radix_ports: bool = False,
    include_source_cylinder: bool = False,
) -> dict[str, object]:
    if type(include_radix_ports) is not bool:
        raise TypeError("radix-port demand must be Boolean")
    if type(include_source_cylinder) is not bool:
        raise TypeError("two-sided source-cylinder demand must be Boolean")
    if include_source_cylinder and not include_radix_ports:
        raise ValueError("source cylinders require the detailed Mahler port demand")
    arithmetic = authenticated_arithmetic_result(result)
    source_binding = result.source_binding
    workspace = arithmetic.source_term.mahler_workspace
    created_workspace = workspace is None
    if workspace is None:
        workspace = MahlerWorkspace(arithmetic)
    memo_before = workspace.window_memo_container
    try:
        packet = workspace.packet_after_source_validation(
            arithmetic,
            include_radix_ports=include_radix_ports,
            include_source_cylinder=include_source_cylinder,
        )
        if created_workspace:
            arithmetic.source_term.mahler_workspace = workspace
        if (
            workspace.window_memo_container is not None
            and not workspace.window_contract_registered
        ):
            from number_compiler.sequences.antihydra.payload_audit import (
                refresh_antihydra_payload_contract,
            )

            refresh_antihydra_payload_contract(arithmetic.source_term)
            workspace.mark_window_contract_registered()
    except BaseException:
        # A failed first memo publication must not leave an existing source
        # workspace holding a store that the restored pre-memo contract does
        # not own.  Preserve an older memo if this was a repeat demand.
        if memo_before is None and workspace.window_memo_container is not None:
            workspace.dispose()
        if created_workspace:
            arithmetic.source_term.mahler_workspace = None
        raise
    packet["source_binding"] = source_binding
    return packet
