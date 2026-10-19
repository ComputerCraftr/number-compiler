"""Antihydra's return law and physical projection of shared dyadic images.

Source admission, precision transport, composition, and failure descent belong
to the shared scheduler engine.  This adapter only supplies the arithmetic law
and converts demanded bounded leaves to the existing guarded roof consumer.
"""

from __future__ import annotations

from collections.abc import Callable, Hashable, Iterator
from typing import TYPE_CHECKING, Final

from number_compiler.arithmetic.fields.consumer_pullback import (
    compose_prefix_safety_values,
)
from number_compiler.arithmetic.fields.skew_transfer import (
    SkewTransfer,
    integer_dyadic_fiber_action,
)
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.hashlife.execution.dyadic_return_images import (
    DyadicImageSummary,
    DyadicReturnActionID,
    DyadicReturnImageID,
    DyadicReturnImageWorkspace,
    DyadicReturnLaw,
    DyadicReturnSourceID,
    DyadicReturnSupportID,
)
from number_compiler.hashlife.execution.dyadic_return_runs import (
    RunArithmeticWorkspace,
    publish_exact_run_candidate,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all, cleanup_on_error
from number_compiler.resources.metric_keys import antihydra as _antihydra_keys
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.antihydra.blocks import ArithmeticCylinder
from number_compiler.sequences.antihydra.mahler_odd_prefilter import (
    PREFILTER_BITS,
    might_have_odd_macro_low_suffix,
)
from number_compiler.sequences.antihydra.mahler_odd_source_transfer import (
    MahlerOddMacroSelection,
    select_source_certified_odd_macro,
)
from number_compiler.sequences.antihydra.mahler_source_actions import (
    MAX_MAHLER_SOURCE_EXTENT,
)

if TYPE_CHECKING:
    from number_compiler.sequences.antihydra.mahler_source_actions import (
        MahlerOccurrenceConsumer,
    )


ANTIHYDRA_ARITHMETIC_SEMANTIC_VERSION: Final[str] = (
    "antihydra-arithmetic-source-image-v2-dyadic"
)

ANTIHYDRA_ARITHMETIC_LAW = DyadicReturnLaw(
    family="antihydra-arithmetic-source-image",
    semantic_version=ANTIHYDRA_ARITHMETIC_SEMANTIC_VERSION,
    gains=(3, 3),
    offsets=(0, -1),
    weights=(2, -1),
)


class AntihydraArithmeticImageWorkspace(DyadicReturnImageWorkspace):
    """Pinned blank-tape arithmetic source; physical roofs remain demanded."""

    def __init__(
        self,
        ledger: ResourceLedger,
        returns: int,
        *,
        shared_cache: bool = True,
        prepare_mahler: bool = False,
        prepare_source_action: bool = False,
    ) -> None:
        if type(shared_cache) is not bool:
            raise TypeError("shared_cache must be a bool")
        if type(prepare_mahler) is not bool:
            raise TypeError("Mahler preparation must be Boolean")
        if type(prepare_source_action) is not bool:
            raise TypeError("source-action preparation must be Boolean")
        self.shared_cache = shared_cache
        self.mahler_bindings: (
            LedgerDict[
                tuple[DyadicReturnSourceID, DyadicReturnActionID],
                tuple[int, int, int | None],
            ]
            | None
        ) = None
        self._mahler_wire: tuple[int, int, int | None] | None = None
        self.mahler_binding_owner: int | None = None
        self._mahler_consumer: MahlerOccurrenceConsumer | None = None
        if (prepare_mahler or prepare_source_action) and returns:
            from number_compiler.sequences.antihydra.mahler_source_actions import (
                MahlerOccurrenceConsumer,
            )

            self._mahler_consumer = MahlerOccurrenceConsumer(
                ledger,
                ANTIHYDRA_ARITHMETIC_LAW,
                shared_cache=shared_cache,
                counter_family="mahler" if prepare_mahler else "antihydra",
            )
        consumer = self._mahler_consumer
        consumer_closed = False

        def close_consumer() -> None:
            nonlocal consumer_closed
            if consumer is not None and not consumer_closed:
                consumer.close()
                consumer_closed = True

        def cleanup_failed_construction() -> None:
            cleanups: list[Callable[[], object]] = []
            if consumer is not None and not consumer_closed:
                cleanups.append(close_consumer)
            if hasattr(self, "_closed"):
                cleanups.append(self.dispose)
            cleanup_all(cleanups)

        with cleanup_on_error(cleanup_failed_construction):
            super().__init__(ledger, 8, returns, ANTIHYDRA_ARITHMETIC_LAW)
            if consumer is not None:
                source = self.source_node(self.root_source)
                record = consumer.records.get((returns, source.residue))
                if record is None:
                    raise ValueError(
                        "source-action construction lost its root occurrence"
                    )
                node, normal, _publisher = record
                summary = self.image_node(self.root_payload).summary
                if (node.transfer, node.delta, node.minimum, node.odd_steps) != (
                    summary.transfer,
                    summary.delta,
                    summary.minimum,
                    summary.odd_steps,
                ):
                    raise ValueError(
                        "source-action occurrence has another admitted root image"
                    )
                consumer.count("source_action_active")
                if prepare_mahler:
                    owner = ledger.register(
                        f"mahler-root-action-{self.image_owner}",
                        "arithmetic_source_action",
                    )
                    self.mahler_binding_owner = owner
                    bindings: LedgerDict[
                        tuple[DyadicReturnSourceID, DyadicReturnActionID],
                        tuple[int, int, int | None],
                    ] = ledger.make_dict(owner, nodes_per_entry=3)
                    self.mahler_bindings = bindings
                    ledger.reserve(owner, entries=1, nodes=3)
                    wire = normal.wire()
                    bindings[(self.root_source, self.root_action)] = wire
                    self._mahler_wire = wire
            from number_compiler.sequences.antihydra.payload_audit import (
                register_antihydra_payload_contract,
            )

            register_antihydra_payload_contract(self)
            close_consumer()
            self._mahler_consumer = None

    def dispose(self) -> None:
        cleanup_all((self._dispose_mahler_bindings, super().dispose))

    def _dispose_mahler_bindings(self) -> None:
        owner = self.mahler_binding_owner
        if owner is None:
            return
        retained = self.ledger.inventory_owner(owner)
        if self.mahler_bindings is not None:
            self.mahler_bindings.clear()
        self.ledger.release(owner, entries=retained.entries, nodes=retained.nodes)
        self.ledger.mark_disposed(owner)
        self.mahler_bindings = None
        self.mahler_binding_owner = None
        self._mahler_wire = None

    def mahler_root_wire(self) -> tuple[int, int, int | None] | None:
        """Read the exact companion of this already admitted source/action."""
        if self.mahler_bindings is None:
            return None
        wire = self.mahler_bindings.get((self.root_source, self.root_action))
        if wire is not self._mahler_wire or type(wire) is not tuple or len(wire) != 3:
            raise ValueError("Mahler root lost its exact occurrence binding")
        extent, offset, cap = wire
        transfer = self.image_node(self.root_payload).summary.transfer
        self.ledger.bump(
            _antihydra_keys.MAHLER_HASHLIFE_ROOT_VALIDATION_OPERAND_BITS,
            transfer.upper.bit_length()
            + abs(transfer.offset).bit_length()
            + transfer.lower.bit_length(),
        )
        if (
            type(extent) is not int
            or type(offset) is not int
            or type(cap) is not int
            or extent != self.steps
            or offset != -12 * (transfer.upper + transfer.offset - transfer.lower)
            or cap != (6 if extent == 1 else 6 * transfer.upper + offset)
        ):
            raise ValueError("Mahler root lost its source-bound predicate")
        return wire

    @property
    def returns(self) -> int:
        return self.steps

    def validate(self) -> None:
        try:
            super().validate()
            if self.seed != 8 or self.law != ANTIHYDRA_ARITHMETIC_LAW:
                raise ValueError("another source law")
        except (ValueError, TypeError, AttributeError) as error:
            raise ValueError("Antihydra arithmetic source image was changed") from error

    @staticmethod
    def _centered_source(h: int, scratch: RunArithmeticWorkspace) -> int:
        scratch.require_bits(8 * (h.bit_length() + 16))
        centered = h - 1
        if centered < 0:
            raise ValueError("Antihydra run source must be nonnegative centered value")
        return centered

    def _record_fixed_point_run(self, length: int) -> None:
        """Charge the exact fixed-point summary without building a discarded gain."""
        self.bump_metric("temporal_zero_run_pumps")
        self.bump_metric("temporal_run_actions")
        self.bump_metric("temporal_run_operand_bits", length.bit_length())

    def _run_candidate(
        self,
        action: DyadicReturnActionID,
        source: SourceImageView,
        *,
        macro_selection: MahlerOddMacroSelection | None = None,
        scratch: RunArithmeticWorkspace | None = None,
        source_h: int | None = None,
    ) -> SourceImageCandidate:
        if scratch is not None:
            return self._run_candidate_with_scratch(
                action,
                source,
                macro_selection=macro_selection,
                scratch=scratch,
                source_h=source_h,
            )
        with RunArithmeticWorkspace.for_ledger(
            self.ledger, self.counter_prefix
        ).scope() as local_scratch:
            return self._run_candidate_with_scratch(
                action,
                source,
                macro_selection=macro_selection,
                scratch=local_scratch,
                source_h=source_h,
            )

    def _run_candidate_with_scratch(
        self,
        action: DyadicReturnActionID,
        source: SourceImageView,
        *,
        macro_selection: MahlerOddMacroSelection | None,
        scratch: RunArithmeticWorkspace,
        source_h: int | None,
    ) -> SourceImageCandidate:
        node = self.action_node(action)
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            raise TypeError("Antihydra run source has another sort")
        admitted = self.source_node(source_id)
        if not admitted.exact or admitted.precision != node.width:
            raise ValueError("Antihydra run requires its complete exact source")
        self.bump_metric("temporal_run_routes")
        scratch.require_bits(
            8
            * (
                max(
                    admitted.residue.bit_length(),
                    admitted.precision + admitted.lift.bit_length()
                    if admitted.lift
                    else 0,
                )
                + 16
            )
        )
        if source_h is None:
            source_h = self._source_value(admitted)
        endpoint_d = source_h - 1
        delta, minimum, odd_steps = 0, 0, 0
        remaining = node.width
        if macro_selection is not None:
            if macro_selection.prefix_steps:
                for (
                    prefix_width,
                    run_delta,
                    run_minimum,
                    run_odds,
                    prefix_endpoint_d,
                ) in self._punctured_steps(
                    source_h, macro_selection.prefix_steps, scratch
                ):
                    delta, minimum = compose_prefix_safety_values(
                        delta, minimum, run_delta, run_minimum
                    )
                    odd_steps += run_odds
                    remaining -= prefix_width
                    endpoint_d = prefix_endpoint_d
            if endpoint_d != macro_selection.source:
                raise ArithmeticError("odd macro selector changed its admitted source")
            powered_extent = macro_selection.extent
            scratch.require_bits(
                8 * (endpoint_d.bit_length() + 2 * powered_extent + 3 * node.width + 32)
            )
            powered = macro_selection.ring.power(
                macro_selection.repetitions,
                max_extent=MAX_MAHLER_SOURCE_EXTENT,
            )
            powered_endpoint, powered_balance = powered.advance(endpoint_d, delta)
            delta, minimum = compose_prefix_safety_values(
                delta, minimum, powered.delta, powered.minimum
            )
            if powered_balance != delta:
                raise ArithmeticError("powered odd macro changed its ledger cocycle")
            odd_steps += powered.extent - powered.odd_events
            endpoint_d = powered_endpoint
            remaining -= powered_extent
            self.bump_metric("temporal_odd_macro_evaluations")
            self.bump_metric(
                "temporal_odd_macro_repetitions", macro_selection.repetitions
            )
            self.bump_metric("temporal_odd_macro_return_steps", powered_extent)
            self.bump_metric(
                "temporal_odd_macro_operand_bits",
                endpoint_d.bit_length()
                + powered.joint.gain.bit_length()
                + powered.joint.innovation.bit_length(),
            )
            self.bump_metric(
                "temporal_odd_macro_residual_steps",
                node.width - macro_selection.prefix_steps - powered_extent,
            )
        residual_source_h = endpoint_d + 1
        for (
            _length,
            run_delta,
            run_minimum,
            run_odds,
            residual_endpoint_d,
        ) in self._punctured_steps(residual_source_h, remaining, scratch):
            delta, minimum = compose_prefix_safety_values(
                delta, minimum, run_delta, run_minimum
            )
            # Shared dyadic images count odd h, the complement of centered D.
            odd_steps += run_odds
            endpoint_d = residual_endpoint_d
        # Every centered branch has slope 3/2. Recover the branch affine
        # intercept from its exact source and endpoint once, rather than
        # repeatedly composing coefficients against the growing prefix.
        scratch.require_bits(8 * (source_h.bit_length() + 3 * node.width + 16))
        upper, lower = 3**node.width, 1 << node.width
        offset = (endpoint_d + 1) * lower - upper * source_h
        self.bump_metric(
            "temporal_composition_operand_bits",
            upper.bit_length()
            + lower.bit_length()
            + abs(offset).bit_length()
            + source_h.bit_length()
            + endpoint_d.bit_length(),
        )
        transfer = SkewTransfer(upper, offset, lower)
        return publish_exact_run_candidate(
            self, action, source, transfer, odd_steps, delta, minimum
        )

    def _try_odd_macro_candidate(
        self, action: DyadicReturnActionID, source: SourceImageView
    ) -> SourceImageCandidate | None:
        """Power a source-witnessed odd motif before the scheduler opens children."""
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            raise TypeError("Antihydra macro source has another sort")
        admitted = self.source_node(source_id)
        width = self.action_node(action).width
        if (
            not admitted.exact
            or admitted.precision != width
            or width <= self.MAX_LEAF_STEPS
        ):
            return None
        # This low 2-adic check can only reject a source when every upcoming
        # selector exponent is fixed and no repeated motif fits the exact
        # residual budget. An unknown valuation always falls through to the
        # full issuer. Use only the already admitted residue/lift so the
        # negative check happens before allocating selector scratch state.
        low_mask = (1 << PREFILTER_BITS) - 1
        pointed_low = admitted.residue & low_mask
        if admitted.lift and admitted.precision < PREFILTER_BITS:
            pointed_low += (
                admitted.lift & ((1 << (PREFILTER_BITS - admitted.precision)) - 1)
            ) << admitted.precision
        centered_low = (pointed_low - 1) & low_mask
        if not might_have_odd_macro_low_suffix(
            centered_low,
            remaining_steps=width,
            max_residual_steps=self.MAX_LEAF_STEPS,
        ):
            self.bump_metric("temporal_odd_macro_prefilter_rejections")
            self.bump_metric("temporal_odd_macro_selector_misses")
            return None
        scratch_workspace = RunArithmeticWorkspace.for_ledger(
            self.ledger, self.counter_prefix
        )
        with scratch_workspace.scope() as scratch:
            scratch.require_bits(
                8
                * (
                    max(
                        admitted.residue.bit_length(),
                        admitted.precision + admitted.lift.bit_length()
                        if admitted.lift
                        else 0,
                    )
                    + 16
                )
            )
            # An exact source with no high lift is already its low residue;
            # preserve the no-reconstruction path for small admitted seeds.
            source_h = (
                admitted.residue if admitted.lift == 0 else self._source_value(admitted)
            )
            centered = source_h - 1
            self.bump_metric("temporal_odd_macro_selector_calls")
            if centered <= 0:
                self.bump_metric("temporal_odd_macro_selector_misses")
                return None
            selection = select_source_certified_odd_macro(
                centered,
                width,
                max_extent=min(width, MAX_MAHLER_SOURCE_EXTENT),
                max_residual_steps=self.MAX_LEAF_STEPS,
                reserve_bits=scratch.require_bits,
                on_event_work=self._account_odd_macro_selector_work,
            )
            if selection is None:
                self.bump_metric("temporal_odd_macro_selector_misses")
                return None
            residual_steps = width - selection.prefix_steps - selection.extent
            if residual_steps > self.MAX_LEAF_STEPS:
                self.bump_metric("temporal_odd_macro_partial_fallbacks")
                return None
            self.bump_metric(
                "temporal_odd_macro_selection_events", selection.witnessed_events
            )
            return self._run_candidate_with_scratch(
                action,
                source,
                macro_selection=selection,
                scratch=scratch,
                source_h=source_h,
            )

    def _account_odd_macro_selector_work(
        self, event_count: int, operand_bits: int
    ) -> None:
        if event_count:
            self.bump_metric("temporal_odd_macro_selector_events", event_count)
        if operand_bits:
            self.bump_metric("temporal_odd_macro_selector_operand_bits", operand_bits)

    def _punctured_steps(
        self, h: int, width: int, scratch: RunArithmeticWorkspace
    ) -> Iterator[tuple[int, int, int, int, int]]:
        """Contract bounded source events inside the scheduler's exact leaf.

        A complete ``0**(q-1) 1`` occurrence has endpoint
        ``3**q * (D >> q) + (3**q+1)//2``, ledger delta ``3-q`` and
        minimum ``1-q``. Neither its event word nor a separate event cylinder
        is needed. Consecutive q=1 occurrences still share one powered odd
        run; a final incomplete zero run retains its own powered action.
        Long mixed sources remain owned by balanced scheduler composition.
        """
        d = self._centered_source(h, scratch)
        remaining = width
        while remaining:
            source_bits = d.bit_length()
            scratch.require_bits(8 * (source_bits + 16))
            if d == 0:
                # h=1 is fixed, hence all remaining family symbols are odd.
                # Keep its exact skew/safety summary without evaluating v2(0).
                length = remaining
                self._record_fixed_point_run(length)
                yield length, -length, -length, length, 0
                return
            elif d & 1:
                # Preserve the homogeneous run quotient, including large runs.
                length = min(remaining, v2_positive(d + 1))
                scratch.require_bits(8 * (source_bits + 2 * length + 16))
                upper = 3**length
                d = upper * ((d + 1) >> length) - 1
                delta, minimum, odd_steps = 2 * length, 0, 0
                self.bump_metric("temporal_one_run_pumps")
            else:
                zeros = v2_positive(d)
                length = min(remaining, zeros + 1)
                scratch.require_bits(8 * (source_bits + 2 * length + 16))
                upper = 3**length
                if length > zeros:
                    d = upper * (d >> length) + (upper + 1) // 2
                    delta, minimum, odd_steps = 3 - length, 1 - length, zeros
                    self.bump_metric("temporal_punctured_event_actions")
                    self.bump_metric("temporal_punctured_event_symbols", length)
                else:
                    d = upper * (d >> length)
                    delta, minimum, odd_steps = -length, -length, length
                    self.bump_metric("temporal_zero_run_pumps")
            self.bump_metric("temporal_run_actions")
            self.bump_metric(
                "temporal_run_operand_bits",
                source_bits + d.bit_length() + upper.bit_length(),
            )
            yield length, delta, minimum, odd_steps, d
            remaining -= length

    def retain_chronological_support(self) -> bool:
        """Retain only the complete affine and ledger effect until explicit demand."""
        return False

    def _whole_initial_run(self, source: SourceImageView, width: int) -> bool:
        """Admit a homogeneous run from its low cylinder, without its value.

        For ``h=r+2**width*u`` and centered ``d=h-1``, a run of at least
        ``width`` symbols is exactly ``r in {0,1}`` with ``u>0``. At r=0
        the odd centered branch has ``d+1=h``; at r=1 the even branch has
        ``d=h-1``. Both tests depend only on the admitted cylinder ports.
        """
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            raise TypeError("Antihydra source has another sort")
        admitted = self.source_node(source_id)
        if not admitted.exact or admitted.precision != width or width <= 0:
            raise ValueError("Antihydra run selection requires its exact cylinder")
        self.bump_metric(
            "temporal_run_selection_operand_bits",
            admitted.residue.bit_length()
            + admitted.lift.bit_length()
            + width.bit_length(),
        )
        return admitted.lift > 0 and admitted.residue in (0, 1)

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        """Publish one source-bound carry and ledger, without a branch itinerary."""
        self.validate_action(action)
        self.validate_payload(source.payload)
        if (
            demand not in (None, SourceImageDemand("physical-summary"))
            or source.binding.action != self.identity
            or type(action) is not DyadicReturnActionID
            or self.action_node(action).width == 0
        ):
            return super().apply_composite(action, source, demand)
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            raise TypeError("Antihydra source has another sort")
        width = self.action_node(action).width
        consumer = self._mahler_consumer
        if consumer is not None:
            admitted = self.source_node(source_id)
            source_value = admitted.residue + (admitted.lift << admitted.precision)
            effect = consumer.lookup(width, admitted.residue, source=source_value)
            if effect is not None:
                candidate = publish_exact_run_candidate(
                    self,
                    action,
                    source,
                    effect.transfer,
                    effect.odd_steps,
                    effect.delta,
                    effect.minimum,
                )
                consumer.applied(
                    parent=(
                        source_id == self.root_source
                        and action == self.root_action
                        and width == self.returns
                    )
                )
                return candidate
        if self.source_node(source_id).exact and (
            width <= self.MAX_LEAF_STEPS or self._whole_initial_run(source, width)
        ):
            candidate = self._run_candidate(action, source)
        elif self.source_node(source_id).exact:
            macro_candidate = self._try_odd_macro_candidate(action, source)
            if macro_candidate is None:
                # For this bounded high-cost span, the exact admitted integer
                # lets the existing punctured carry/run constructor avoid the
                # balanced residue tree. This is an occurrence constructor,
                # not authority borrowed from a matrix observer. Keep smaller
                # exact-source clients on their established saturated path.
                if 1536 <= width <= 2048:
                    self.bump_metric("temporal_run_routes")
                    candidate = self._run_candidate(action, source)
                else:
                    self.bump_metric("temporal_balanced_routes")
                    candidate = self.complete_composite_candidate(action, source)
            else:
                candidate = macro_candidate
        else:
            self.bump_metric("temporal_balanced_routes")
            candidate = self.complete_composite_candidate(action, source)
        if consumer is not None and candidate is not None:
            self._publish_mahler_root_candidate(candidate, action, source)
        return candidate

    def primitive_run_candidate(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate | None:
        source_id = source.binding.source
        if type(source_id) is not DyadicReturnSourceID:
            raise TypeError("Antihydra source has another sort")
        if (
            type(action) is DyadicReturnActionID
            and 0 < self.action_node(action).width <= self.MAX_LEAF_STEPS
            and self.source_node(source_id).exact
            and source.binding.action == self.identity
        ):
            candidate = self._run_candidate(action, source)
            if candidate is not None:
                self._publish_mahler_root_candidate(candidate, action, source)
            return candidate
        return None

    def _publish_mahler_root_candidate(
        self,
        candidate: SourceImageCandidate,
        action: Hashable,
        source: SourceImageView,
    ) -> None:
        consumer = self._mahler_consumer
        if (
            consumer is None
            or type(action) is not DyadicReturnActionID
            or action != self.root_action
            or source.binding.source != self.root_source
            or self.action_node(action).width != self.returns
        ):
            return
        payload = candidate.payload
        if type(payload) is not DyadicReturnImageID:
            raise TypeError("Mahler constructor returned another image sort")
        root_source = self.source_node(self.root_source)
        publisher = root_source.residue + (root_source.lift << root_source.precision)
        consumer.publish_root(self.image_node(payload).summary, publisher=publisher)

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        if demand == SourceImageDemand("mahler-associated-action"):
            # The associated action is a consumer of this same admitted image.
            # Its first two centered bits are 11, although the physical h bits
            # are 00.  Their cap becomes negative at return two, so all later
            # source-selected steps act affinely on that prefix image.
            if (
                image.payload != self.root_payload
                or image.binding.source != self.root_source
                or image.binding.action != self.root_action
                or image.binding.extent != self.returns
                or self.seed != 8
                or self.law != ANTIHYDRA_ARITHMETIC_LAW
            ):
                raise ValueError("Mahler projection has another source image")
            from number_compiler.sequences.antihydra.mahler_cache import (
                cached_associated_action,
            )

            action = cached_associated_action(self)
            return SourceImageProjection(action)
        return super().project(image, demand)

    def segments(self) -> Iterator[tuple[int, ArithmeticCylinder]]:
        for start, summary, word in self.leaf_summaries():
            transfer = summary.transfer
            chart = integer_dyadic_fiber_action(
                transfer, summary.residue, summary.width
            )
            output = chart.addend
            yield (
                start,
                ArithmeticCylinder(
                    summary.width,
                    summary.residue,
                    output,
                    summary.delta,
                    summary.minimum,
                    word,
                ),
            )


AntihydraArithmeticActionID = DyadicReturnActionID
AntihydraArithmeticImageID = DyadicReturnImageID
AntihydraArithmeticSourceID = DyadicReturnSourceID
AntihydraArithmeticSupportID = DyadicReturnSupportID
ArithmeticImageSummary = DyadicImageSummary

__all__ = [
    "ANTIHYDRA_ARITHMETIC_LAW",
    "AntihydraArithmeticActionID",
    "AntihydraArithmeticImageID",
    "AntihydraArithmeticImageWorkspace",
    "AntihydraArithmeticSourceID",
    "AntihydraArithmeticSupportID",
    "ArithmeticImageSummary",
]
