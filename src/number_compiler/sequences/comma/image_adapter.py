"""Canonical source-image adapter for comma arithmetic and observations."""

from __future__ import annotations

from collections.abc import Generator, Hashable
from contextlib import contextmanager
from dataclasses import dataclass
from math import gcd
from typing import TYPE_CHECKING, Final, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
)
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageBinding,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.sequences.comma.action_arena import (
    CommaActionArena,
    CommaActionID,
    CommaActionRecord,
)
from number_compiler.sequences.comma.arithmetic import (
    comma_children,
    decimal_sector,
    large_sector_children,
    phase_prefix_displacement,
    safe_complete_cycles_from_sector,
)
from number_compiler.sequences.comma.boundary_quotient import (
    PERIOD,
    BoundaryState,
    MacroTemplate,
)
from number_compiler.sequences.comma.boundary_receipt import (
    SOURCE,
    BoundaryPrefixCursor,
    BoundarySelectionReceipt,
    BoundarySelectionReceiptID,
    CommaImagePayload,
    validate_action_result,
)

if TYPE_CHECKING:
    from number_compiler.sequences.comma.power import CommaTerm

SEMANTIC_VERSION: Final[str] = "comma-source-cylinder-v7-receiver-bound-prefix"
STRICT_INTERIOR_CYCLE_CONSUMER_TAG: Final[str] = "strict-interior-cycle-v2-phase-coset"


class UnresolvedCommaBranch(ValueError):
    """The next term requires certified infinite-future branch selection."""


@dataclass(frozen=True, slots=True)
class CommaOccurrenceID(ArenaHandle):
    """Source authority for one completed image without recursive ID nesting."""


@dataclass(frozen=True, slots=True)
class CommaSource:
    value: int
    certificate_version: str = "uncertified-arithmetic"


class CommaImageAdapter(SourceBoundImageAdapter):
    family = "a367620"
    semantic_version = SEMANTIC_VERSION

    def __init__(self, arena: CommaActionArena, scheduler: TileScheduler) -> None:
        self.arena = arena
        self.scheduler = scheduler
        self.ledger = arena.ledger
        self._term: CommaTerm | None = None

    def bind_owner(self, owner: CommaTerm) -> None:
        """Bind the one term that owns this adapter's source occurrences."""
        if owner.arena is not self.arena or owner.scheduler is not self.scheduler:
            raise ValueError("comma adapter owner belongs to another runtime")
        if self._term is not None and self._term is not owner:
            raise ValueError("comma adapter already has another owner")
        self._term = owner

    def _require_open_owner(self) -> CommaTerm:
        owner = self._term
        if owner is None:
            raise ValueError("comma adapter has no source owner")
        owner.require_open()
        return owner
        return owner

    @contextmanager
    def composite_transaction(self) -> Generator[None, None, None]:
        """Scope receipt issuance through primitive validation and publication."""
        owner = self._term
        if owner is None:
            raise ValueError("comma receipt transaction has no term owner")
        owner.require_open()
        with owner.boundary_receipt_transaction():
            yield

    @property
    def bound_term(self) -> CommaTerm | None:
        """Return the owner binding for read-only cross-module verification."""
        return self._term

    def audit_image_binding(
        self,
        binding: SourceImageBinding,
        payload: object,
        failure_prefix: Hashable | None,
    ) -> tuple[Hashable, ...] | None:
        from number_compiler.sequences.comma.payload_audit import (
            audit_comma_image_binding,
        )

        return audit_comma_image_binding(self, binding, payload, failure_prefix)

    def validate_source(self, source: Hashable) -> None:
        owner = self._require_open_owner()
        self.arena.charge()
        if type(source) is CommaSource:
            if (
                type(source.value) is not int
                or source.value != SOURCE
                or source.certificate_version != owner.certificate_version
            ):
                raise ValueError("comma source is not the authenticated root 20")
            return
        if type(source) is CommaOccurrenceID:
            self._occurrence_payload(source)
            return
        if type(source) is SourceImageID:
            record = self.scheduler.source_image_core().resolve(source)
            if (
                record.binding.family != self.family
                or record.binding.semantic_version != self.semantic_version
            ):
                raise ValueError("comma provider image is foreign")
            self.validate_payload(record.payload)
            return
        raise TypeError("comma source requires root 20 or an admitted image")

    def validate_action(self, action: Hashable) -> None:
        self._require_open_owner()
        self.arena.charge()
        self.arena.node(cast(CommaActionID, action))

    def validate_payload(self, payload: Hashable) -> None:
        self._require_open_owner()
        self.arena.charge()
        if type(payload) is not CommaImagePayload:
            raise TypeError("comma image has another payload sort")
        if (
            type(payload.value) is not int
            or type(payload.absolute_index) is not int
            or type(payload.certificate_version) is not str
            or not payload.certificate_version
            or self._term is None
            or payload.certificate_version != self._term.certificate_version
            or payload.value < SOURCE
            or payload.absolute_index < 1
        ):
            raise ValueError("comma image has invalid endpoint coordinates")
        cursor = payload.boundary_cursor
        if cursor is not None:
            from number_compiler.sequences.comma.boundary_quotient import (
                boundary_state_signature,
            )

            if (
                type(cursor) is not BoundaryPrefixCursor
                or type(cursor.state) is not BoundaryState
                or type(cursor.exponent) is not int
                or cursor.exponent < 5
                or type(cursor.transitions) is not int
                or cursor.transitions < 0
                or payload.absolute_index - cursor.transitions < 1
            ):
                raise ValueError("comma image has an invalid boundary cursor")
            boundary_state_signature(cursor.state)
            if cursor.exponent % PERIOD != cursor.state.exponent_residue:
                raise ValueError("comma image has an invalid boundary cursor phase")
            self.arena.charge_bits(
                cursor.exponent.bit_length()
                + cursor.transitions.bit_length()
                + cursor.state.a.bit_length()
                + cursor.state.exponent_residue.bit_length()
            )
            receipt = cursor.selection_receipt
            if receipt is not None:
                if type(receipt) is not BoundarySelectionReceiptID:
                    raise ValueError(
                        "comma cursor has another selection receipt handle"
                    )
                owner = self._term
                if owner is None:
                    raise ValueError("comma selection receipt has no source owner")
                issued_receipt = owner.resolve_boundary_selection_receipt(receipt)
                provider = owner.require_global_future_provider(
                    issued_receipt.artifact_sha256
                )
                issued_receipt.validate_provider(provider)
                issued_receipt.validate_output(
                    value=payload.value,
                    absolute_index=payload.absolute_index,
                    cursor=cursor,
                    receipt_id=receipt,
                )
                selection = issued_receipt.selection
                self.arena.charge()
                self.arena.charge_bits(
                    len(issued_receipt.artifact_sha256) * 8
                    + issued_receipt.source_state.a.bit_length()
                    + issued_receipt.source_state.exponent_residue.bit_length()
                    + issued_receipt.source_exponent.bit_length()
                    + issued_receipt.source_value.bit_length()
                    + issued_receipt.source_index.bit_length()
                    + issued_receipt.source_extent.bit_length()
                    + issued_receipt.target_state.a.bit_length()
                    + issued_receipt.target_state.exponent_residue.bit_length()
                    + issued_receipt.target_exponent.bit_length()
                    + issued_receipt.target_value.bit_length()
                    + issued_receipt.transitions.bit_length()
                    + selection.source_class.bit_length()
                    + selection.fork_coefficient.bit_length()
                    + sum(cid.bit_length() for cid in selection.ordered_child_classes)
                    + selection.selected_slot.bit_length()
                )

    def validate_action_result(
        self,
        action: CommaActionRecord,
        source_payload: CommaImagePayload,
        source_extent: int,
        result_payload: CommaImagePayload,
        result_extent: int,
        result_ports: tuple[Hashable, ...],
        *,
        expected_transitions: int | None = None,
        template: MacroTemplate | None = None,
    ) -> None:
        self._require_open_owner()
        validate_action_result(
            self.arena,
            self._term,
            action,
            source_payload,
            source_extent,
            result_payload,
            result_extent,
            result_ports,
            expected_transitions=expected_transitions,
            template=template,
        )

    def identity_action(self, source: Hashable) -> CommaActionID:
        self._require_open_owner()
        self.validate_source(source)
        return self.arena.identity

    def action_children(
        self, action: Hashable
    ) -> tuple[CommaActionID, CommaActionID] | None:
        self._require_open_owner()
        node = self.arena.node(cast(CommaActionID, action))
        if node.before is None or node.after is None:
            return None
        return node.before, node.after

    def compose_actions(self, before: Hashable, after: Hashable) -> CommaActionID:
        self._require_open_owner()
        return self.arena.compose(
            cast(CommaActionID, before), cast(CommaActionID, after)
        )

    def source_payload(self, source: Hashable) -> CommaImagePayload:
        self.validate_source(source)
        if type(source) is CommaSource:
            return CommaImagePayload(source.value, 1, source.certificate_version)
        if type(source) is SourceImageID:
            record = self.scheduler.source_image_core().resolve(source)
            return cast(CommaImagePayload, record.payload)
        return self._occurrence_payload(cast(CommaOccurrenceID, source))

    def _occurrence_payload(self, source: CommaOccurrenceID) -> CommaImagePayload:
        owner = self._term
        if owner is None:
            raise ValueError("comma adapter has no source owner")
        record = owner.occurrence_record(source)
        image = self.scheduler.source_image_core().resolve(record.image)
        if (
            image.binding.family != self.family
            or image.binding.semantic_version != self.semantic_version
            or record.certificate_version != owner.certificate_version
            or type(image.payload) is not CommaImagePayload
            or image.payload.value != record.value
            or image.payload.absolute_index != record.absolute_index
            or image.payload.certificate_version != record.certificate_version
            or image.payload.boundary_cursor != record.boundary_cursor
        ):
            raise ValueError("comma occurrence lost its completed provider image")
        self.validate_payload(image.payload)
        return image.payload

    def _candidate(self, value: int, index: int, extent: int) -> SourceImageCandidate:
        self.arena.charge_bits(3 * value.bit_length())
        sector = decimal_sector(value)
        owner = self._term
        if owner is None:
            raise ValueError("comma adapter has no source owner")
        return SourceImageCandidate(
            CommaImagePayload(value, index, owner.certificate_version),
            extent,
            (sector.leading, sector.digit, sector.headroom),
            radix=10,
        )

    def _authenticated_cycle_ports(
        self,
        node: CommaActionRecord,
        source: SourceImageView,
        *,
        malformed_message: str,
    ) -> tuple[int, int, int] | None:
        ports = source.binding.boundary_ports
        if len(ports) != 3 or any(type(value) is not int for value in ports):
            raise ValueError(malformed_message)
        leading, digit, headroom = cast(tuple[int, int, int], ports)
        phase_class = gcd(node.leading, 10)
        if leading != node.leading or digit % phase_class != node.entering_digit:
            return None
        return leading, digit, headroom

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        self._require_open_owner()
        payload = self.source_payload(source)
        if type(source) is CommaSource:
            return self._candidate(payload.value, payload.absolute_index, 0)
        if type(source) is SourceImageID:
            record = self.scheduler.source_image_core().resolve(source)
            return SourceImageCandidate(
                payload,
                0,
                record.binding.boundary_ports,
                orientation=record.binding.orientation,
                radix=record.binding.radix,
                precision=record.binding.precision,
            )
        occurrence = cast(CommaOccurrenceID, source)
        owner = self._term
        if owner is None:
            raise ValueError("comma adapter has no source owner")
        occurrence_record = owner.occurrence_record(occurrence)
        image = self.scheduler.source_image_core().resolve(occurrence_record.image)
        return SourceImageCandidate(
            payload,
            0,
            image.binding.boundary_ports,
            orientation=image.binding.orientation,
            radix=image.binding.radix,
            precision=image.binding.precision,
        )

    def _apply(
        self,
        node: CommaActionRecord,
        source: SourceImageView,
        *,
        boundary_template: MacroTemplate | None = None,
    ) -> SourceImageCandidate:
        payload = cast(CommaImagePayload, source.payload)
        output_ports: tuple[int, int, int] | None = None
        if node.kind == "identity":
            return SourceImageCandidate(
                payload,
                source.binding.extent,
                source.binding.boundary_ports,
                orientation=source.binding.orientation,
                radix=source.binding.radix,
                precision=source.binding.precision,
            )
        if node.kind == "boundary-prefix-occurrence":
            state = node.boundary_source
            if state is None:
                raise ValueError("comma boundary action is incomplete")
            root = self.source_payload(source.binding.source)
            cursor = root.boundary_cursor
            if cursor is None:
                exponent = decimal_sector(root.value).exponent
                if exponent % PERIOD != state.exponent_residue:
                    raise ValueError(
                        "comma receiver prefix has another source occurrence "
                        "(root exponent/phase mismatch)"
                    )
                if (
                    state.value(exponent, charge_bits=self.arena.charge_bits)
                    != root.value
                ):
                    raise ValueError(
                        "comma receiver prefix has another source occurrence "
                        "(root value mismatch)"
                    )
                prior_steps = 0
            else:
                if cursor.state != state:
                    raise ValueError(
                        "comma receiver prefix has another source occurrence "
                        "(cursor chart mismatch)"
                    )
                exponent = cursor.exponent
                prior_steps = cursor.transitions
            template = (
                self.arena.boundary_template(state)
                if boundary_template is None
                else boundary_template
            )
            if type(template) is not MacroTemplate or template.source != state:
                raise ValueError("comma global action has another boundary template")
            if root.boundary_cursor != payload.boundary_cursor:
                raise ValueError(
                    "comma receiver prefix has another source occurrence "
                    "(cursor authority mismatch)"
                )
            if (
                root.absolute_index != payload.absolute_index
                or root.value != payload.value
            ):
                raise ValueError(
                    "comma receiver prefix has another source occurrence "
                    "(receiving endpoint mismatch)"
                )
            transitions = prior_steps + node.steps
            if transitions > template.weight.evaluate(
                exponent, charge_bits=self.arena.charge_bits
            ):
                raise ValueError("comma receiver prefix crosses its next branch")
            base_index = root.absolute_index - prior_steps
            if base_index < 1:
                raise ValueError(
                    "comma receiver prefix has another source occurrence "
                    "(cursor index mismatch)"
                )
            value = template.point(
                exponent,
                transitions,
                charge=self.arena.charge,
                charge_bits=self.arena.charge_bits,
                validate_read=self.arena.boundary_read_guard(state, template),
            )
            self.ledger.bump(_comma_keys.COMMA_BOUNDARY_PREFIX_APPLICATIONS)
            self.ledger.bump(
                _comma_keys.COMMA_BOUNDARY_REPRESENTED_TRANSITIONS, node.steps
            )
            sector = decimal_sector(value)
            next_index = payload.absolute_index + node.steps
            self.arena.charge_bits(
                value.bit_length()
                + next_index.bit_length()
                + exponent.bit_length()
                + transitions.bit_length()
                + state.a.bit_length()
                + state.exponent_residue.bit_length()
            )
            self.ledger.bump(_comma_keys.COMMA_OPERAND_BIT_WORK, value.bit_length())
            return SourceImageCandidate(
                CommaImagePayload(
                    value,
                    next_index,
                    payload.certificate_version,
                    BoundaryPrefixCursor(state, exponent, transitions),
                ),
                source.binding.extent + node.steps,
                (sector.leading, sector.digit, sector.headroom),
                radix=10,
            )
        elif node.kind == "source20-first-child":
            owner = self._term
            if owner is None:
                raise ValueError("comma adapter has no source owner")
            provider = owner.require_global_future_provider(node.future_digest)
            from number_compiler.sequences.comma.future_authority import (
                SOURCE20_FIRST_FORK_CHILDREN,
                SOURCE20_FIRST_FORK_INDEX,
                SOURCE20_FIRST_FORK_VALUE,
                SOURCE20_SELECTED_CHILD_INDEX,
            )
            from number_compiler.sequences.comma.semantic_branch import (
                bind_source20_first_child_entry,
            )

            if (
                payload.absolute_index != SOURCE20_FIRST_FORK_INDEX
                or payload.value != SOURCE20_FIRST_FORK_VALUE
            ):
                raise ValueError("comma source-20 action has another first fork")
            children = comma_children(payload.value)
            if children != SOURCE20_FIRST_FORK_CHILDREN:
                raise ValueError("comma source-20 action has altered children")
            ordered_children = (children[0], children[1])
            entry = bind_source20_first_child_entry(
                parent_index=payload.absolute_index,
                parent_value=payload.value,
                ordered_children=ordered_children,
                child_index=SOURCE20_SELECTED_CHILD_INDEX,
                provider=provider,
                charge_work=self.arena.charge,
                charge_bits=self.arena.charge_bits,
            )
            value = entry.child_value
            target = entry.selected_occurrence
            sector = decimal_sector(value)
            self.ledger.bump(_comma_keys.COMMA_GLOBAL_BRANCH_ACTION_APPLICATIONS)
            self.ledger.bump(_comma_keys.COMMA_OPERAND_BIT_WORK, value.bit_length())
            self.arena.charge_bits(
                value.bit_length() + payload.absolute_index.bit_length() + 1
            )
            return SourceImageCandidate(
                CommaImagePayload(
                    value,
                    payload.absolute_index + 1,
                    payload.certificate_version,
                    BoundaryPrefixCursor(target.state, target.exponent, 0),
                ),
                source.binding.extent + 1,
                (sector.leading, sector.digit, sector.headroom),
                radix=10,
            )
        elif node.kind == "global-boundary-return":
            state = node.boundary_source
            owner = self._term
            if owner is None or state is None or node.boundary_target is not None:
                raise ValueError("comma global boundary action is incomplete")
            provider = owner.require_global_future_provider(node.future_digest)
            exponent = decimal_sector(payload.value).exponent
            from number_compiler.sequences.comma.occurrence import (
                BoundaryOccurrence,
                OccurrencePrefixReturn,
            )
            from number_compiler.sequences.comma.semantic_branch import (
                select_global_semantic_macro_child_from_prefix,
            )

            source_occurrence = BoundaryOccurrence(state, exponent)
            if (
                source_occurrence.value(
                    charge_work=self.arena.charge,
                    charge_bits=self.arena.charge_bits,
                )
                != payload.value
            ):
                raise ValueError("comma global boundary action has another source")
            template = self.arena.boundary_template(state)
            prefix = OccurrencePrefixReturn(
                source_occurrence,
                template,
                charge_work=self.arena.charge,
                charge_bits=self.arena.charge_bits,
            )
            if prefix.outcome != "fork":
                raise ValueError("comma global boundary action reached a landmine")
            selected = select_global_semantic_macro_child_from_prefix(
                source_occurrence,
                prefix,
                provider=provider,
                charge_work=self.arena.charge,
                charge_bits=self.arena.charge_bits,
            )
            value = selected.literal_value
            steps = selected.total_transition_count
            weighted_steps = selected.weighted_action.weight.evaluate(
                selected.source.exponent, charge_bits=self.arena.charge_bits
            )
            if weighted_steps != steps:
                raise ValueError(
                    "comma weighted return differs from its exact endpoint"
                )
            receipt = BoundarySelectionReceipt.from_semantic_child(
                selected,
                provider,
                source_value=payload.value,
                source_index=payload.absolute_index,
                source_extent=source.binding.extent,
            )
            owner = self._term
            if owner is None:
                raise ValueError("comma selection receipt has no term owner")
            receipt_id = owner.issue_boundary_selection_receipt(receipt)
            sector = decimal_sector(value)
            self.ledger.bump(_comma_keys.COMMA_GLOBAL_BRANCH_ACTION_APPLICATIONS)
            self.ledger.bump(_comma_keys.COMMA_BOUNDARY_WEIGHTED_APPLICATIONS)
            self.ledger.bump(_comma_keys.COMMA_BOUNDARY_REPRESENTED_TRANSITIONS, steps)
            self.ledger.bump(_comma_keys.COMMA_OPERAND_BIT_WORK, value.bit_length())
            self.arena.charge_bits(
                value.bit_length()
                + payload.absolute_index.bit_length()
                + steps.bit_length()
            )
            return SourceImageCandidate(
                CommaImagePayload(
                    value,
                    payload.absolute_index + steps,
                    payload.certificate_version,
                    BoundaryPrefixCursor(
                        selected.target.state,
                        selected.target.exponent,
                        0,
                        receipt_id,
                    ),
                ),
                source.binding.extent + steps,
                (sector.leading, sector.digit, sector.headroom),
                radix=10,
            )
        elif node.kind == "step":
            self.ledger.bump(_comma_keys.COMMA_EVALUATED_TRANSITIONS)
            sector = decimal_sector(payload.value)
            if sector.exponent < 2:
                self.arena.charge(9)
                self.arena.charge_bits(18 * payload.value.bit_length())
                children = comma_children(payload.value)
                self.ledger.bump(_comma_keys.COMMA_CHILD_CANDIDATE_CHECKS, 9)
            else:
                self.arena.charge(2)
                self.arena.charge_bits(4 * payload.value.bit_length())
                children = large_sector_children(payload.value, sector)
                self.ledger.bump(_comma_keys.COMMA_SEAM_PREDICATE_CHECKS, 2)
            if not children:
                raise UnresolvedCommaBranch(
                    f"comma landmine at index {payload.absolute_index} has no child"
                )
            if len(children) != 1:
                raise UnresolvedCommaBranch(
                    f"comma fork at index {payload.absolute_index} needs "
                    "an authenticated boundary-return action"
                )
            value = children[0]
            if value - payload.value != 10 * (payload.value % 10) + node.child_digit:
                raise ValueError("comma action selected another child")
            self.ledger.bump(_comma_keys.COMMA_SCALAR_SEAM_STEPS)
        elif node.kind == "phase-prefix":
            sector = decimal_sector(payload.value)
            transfer = self.arena.transfer(node.leading, node.entering_digit)
            if (
                sector.exponent < 2
                or sector.leading != node.leading
                or sector.digit != node.entering_digit
                or not 0 < node.steps < transfer.period
            ):
                raise ValueError("comma phase prefix has another source or extent")
            self.arena.charge(node.steps + 2)
            self.arena.charge_bits(4 * payload.value.bit_length() + 32 * node.steps)
            displacement = phase_prefix_displacement(
                node.leading, node.entering_digit, node.steps
            )
            if (
                node.displacement != displacement
                or node.maximum_guard != displacement + int(node.leading < 9)
                or sector.headroom <= node.maximum_guard
            ):
                raise ValueError("comma phase prefix crosses an unadmitted seam")
            value = payload.value + displacement
            self.ledger.bump(_comma_keys.COMMA_PHASE_PREFIX_APPLICATIONS)
            self.ledger.bump(_comma_keys.COMMA_PHASE_PREFIX_TRANSITIONS, node.steps)
            self.ledger.bump(_comma_keys.COMMA_POWERED_IMAGE_APPLICATIONS)
        elif node.kind == "cycle":
            self.arena.charge(2)
            self.arena.charge_bits(
                12 * payload.value.bit_length()
                + 6 * node.cycles.bit_length()
                + 4 * node.steps.bit_length()
            )
            ports = self._authenticated_cycle_ports(
                node,
                source,
                malformed_message="comma image lost its authenticated sector ports",
            )
            if ports is None or node.cycles < 1:
                raise ValueError("comma powered action has another phase coset")
            leading, digit, headroom = ports
            # Validate seam safety at the actual receiving phase. The complete
            # orbit's total displacement and maximum guard are invariant under
            # rotation within this gcd coset, while source authority remains
            # bound to the exact image above.
            transfer = self.arena.transfer(node.leading, digit)
            if (
                node.steps != node.cycles * transfer.period
                or node.displacement != node.cycles * transfer.displacement
                or node.maximum_guard != node.displacement + int(node.leading < 9)
                or safe_complete_cycles_from_sector(
                    leading, digit, headroom, transfer, node.steps
                )
                < node.cycles
            ):
                raise ValueError("comma powered action crosses an unadmitted seam")
            value = payload.value + node.displacement
            output_headroom = headroom - node.displacement
            if output_headroom <= int(leading < 9):
                raise ValueError("comma powered output lost its strict seam margin")
            output_ports = (leading, digit, output_headroom)
            self.ledger.bump(_comma_keys.COMMA_PHASE_CYCLES, node.cycles)
            self.ledger.bump(_comma_keys.COMMA_POWERED_IMAGE_APPLICATIONS)
        else:
            raise ValueError("composite comma action needs chronological children")
        self.ledger.bump(_comma_keys.COMMA_OPERAND_BIT_WORK, value.bit_length())
        if output_ports is not None:
            self.arena.charge_bits(
                value.bit_length()
                + payload.absolute_index.bit_length()
                + node.steps.bit_length()
            )
            return SourceImageCandidate(
                CommaImagePayload(
                    value,
                    payload.absolute_index + node.steps,
                    payload.certificate_version,
                ),
                source.binding.extent + node.steps,
                output_ports,
                radix=10,
            )
        return self._candidate(
            value,
            payload.absolute_index + node.steps,
            source.binding.extent + node.steps,
        )

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        self._require_open_owner()
        node = self.arena.node(cast(CommaActionID, action))
        boundary_template = (
            self.arena.boundary_template(node.boundary_source)
            if node.kind == "global-boundary-return"
            and node.boundary_source is not None
            else None
        )
        candidate = self._apply(node, source, boundary_template=boundary_template)
        self.validate_action_result(
            node,
            cast(CommaImagePayload, source.payload),
            source.binding.extent,
            cast(CommaImagePayload, candidate.payload),
            candidate.extent,
            candidate.boundary_ports,
            template=boundary_template,
        )
        return candidate

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
        self._require_open_owner()
        del demand
        node = self.arena.node(cast(CommaActionID, action))
        return self._apply(node, source) if node.kind == "cycle" else None

    def compose_chronological(
        self,
        action: Hashable,
        source: SourceImageView,
        before: SourceImageView,
        after: SourceImageView,
    ) -> SourceImageCandidate:
        self._require_open_owner()
        node = self.arena.node(cast(CommaActionID, action))
        if node.kind == "sequence":
            initial = cast(CommaImagePayload, source.payload)
            midpoint = cast(CommaImagePayload, before.payload)
            terminal = cast(CommaImagePayload, after.payload)
            if (
                node.before is None
                or node.after is None
                or midpoint.absolute_index
                != initial.absolute_index + self.arena.node(node.before).steps
                or terminal.absolute_index != initial.absolute_index + node.steps
                or after.binding.action != action
            ):
                raise ValueError("comma chronological children have another action")
            return SourceImageCandidate(
                terminal,
                after.binding.extent,
                after.binding.boundary_ports,
                radix=10,
            )
        del before
        expected = self._apply(node, source)
        if expected.payload != after.payload:
            raise ValueError("comma chronological image disagrees with transfer")
        return expected

    def admitted_input_key(
        self, action: Hashable, source: SourceImageView
    ) -> tuple[str, int, int, str] | None:
        """Share a completed interior phase only after checking this source.

        The source-image core includes the exact action and adapter version in
        its relative key.  The relative state adds the source's phase and
        certificate binding.  A different headroom is admitted only after the
        complete cycle's strict seam guard has been checked at that source.
        """
        self._require_open_owner()
        node = self.arena.node(cast(CommaActionID, action))
        if node.kind != "cycle":
            return None
        payload = cast(CommaImagePayload, source.payload)
        ports = self._authenticated_cycle_ports(
            node,
            source,
            malformed_message="comma image lost its authenticated sector ports",
        )
        if ports is None:
            return None
        leading, digit, headroom = ports
        phase_class = gcd(node.leading, 10)
        self.arena.charge()
        self.arena.charge_bits(
            leading.bit_length()
            + digit.bit_length()
            + headroom.bit_length()
            + node.maximum_guard.bit_length()
            + len(payload.certificate_version) * 8
        )
        self.ledger.bump(_comma_keys.COMMA_RELATIVE_GUARD_CHECKS)
        # The action's normalized maximum guard covers every chronological
        # phase prefix.  A source admits the whole action exactly when the
        # strict interior margin remains positive.
        if node.cycles < 1 or headroom <= node.maximum_guard:
            return None
        return (
            payload.certificate_version,
            leading,
            digit % phase_class,
            STRICT_INTERIOR_CYCLE_CONSUMER_TAG,
        )

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        self._require_open_owner()
        node = self.arena.node(cast(CommaActionID, action))
        if node.kind != "cycle":
            raise ValueError("comma relative transport requires an interior cycle")
        cached_payload = cast(CommaImagePayload, cached_source.payload)
        result_payload = cast(CommaImagePayload, cached_result.payload)
        payload = cast(CommaImagePayload, source.payload)
        source_ports = self._authenticated_cycle_ports(
            node,
            source,
            malformed_message="comma relative transfer lost authenticated ports",
        )
        cached_ports = self._authenticated_cycle_ports(
            node,
            cached_source,
            malformed_message="comma relative transfer lost authenticated ports",
        )
        if source_ports is None or cached_ports is None:
            raise ValueError("comma relative cycle has another source or effect")
        source_leading, source_digit, source_headroom = source_ports
        cached_leading, cached_digit, cached_headroom = cached_ports
        cached_output_headroom = cached_headroom - node.displacement
        # The scheduler has authenticated both relative input keys immediately
        # before this hook. Check the compact source binding again without
        # rediscovering either decimal scale.
        if (
            source_headroom <= node.maximum_guard
            or cached_headroom <= node.maximum_guard
            or cached_output_headroom <= int(node.leading < 9)
            or cached_result.binding.boundary_ports
            != (cached_leading, cached_digit, cached_output_headroom)
            or payload.certificate_version != cached_payload.certificate_version
            or result_payload.value != cached_payload.value + node.displacement
            or result_payload.absolute_index
            != cached_payload.absolute_index + node.steps
            or cached_result.binding.extent != cached_source.binding.extent + node.steps
        ):
            raise ValueError("comma relative cycle has another source or effect")
        value = payload.value + node.displacement
        self.ledger.bump(_comma_keys.COMMA_RELATIVE_CYCLE_REBINDINGS)
        self.ledger.bump(_comma_keys.COMMA_PHASE_CYCLES, node.cycles)
        self.ledger.bump(_comma_keys.COMMA_POWERED_IMAGE_APPLICATIONS)
        output_headroom = source_headroom - node.displacement
        if output_headroom <= int(node.leading < 9):
            raise ValueError("comma relative result lost its strict seam margin")
        self.arena.charge_bits(
            value.bit_length()
            + payload.absolute_index.bit_length()
            + node.steps.bit_length()
            + output_headroom.bit_length()
        )
        return SourceImageCandidate(
            CommaImagePayload(
                value,
                payload.absolute_index + node.steps,
                payload.certificate_version,
            ),
            source.binding.extent + node.steps,
            (source_leading, source_digit, output_headroom),
            radix=10,
        )

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
        self._require_open_owner()
        payload = cast(CommaImagePayload, image.payload)
        if demand.name == "value" and not demand.parameters:
            return SourceImageProjection(payload.value)
        if demand.name == "width" and not demand.parameters:
            self.arena.charge_bits(3 * payload.value.bit_length())
            return SourceImageProjection(decimal_sector(payload.value).exponent + 1)
        if demand.name == "digit" and len(demand.parameters) == 1:
            position = demand.parameters[0]
            if type(position) is int and position >= 0:
                self.arena.charge_bits(3 * payload.value.bit_length())
                if position > decimal_sector(payload.value).exponent:
                    return SourceImageProjection(0)
                self.arena.charge_bits(payload.value.bit_length())
                return SourceImageProjection(payload.value // pow(10, position) % 10)
        raise ValueError("unsupported comma source-image demand")

    def first_failure(self, image: SourceImageView) -> None:
        del image
