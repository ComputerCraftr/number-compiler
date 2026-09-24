"""Source-bound powered comma arithmetic on the shared TileScheduler."""

from __future__ import annotations

from collections.abc import Generator, Hashable
from dataclasses import dataclass
from typing import cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.arithmetic.fields.consumer_pullback import PrefixSafety
from number_compiler.arithmetic.fields.radix import iter_digits_lsd
from number_compiler.hashlife.execution.source_bound_images import (
    SourceBoundImageAdapter,
    SourceImageCandidate,
    SourceImageDemand,
    SourceImageID,
    SourceImageProjection,
    SourceImageView,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.comma.arithmetic import (
    _large_sector_children,
    comma_children,
    decimal_sector,
    safe_complete_cycles,
)
from number_compiler.sequences.comma.action_arena import (
    CommaActionArena,
    CommaActionID,
    _Action,
)
from number_compiler.sequences.comma.boundary_quotient import PERIOD

SEMANTIC_VERSION = "comma-source-cylinder-v2"
SOURCE = 20
FIRST_FORK_VALUE = 19_999_999_918
# Independently checked by full nine-candidate literal enumeration. OEIS and
# the paper label this value 412,987,860; their label is one greater than the
# literal one-based count and is not used as an admission rule.
FIRST_FORK_INDEX = 412_987_859


class UnresolvedCommaBranch(ValueError):
    """The next term requires certified infinite-future branch selection."""


@dataclass(frozen=True, slots=True)
class CommaOccurrenceID(ArenaHandle):
    """Source authority for one completed image without recursive ID nesting."""


@dataclass(frozen=True, slots=True)
class _Occurrence:
    image: SourceImageID
    value: int
    absolute_index: int
    certificate_version: str


@dataclass(frozen=True, slots=True)
class CommaSource:
    value: int
    certificate_version: str = "uncertified-arithmetic"


@dataclass(frozen=True, slots=True)
class CommaImagePayload:
    value: int
    absolute_index: int
    certificate_version: str = "uncertified-arithmetic"


class _CommaImageAdapter(SourceBoundImageAdapter):
    family = "a367620"
    semantic_version = SEMANTIC_VERSION

    def __init__(self, arena: CommaActionArena, scheduler: TileScheduler) -> None:
        self.arena = arena
        self.scheduler = scheduler
        self.ledger = arena.ledger
        self._term: CommaTerm | None = None

    def validate_source(self, source: Hashable) -> None:
        self.arena.charge()
        if type(source) is CommaSource:
            owner = self._term
            if (
                owner is None
                or type(source.value) is not int
                or source.value != SOURCE
                or source.certificate_version != owner.certificate_version
            ):
                raise ValueError("comma source is not the authenticated root 20")
            return
        if type(source) is CommaOccurrenceID:
            self._occurrence_payload(source)
            return
        if type(source) is SourceImageID:
            record = self.scheduler._source_image_core().resolve(source)
            if (
                record.binding.family != self.family
                or record.binding.semantic_version != self.semantic_version
            ):
                raise ValueError("comma provider image is foreign")
            self.validate_payload(record.payload)
            return
        raise TypeError("comma source requires root 20 or an admitted image")

    def validate_action(self, action: Hashable) -> None:
        self.arena.charge()
        self.arena.node(cast(CommaActionID, action))

    def validate_payload(self, payload: Hashable) -> None:
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

    def identity_action(self, source: Hashable) -> CommaActionID:
        self.validate_source(source)
        return self.arena.identity

    def action_children(
        self, action: Hashable
    ) -> tuple[CommaActionID, CommaActionID] | None:
        node = self.arena.node(cast(CommaActionID, action))
        if node.before is None or node.after is None:
            return None
        return node.before, node.after

    def compose_actions(self, before: Hashable, after: Hashable) -> CommaActionID:
        return self.arena.compose(
            cast(CommaActionID, before), cast(CommaActionID, after)
        )

    def _source_payload(self, source: Hashable) -> CommaImagePayload:
        self.validate_source(source)
        if type(source) is CommaSource:
            return CommaImagePayload(source.value, 1, source.certificate_version)
        if type(source) is SourceImageID:
            record = self.scheduler._source_image_core().resolve(source)
            return cast(CommaImagePayload, record.payload)
        return self._occurrence_payload(cast(CommaOccurrenceID, source))

    def _occurrence_payload(self, source: CommaOccurrenceID) -> CommaImagePayload:
        owner = self._term
        if owner is None:
            raise ValueError("comma adapter has no source owner")
        source.validate(
            owner._occurrence_token,
            owner._occurrence_kind,
            size=len(owner._occurrences),
        )
        if source.local_id >= len(owner._occurrence_seals):
            raise ValueError("comma occurrence has no publication seal")
        record = owner._occurrences[source.local_id]
        if record is not owner._occurrence_seals[source.local_id]:
            raise ValueError("comma occurrence publication was altered")
        image = self.scheduler._source_image_core().resolve(record.image)
        if (
            image.binding.family != self.family
            or image.binding.semantic_version != self.semantic_version
            or record.certificate_version != owner.certificate_version
            or image.payload
            != CommaImagePayload(
                record.value, record.absolute_index, record.certificate_version
            )
        ):
            raise ValueError("comma occurrence lost its completed provider image")
        return CommaImagePayload(
            record.value, record.absolute_index, record.certificate_version
        )

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

    def admit_source(self, source: Hashable) -> SourceImageCandidate:
        payload = self._source_payload(source)
        return self._candidate(payload.value, payload.absolute_index, 0)

    def _apply(self, node: _Action, source: SourceImageView) -> SourceImageCandidate:
        payload = cast(CommaImagePayload, source.payload)
        if node.kind == "identity":
            return self._candidate(
                payload.value, payload.absolute_index, source.binding.extent
            )
        if node.kind == "boundary-prefix":
            state = node.boundary_source
            if state is None or node.boundary_exponent < 5:
                raise ValueError("comma boundary action is incomplete")
            representative = state.exponent_residue
            if representative < 5:
                representative += PERIOD
            if node.boundary_exponent != representative:
                raise ValueError("comma boundary lifting is not yet admitted")
            expected = state.value(
                node.boundary_exponent, charge_bits=self.arena.charge_bits
            )
            if payload.value != expected:
                raise ValueError("comma boundary action has another source occurrence")
            template = self.arena._boundary_template(state)
            value = template.point(
                node.boundary_exponent,
                node.steps,
                charge=self.arena.charge,
                charge_bits=self.arena.charge_bits,
                validate_read=self.arena._boundary_read_guard(state, template),
            )
            self.ledger.bump("comma_boundary_prefix_applications")
            self.ledger.bump("comma_boundary_represented_transitions", node.steps)
        elif node.kind == "step":
            self.ledger.bump("comma_evaluated_transitions")
            sector = decimal_sector(payload.value)
            if sector.exponent < 2:
                self.arena.charge(9)
                self.arena.charge_bits(18 * payload.value.bit_length())
                children = comma_children(payload.value)
                self.ledger.bump("comma_child_candidate_checks", 9)
            else:
                self.arena.charge(2)
                self.arena.charge_bits(4 * payload.value.bit_length())
                children = _large_sector_children(payload.value, sector)
                self.ledger.bump("comma_seam_predicate_checks", 2)
            if not children:
                raise UnresolvedCommaBranch(
                    f"comma landmine at index {payload.absolute_index} has no child"
                )
            owner = self._term
            if owner is None:
                raise ValueError("comma adapter has no source owner")
            value = (
                children[0]
                if len(children) == 1
                else owner._certified_fork_child(
                    payload.absolute_index, payload.value, children
                )
            )
            if value - payload.value != 10 * (payload.value % 10) + node.child_digit:
                raise ValueError("comma action selected another child")
            self.ledger.bump("comma_scalar_seam_steps")
        elif node.kind == "cycle":
            self.arena.charge(2)
            self.arena.charge_bits(
                12 * payload.value.bit_length()
                + 6 * node.cycles.bit_length()
                + 4 * node.steps.bit_length()
            )
            transfer = self.arena.transfer(node.leading, node.entering_digit)
            safety = PrefixSafety(
                -transfer.displacement, -transfer.maximum_guard
            ).repeat(node.cycles)
            if (
                node.steps != node.cycles * transfer.period
                or node.displacement != -safety.delta
                or node.maximum_guard != -safety.minimum
                or safe_complete_cycles(payload.value, transfer, node.steps)
                < node.cycles
            ):
                raise ValueError("comma powered action crosses an unadmitted seam")
            value = payload.value + node.displacement
            self.ledger.bump("comma_phase_cycles", node.cycles)
            self.ledger.bump("comma_powered_image_applications")
        else:
            raise ValueError("composite comma action needs chronological children")
        self.ledger.bump("comma_operand_bit_work", value.bit_length())
        return self._candidate(
            value,
            payload.absolute_index + node.steps,
            source.binding.extent + node.steps,
        )

    def apply_primitive(
        self, action: Hashable, source: SourceImageView
    ) -> SourceImageCandidate:
        return self._apply(self.arena.node(cast(CommaActionID, action)), source)

    def apply_composite(
        self,
        action: Hashable,
        source: SourceImageView,
        demand: SourceImageDemand | None,
    ) -> SourceImageCandidate | None:
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
        node = self.arena.node(cast(CommaActionID, action))
        if node.kind != "cycle":
            return None
        payload = cast(CommaImagePayload, source.payload)
        self.arena.charge_bits(3 * payload.value.bit_length())
        sector = decimal_sector(payload.value)
        if sector.leading != node.leading or sector.digit != node.entering_digit:
            return None
        self.arena.charge()
        self.arena.charge_bits(
            sector.headroom.bit_length() + node.maximum_guard.bit_length()
        )
        self.ledger.bump("comma_relative_guard_checks")
        # The action's normalized maximum guard covers every chronological
        # phase prefix.  A source admits the whole action exactly when the
        # strict interior margin remains positive.
        if node.cycles < 1 or sector.headroom <= node.maximum_guard:
            return None
        return (
            payload.certificate_version,
            sector.leading,
            sector.digit,
            "strict-interior-cycle-v1",
        )

    def transport_reuse(
        self,
        action: Hashable,
        cached_source: SourceImageView,
        cached_result: SourceImageView,
        source: SourceImageView,
    ) -> SourceImageCandidate:
        node = self.arena.node(cast(CommaActionID, action))
        if node.kind != "cycle":
            raise ValueError("comma relative transport requires an interior cycle")
        cached_payload = cast(CommaImagePayload, cached_source.payload)
        result_payload = cast(CommaImagePayload, cached_result.payload)
        payload = cast(CommaImagePayload, source.payload)
        admitted = self.admitted_input_key(action, source)
        if (
            admitted is None
            or admitted != self.admitted_input_key(action, cached_source)
            or result_payload.value != cached_payload.value + node.displacement
            or result_payload.absolute_index
            != cached_payload.absolute_index + node.steps
            or cached_result.binding.extent != cached_source.binding.extent + node.steps
        ):
            raise ValueError("comma relative cycle has another source or effect")
        value = payload.value + node.displacement
        self.ledger.bump("comma_relative_cycle_rebindings")
        self.ledger.bump("comma_phase_cycles", node.cycles)
        self.ledger.bump("comma_powered_image_applications")
        self.arena.charge_bits(value.bit_length())
        return self._candidate(
            value,
            payload.absolute_index + node.steps,
            source.binding.extent + node.steps,
        )

    def project(
        self, image: SourceImageView, demand: SourceImageDemand
    ) -> SourceImageProjection:
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
        return None


class CommaTerm:
    """One source-20 unique-prefix term, with exact weighted sector jumps.

    This arithmetic owner does not certify that root 20 has an infinite path.
    The public API must require a checked prefix certificate before exposing
    any value as OEIS A367620.
    """

    def __init__(
        self,
        index: int,
        *,
        max_states: int = 131_072,
        max_work: int = 1_000_000,
        max_context_nodes: int | None = None,
        max_cache_entries: int | None = None,
        certificate_version: str = "uncertified-arithmetic",
        shared_cache: bool = True,
    ) -> None:
        if type(index) is not int or index < 1:
            raise ValueError("A367620 uses one-based indices beginning at 1")
        if type(max_states) is not int or max_states < 1:
            raise ValueError("--max-comma-states must be positive")
        if type(max_work) is not int or max_work < 1:
            raise ValueError("--max-comma-work must be positive")
        if type(certificate_version) is not str or not certificate_version:
            raise ValueError("comma certificate binding must be nonempty")
        if type(shared_cache) is not bool:
            raise ValueError("comma shared-cache selection must be boolean")
        if max_context_nodes is not None and (
            type(max_context_nodes) is not int or max_context_nodes < 1
        ):
            raise ValueError("comma context node budget must be positive")
        if max_cache_entries is not None and (
            type(max_cache_entries) is not int or max_cache_entries < 1
        ):
            raise ValueError("comma cache entry budget must be positive")
        self.index = index
        self.max_states = max_states
        self.max_work = max_work
        self.certificate_version = certificate_version
        self.shared_cache = shared_cache
        self.ledger = ResourceLedger(
            max_nodes=min(
                max_states,
                max_context_nodes if max_context_nodes is not None else max_states,
            ),
            max_cache_entries=min(
                max_states,
                max_cache_entries if max_cache_entries is not None else max_states,
            ),
        )
        from number_compiler.sequences.comma.certificates import new_certificate_memo

        self.certificate_memo = new_certificate_memo(self.ledger)
        self.arena = CommaActionArena(self.ledger, max_work)
        self.scheduler = TileScheduler.source_only(self.ledger)
        self.adapter = _CommaImageAdapter(self.arena, self.scheduler)
        self.adapter._term = self
        self.scheduler.register_source_image_adapter(self.adapter)
        self._image: SourceImageID | None = None
        self._source: CommaSource | CommaOccurrenceID = CommaSource(
            SOURCE, certificate_version
        )
        self._occurrence_token = ArenaToken("comma-occurrences")
        self._occurrence_kind = "comma-occurrence"
        self._occurrence_owner = self.ledger.register(
            "comma-occurrences", "source_occurrence"
        )
        self._occurrences: LedgerList[_Occurrence] = self.ledger.make_list(
            self._occurrence_owner, append_only=False
        )
        self._occurrence_seal_owner = self.ledger.register(
            "comma-occurrence-seals", "source_occurrence_seal"
        )
        self._occurrence_seals: LedgerList[_Occurrence] = self.ledger.make_list(
            self._occurrence_seal_owner, append_only=False
        )
        self._value: int | None = None
        self._current_value = SOURCE
        self._current_index = 1

    @property
    def maximum_value(self) -> int:
        return SOURCE + 99 * (self.index - 1)

    @property
    def estimated_bit_length(self) -> int:
        return self.maximum_value.bit_length()

    def _charge(self, amount: int = 1) -> None:
        self.arena.charge(amount)

    def _certified_fork_child(
        self, source_index: int, source_value: int, children: tuple[int, ...]
    ) -> int:
        """Demand an independently checked, source-bound branch choice.

        Arithmetic never treats the smallest child, fixture data, or a
        caller-provided selector as evidence of an infinite continuation.
        """
        if self.certificate_version == "uncertified-arithmetic":
            raise UnresolvedCommaBranch(
                f"comma branch at index {source_index} requires a certificate"
            )
        from number_compiler.sequences.comma.certificates import (
            require_selected_child,
        )

        child = require_selected_child(
            source_index=source_index,
            source_value=source_value,
            children=children,
            certificate_version=self.certificate_version,
            ledger=self.ledger,
            max_work=self.max_work,
            shared_cache=self.shared_cache,
            memo=self.certificate_memo,
        )
        if type(child) is not int or child not in children:
            raise ValueError("comma certificate selected a non-child")
        return child

    def _publish(self, action: CommaActionID) -> int:
        self._charge()
        if self.adapter._source_payload(self._source) != CommaImagePayload(
            self._current_value, self._current_index, self.certificate_version
        ):
            raise ValueError("comma query source differs from its admitted occurrence")
        self.ledger.reserve_many(
            (
                (self._occurrence_owner, 1, 1),
                (self._occurrence_seal_owner, 1, 1),
            )
        )
        try:
            image = self.scheduler.source_image(self.adapter, self._source, action)
            payload = cast(
                CommaImagePayload,
                self.scheduler._source_image_core().view(image).payload,
            )
            next_source = CommaOccurrenceID(
                self._occurrence_token,
                self._occurrence_kind,
                len(self._occurrences),
            )
            record = _Occurrence(
                image, payload.value, payload.absolute_index, self.certificate_version
            )
            self._occurrences.append(record)
            self._occurrence_seals.append(record)
        except BaseException:
            if len(self._occurrence_seals) > len(self._occurrences):
                self._occurrence_seals.pop()
            if len(self._occurrences) > len(self._occurrence_seals):
                self._occurrences.pop()
            self.ledger.release(self._occurrence_owner, entries=1, nodes=1)
            self.ledger.release(self._occurrence_seal_owner, entries=1, nodes=1)
            raise
        self._source = next_source
        self._image = image
        # Successful query progress differs from an evaluated image whose
        # projection/publication subsequently exhausted its budget.
        self.ledger.bump(
            "comma_represented_transitions",
            payload.absolute_index - self._current_index,
        )
        self._current_value = payload.value
        self._current_index = payload.absolute_index
        return payload.value

    def _resolve(self) -> int:
        if self._value is not None:
            return self._value
        value = self._current_value
        remaining = self.index - self._current_index
        while remaining:
            self._charge()
            self.arena.charge_bits(8 * value.bit_length() + 4 * remaining.bit_length())
            sector = decimal_sector(value)
            transfer = self.arena.transfer(sector.leading, sector.digit)
            cycles = safe_complete_cycles(value, transfer, remaining)
            if cycles:
                action = self.arena.cycles(sector.leading, sector.digit, cycles)
                value = self._publish(action)
                remaining -= cycles * transfer.period
                continue
            if sector.exponent < 2:
                self._charge(9)
                self.arena.charge_bits(18 * value.bit_length())
                children = comma_children(value)
                self.ledger.bump("comma_child_candidate_checks", 9)
            else:
                self._charge(2)
                self.arena.charge_bits(4 * value.bit_length())
                children = _large_sector_children(value, sector)
                self.ledger.bump("comma_seam_predicate_checks", 2)
            if not children:
                raise UnresolvedCommaBranch(
                    f"comma source 20 reaches a landmine at value {value} "
                    f"before index {self.index}"
                )
            child = (
                children[0]
                if len(children) == 1
                else self._certified_fork_child(self._current_index, value, children)
            )
            action = self.arena.step(child - value - 10 * sector.digit)
            value = self._publish(action)
            remaining -= 1
        self._value = value
        return value

    def materialize(self, *, max_bits: int | None = None) -> int:
        value = self._resolve()
        if max_bits is not None and value.bit_length() > max_bits:
            raise ValueError(f"output exceeds --max-output-bits ({max_bits})")
        return value

    def width(self) -> int:
        value = self._resolve()
        self.arena.charge_bits(3 * value.bit_length())
        return decimal_sector(value).exponent + 1

    def digit(self, position: int) -> int:
        if type(position) is not int or position < 0:
            raise ValueError("comma digit position must be nonnegative")
        value = self._resolve()
        self.arena.charge_bits(3 * value.bit_length())
        if position > decimal_sector(value).exponent:
            return 0
        if self._image is None:
            divisor: int = pow(10, position)
            return SOURCE // divisor % 10
        return cast(
            int,
            self.scheduler.source_projection(
                self.adapter, self._image, SourceImageDemand("digit", (position,))
            ).value,
        )

    def iter_digits(self) -> Generator[int, None, None]:
        value = self._resolve()
        self.ledger.bump("comma_stream_requests")

        def workspace(slots: int, bits: int) -> None:
            for name, current in (
                ("comma_stream_workspace_peak_slots", slots),
                ("comma_stream_workspace_peak_integer_bits", bits),
            ):
                peak = self.ledger.counters.get(name, 0)
                if current > peak:
                    self.ledger.bump(name, current - peak)

        stream = iter_digits_lsd(
            value,
            10,
            charge=self.arena.charge,
            charge_bits=self.arena.charge_bits,
            observe_workspace=workspace,
        )
        try:
            for digit in stream:
                self.ledger.bump("comma_stream_emitted_digits")
                yield digit
        finally:
            stream.close()

    def clock(self) -> dict[str, int]:
        value = self._resolve()
        self.arena.charge_bits(3 * value.bit_length())
        sector = decimal_sector(value)
        return {
            "represented_transitions": self.index - 1,
            "phase_cycles": self.ledger.counters.get("comma_phase_cycles", 0),
            "seam_steps": self.ledger.counters.get("comma_scalar_seam_steps", 0),
            "leading_digit": sector.leading,
            "digit_phase": sector.digit,
            "headroom": sector.headroom,
        }

    def tropical(self) -> dict[str, int | str]:
        value = self._resolve()
        self.arena.charge_bits(3 * value.bit_length())
        sector = decimal_sector(value)
        digit = sector.digit
        if sector.leading == 9:
            return {
                "seam_kind": "power_of_ten_landmine",
                "headroom": sector.headroom,
                "lower_margin": sector.headroom - (10 * digit + 1),
                "upper_margin": sector.headroom - (10 * digit + 9),
            }
        return {
            "seam_kind": "next_leading_digit_fork",
            "headroom": sector.headroom,
            "margin": sector.headroom - (10 * digit + sector.leading + 1),
        }


__all__ = [
    "CommaTerm",
    "FIRST_FORK_INDEX",
    "FIRST_FORK_VALUE",
    "SEMANTIC_VERSION",
    "SOURCE",
    "UnresolvedCommaBranch",
]
