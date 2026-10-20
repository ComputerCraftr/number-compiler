"""Source-bound powered comma arithmetic on the shared TileScheduler."""

from __future__ import annotations

from collections.abc import Generator, Sequence
from dataclasses import dataclass
from importlib.resources import as_file, files
from pathlib import Path
from threading import RLock
from typing import TYPE_CHECKING, Self, cast

from number_compiler.arithmetic.contracts.input_validation import is_runtime_instance
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.arithmetic.fields.radix import iter_digits_lsd
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageDemand,
    SourceImageID,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.output_stream_metrics import (
    initialize_output_stream_metrics,
    measured_output_stream,
)
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.comma.action_arena import (
    CommaActionArena,
    CommaActionArenaAuditSnapshot,
    CommaActionID,
)
from number_compiler.sequences.comma.arithmetic import (
    classify_near_port,
    comma_children,
    decimal_sector,
    large_sector_children,
    safe_complete_cycles_from_sector,
)
from number_compiler.sequences.comma.future_authority import (
    SOURCE20_FIRST_FORK_INDEX as FIRST_FORK_INDEX,
)
from number_compiler.sequences.comma.future_authority import (
    SOURCE20_FIRST_FORK_VALUE as FIRST_FORK_VALUE,
)
from number_compiler.sequences.comma.image_adapter import (
    SEMANTIC_VERSION,
    SOURCE,
    BoundaryPrefixCursor,
    CommaImageAdapter,
    CommaImagePayload,
    CommaOccurrenceID,
    CommaSource,
    UnresolvedCommaBranch,
)

if TYPE_CHECKING:
    from number_compiler.sequences.comma.future_provider import (
        SemanticFutureProviderLease,
        SemanticFutureProviderStore,
    )


@dataclass(frozen=True, slots=True)
class CommaOccurrenceRecord:
    image: SourceImageID
    value: int
    absolute_index: int
    certificate_version: str
    boundary_cursor: BoundaryPrefixCursor | None = None


@dataclass(frozen=True, slots=True)
class CommaTermPayloadAuditSnapshot:
    """Read-only occurrence and action payload views owned by one term."""

    arena: CommaActionArenaAuditSnapshot
    occurrence_token: ArenaToken
    occurrence_kind: str
    occurrence_owner: int
    occurrence_seal_owner: int
    occurrences: Sequence[CommaOccurrenceRecord]
    occurrence_seals: Sequence[CommaOccurrenceRecord]
    stores_owned: bool


class CommaTerm:
    """One source-20 unique-prefix term, with exact weighted sector jumps.

    This arithmetic owner does not certify that root 20 has an infinite path.
    The public API must require a checked prefix certificate before exposing
    any value as OEIS A367620.
    """

    index: int
    max_states: int
    max_work: int
    certificate_version: str
    shared_cache: bool
    ledger: ResourceLedger
    arena: CommaActionArena
    scheduler: TileScheduler
    adapter: CommaImageAdapter
    _current_index: int
    _current_value: int

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
        initialize_output_stream_metrics(self.ledger, "comma_stream")
        from number_compiler.sequences.comma.certificates import new_certificate_memo

        self.certificate_memo = new_certificate_memo(self.ledger)
        self.arena = CommaActionArena(self.ledger, max_work, shared_cache=shared_cache)
        self._future_provider_store: SemanticFutureProviderStore | None = None
        self._future_provider_lease: SemanticFutureProviderLease | None = None
        self._future_provider_lock = RLock()
        self.scheduler = TileScheduler.source_only(self.ledger)
        self.adapter = CommaImageAdapter(self.arena, self.scheduler)
        self.adapter.bind_owner(self)
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
        self._occurrences: LedgerList[CommaOccurrenceRecord] = self.ledger.make_list(
            self._occurrence_owner, append_only=False
        )
        self._occurrence_seal_owner = self.ledger.register(
            "comma-occurrence-seals", "source_occurrence_seal"
        )
        self._occurrence_seals: LedgerList[CommaOccurrenceRecord] = (
            self.ledger.make_list(self._occurrence_seal_owner, append_only=False)
        )
        self.arena.bind_payload_audit_root(self)
        self._audit_occurrences = self._occurrences
        self._audit_occurrence_seals = self._occurrence_seals
        from number_compiler.sequences.comma.payload_audit import (
            register_comma_term_audit,
        )

        register_comma_term_audit(self)
        self._value: int | None = None
        self._current_value = SOURCE
        self._current_index = 1
        self._boundary_occurrence: object | None = None
        self._boundary_occurrence_owner: CommaOccurrenceID | None = None

    def occurrence_record(self, source: CommaOccurrenceID) -> CommaOccurrenceRecord:
        """Return one occurrence only after its arena authority and seal agree."""
        source.validate(
            self._occurrence_token,
            self._occurrence_kind,
            size=len(self._occurrences),
        )
        if source.local_id >= len(self._occurrence_seals):
            raise ValueError("comma occurrence has no publication seal")
        record = self._occurrences[source.local_id]
        if record is not self._occurrence_seals[source.local_id]:
            raise ValueError("comma occurrence publication was altered")
        return record

    def audit_snapshot(self) -> CommaTermPayloadAuditSnapshot:
        """Expose exact retained stores through read-only audit views."""
        stores_owned = (
            self.arena.payload_audit_root_is_bound(self)
            and self._audit_occurrences is self._occurrences
            and self._audit_occurrence_seals is self._occurrence_seals
        )
        return CommaTermPayloadAuditSnapshot(
            arena=self.arena.audit_snapshot(),
            occurrence_token=self._occurrence_token,
            occurrence_kind=self._occurrence_kind,
            occurrence_owner=self._occurrence_owner,
            occurrence_seal_owner=self._occurrence_seal_owner,
            occurrences=self._occurrences.audit_view(),
            occurrence_seals=self._occurrence_seals.audit_view(),
            stores_owned=stores_owned,
        )

    def _stage_global_future_provider_artifact(self, artifact: Path) -> None:
        """Load a registered global provider before any query progress exists.

        The public prefix gate may consume this lease only after it rechecks the
        exact global-release contract. With no registered release artifact, the
        public path keeps using its finite forest/prefix certificate.
        """
        with self._future_provider_lock:
            self._stage_global_future_provider_artifact_locked(artifact)

    def _stage_global_future_provider_artifact_locked(self, artifact: Path) -> None:
        if not is_runtime_instance(artifact, Path):
            raise TypeError("comma future artifact must be a pathlib Path")
        if (
            self._future_provider_lease is not None
            or self._future_provider_store is not None
            or self._image is not None
            or self._current_index != 1
            or self._value is not None
        ):
            raise ValueError("comma provider staging is only allowed before use")
        from number_compiler.sequences.comma.future_provider import (
            SemanticFutureProviderStore,
        )

        store = SemanticFutureProviderStore(self.ledger)
        try:
            lease = store.load_file(artifact, charge_work=self.arena.charge)
            lease.require_global_release_admission()
        except BaseException:
            store.close()
            raise
        self._future_provider_store = store
        self._future_provider_lease = lease

    def _stage_registered_global_future_provider_locked(self) -> bool:
        """Stage only the package artifact named by an admitted exact digest.

        The empty production registry returns before resolving package
        resources, leaving the finite-prefix forest path untouched. A
        registered digest with missing or mismatched bytes fails closed.
        """
        from number_compiler.sequences.comma.future_provider import (
            FUTURE_PROVIDER_ASSET,
            registered_global_release_artifact_sha256,
        )

        expected_digest = registered_global_release_artifact_sha256()
        if expected_digest is None:
            if self._future_provider_store is not None:
                raise PermissionError("comma provider store has no registered lease")
            return False
        if self._future_provider_lease is not None:
            lease = self.require_global_future_provider()
            if lease.artifact_sha256 != expected_digest:
                raise PermissionError("comma provider lease differs from registry")
            return True
        if self._future_provider_store is not None:
            raise PermissionError("comma provider store has no registered lease")

        asset = files("number_compiler").joinpath("kernels", FUTURE_PROVIDER_ASSET)
        with as_file(asset) as artifact:
            self._stage_global_future_provider_artifact_locked(artifact)
        lease = self.require_global_future_provider()
        if lease.artifact_sha256 != expected_digest:
            self.close()
            raise PermissionError("comma provider artifact differs from registry")
        return True

    @property
    def has_global_future_provider(self) -> bool:
        lease = self._future_provider_lease
        if lease is None:
            return False
        try:
            self.require_global_future_provider()
            return True
        except (PermissionError, RuntimeError, TypeError):
            return False

    def global_future_provider_for_prefix_admission(
        self,
    ) -> SemanticFutureProviderLease | None:
        """Return only this term's lease after rechecking global authority."""
        with self._future_provider_lock:
            if (
                self._future_provider_lease is None
                and not self._stage_registered_global_future_provider_locked()
            ):
                return None
            return self.require_global_future_provider()

    def require_certified_public_prefix(self) -> None:
        """Authenticate the current public index against its release authority."""
        from number_compiler.sequences.comma.certificates import (
            CERTIFICATE_ID,
            UnresolvedCommaTerm,
            require_certified_index,
        )

        provider = self.global_future_provider_for_prefix_admission()
        if self.certificate_version != CERTIFICATE_ID and provider is None:
            raise UnresolvedCommaTerm(
                self.index, 0, CERTIFICATE_ID, "stale comma certificate binding"
            )
        require_certified_index(
            self.index,
            self.ledger,
            self.max_work,
            shared_cache=self.shared_cache,
            memo=self.certificate_memo,
            global_provider=provider,
        )

    @property
    def retained_global_future_provider(self) -> SemanticFutureProviderLease | None:
        """Return an already retained release lease without staging or charging."""
        from number_compiler.sequences.comma.future_provider import (
            registered_global_release_artifact_sha256,
        )

        with self._future_provider_lock:
            lease = self._future_provider_lease
            expected_digest = registered_global_release_artifact_sha256()
            if (
                lease is None
                or expected_digest is None
                or not lease.matches_global_release_binding(
                    self.ledger, expected_digest
                )
            ):
                return None
            return lease

    def require_global_future_provider(
        self, artifact_sha256: str | None = None
    ) -> SemanticFutureProviderLease:
        from number_compiler.sequences.comma.future_provider import (
            SemanticFutureProviderLease,
            SemanticFutureProviderStore,
        )

        lease = self._future_provider_lease
        if type(lease) is not SemanticFutureProviderLease:
            raise PermissionError("comma global future provider is not configured")
        store = self._future_provider_store
        if (
            type(store) is not SemanticFutureProviderStore
            or getattr(lease, "_store", None) is not store
            or getattr(store, "ledger", None) is not self.ledger
        ):
            raise PermissionError(
                "comma global future provider is not owned by this term"
            )
        lease.require_global_release_admission()
        if artifact_sha256 is not None and lease.artifact_sha256 != artifact_sha256:
            raise PermissionError("comma action belongs to another global artifact")
        return lease

    def close(self) -> None:
        """Release only the privately staged future-provider resources."""
        with self._future_provider_lock:
            store = self._future_provider_store
            if store is None:
                return
            store.close()
            self._future_provider_store = None
            self._future_provider_lease = None
            self._boundary_occurrence = None
            self._boundary_occurrence_owner = None

    def __enter__(self) -> Self:
        return self

    def __exit__(self, _exc_type: object, _exc: object, _tb: object) -> None:
        self.close()

    @property
    def maximum_value(self) -> int:
        return SOURCE + 99 * (self.index - 1)

    @property
    def estimated_bit_length(self) -> int:
        return self.maximum_value.bit_length()

    def _charge(self, amount: int = 1) -> None:
        self.arena.charge(amount)

    def certified_fork_child(
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

    def _publish(
        self,
        action: CommaActionID,
        *,
        next_boundary: object | None = None,
    ) -> int:
        self._charge()
        action_node = self.arena.node(action)
        if next_boundary is not None:
            from number_compiler.sequences.comma.occurrence import (
                BoundaryOccurrence,
            )

            if type(
                next_boundary
            ) is not BoundaryOccurrence or action_node.kind not in {
                "source20-first-child",
                "global-boundary-return",
            }:
                raise TypeError("only an admitted comma return can publish a boundary")
            next_boundary.validate()
            if action_node.kind == "global-boundary-return":
                source = self._boundary_occurrence
                if (
                    type(source) is not BoundaryOccurrence
                    or self._boundary_occurrence_owner is not self._source
                    or action_node.boundary_source != source.state
                    or action_node.boundary_target != next_boundary.state
                ):
                    raise ValueError("comma action and target occurrence disagree")
                template = self.arena.boundary_template(source.state)
                if next_boundary.exponent != source.exponent + template.exponent_delta:
                    raise ValueError("comma action changed its occurrence exponent")
            else:
                from number_compiler.sequences.comma.boundary_quotient import (
                    BoundaryState,
                )

                if (
                    next_boundary.state != BoundaryState("N", 2, 10)
                    or next_boundary.exponent != 10
                ):
                    raise ValueError("source-20 action has another boundary target")
        query_source = self.adapter.source_payload(self._source)
        if (
            query_source.value != self._current_value
            or query_source.absolute_index != self._current_index
            or query_source.certificate_version != self.certificate_version
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
                self.scheduler.source_image_core().view(image).payload,
            )
            next_source = CommaOccurrenceID(
                self._occurrence_token,
                self._occurrence_kind,
                len(self._occurrences),
            )
            record = CommaOccurrenceRecord(
                image,
                payload.value,
                payload.absolute_index,
                self.certificate_version,
                payload.boundary_cursor,
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
        self._boundary_occurrence = next_boundary
        self._boundary_occurrence_owner = (
            next_source if next_boundary is not None else None
        )
        # Successful query progress differs from an evaluated image whose
        # projection/publication subsequently exhausted its budget.
        self.ledger.bump(
            _comma_keys.COMMA_REPRESENTED_TRANSITIONS,
            payload.absolute_index - self._current_index,
        )
        self._current_value = payload.value
        self._current_index = payload.absolute_index
        return payload.value

    def _continue_boundary_occurrence(self, remaining: int) -> tuple[int, int]:
        """Consume one authenticated boundary prefix or complete guarded return."""
        from number_compiler.sequences.comma.occurrence import (
            BoundaryOccurrence,
        )

        source = self._boundary_occurrence
        if (
            type(source) is not BoundaryOccurrence
            or self._boundary_occurrence_owner is not self._source
        ):
            raise ValueError("comma boundary occurrence lost its source lease")
        source.validate()
        provider = self.require_global_future_provider()
        template = self.arena.boundary_template(source.state)
        prefix_steps = template.weight.evaluate(
            source.exponent,
            charge_bits=self.arena.charge_bits,
        )
        self.ledger.bump(_comma_keys.COMMA_BOUNDARY_WEIGHTED_LOCATOR_REQUESTS)
        if remaining <= prefix_steps:
            action = self.arena.boundary_prefix_occurrence(source, remaining)
            prior_index = self._current_index
            value = self._publish(action)
            consumed = self._current_index - prior_index
            if consumed != remaining:
                raise ValueError("comma partial boundary locator changed its weight")
            return value, 0
        if template.outcome != "fork":
            raise UnresolvedCommaBranch(
                f"comma boundary at index {self._current_index} is a landmine"
            )
        selection = provider.select_unique_unranked_child(
            source.state,
            charge_work=self.arena.charge,
        )
        from number_compiler.sequences.comma.future_provider import (
            UnrankedChildSelection,
        )
        from number_compiler.sequences.comma.semantic_branch import (
            validate_selection_class_bindings,
        )

        if type(selection) is not UnrankedChildSelection:
            raise ValueError("comma provider returned a malformed child selection")
        validate_selection_class_bindings(
            source.state,
            template.ordered_children,
            selection,
            provider,
            charge_work=self.arena.charge,
        )
        if (
            selection.source != source.state
            or selection.selected_slot not in (0, 1)
            or selection.fork_coefficient != template.destination_a
        ):
            raise ValueError("comma provider selected another macro control")
        target_state = template.ordered_children[selection.selected_slot]
        target = BoundaryOccurrence(
            target_state,
            source.exponent + template.exponent_delta,
        )
        action = self.arena.global_boundary_return(
            source.state,
            target_state,
            provider.artifact_sha256,
        )
        prior_index = self._current_index
        value = self._publish(action, next_boundary=target)
        consumed = self._current_index - prior_index
        if consumed != prefix_steps + 1 or consumed > remaining:
            raise ValueError("comma completed weighted return changed its extent")
        return value, remaining - consumed

    def resolve_index(self) -> int:
        if self._value is not None:
            return self._value
        value = self._current_value
        remaining = self.index - self._current_index
        while remaining:
            if self._boundary_occurrence is not None:
                value, remaining = self._continue_boundary_occurrence(remaining)
                continue
            self._charge()
            self.arena.charge_bits(8 * value.bit_length() + 4 * remaining.bit_length())
            sector = decimal_sector(value)
            transfer = self.arena.transfer(sector.leading, sector.digit)
            cycles = safe_complete_cycles_from_sector(
                sector.leading,
                sector.digit,
                sector.headroom,
                transfer,
                remaining,
            )
            if cycles:
                try:
                    action, reused = self.arena.cycle_request(
                        sector.leading, sector.digit, cycles
                    )
                    value = self._publish(action)
                except Exception:
                    self.ledger.bump(_comma_keys.COMMA_HASHLIFE_FAILED_WORK)
                    raise
                if reused:
                    self.arena.cycle_reuse.count("applied_hits")
                    if cycles > 1:
                        self.arena.cycle_reuse.count("applied_parent_hits")
                remaining -= cycles * transfer.period
                continue
            if (
                sector.exponent >= 2
                and sector.headroom
                > 10 * sector.digit + sector.leading + int(sector.leading < 9)
            ):
                port = classify_near_port(
                    sector.leading,
                    sector.headroom,
                    charge_work=self.arena.charge,
                    charge_bits=self.arena.charge_bits,
                )
                self.ledger.bump(_comma_keys.COMMA_PORT_CLASSIFICATIONS)
                self.ledger.bump(_comma_keys.COMMA_PORT_VISITS, port.port_visits)
                self.ledger.bump(
                    _comma_keys.COMMA_LOCATOR_COMPARISONS, port.locator_comparisons
                )
                steps = min(remaining, port.physical_steps)
                if steps:
                    action = self.arena.phase_prefix(
                        sector.leading, sector.digit, steps
                    )
                    value = self._publish(action)
                    remaining -= steps
                    continue
            if sector.exponent < 2:
                self._charge(9)
                self.arena.charge_bits(18 * value.bit_length())
                children = comma_children(value)
                self.ledger.bump(_comma_keys.COMMA_CHILD_CANDIDATE_CHECKS, 9)
            else:
                self._charge(2)
                self.arena.charge_bits(4 * value.bit_length())
                children = large_sector_children(value, sector)
                self.ledger.bump(_comma_keys.COMMA_SEAM_PREDICATE_CHECKS, 2)
            if not children:
                raise UnresolvedCommaBranch(
                    f"comma source 20 reaches a landmine at value {value} "
                    f"before index {self.index}"
                )
            if len(children) == 1:
                child = children[0]
            elif self._future_provider_lease is not None:
                from number_compiler.sequences.comma.boundary_quotient import (
                    BoundaryState,
                )
                from number_compiler.sequences.comma.future_authority import (
                    SOURCE20_FIRST_FORK_CHILDREN,
                    SOURCE20_FIRST_FORK_INDEX,
                    SOURCE20_FIRST_FORK_VALUE,
                    SOURCE20_SELECTED_CHILD_INDEX,
                )
                from number_compiler.sequences.comma.semantic_branch import (
                    bind_source20_first_child_entry,
                )

                provider = self.require_global_future_provider()
                if (
                    self._current_index != SOURCE20_FIRST_FORK_INDEX
                    or value != SOURCE20_FIRST_FORK_VALUE
                    or children != SOURCE20_FIRST_FORK_CHILDREN
                ):
                    raise UnresolvedCommaBranch(
                        "global comma provider has no admitted occurrence for this fork"
                    )
                entry = bind_source20_first_child_entry(
                    parent_index=self._current_index,
                    parent_value=value,
                    ordered_children=(children[0], children[1]),
                    child_index=SOURCE20_SELECTED_CHILD_INDEX,
                    provider=provider,
                    charge_work=self.arena.charge,
                    charge_bits=self.arena.charge_bits,
                )
                target = entry.weighted_source(
                    provider,
                    charge_work=self.arena.charge,
                )
                if target.state != BoundaryState("N", 2, 10) or target.exponent != 10:
                    raise ValueError("source-20 theorem returned another boundary")
                action = self.arena.source20_first_child(provider.artifact_sha256)
                prior_index = self._current_index
                value = self._publish(action, next_boundary=target)
                remaining -= self._current_index - prior_index
                continue
            else:
                child = self.certified_fork_child(self._current_index, value, children)
            action = self.arena.step(child - value - 10 * sector.digit)
            value = self._publish(action)
            remaining -= 1
        self._value = value
        return value

    def materialize(self, *, max_bits: int | None = None) -> int:
        value = self.resolve_index()
        if max_bits is not None and value.bit_length() > max_bits:
            raise ValueError(f"output exceeds --max-output-bits ({max_bits})")
        return value

    def width(self) -> int:
        value = self.resolve_index()
        self.arena.charge_bits(3 * value.bit_length())
        return decimal_sector(value).exponent + 1

    def digit(self, position: int) -> int:
        if type(position) is not int or position < 0:
            raise ValueError("comma digit position must be nonnegative")
        value = self.resolve_index()
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
        def source() -> Generator[int, None, None]:
            value = self.resolve_index()

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
                yield from stream
            finally:
                stream.close()

        return measured_output_stream(self.ledger, "comma_stream", source)

    def clock(self) -> dict[str, int]:
        value = self.resolve_index()
        self.arena.charge_bits(3 * value.bit_length())
        sector = decimal_sector(value)
        return {
            "represented_transitions": self.index - 1,
            "phase_cycles": self.ledger.counters.get(_comma_keys.COMMA_PHASE_CYCLES, 0),
            "phase_prefix_transitions": self.ledger.counters.get(
                _comma_keys.COMMA_PHASE_PREFIX_TRANSITIONS, 0
            ),
            "seam_steps": self.ledger.counters.get(
                _comma_keys.COMMA_SCALAR_SEAM_STEPS, 0
            ),
            "leading_digit": sector.leading,
            "digit_phase": sector.digit,
            "headroom": sector.headroom,
        }

    def tropical(self) -> dict[str, int | str]:
        value = self.resolve_index()
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
    "FIRST_FORK_INDEX",
    "FIRST_FORK_VALUE",
    "SEMANTIC_VERSION",
    "SOURCE",
    "CommaTerm",
    "UnresolvedCommaBranch",
]
