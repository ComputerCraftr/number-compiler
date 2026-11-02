"""Bounded source-qualified dyadic macros for normalized Collatz runs.

Each width-w occurrence owns its low-w source germ and affine high-fiber action.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass, field
from typing import Final, Literal, Self, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.input_validation import is_exact_object_tuple
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.resources.payload_cost import retained_payload_node_count
from number_compiler.resources.process_cache import (
    MISSING,
    CacheRecordIssuerMismatch,
    get_process_cache,
)
from number_compiler.sequences.collatz.conditional_scheduler_memo import (
    ConditionalSchedulerMemoOwner,
)
from number_compiler.sequences.collatz.source_cylinder_types import (
    CollatzDyadicOccurrence,
    admit_source_key,
    decode_width_summary,
    validate_width_summary,
)
from number_compiler.sequences.collatz.source_cylinder_types import (
    canonical_gain as _canonical_gain,  # Cache tests patch this hook.
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzTapeWidthSummary,
    compose_width_ledger,
)

# Trusted producer-path marker only; CacheLease does not prove Collatz semantics.
_OCCURRENCE_PUBLISHER = object()
_GAIN_PUBLISHER = object()
_WIDTH_SPINE_PUBLISHER = object()
_MixedActionMetric = Literal[
    "failed_work",
    "mixed_admitted",
    "mixed_applied_hits",
    "mixed_bypasses",
    "mixed_inapplicable",
    "mixed_invalid_records",
    "mixed_key_operand_bits",
    "mixed_lookups",
    "mixed_misses",
    "mixed_payload_operand_bits",
    "mixed_publications",
    "mixed_rejected_fit",
    "mixed_retrieved",
    "mixed_root_tail_rejections",
    "mixed_validation_operand_bits",
]
_MIXED_ACTION_METRICS: Final[frozenset[str]] = frozenset(
    {
        "failed_work",
        "mixed_admitted",
        "mixed_applied_hits",
        "mixed_bypasses",
        "mixed_inapplicable",
        "mixed_invalid_records",
        "mixed_key_operand_bits",
        "mixed_lookups",
        "mixed_misses",
        "mixed_payload_operand_bits",
        "mixed_publications",
        "mixed_rejected_fit",
        "mixed_retrieved",
        "mixed_root_tail_rejections",
        "mixed_validation_operand_bits",
    }
)


@dataclass(frozen=True, slots=True, init=False)
class CanonicalGain:
    """Exact Collatz gain tied to its odd-event exponent."""

    odd_symbols: int
    multiplier: int
    _seal: tuple[int, int] = field(repr=False, compare=False)

    def __init__(self, odd_symbols: int) -> None:
        if type(odd_symbols) is not int or odd_symbols < 0:
            raise ValueError("Collatz gain exponent must be natural")
        object.__setattr__(self, "odd_symbols", odd_symbols)
        multiplier = _canonical_gain(odd_symbols)
        object.__setattr__(self, "multiplier", multiplier)
        object.__setattr__(self, "_seal", (odd_symbols, multiplier))

    @classmethod
    def from_issued_payload(cls, odd_symbols: int, multiplier: int) -> CanonicalGain:
        if (
            type(odd_symbols) is not int
            or odd_symbols < 0
            or type(multiplier) is not int
            or multiplier <= 0
        ):
            raise ValueError("Collatz canonical gain cache is malformed")
        gain = object.__new__(cls)
        object.__setattr__(gain, "odd_symbols", odd_symbols)
        object.__setattr__(gain, "multiplier", multiplier)
        object.__setattr__(gain, "_seal", (odd_symbols, multiplier))
        return gain

    def matches_seal(self) -> bool:
        return self._seal == (self.odd_symbols, self.multiplier)


@dataclass(frozen=True, slots=True)
class CollatzDyadicMacrosAuditSnapshot:
    """Read-only lifecycle facts for a source-qualified memo owner."""

    closed: bool
    cleanup_complete: bool
    occurrences_disposed: bool
    width_spines_disposed: bool
    gains_disposed: bool
    frontier_disposed: bool
    mixed_actions_disposed: bool


class CollatzDyadicMacros(ConditionalSchedulerMemoOwner):
    """Ledger-owned bounded local records with optional bounded cross-query reuse."""

    LIMIT = 4096
    MAX_INTERIOR_RECORDS = 64
    VERSION: Final[str] = "collatz-normalized-cylinder-v3-fiber-gain"
    GAIN_VERSION: Final[str] = "exact-v2-exponent-payload"
    GAIN_LIMIT = 4096
    WIDTH_SPINE_LIMIT = 4096
    WIDTH_SPINE_VERSION: Final[str] = "collatz-exact-source-width-spine-v1"

    def __init__(self, ledger: ResourceLedger, *, shared_cache: bool = False) -> None:
        if type(ledger) is not ResourceLedger or type(shared_cache) is not bool:
            raise TypeError("Collatz macros require a ledger and Boolean cache flag")
        self.ledger = ledger
        self._closed = False
        self._cleanup_complete = False
        self._bump("primitive_steps", 0)
        for metric in (
            "occurrence_lookups",
            "occurrence_exact_hits",
            "occurrence_transported_hits",
            "occurrence_local_hits",
            "occurrence_process_hits",
            "occurrence_misses",
            "occurrence_publications",
            "occurrence_bypasses",
            "occurrence_disabled_bypasses",
            "occurrence_evictions",
            "occurrence_applied_hits",
            "occurrence_applied_parent_hits",
            "occurrence_rejected_fit",
            "occurrence_admission_rejections",
            "failed_work",
            "gain_operand_bits",
            "gain_local_hits",
            "gain_process_hits",
            "gain_key_operand_bits",
            "gain_construction_operand_bits",
            "gain_validation_operand_bits",
            "gain_bypasses",
            "gain_evictions",
            "width_spine_lookups",
            "width_spine_local_hits",
            "width_spine_process_hits",
            "width_spine_misses",
            "width_spine_publications",
            "width_spine_bypasses",
            "width_spine_evictions",
            "width_spine_admission_rejections",
            "width_spine_key_operand_bits",
            "width_spine_payload_operand_bits",
            "mixed_lookups",
            "mixed_retrieved",
            "mixed_admitted",
            "mixed_inapplicable",
            "mixed_misses",
            "mixed_publications",
            "mixed_applied_hits",
            "mixed_rejected_fit",
            "mixed_root_tail_rejections",
            "mixed_bypasses",
            "mixed_invalid_records",
            "mixed_key_operand_bits",
            "mixed_payload_operand_bits",
            "mixed_validation_operand_bits",
        ):
            self._bump(metric, 0)
        self.shared_cache = shared_cache
        self._interior_records = 0
        prefix = f"collatz-dyadic-{ledger.owner_count}"
        stores: list[OwnedMemo[object, object]] = []

        def make_store(
            suffix: str,
            role: str,
            *,
            nodes_per_entry: int = 0,
            node_cost: Callable[[object, object], int] | None = None,
            evictable: bool = False,
        ) -> OwnedMemo[object, object]:
            owner = ledger.register(prefix + suffix, role)
            try:
                store: OwnedMemo[object, object] = OwnedMemo(
                    ledger,
                    owner,
                    evictable=evictable,
                    nodes_per_entry=nodes_per_entry,
                    node_cost=node_cost,
                )
            except BaseException:
                # OwnedMemo registers an empty ledger owner before finishing
                # its own setup. Retire that empty owner if setup is interrupted.
                ledger.mark_disposed(owner)
                raise
            stores.append(store)
            return store

        try:
            self.occurrences = cast(
                OwnedMemo[
                    tuple[int, int],
                    tuple[CollatzDyadicOccurrence, int, tuple[int, ...]],
                ],
                make_store(
                    "-occurrences", "query_memo", nodes_per_entry=3, evictable=True
                ),
            )
            self.width_spines = cast(
                OwnedMemo[tuple[int, int, int], CollatzTapeWidthSummary],
                make_store(
                    "-exact-width-spines",
                    "query_memo",
                    nodes_per_entry=10,
                    evictable=True,
                ),
            )
            self.gains = cast(
                OwnedMemo[int, CanonicalGain],
                # Each immutable gain seal retains one additional tuple.
                make_store("-gains", "query_memo", nodes_per_entry=1, evictable=True),
            )
            # Adjacent executed occurrences form a temporary binary frontier.
            self.frontier = cast(
                OwnedMemo[int, tuple[int, int, CollatzTapeWidthSummary | None]],
                make_store("-frontier", "execution_stack", nodes_per_entry=10),
            )
            self.mixed_actions = make_store(
                "-mixed-actions",
                "query_memo",
                node_cost=lambda key, value: retained_payload_node_count((key, value)),
                evictable=True,
            )
            ledger.register_execution_root(self)
        except BaseException:
            self._closed = True
            cleanup_all(store.dispose for store in reversed(stores))
            raise

    def __enter__(self) -> Self:
        self.check_open()
        return self

    def __exit__(self, exc_type: object, exc: object, traceback: object) -> None:
        self.close()

    def close(self) -> None:
        if self._cleanup_complete:
            return
        self._closed = True
        disposals = [
            self.close_conditional_scheduler_memo,
            self.frontier.dispose,
            self.gains.dispose,
            self.width_spines.dispose,
            self.occurrences.dispose,
            self.mixed_actions.dispose,
        ]
        cleanup_all(disposals)
        self._cleanup_complete = True

    def check_open(self) -> None:
        if self._closed:
            raise RuntimeError("Collatz dyadic macros are closed")

    def audit_snapshot(self) -> CollatzDyadicMacrosAuditSnapshot:
        """Report teardown state without exposing cache storage or seal fields."""
        return CollatzDyadicMacrosAuditSnapshot(
            closed=self._closed,
            cleanup_complete=self._cleanup_complete,
            occurrences_disposed=self.occurrences.audit_snapshot().disposed,
            width_spines_disposed=self.width_spines.audit_snapshot().disposed,
            gains_disposed=self.gains.audit_snapshot().disposed,
            frontier_disposed=self.frontier.audit_snapshot().disposed,
            mixed_actions_disposed=self.mixed_actions.audit_snapshot().disposed,
        )

    def _bump(self, suffix: str, amount: int = 1) -> None:
        self.check_open()
        self.ledger.bump("collatz_hashlife_" + suffix, amount)

    def bump_mixed_action_metric(
        self, suffix: _MixedActionMetric, amount: int = 1
    ) -> None:
        """Record one metric owned by the mixed-action cache collaborator."""
        self.check_open()
        if suffix not in _MIXED_ACTION_METRICS:
            raise ValueError("unknown Collatz mixed-action cache metric")
        self.ledger.bump("collatz_hashlife_" + suffix, amount)

    def _retain_gain(self, gain: CanonicalGain) -> None:
        if gain.odd_symbols not in self.gains and len(self.gains) >= self.GAIN_LIMIT:
            del self.gains[next(iter(self.gains))]
            self._bump("gain_evictions")
        try:
            self.gains[gain.odd_symbols] = gain
        except BlockContextBudgetExceeded:
            # The gain is still available as a temporary certified value for
            # this occurrence; retaining it is an optional query-memo benefit.
            self._bump("gain_bypasses")

    def canonical_gain(self, odd_symbols: int) -> CanonicalGain:
        self.check_open()
        if type(odd_symbols) is not int or odd_symbols < 0:
            raise ValueError("Collatz gain exponent must be natural")
        self._bump("gain_key_operand_bits", odd_symbols.bit_length())
        found = self.gains.get(odd_symbols)
        if found is not None:
            if (
                type(found) is not CanonicalGain
                or found.odd_symbols != odd_symbols
                or type(found.multiplier) is not int
                or found.multiplier <= 0
                or not found.matches_seal()
            ):
                raise ValueError("Collatz local canonical gain is malformed")
            self._bump("gain_local_hits")
            return found
        cache = get_process_cache()
        if self.shared_cache and not cache.enabled:
            self._bump("gain_bypasses")
        if self.shared_cache and cache.enabled:
            try:
                lease = cache.acquire(
                    "collatz-power-of-three", self.GAIN_VERSION, (odd_symbols,)
                )
            except BlockContextBudgetExceeded:
                self._bump("gain_bypasses")
            else:
                with lease:
                    value = lease.get_issued(("gain",), _GAIN_PUBLISHER)
                    if value is not MISSING:
                        if not is_exact_object_tuple(value):
                            raise ValueError(
                                "Collatz canonical gain cache is malformed"
                            )
                        raw_gain_payload = value
                        if (
                            len(raw_gain_payload) != 2
                            or type(raw_gain_payload[0]) is not int
                            or raw_gain_payload[0] != odd_symbols
                            or type(raw_gain_payload[1]) is not int
                            or raw_gain_payload[1] <= 0
                        ):
                            raise ValueError(
                                "Collatz canonical gain cache is malformed"
                            )
                        gain_payload = cast(tuple[int, int], value)
                        gain = CanonicalGain.from_issued_payload(*gain_payload)
                        self._retain_gain(gain)
                        self._bump("gain_process_hits")
                        return gain
                    gain = self._construct_gain(odd_symbols)
                    if not lease.put_issued(
                        ("gain",),
                        (odd_symbols, gain.multiplier),
                        _GAIN_PUBLISHER,
                    ):
                        self._bump("gain_bypasses")
                    return gain
        return self._construct_gain(odd_symbols)

    def _construct_gain(self, odd_symbols: int) -> CanonicalGain:
        gain = CanonicalGain(odd_symbols)
        self._bump("gain_operand_bits", gain.multiplier.bit_length())
        self._bump("gain_construction_operand_bits", gain.multiplier.bit_length())
        self._retain_gain(gain)
        return gain

    def _publish(
        self, occurrence: CollatzDyadicOccurrence, publisher_fiber: int
    ) -> CollatzDyadicOccurrence:
        self.check_open()
        if type(publisher_fiber) is not int or publisher_fiber < 0:
            raise ValueError("Collatz occurrence publisher fiber must be natural")
        self._bump(
            "operand_bits",
            occurrence.residue.bit_length()
            + occurrence.target_origin.bit_length()
            + occurrence.multiplier.bit_length()
            + publisher_fiber.bit_length(),
        )
        if (occurrence.width, occurrence.residue) not in self.occurrences and len(
            self.occurrences
        ) >= self.LIMIT:
            del self.occurrences[next(iter(self.occurrences))]
            self._bump("occurrence_evictions")
        # The occurrence is frozen only by convention: object.__setattr__ can
        # still alter its fields after publication. Keep an independent scalar
        # snapshot beside it so a local memo hit cannot silently reuse a
        # changed affine action or publisher fiber.
        self.occurrences[occurrence.width, occurrence.residue] = (
            occurrence,
            publisher_fiber,
            self._occurrence_snapshot(occurrence, publisher_fiber),
        )
        self._bump("occurrence_publications")
        level = occurrence.width.bit_length() - 1
        previous = self.ledger.counters.get(_collatz_keys.COLLATZ_HASHLIFE_MAX_LEVEL, 0)
        self._bump("max_level", max(0, level - previous))
        return occurrence

    @staticmethod
    def _occurrence_snapshot(
        occurrence: CollatzDyadicOccurrence, publisher_fiber: int
    ) -> tuple[int, ...]:
        return (
            occurrence.width,
            occurrence.residue,
            occurrence.odd_symbols,
            occurrence.target_origin,
            occurrence.multiplier,
            publisher_fiber,
        )

    @classmethod
    def _checked_local_occurrence(
        cls, value: object, width: int, residue: int
    ) -> tuple[CollatzDyadicOccurrence, int]:
        if not (
            is_exact_object_tuple(value)
            and len(value) == 3
            and type(value[0]) is CollatzDyadicOccurrence
            and type(value[1]) is int
            and value[1] >= 0
            and is_exact_object_tuple(value[2])
            and len(value[2]) == 6
            and all(type(item) is int for item in value[2])
        ):
            raise ValueError("Collatz local occurrence record is malformed")
        raw_occurrence, raw_fiber, raw_snapshot = value
        occurrence = cast(CollatzDyadicOccurrence, raw_occurrence)
        publisher_fiber = cast(int, raw_fiber)
        snapshot = cast(tuple[int, ...], raw_snapshot)
        try:
            occurrence.validate_canonical_gain()
        except (TypeError, ValueError) as exc:
            raise ValueError("Collatz local occurrence binding was changed") from exc
        if (
            occurrence.width != width
            or occurrence.residue != residue
            or (cls._occurrence_snapshot(occurrence, publisher_fiber) != snapshot)
        ):
            raise ValueError("Collatz local occurrence binding was changed")
        return occurrence, publisher_fiber

    def lookup(self, source: int, width: int) -> CollatzDyadicOccurrence | None:
        self.check_open()
        residue, key_bits = admit_source_key(source, width)
        # The low-width slice forms the lookup key; the full source also
        # classifies an exact publisher match versus a transported fiber.
        self._bump("key_operand_bits", key_bits)
        self._bump("occurrence_lookups")
        local = self.occurrences.get((width, residue))
        if local is not None:
            try:
                found, publisher_fiber = self._checked_local_occurrence(
                    local, width, residue
                )
            except (TypeError, ValueError):
                self._bump("occurrence_admission_rejections")
                self._bump("failed_work")
                raise
            self._retrieved(source, width, publisher_fiber, "local")
            return found
        if self.shared_cache:
            cache = get_process_cache()
            if not cache.enabled:
                self._bump("occurrence_disabled_bypasses")
                self._bump("occurrence_misses")
                return None
            try:
                lease = cache.acquire(
                    "collatz-dyadic-occurrence", self.VERSION, (width, residue)
                )
            except BlockContextBudgetExceeded:
                self._bump("occurrence_bypasses")
                self._bump("occurrence_misses")
                return None
            with lease:
                try:
                    payload = lease.get_issued(("effect",), _OCCURRENCE_PUBLISHER)
                except CacheRecordIssuerMismatch:
                    self._bump("occurrence_admission_rejections")
                    self._bump("failed_work")
                    raise
                if payload is not MISSING:
                    try:
                        if not is_exact_object_tuple(payload):
                            raise ValueError(
                                "Collatz shared occurrence payload is invalid"
                            )
                        raw_occurrence_payload = payload
                        if len(raw_occurrence_payload) != 4 or any(
                            type(item) is not int for item in raw_occurrence_payload
                        ):
                            raise ValueError(
                                "Collatz shared occurrence payload is invalid"
                            )
                        occurrence_payload = cast(tuple[int, int, int, int], payload)
                        ones, origin, gain, publisher_fiber = occurrence_payload
                        if not 0 <= ones <= width or publisher_fiber < 0:
                            raise ValueError(
                                "Collatz shared occurrence has an invalid gain key"
                            )
                        canonical_gain = self.canonical_gain(ones)
                        self._bump(
                            "gain_validation_operand_bits",
                            canonical_gain.multiplier.bit_length() + gain.bit_length(),
                        )
                        if gain != canonical_gain.multiplier:
                            raise ValueError("Collatz shared occurrence gain differs")
                        self._bump(
                            "gain_validation_operand_bits",
                            ones.bit_length() + canonical_gain.multiplier.bit_length(),
                        )
                        found = CollatzDyadicOccurrence.from_canonical_gain(
                            width,
                            residue,
                            ones,
                            origin,
                            canonical_gain,
                        )
                        self._bump(
                            "operand_bits",
                            gain.bit_length()
                            + origin.bit_length()
                            + width
                            + publisher_fiber.bit_length(),
                        )
                    except (TypeError, ValueError, BlockContextBudgetExceeded):
                        self._bump("occurrence_admission_rejections")
                        self._bump("failed_work")
                        raise
                    try:
                        result = self._publish(found, publisher_fiber)
                    except BlockContextBudgetExceeded:
                        self._bump("occurrence_admission_rejections")
                        self._bump("failed_work")
                        raise
                    self._retrieved(source, width, publisher_fiber, "process")
                    return result
        else:
            self._bump("occurrence_disabled_bypasses")
        self._bump("occurrence_misses")
        return None

    def _retrieved(
        self, source: int, width: int, publisher_fiber: int, location: str
    ) -> None:
        self.check_open()
        self._bump(f"occurrence_{location}_hits")
        self._bump(
            "occurrence_exact_hits"
            if source >> width == publisher_fiber
            else "occurrence_transported_hits"
        )

    def applied(self) -> None:
        """Called only after the admitted cached block advances the caller."""
        self.check_open()
        self._bump("occurrence_applied_hits")
        self._bump("occurrence_applied_parent_hits")

    def rejected_fit(self) -> None:
        self.check_open()
        self._bump("occurrence_rejected_fit")

    def _share(self, source: int, found: CollatzDyadicOccurrence) -> None:
        self.check_open()
        if self.shared_cache:
            cache = get_process_cache()
            if not cache.enabled:
                self._bump("occurrence_disabled_bypasses")
                return
            try:
                lease = cache.acquire(
                    "collatz-dyadic-occurrence",
                    self.VERSION,
                    (found.width, found.residue),
                )
            except BlockContextBudgetExceeded:
                self._bump("occurrence_bypasses")
                return
            with lease:
                if not lease.put_issued(
                    ("effect",),
                    (
                        found.odd_symbols,
                        found.target_origin,
                        found.multiplier,
                        source >> found.width,
                    ),
                    _OCCURRENCE_PUBLISHER,
                ):
                    self._bump("occurrence_bypasses")

    def remember(
        self,
        source: int,
        width: int,
        ones: int,
        endpoint: int,
        *,
        tape_width_summary: CollatzTapeWidthSummary | None = None,
    ) -> bool:
        self.check_open()
        residue, key_bits = admit_source_key(source, width)
        if type(ones) is not int or not 0 <= ones <= width:
            raise ValueError("Collatz macro odd count is invalid")
        if type(endpoint) is not int or endpoint < 0:
            raise ValueError(
                "Collatz macro endpoint must be a nonnegative exact integer"
            )
        if tape_width_summary is not None:
            validate_width_summary(tape_width_summary, source, width)
            if (
                tape_width_summary.odd_steps != ones
                or tape_width_summary.target_width != endpoint.bit_length()
            ):
                raise ValueError("Collatz width spine differs from occurrence action")
        self._bump("key_operand_bits", key_bits)
        occurrence_key = (width, residue)
        if occurrence_key in self.occurrences:
            try:
                existing_record = self.occurrences[occurrence_key]
                existing, _publisher_fiber = self._checked_local_occurrence(
                    existing_record, width, residue
                )
                existing.validate_canonical_gain()
                canonical_gain = self.canonical_gain(ones)
                self._bump(
                    "gain_validation_operand_bits",
                    existing.multiplier.bit_length()
                    + canonical_gain.multiplier.bit_length()
                    + ones.bit_length(),
                )
                if (
                    existing.width != width
                    or existing.residue != residue
                    or existing.odd_symbols != ones
                ):
                    raise ValueError(
                        "Collatz duplicate occurrence has a conflicting source germ"
                    )
                existing.validate_canonical_gain(canonical_gain.multiplier)
                high_fiber = source >> width
                self._bump(
                    "operand_bits",
                    source.bit_length()
                    + high_fiber.bit_length()
                    + existing.target_origin.bit_length()
                    + existing.multiplier.bit_length()
                    + max(
                        existing.target_origin.bit_length(),
                        existing.multiplier.bit_length() + high_fiber.bit_length(),
                    )
                    + endpoint.bit_length(),
                )
                predicted_endpoint = existing.apply(source)
                if predicted_endpoint != endpoint:
                    raise ValueError(
                        "Collatz duplicate occurrence disagrees with the new endpoint"
                    )
            except (
                CacheRecordIssuerMismatch,
                TypeError,
                ValueError,
                BlockContextBudgetExceeded,
            ):
                self._bump("occurrence_admission_rejections")
                self._bump("failed_work")
                raise
            if tape_width_summary is not None:
                self._remember_exact_width(source, width, tape_width_summary)
            return False
        try:
            gain = self.canonical_gain(ones)
        except (CacheRecordIssuerMismatch, ValueError):
            self._bump("occurrence_admission_rejections")
            self._bump("failed_work")
            raise
        # The private factory accepts only a typed gain from the canonical
        # producer or an exactly issued process-cache record.
        self._bump(
            "gain_validation_operand_bits",
            ones.bit_length() + gain.multiplier.bit_length(),
        )
        cell = CollatzDyadicOccurrence.from_canonical_gain(
            width,
            residue,
            ones,
            endpoint - gain.multiplier * (source >> width),
            gain,
        )
        try:
            self._publish(cell, source >> width)
        except BlockContextBudgetExceeded:
            self._bump("occurrence_admission_rejections")
            self._bump("failed_work")
            raise
        self._share(source, cell)
        if tape_width_summary is not None:
            self._remember_exact_width(source, width, tape_width_summary)
        return True

    def _remember_exact_width(
        self,
        source: int,
        width: int,
        summary: CollatzTapeWidthSummary,
    ) -> None:
        residue, _ = admit_source_key(source, width)
        fiber = source >> width
        key = (width, residue, fiber)
        validate_width_summary(summary, source, width)
        if key in self.width_spines:
            existing = self.width_spines[key]
            validate_width_summary(existing, source, width)
            if existing != summary:
                raise ValueError(
                    "conflicting Collatz width spines for one exact source"
                )
            return
        retained = self._retain_width_summary(key, summary)
        shared = self._share_width_summary(key, summary)
        if retained or shared:
            self._bump("width_spine_publications")

    def _compose_width_summaries(
        self,
        before: CollatzTapeWidthSummary | None,
        after: CollatzTapeWidthSummary | None,
    ) -> CollatzTapeWidthSummary | None:
        if before is None or after is None:
            return None
        if before.target_width != after.source_width:
            raise ValueError("adjacent Collatz width summaries do not meet")
        blank = compose_width_ledger(self.ledger, before.blank, after.blank)
        return CollatzTapeWidthSummary(
            before.source_width,
            after.target_width,
            before.physical_ticks + after.physical_ticks,
            before.normalized_symbols + after.normalized_symbols,
            before.odd_steps + after.odd_steps,
            blank,
        )

    def observe(
        self,
        source: int,
        width: int,
        ones: int,
        endpoint: int,
        *,
        anchor: int,
        tape_width_summary: CollatzTapeWidthSummary | None = None,
    ) -> None:
        """Retain useful dyadic submacros from the existing producer, once.

        No branch is evaluated here. Adjacent equal-sized intervals coalesce
        using their measured odd count and endpoint. Root-prefix intervals are
        retained directly; interior intervals are retained only after an
        existing join supplies their exact source, action, and endpoint.
        Irregular run boundaries end the frontier rather than trigger splitting
        or source rediscovery.
        """
        self.check_open()
        if width < 8 or width & (width - 1):
            self.frontier.clear()
            return
        if tape_width_summary is not None:
            validate_width_summary(tape_width_summary, source, width)
            if (
                tape_width_summary.normalized_symbols != width
                or tape_width_summary.odd_steps != ones
                or tape_width_summary.physical_ticks != width + ones
                or tape_width_summary.target_width != endpoint.bit_length()
            ):
                raise ValueError("Collatz observed width spine differs from segment")
        if any(smaller < width for smaller in self.frontier):
            # A shorter unmatched suffix separates this block from any earlier
            # block of the same width. They must never be composed as adjacent.
            self.frontier.clear()
        joined = False
        while True:
            root_prefix = source == anchor
            useful_join = (
                joined
                and not root_prefix
                and self._interior_records < self.MAX_INTERIOR_RECORDS
            )
            if (
                (root_prefix or useful_join)
                and 16 <= width <= source.bit_length()
                and self.remember(
                    source,
                    width,
                    ones,
                    endpoint,
                    tape_width_summary=tape_width_summary,
                )
                and useful_join
            ):
                self._interior_records += 1
            left = self.frontier.pop(width, None)
            if left is None:
                if endpoint > 2:
                    self.frontier[width] = (source, ones, tape_width_summary)
                else:
                    # The exact finite action is useful even when it reaches
                    # the cycle. Retain it above, but never join across the
                    # terminal entry and its subsequent cycle.
                    self.frontier.clear()
                break
            source, left_ones, left_summary = left
            ones += left_ones
            width *= 2
            tape_width_summary = self._compose_width_summaries(
                left_summary, tape_width_summary
            )
            joined = True
            self._bump("occurrence_frontier_joins")

    def lookup_largest(
        self, source: int, width: int, physical_ticks: int
    ) -> CollatzDyadicOccurrence | None:
        """Try the admitted parent before smaller cached cylinders."""
        self.check_open()
        while width >= 16:
            found = self.lookup(source, width)
            if found is not None:
                if width + found.odd_symbols <= physical_ticks:
                    return found
                self.rejected_fit()
            width //= 2
        return None

    def lookup_largest_with_width(
        self, source: int, width: int, physical_ticks: int
    ) -> tuple[CollatzDyadicOccurrence, CollatzTapeWidthSummary | None] | None:
        """Select the largest endpoint macro and its exact-source width spine.

        The endpoint macro may transport to any high fiber with the same low
        residue. Its width spine is fetched from a separate exact-fiber key and
        is therefore absent for a transported source unless that exact source
        was itself admitted during an earlier construction.
        """
        found = self.lookup_largest(source, width, physical_ticks)
        if found is None:
            return None
        return found, self.lookup_width_summary(source, found.width)

    def lookup_width_summary(
        self, source: int, width: int
    ) -> CollatzTapeWidthSummary | None:
        """Look up a completed width spine only for its exact source fiber."""
        self.check_open()
        residue, _ = admit_source_key(source, width)
        fiber = source >> width
        key = (width, residue, fiber)
        self._bump("width_spine_lookups")
        self._bump(
            "width_spine_key_operand_bits",
            width.bit_length() + residue.bit_length() + fiber.bit_length(),
        )
        if key in self.width_spines:
            local = self.width_spines[key]
            try:
                if type(local) is not CollatzTapeWidthSummary:
                    raise ValueError("local Collatz width spine has another sort")
                validate_width_summary(local, source, width)
            except (TypeError, ValueError):
                self._bump("width_spine_admission_rejections")
                self._bump("failed_work")
                raise
            self._bump("width_spine_local_hits")
            return local
        if not self.shared_cache:
            self._bump("width_spine_misses")
            return None
        cache = get_process_cache()
        if not cache.enabled:
            self._bump("width_spine_bypasses")
            self._bump("width_spine_misses")
            return None
        try:
            lease = cache.acquire(
                "collatz-dyadic-width-spine", self.WIDTH_SPINE_VERSION, key
            )
        except BlockContextBudgetExceeded:
            self._bump("width_spine_bypasses")
            self._bump("width_spine_misses")
            return None
        with lease:
            try:
                payload = lease.get_issued(("summary",), _WIDTH_SPINE_PUBLISHER)
            except CacheRecordIssuerMismatch:
                self._bump("width_spine_admission_rejections")
                self._bump("failed_work")
                raise
            if payload is MISSING:
                self._bump("width_spine_misses")
                return None
            try:
                summary, payload_bits = decode_width_summary(payload, source, width)
                self._bump("width_spine_payload_operand_bits", payload_bits)
                self._retain_width_summary(key, summary)
            except (TypeError, ValueError, BlockContextBudgetExceeded):
                self._bump("width_spine_admission_rejections")
                self._bump("failed_work")
                raise
            self._bump("width_spine_process_hits")
            return summary

    def _retain_width_summary(
        self,
        key: tuple[int, int, int],
        summary: CollatzTapeWidthSummary,
    ) -> bool:
        if key in self.width_spines:
            return False
        if len(self.width_spines) >= self.WIDTH_SPINE_LIMIT:
            del self.width_spines[next(iter(self.width_spines))]
            self._bump("width_spine_evictions")
        try:
            self.width_spines[key] = summary
        except BlockContextBudgetExceeded:
            self._bump("width_spine_bypasses")
            return False
        return True

    def _share_width_summary(
        self,
        key: tuple[int, int, int],
        summary: CollatzTapeWidthSummary,
    ) -> bool:
        if not self.shared_cache:
            return False
        cache = get_process_cache()
        if not cache.enabled:
            self._bump("width_spine_bypasses")
            return False
        try:
            lease = cache.acquire(
                "collatz-dyadic-width-spine", self.WIDTH_SPINE_VERSION, key
            )
        except BlockContextBudgetExceeded:
            self._bump("width_spine_bypasses")
            return False
        with lease:
            published = lease.put_issued(
                ("summary",),
                (
                    summary.source_width,
                    summary.target_width,
                    summary.physical_ticks,
                    summary.normalized_symbols,
                    summary.odd_steps,
                    *summary.blank.as_tuple(),
                ),
                _WIDTH_SPINE_PUBLISHER,
            )
            if not published:
                self._bump("width_spine_bypasses")
            return published
