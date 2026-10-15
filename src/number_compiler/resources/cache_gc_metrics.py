"""Exact cache-event distributions and retirement diagnostics.

Counter keys contain only bounded kinds, outcomes, levels, and temporal spans.
They retain no request, tile, digit, or source payload.
"""

from __future__ import annotations

from contextlib import suppress

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import resources as _resources_keys
from number_compiler.resources.stores import LedgerDict

_KINDS = frozenset(("tile", "result", "interface", "behavior", "symmetry"))
_OUTCOMES = frozenset(("early_hit", "miss", "publication", "late_duplicate"))
MAX_CACHE_EVENT_BUCKETS = 1_024


class CacheEventMetrics:
    """Charged, index-owned histogram buckets attached to the tile arena."""

    def __init__(self, ledger: ResourceLedger, prefix: str) -> None:
        if type(ledger) is not ResourceLedger or type(prefix) is not str or not prefix:
            raise ValueError("cache histograms require an index ledger and owner name")
        self.ledger = ledger
        self.owner = ledger.register(prefix + "-cache-events", "observation_memo")
        self.buckets: LedgerDict[tuple[str, str, str, int], int] = ledger.make_dict(
            self.owner,
        )
        ledger.register_container(
            self.owner,
            self.buckets,
            node_count=lambda: 0,
            payloads=self.buckets.items,
        )

    @staticmethod
    def _keys(
        kind: str,
        outcome: str,
        spatial_level: int,
        temporal_span: int | None,
    ) -> tuple[tuple[str, str, str, int], ...]:
        if kind not in _KINDS or outcome not in _OUTCOMES:
            raise ValueError("cache accounting has an unsupported kind or outcome")
        if type(spatial_level) is not int or spatial_level < 0:
            raise ValueError("cache accounting requires a nonnegative exact level")
        if temporal_span is not None and (
            type(temporal_span) is not int or temporal_span < 0
        ):
            raise ValueError("cache accounting requires a nonnegative exact span")
        return (("level", kind, outcome, spatial_level),) + (
            () if temporal_span is None else (("span", kind, outcome, temporal_span),)
        )

    def record(
        self,
        kind: str,
        outcome: str,
        *,
        spatial_level: int,
        temporal_span: int | None,
        allow_new: bool = True,
    ) -> None:
        keys = self._keys(kind, outcome, spatial_level, temporal_span)
        old = {key: self.buckets.get(key) for key in keys}
        missing = sum(key not in self.buckets for key in keys)
        if missing and not allow_new:
            self.ledger.bump(_resources_keys.CACHE_EVENT_HISTOGRAM_DROPPED)
            return
        if len(self.buckets) + missing > MAX_CACHE_EVENT_BUCKETS:
            self.ledger.bump(_resources_keys.CACHE_EVENT_HISTOGRAM_DROPPED)
            return
        try:
            self.ledger.reserve(self.owner, entries=missing)
        except BlockContextBudgetExceeded:
            self.ledger.bump(_resources_keys.CACHE_EVENT_HISTOGRAM_DROPPED)
            return
        completed = False
        with suppress(Exception):
            for key in keys:
                self.buckets[key] = self.buckets.get(key, 0) + 1
            completed = True
        if not completed:
            for key, value in old.items():
                if value is None:
                    self.buckets.pop(key, None)
                else:
                    self.buckets[key] = value
            self.ledger.release(self.owner, entries=missing)
            self.ledger.bump(_resources_keys.CACHE_EVENT_HISTOGRAM_DROPPED)

    def prepare(
        self,
        kind: str,
        outcome: str,
        *,
        spatial_level: int,
        temporal_span: int | None,
    ) -> None:
        """Reserve a zero-valued warm bucket during the cold publication path."""
        keys = self._keys(kind, outcome, spatial_level, temporal_span)
        missing = tuple(key for key in keys if key not in self.buckets)
        if len(self.buckets) + len(missing) > MAX_CACHE_EVENT_BUCKETS:
            self.ledger.bump(_resources_keys.CACHE_EVENT_HISTOGRAM_DROPPED)
            return
        try:
            self.ledger.reserve(self.owner, entries=len(missing))
        except BlockContextBudgetExceeded:
            self.ledger.bump(_resources_keys.CACHE_EVENT_HISTOGRAM_DROPPED)
            return
        completed = False
        with suppress(Exception):
            for key in missing:
                self.buckets[key] = 0
            completed = True
        if not completed:
            for key in missing:
                self.buckets.pop(key, None)
            self.ledger.release(self.owner, entries=len(missing))
            self.ledger.bump(_resources_keys.CACHE_EVENT_HISTOGRAM_DROPPED)


def record_cache_event(
    metrics: CacheEventMetrics,
    kind: str,
    outcome: str,
    *,
    spatial_level: int,
    temporal_span: int | None,
    allow_new: bool = True,
) -> None:
    """Record one actual event without retaining its semantic request."""
    if type(metrics) is not CacheEventMetrics:
        raise TypeError("cache accounting requires the tile arena histogram")
    metrics.record(
        kind,
        outcome,
        spatial_level=spatial_level,
        temporal_span=temporal_span,
        allow_new=allow_new,
    )


def _admitted_temporal_span(
    authority: object,
    action: object,
    action_admission: object,
) -> int | None:
    """Read a cocycle through an authenticated causal action admission."""
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.resources.causal_workspace import admitted_action_metadata

    if type(action) is not FieldCellActionID:
        raise TypeError("admitted cache accounting requires a field action ID")
    _signature, _kernel, record = admitted_action_metadata(
        action_admission, authority, action
    )
    value = record.cocycle
    span = getattr(value, "physical_ticks", None)
    return span if type(span) is int and span >= 0 else None


def temporal_span(
    authority: object,
    action: object,
    *,
    action_admission: object | None = None,
) -> int | None:
    """Read an action's cocycle, using live admission when supplied."""
    if action_admission is not None:
        return _admitted_temporal_span(authority, action, action_admission)
    method = getattr(authority, "action_cocycle", None)
    if not callable(method) or getattr(method, "__self__", None) is not authority:
        return None
    value = method(action)
    span = getattr(value, "physical_ticks", None)
    return span if type(span) is int and span >= 0 else None


def record_execution_cache_event(
    arena: object,
    kind: str,
    outcome: str,
    action: object,
    input_tile: object,
    *,
    allow_new: bool = True,
    action_admission: object | None = None,
) -> None:
    """Record an execution memo event using already-owned arena metadata."""
    metrics, level, authority = _execution_metadata(arena, input_tile)
    metrics.record(
        kind,
        outcome,
        spatial_level=level,
        temporal_span=temporal_span(
            authority,
            action,
            action_admission=action_admission,
        ),
        allow_new=allow_new,
    )


def prepare_execution_cache_event(
    arena: object,
    kind: str,
    outcome: str,
    action: object,
    input_tile: object,
    *,
    action_admission: object | None = None,
) -> None:
    metrics, level, authority = _execution_metadata(arena, input_tile)
    metrics.prepare(
        kind,
        outcome,
        spatial_level=level,
        temporal_span=temporal_span(
            authority,
            action,
            action_admission=action_admission,
        ),
    )


def cache_event_histograms(
    metrics: CacheEventMetrics,
) -> tuple[dict[str, int], dict[str, int]]:
    """Project dynamic event counters from one immutable ledger snapshot."""
    levels: dict[str, int] = {}
    spans: dict[str, int] = {}
    if type(metrics) is not CacheEventMetrics:
        raise TypeError("cache accounting requires the tile arena histogram")
    for (axis, kind, outcome, value), count in metrics.buckets.items():
        if not count:
            continue
        target = levels if axis == "level" else spans
        target[f"{kind}:{outcome}:{value}"] = count
    return levels, spans


def cache_event_owner_audit(
    roots: tuple[object, ...],
    ledger: ResourceLedger,
) -> tuple[frozenset[int], frozenset[tuple[int, int]]]:
    """Recognize only bounded, typed histogram stores as diagnostic payloads."""
    owners: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    containers = dict(ledger.iter_containers())
    for root in roots:
        metrics = getattr(root, "_cache_metrics", None)
        if type(metrics) is not CacheEventMetrics or metrics.ledger is not ledger:
            continue
        owner, buckets = metrics.owner, metrics.buckets
        valid = (
            containers.get(owner) is buckets and len(buckets) <= MAX_CACHE_EVENT_BUCKETS
        )
        for key, count in buckets.items():
            try:
                axis, kind, outcome, value = key
                CacheEventMetrics._keys(
                    kind,
                    outcome,
                    value if axis == "level" else 0,
                    value if axis == "span" else None,
                )
                valid &= axis in ("level", "span") and type(count) is int and count >= 0
            except (TypeError, ValueError):
                valid = False
        if valid:
            owners.add(owner)
        else:
            invalid.add((owner, id(buckets)))
    return frozenset(owners), frozenset(invalid)


__all__ = [
    "MAX_CACHE_EVENT_BUCKETS",
    "CacheEventMetrics",
    "cache_event_histograms",
    "cache_event_owner_audit",
    "prepare_execution_cache_event",
    "record_cache_event",
    "record_execution_cache_event",
    "temporal_span",
]


def _execution_metadata(
    arena: object, input_tile: object
) -> tuple[CacheEventMetrics, int, object]:
    """Validate the shared live tile geometry for accounting and reservation."""
    tiles = getattr(arena, "tiles", None)
    authority = getattr(arena, "action_authority", None)
    metrics = getattr(tiles, "_cache_metrics", None)
    resolve = getattr(tiles, "resolve", None)
    if type(metrics) is not CacheEventMetrics or not callable(resolve):
        raise TypeError("execution cache accounting requires the canonical tile arena")
    level = getattr(resolve(input_tile), "level", None)
    if type(level) is not int:
        raise TypeError("execution cache accounting requires canonical tile geometry")
    return metrics, level, authority
