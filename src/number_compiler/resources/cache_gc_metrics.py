"""Exact cache-event distributions and retirement diagnostics.

Counter keys contain only bounded kinds, outcomes, levels, and temporal spans.
They retain no request, tile, digit, or source payload.
"""

from __future__ import annotations

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
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
            self.ledger.bump("cache_event_histogram_dropped")
            return
        if len(self.buckets) + missing > MAX_CACHE_EVENT_BUCKETS:
            self.ledger.bump("cache_event_histogram_dropped")
            return
        try:
            self.ledger.reserve(self.owner, entries=missing)
        except BlockContextBudgetExceeded:
            self.ledger.bump("cache_event_histogram_dropped")
            return
        try:
            for key in keys:
                self.buckets[key] = self.buckets.get(key, 0) + 1
        except Exception:
            for key, value in old.items():
                if value is None:
                    self.buckets.pop(key, None)
                else:
                    self.buckets[key] = value
            self.ledger.release(self.owner, entries=missing)
            self.ledger.bump("cache_event_histogram_dropped")

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
            self.ledger.bump("cache_event_histogram_dropped")
            return
        try:
            self.ledger.reserve(self.owner, entries=len(missing))
        except BlockContextBudgetExceeded:
            self.ledger.bump("cache_event_histogram_dropped")
            return
        try:
            for key in missing:
                self.buckets[key] = 0
        except Exception:
            for key in missing:
                self.buckets.pop(key, None)
            self.ledger.release(self.owner, entries=len(missing))
            self.ledger.bump("cache_event_histogram_dropped")


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


def temporal_span(authority: object, action: object) -> int | None:
    """Read an admitted action's immutable cocycle without evaluating semantics."""
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
) -> None:
    """Record an execution memo event using already-owned arena metadata."""
    tiles = getattr(arena, "tiles", None)
    authority = getattr(arena, "action_authority", None)
    metrics = getattr(tiles, "_cache_metrics", None)
    resolve = getattr(tiles, "resolve", None)
    if type(metrics) is not CacheEventMetrics or not callable(resolve):
        raise TypeError("execution cache accounting requires the canonical tile arena")
    record = resolve(input_tile)
    level = getattr(record, "level", None)
    if type(level) is not int:
        raise TypeError("execution cache accounting requires canonical tile geometry")
    metrics.record(
        kind,
        outcome,
        spatial_level=level,
        temporal_span=temporal_span(authority, action),
        allow_new=allow_new,
    )


def prepare_execution_cache_event(
    arena: object,
    kind: str,
    outcome: str,
    action: object,
    input_tile: object,
) -> None:
    tiles = getattr(arena, "tiles", None)
    authority = getattr(arena, "action_authority", None)
    metrics = getattr(tiles, "_cache_metrics", None)
    resolve = getattr(tiles, "resolve", None)
    if type(metrics) is not CacheEventMetrics or not callable(resolve):
        raise TypeError("execution cache accounting requires the canonical tile arena")
    level = getattr(resolve(input_tile), "level", None)
    if type(level) is not int:
        raise TypeError("execution cache accounting requires canonical tile geometry")
    metrics.prepare(
        kind,
        outcome,
        spatial_level=level,
        temporal_span=temporal_span(authority, action),
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
    "CacheEventMetrics",
    "cache_event_histograms",
    "cache_event_owner_audit",
    "record_cache_event",
    "MAX_CACHE_EVENT_BUCKETS",
    "prepare_execution_cache_event",
    "record_execution_cache_event",
    "temporal_span",
]
