"""Composable finite-horizon fresh-prime images for production rank/select.

A query authenticates the final admitted factor ``q`` against the consecutive
Legendre prefix, builds a binary action for the demanded integer prefix, and
projects two ranks from one source-bound image. Parent gaps and integer leaves
are never materialized.
"""

from __future__ import annotations

from number_compiler.hashlife.execution.source_bound_images import (
    SourceImageDemand,
    SourceImageID,
)
from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.metric_keys import prime as _prime_keys
from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG
from number_compiler.sequences.prime.successor_action import (
    PrimeSuccessorActionArena,
    PrimeSuccessorImageAdapter,
    PrimeSuccessorSource,
)


class PrimePartialSuccessorQuery:
    """One bounded query over a real composed fresh-prime prefix action."""

    def __init__(self, rank: CoprimeRankDAG) -> None:
        if type(rank) is not CoprimeRankDAG:
            raise TypeError("prime partial successor query requires its rank owner")
        self.rank = rank
        self._rank_authority = rank, rank.ledger, rank._factor_store_authority
        self._arena: PrimeSuccessorActionArena | None = None
        self._adapter: PrimeSuccessorImageAdapter | None = None
        self._scheduler: TileScheduler | None = None
        self._depth = 0
        self._last_image: SourceImageID | None = None
        self._last_width = 0
        self._closed = False
        self.peak_scheduler_entries = 0

    def _check_open(self) -> None:
        if self._closed:
            raise RuntimeError("prime partial successor query is closed")
        rank, ledger, factors = self._rank_authority
        if (
            self.rank is not rank
            or self.rank.ledger is not ledger
            or self.rank._factor_store_authority is not factors
        ):
            raise ValueError("prime partial query lost its source authority")

    def _dispose_stage(self) -> None:
        try:
            if self._scheduler is not None:
                self._scheduler.dispose_source_images()
        finally:
            if self._arena is not None:
                self._arena.close()
        self._arena = None
        self._adapter = None
        self._scheduler = None
        self._depth = 0
        self._last_image = None
        self._last_width = 0

    def _stage(
        self, depth: int
    ) -> tuple[
        PrimeSuccessorActionArena,
        PrimeSuccessorImageAdapter,
        TileScheduler,
    ]:
        self._check_open()
        if type(depth) is not int or not 1 <= depth <= self.rank.factor_count:
            raise ValueError("prime partial stage depth is outside the source")
        if self._depth == depth:
            cached_arena, cached_adapter, cached_scheduler = (
                self._arena,
                self._adapter,
                self._scheduler,
            )
            if (
                cached_arena is None
                or cached_adapter is None
                or cached_scheduler is None
            ):
                raise RuntimeError("prime partial stage lost its scheduler")
            cached_arena._check_open()
            return cached_arena, cached_adapter, cached_scheduler
        self._dispose_stage()
        # One admitted factor is needed, not a detached copy of every stage.
        fresh = self.rank._factor_store_authority[depth - 1]
        arena: PrimeSuccessorActionArena | None = None
        scheduler: TileScheduler | None = None
        try:
            arena = PrimeSuccessorActionArena(
                self.rank,
                fresh,
                parent_depth=depth - 1,
            )
            adapter = PrimeSuccessorImageAdapter(arena)
            scheduler = TileScheduler.source_only(self.rank.ledger)
            scheduler.register_source_image_adapter(adapter)
        except BaseException:
            try:
                if scheduler is not None:
                    scheduler.dispose_source_images()
            finally:
                if arena is not None:
                    arena.close()
            raise
        if arena is None or scheduler is None:
            raise AssertionError("prime partial stage construction lost its owners")
        self._arena, self._adapter, self._scheduler, self._depth = (
            arena,
            adapter,
            scheduler,
            depth,
        )
        self.rank.ledger.bump(_prime_keys.PRIME_PARTIAL_SUCCESSOR_STAGE_PUBLICATIONS)
        return arena, adapter, scheduler

    def _update_peak(self, arena: PrimeSuccessorActionArena) -> None:
        non_scheduler = (
            self.rank.factor_count
            + len(self.rank.memo)
            + len(self.rank.progression_memo)
        )
        self.peak_scheduler_entries = max(
            self.peak_scheduler_entries,
            self.rank.ledger.entries - non_scheduler,
        )
        if (
            self.rank.max_states is not None
            and self.rank.ledger.entries - self.rank.factor_count > self.rank.max_states
        ):
            raise ValueError("prime state budget exceeded (--max-prime-states)")
        if arena.metrics().parent_gap_positions_materialized:
            raise AssertionError("prime prefix action materialized a parent gap")

    def count_primes(self, lower: int, upper: int, depth: int) -> int:
        """Count primes in ``[lower, upper)`` from one admitted prefix image."""
        self._check_open()
        if (
            type(lower) is not int
            or type(upper) is not int
            or lower < 2
            or lower > upper
        ):
            raise ValueError("invalid production prime interval")
        if lower == upper:
            return 0
        arena, adapter, scheduler = self._stage(depth)
        stop = upper - 1
        if self._last_image is None or stop > self._last_width:
            action = arena.prefix(stop)
            source = PrimeSuccessorSource(arena.descriptor_id, 0)
            image = scheduler.source_image_demanded(
                adapter,
                source,
                action,
                SourceImageDemand("rank-before", (upper - 1,)),
            )
            self._last_image = image
            self._last_width = stop
        else:
            image = self._last_image
            self.rank.charge()
        upper_rank = scheduler.source_projection(
            adapter, image, SourceImageDemand("rank-before", (upper - 1,))
        ).value
        lower_rank = scheduler.source_projection(
            adapter, image, SourceImageDemand("rank-before", (lower - 1,))
        ).value
        if type(upper_rank) is not int or type(lower_rank) is not int:
            raise RuntimeError("prime successor image returned a noninteger rank")
        # Only factors removed by this admitted stage are added back. A rank
        # workspace may already contain a longer consecutive prefix; its later
        # factors still survive this cylinder and must not be counted twice.
        known = min(depth, self.rank.factor_rank(upper - 1)) - min(
            depth, self.rank.factor_rank(lower - 1)
        )
        self._update_peak(arena)
        self.rank.ledger.bump(_prime_keys.PRIME_PARTIAL_SUCCESSOR_INTERVAL_PROJECTIONS)
        return upper_rank - lower_rank + known

    def close(self) -> None:
        if self._closed:
            return
        self._dispose_stage()
        self._closed = True


__all__ = ["PrimePartialSuccessorQuery"]
