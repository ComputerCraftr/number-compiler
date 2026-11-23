"""Source-bound, quotient-first Legendre actions with singleton cutoff storage.

The rank owner supplies its authenticated *consecutive* prime prefix.  This
module never discovers primes or publishes a separate rank/certification owner.
It evaluates demanded full intervals on the existing 210-wheel ordinals.

A row carries sum(w_d * Phi_d(L,H)).  Its single-cutoff representation is
canonical; only two simultaneously live distinct cutoffs allocate a histogram.
Terminal responses are folded into the answer before child insertion.
"""

from __future__ import annotations

from bisect import bisect_right
from collections.abc import Callable
from dataclasses import dataclass
from heapq import heappop, heappush
from math import isqrt
from typing import TYPE_CHECKING

from number_compiler.resources.lifecycle import cleanup_all
from number_compiler.resources.metric_keys import prime as prime_metrics
from number_compiler.resources.owned_memo import LedgerReservation
from number_compiler.sequences.prime.ordered_rank import (
    ORDERED_WHEEL_210_RESIDUES,
    wheel_210_count,
    wheel_210_value,
)

if TYPE_CHECKING:
    from number_compiler.sequences.prime.coprime_rank import CoprimeRankDAG

_W = 210
_RES = ORDERED_WHEEL_210_RESIDUES
# Maximum basis mask: 8 Ki * 4096 cutoffs <= 4 MiB per query, before
# Python object overhead. Beyond this bound use the original child path.
_MASK_ORDINAL_CAP = 8192
_ELIGIBLE = tuple(t in _RES for t in range(_W))


class SignedCutoffRow:
    """Mutable row with exactly zero, one, or several nonzero cutoff weights.

    `take` drains a row before processing so later reactivation starts afresh.
    The owning scheduler, not this class, controls queue uniqueness.
    """

    __slots__ = ("cutoff", "weight", "histogram", "queued")

    def __init__(self) -> None:
        self.cutoff = -1
        self.weight = 0
        self.histogram: dict[int, int] | None = None
        self.queued = False

    def add(self, cutoff: int, weight: int) -> tuple[int, int, int]:
        """Return (promotions, demotions, zero cancellations)."""
        if weight == 0:
            return 0, 0, 0
        hist = self.histogram
        if hist is None:
            if self.weight == 0:
                self.cutoff, self.weight = cutoff, weight
                return 0, 0, 0
            if self.cutoff == cutoff:
                self.weight += weight
                if self.weight == 0:
                    self.cutoff = -1
                    return 0, 0, 1
                return 0, 0, 0
            self.histogram = {self.cutoff: self.weight, cutoff: weight}
            self.cutoff, self.weight = -1, 0
            return 1, 0, 0
        new = hist.get(cutoff, 0) + weight
        if new:
            hist[cutoff] = new
        else:
            hist.pop(cutoff, None)
        if len(hist) <= 1:
            if hist:
                self.cutoff, self.weight = next(iter(hist.items()))
            else:
                self.cutoff, self.weight = -1, 0
            self.histogram = None
            return 0, 1, int(not new)
        return 0, 0, int(not new)

    def __bool__(self) -> bool:
        return self.weight != 0 or bool(self.histogram)

    def take(self) -> tuple[tuple[int, int], ...]:
        hist = self.histogram
        items: tuple[tuple[int, int], ...]
        if hist is None:
            items = ((self.cutoff, self.weight),) if self.weight else ()
        else:
            items = tuple(hist.items())
        self.cutoff, self.weight, self.histogram = -1, 0, None
        return items


def _histogram_size_after(row: SignedCutoffRow, cutoff: int, weight: int) -> int:
    histogram = row.histogram
    if histogram is None:
        if row.weight and row.cutoff != cutoff and weight:
            return 2
        return 0
    size = len(histogram)
    old = histogram.get(cutoff, 0)
    new = old + weight
    if old == 0 and new != 0:
        size += 1
    elif old != 0 and new == 0:
        size -= 1
    if size <= 1:
        return 0
    return size


@dataclass(slots=True)
class WeightedCutoffMetrics:
    singleton_rows: int = 0
    multi_rows: int = 0
    promotions: int = 0
    demotions: int = 0
    cancellations: int = 0
    histogram_allocations: int = 0
    queue_pushes: int = 0
    queue_pops: int = 0
    factor_probes: int = 0
    terminal_corrections: int = 0
    projection_builds: int = 0
    one_wheel_projections: int = 0
    peak_pending_rows: int = 0
    mask_terminal_hits: int = 0
    mask_cutoff_builds: int = 0
    mask_marks: int = 0
    fused_mask_bands: int = 0
    fused_mask_terms: int = 0
    fused_mask_nonempty: int = 0
    mask_budget_fallbacks: int = 0
    # Factor-loop operations only; these do not include rank-owner basis work
    # or lazy prefix-mask construction. They retain the actual operation counts
    # so a smaller projection count cannot masquerade as fewer factors.
    factor_floor_divisions: int = 0
    factor_modulo_tests: int = 0
    wheel_divmods: int = 0
    scalar_guard_empty: int = 0
    scalar_guard_hits: int = 0
    wheel_ineligible_nonempty: int = 0


class LazyBasisPrefixMasks:
    """Query-local exact prefix masks on the authenticated SMALL prime basis.

    Bit k-1 corresponds to the k-th 210-wheel survivor <= basis_limit.
    `excluded[cutoff]` contains only survivors removed by factors at
    positions [4, cutoff). The masks NEVER cover the searched rank interval.
    """

    __slots__ = (
        "owner",
        "factors",
        "basis_limit",
        "ordinal_limit",
        "excluded",
        "metrics",
        "reserve",
    )

    def __init__(
        self,
        owner: CoprimeRankDAG,
        factors: tuple[int, ...],
        metrics: WeightedCutoffMetrics,
        reserve: Callable[[int, int], None],
    ) -> None:
        self.owner = owner
        self.factors = factors
        self.basis_limit = factors[-1]
        self.ordinal_limit = wheel_210_count(self.basis_limit)
        # A four-factor cutoff is the base 210-wheel. No further strikes.
        self.excluded: dict[int, int] = {4: 0}
        self.metrics = metrics
        self.reserve = reserve

    def count(self, lower: int, upper: int, cutoff: int) -> int:
        """Exact survivors in the ordinal interval (lower,upper]."""
        if not (0 <= lower <= upper <= self.ordinal_limit):
            raise ValueError("prefix mask endpoint outside certified prime basis")
        if not (4 <= cutoff <= len(self.factors)):
            raise ValueError("prefix mask cutoff outside consecutive factor prefix")
        if lower == upper:
            return 0
        excluded = self.excluded.get(cutoff)
        if excluded is None:
            self.reserve(1, 1 + (self.ordinal_limit + 63) // 64)
            # Reuse the largest already demanded lower cutoff; build no masks
            # at unrequested intermediate cutoffs. The factor source is fixed
            # for this query, and all factors beyond the 210-wheel are coprime.
            start = max(index for index in self.excluded if index < cutoff)
            excluded = self.excluded[start]
            bound = self.basis_limit
            marks = 0
            for i in range(start, cutoff):
                q = self.factors[i]
                # q is coprime to the certified wheel. Multiples eligible
                # for masking are precisely q times wheel survivors <= B/q.
                # Count and charge these BEFORE constructing their bit ports.
                nmarks = wheel_210_count(bound // q)
                self.owner.charge_many(nmarks + 1)
                for k in range(1, nmarks + 1):
                    multiple = q * wheel_210_value(k)
                    excluded |= 1 << (wheel_210_count(multiple) - 1)
                marks += nmarks
            self.metrics.mask_marks += marks
            self.metrics.mask_cutoff_builds += 1
            self.excluded[cutoff] = excluded
        # The mask is a bit-set of EXCLUDED wheel survivors; the answer
        # is the wheel interval count minus their masked popcount.
        width = upper - lower
        removed = ((excluded >> lower) & ((1 << width) - 1)).bit_count()
        self.owner.charge()
        return width - removed


class WeightedCutoffInterval:
    """Query-local evaluator using the same CoprimeRankDAG factor authority.

    No memo or action escapes a query. The compiler's existing rank engine
    remains the production authority; calls charge the same source ledger.
    """

    def __init__(
        self,
        owner: CoprimeRankDAG,
        scratch_owner: int,
        *,
        fused_masks: bool = False,
        scalar_single_multiple_guard: bool = True,
    ) -> None:
        self.owner = owner
        self.scratch_owner = scratch_owner
        self.prefix_mask_terminal = fused_masks
        self.fused_prefix_mask_bands = fused_masks
        self.scalar_single_multiple_guard = scalar_single_multiple_guard
        self.metrics = WeightedCutoffMetrics()

    def count(self, lower: int, upper: int, depth: int) -> int:
        rank = self.owner
        if type(lower) is not int or type(upper) is not int or lower > upper:
            raise ValueError("invalid weighted interval")
        if type(depth) is not int or depth < 4 or depth > rank.factor_count:
            raise ValueError("weighted interval requires the admitted 210-wheel prefix")
        rank.validate_consecutive_prefix(depth)
        factors = rank.primes
        if depth != len(factors):
            factors = factors[:depth]
        if factors[:4] != (2, 3, 5, 7):
            raise ValueError("weighted rank requires the admitted 210-wheel prefix")
        with LedgerReservation(rank.ledger, self.scratch_owner) as reserve:
            try:
                return self._count_admitted(lower, upper, depth, factors, reserve)
            finally:
                metrics = self.metrics
                cleanup_all(
                    (
                        lambda: rank.ledger.bump(
                            prime_metrics.PRIME_WEIGHTED_FACTOR_PROBES,
                            metrics.factor_probes,
                        ),
                        lambda: rank.ledger.bump(
                            prime_metrics.PRIME_WEIGHTED_FLOOR_DIVISIONS,
                            metrics.factor_floor_divisions,
                        ),
                        lambda: rank.ledger.bump(
                            prime_metrics.PRIME_WEIGHTED_MODULO_TESTS,
                            metrics.factor_modulo_tests,
                        ),
                        lambda: rank.ledger.bump(
                            prime_metrics.PRIME_WEIGHTED_WHEEL_PROJECTIONS,
                            metrics.projection_builds,
                        ),
                        lambda: rank.ledger.bump(
                            prime_metrics.PRIME_WEIGHTED_FUSED_MASK_TERMS,
                            metrics.fused_mask_terms,
                        ),
                        lambda: rank.ledger.bump(
                            prime_metrics.PRIME_WEIGHTED_MASK_BUILDS,
                            metrics.mask_cutoff_builds,
                        ),
                    )
                )

    def _count_admitted(
        self,
        lower: int,
        upper: int,
        depth: int,
        factors: tuple[int, ...],
        reserve: LedgerReservation,
    ) -> int:
        rank = self.owner

        def reserve_space(entries: int, nodes: int) -> None:
            if (
                rank.max_states is not None
                and rank.ledger.entries - rank.factor_count + entries > rank.max_states
            ):
                raise ValueError("prime state budget exceeded (--max-prime-states)")
            reserve.reserve(entries=entries, nodes=nodes)

        low, high = wheel_210_count(lower), wheel_210_count(upper)
        if low == high:
            rank.charge()
            return 0

        # Invariant: one scheduled worklist node for each (low,high), even if
        # several signed cutoffs contribute to its canonical row.
        rows: dict[tuple[int, int], SignedCutoffRow] = {}
        heap: list[tuple[int, int, int]] = []
        result: int = 0
        met = self.metrics = WeightedCutoffMetrics()
        want_masks = self.prefix_mask_terminal or self.fused_prefix_mask_bands
        basis_ordinal_limit = wheel_210_count(factors[-1]) if want_masks else -1
        if want_masks and basis_ordinal_limit > _MASK_ORDINAL_CAP:
            # Never allocate a growing uncharged mask universe. The exact
            # weighted recursion remains the source-owned fallback.
            masks = None
            met.mask_budget_fallbacks += 1
        else:
            masks = (
                LazyBasisPrefixMasks(rank, factors, met, reserve_space)
                if want_masks
                else None
            )

        def add(klo: int, khi: int, cutoff: int, weight: int) -> None:
            nonlocal result
            if not weight or klo >= khi:
                return
            if cutoff == 4 or khi <= 1:
                met.terminal_corrections += 1
                rank.charge()
                result += weight * (khi - klo)
                return
            if (
                self.prefix_mask_terminal
                and masks is not None
                and khi <= basis_ordinal_limit
            ):
                # A direct, exact varying-cutoff reply even when composites
                # survive: evaluate before constructing a mutable action row.
                result += weight * masks.count(klo, khi, cutoff)
                met.mask_terminal_hits += 1
                met.terminal_corrections += 1
                return
            key = (klo, khi)
            row = rows.get(key)
            if row is None:
                rank.charge()
                reserve_space(1, 2)
                row = rows[key] = SignedCutoffRow()
            before = len(row.histogram) if row.histogram is not None else 0
            predicted = _histogram_size_after(row, cutoff, weight)
            growth = max(0, predicted - before)
            if growth:
                reserve_space(growth, growth)
            p, d, z = row.add(cutoff, weight)
            after = len(row.histogram) if row.histogram is not None else 0
            if after != predicted:
                raise RuntimeError("weighted cutoff scratch prediction failed")
            if after < before:
                reserve.release(entries=before - after, nodes=before - after)
            met.promotions += p
            met.histogram_allocations += p
            met.demotions += d
            met.cancellations += z
            if row and not row.queued:
                # All children decrease physical high, hence decrease ordinal
                # high: this is a topologically ordered worklist.
                heappush(heap, (-khi, -klo, cutoff))
                row.queued = True
                met.queue_pushes += 1
            met.peak_pending_rows = max(met.peak_pending_rows, len(rows))

        add(low, high, depth, 1)
        pending_entries = pending_nodes = 0
        try:
            while heap:
                if pending_entries or pending_nodes:
                    reserve.release(entries=pending_entries, nodes=pending_nodes)
                    pending_entries = pending_nodes = 0
                neg_high, neg_low, _ = heappop(heap)
                met.queue_pops += 1
                key = (-neg_low, -neg_high)
                row = rows.pop(key, None)
                if row is None:
                    continue
                histogram_size = len(row.histogram) if row.histogram is not None else 0
                # Retain accounting for the row while its drained cutoff tuple
                # and temporary ordered bands are evaluated.
                temporary = max(1, histogram_size)
                reserve_space(temporary, 4 * temporary)
                pending_entries = 1 + histogram_size + temporary
                pending_nodes = 2 + histogram_size + 4 * temporary
                row.queued = False
                if not row:
                    continue
                parts = row.take()
                bands: tuple[tuple[int, int, int], ...]
                if len(parts) == 1:
                    met.singleton_rows += 1
                else:
                    met.multi_rows += 1
                rank.charge()
                kl, kh = key
                XL, XH = wheel_210_value(kl), wheel_210_value(kh)

                # Certified prime tail: all composites are already removed by
                # primes <= sqrt(XH). Later primes delete only themselves.
                # Fold that tail into one core-cutoff coefficient plus a direct
                # terminal correction. Do this BEFORE constructing children.
                core = max(4, bisect_right(factors, isqrt(XH), 0, depth))
                if core < depth:
                    lo_p = bisect_right(factors, XL, 0, depth)
                    hi_p = bisect_right(factors, XH, 0, depth)
                    folded = SignedCutoffRow()
                    for d, w in parts:
                        if d > core:
                            removed = max(0, min(d, hi_p) - max(core, lo_p))
                            if removed:
                                result -= w * removed
                                met.terminal_corrections += 1
                                rank.charge()
                            d = core
                        p, de, z = folded.add(d, w)
                        met.promotions += p
                        met.histogram_allocations += p
                        met.demotions += de
                        met.cancellations += z
                    parts = folded.take()
                    if not parts:
                        continue
                total_weight = sum(weight for _, weight in parts)
                result += total_weight * (kh - kl)
                rank.charge()

                # Process sparse coefficient *bands*; a singleton row performs
                # the common case with no histogram construction or sorting.
                if len(parts) == 1:
                    cutoff, weight = parts[0]
                    bands = ((cutoff, 4, weight),)
                else:
                    by_cutoff = sorted(parts, reverse=True)
                    suffix = 0
                    bands_list: list[tuple[int, int, int]] = []
                    for i, (cutoff, weight) in enumerate(by_cutoff):
                        suffix += weight
                        bound = by_cutoff[i + 1][0] if i + 1 < len(by_cutoff) else 4
                        if suffix and cutoff > bound:
                            bands_list.append((cutoff, bound, suffix))
                    bands = tuple(bands_list)
                threshold = XH // _W
                width = XH - XL

                for top, bottom, coeff in bands:
                    # The same source-owned factor traversal serves fused
                    # mask responses and the original weighted child path.
                    # In either case every factor is visited exactly once.
                    split = top
                    if self.fused_prefix_mask_bands and masks is not None:
                        # q > XH//(B+1) ensures every projected cofactor fits
                        # inside the authenticated, basis-bounded mask.
                        split = max(
                            bottom,
                            bisect_right(factors, XH // (factors[-1] + 1), bottom, top),
                        )
                        if top > split:
                            met.fused_mask_bands += 1
                    # One split makes all higher factors sparse, without a
                    # q>width comparison on each factor or a second search.
                    sparse_start = (
                        max(bottom, bisect_right(factors, width, bottom, top))
                        if self.scalar_single_multiple_guard
                        else top
                    )
                    for i in range(top, bottom, -1):
                        q = factors[i - 1]
                        met.factor_probes += 1
                        # Keep the original conservative source work charge
                        # even when the scalar guard rejects a child early.
                        rank.charge(XH.bit_length() + q.bit_length())
                        if i > sparse_start:
                            met.factor_modulo_tests += 1
                            # q>width: at most one multiple in (XL,XH].
                            # Test a remainder before paying for H//q.
                            if XH % q >= width:
                                met.scalar_guard_empty += 1
                                if i > split:
                                    met.fused_mask_terms += 1
                                continue
                            t = XH // q
                            met.factor_floor_divisions += 1
                            # Even an exact integer multiple contributes no
                            # ordinal child unless its cofactor survives W.
                            eligible = (
                                _ELIGIBLE[t] if q > threshold else _ELIGIBLE[t % _W]
                            )
                            if not eligible:
                                met.wheel_ineligible_nonempty += 1
                                if i > split:
                                    met.fused_mask_terms += 1
                                continue
                            if q > threshold:
                                h = wheel_210_count(t)
                                met.one_wheel_projections += 1
                            else:
                                h = wheel_210_count(t)
                                met.wheel_divmods += int(t >= 1)
                            lower_ordinal = h - 1
                            met.scalar_guard_hits += 1
                            met.projection_builds += 1
                        else:
                            xl, xh = XL // q, XH // q
                            met.factor_floor_divisions += 2
                            if q > threshold:
                                lower_ordinal, h = (
                                    wheel_210_count(xl),
                                    wheel_210_count(xh),
                                )
                                met.one_wheel_projections += 2
                            else:
                                lower_ordinal, h = (
                                    wheel_210_count(xl),
                                    wheel_210_count(xh),
                                )
                                met.wheel_divmods += int(xl >= 1) + int(xh >= 1)
                            met.projection_builds += 2
                        if i > split:
                            met.fused_mask_terms += 1
                            if lower_ordinal < h:
                                assert masks is not None
                                result -= coeff * masks.count(lower_ordinal, h, i - 1)
                                met.terminal_corrections += 1
                                met.fused_mask_nonempty += 1
                        elif lower_ordinal < h:
                            add(lower_ordinal, h, i - 1, -coeff)
            return result
        finally:
            # Every mutable action is query-local, including after budget
            # errors. No source prefix, rank memo, or shared cache is changed.
            rows.clear()
            heap.clear()
