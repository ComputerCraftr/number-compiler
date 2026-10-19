"""Lazy spatial carry ports for one authenticated reverse/add source."""

from __future__ import annotations

from collections.abc import Callable, Generator, Iterator, Mapping
from dataclasses import dataclass

from number_compiler.arithmetic.carry.carry_monoid import (
    CarryFn,
    apply_carry_fn,
    compose_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.contracts.cylinder_chart import (
    CylinderChart,
    right_dyadic_blocks,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.formula.decimal_pair_coordinates import (
    decimal_add_cocycle,
    decimal_cocycle_value,
    decimal_normalize_cocycle,
)
from number_compiler.arithmetic.formula.skew_residue_laws import (
    pair_growth_edge,
    pair_growth_interior,
    pair_no_growth,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as _reverse_add_keys
from number_compiler.resources.output_stream_metrics import closing_output_stream
from number_compiler.resources.owned_memo import OwnedMemoAuditSnapshot


@dataclass(slots=True)
class _IntervalFrame:
    key: tuple[int, int, int]
    expanded: bool = False


class _QueryWorkspace:
    """Explicitly charged, nonretained references for one interval query."""

    __slots__ = ("created", "ledger", "owner", "pruned", "stack")

    def __init__(self, ledger: ResourceLedger, owner: int) -> None:
        self.ledger = ledger
        self.owner = owner
        self.stack: list[_IntervalFrame] = []
        self.created: dict[tuple[int, int, int], None] = {}
        self.pruned: dict[tuple[int, int, int], None] = {}

    def _note_peak(self) -> None:
        count = len(self.stack) + len(self.created) + len(self.pruned)
        peak = self.ledger.counters.get(
            _reverse_add_keys.REVERSE_SOURCE_PORTS_WORKSPACE_PEAK, 0
        )
        if count > peak:
            self.ledger.bump(
                _reverse_add_keys.REVERSE_SOURCE_PORTS_WORKSPACE_PEAK, count - peak
            )

    def push(self, frame: _IntervalFrame) -> None:
        self.ledger.reserve(self.owner, nodes=1)
        try:
            self.stack.append(frame)
        except BaseException:
            self.ledger.release(self.owner, nodes=1)
            raise
        self._note_peak()

    def pop(self) -> _IntervalFrame:
        frame = self.stack.pop()
        self.ledger.release(self.owner, nodes=1)
        return frame

    def record(self, key: tuple[int, int, int]) -> None:
        self.ledger.reserve(self.owner, nodes=1)
        try:
            self.created[key] = None
        except BaseException:
            self.ledger.release(self.owner, nodes=1)
            raise
        self._note_peak()

    def forget(self, key: tuple[int, int, int]) -> None:
        if key not in self.created:
            return
        del self.created[key]
        self.ledger.release(self.owner, nodes=1)

    def pop_created(self) -> tuple[int, int, int]:
        key, _value = self.created.popitem()
        self.ledger.release(self.owner, nodes=1)
        return key

    def prune(self, key: tuple[int, int, int]) -> None:
        if key in self.pruned:
            return
        self.ledger.reserve(self.owner, nodes=1)
        try:
            self.pruned[key] = None
        except BaseException:
            self.ledger.release(self.owner, nodes=1)
            raise
        self._note_peak()

    def commit_pruning(
        self,
        cache: OwnedMemo[tuple[int, int, int], CarryFn],
    ) -> None:
        # Validate the complete transaction before removing any pre-existing
        # admitted child. Normal deletion is then nonfailing and exactly
        # releases the child's retained cache reservation.
        for key in self.pruned:
            found = cache.get(key)
            if found is not None and (
                type(found) is not CarryFn or found is not CarryFn.ID
            ):
                raise ValueError("identity carry interval has a nonidentity child")
        while self.pruned:
            key, _value = self.pruned.popitem()
            self.ledger.release(self.owner, nodes=1)
            if key in cache:
                del cache[key]
                self.forget(key)
                self.ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PORTS_IDENTITY_CHILDREN_PRUNED
                )

    def close(self) -> None:
        nodes = len(self.stack) + len(self.created) + len(self.pruned)
        self.stack.clear()
        self.created.clear()
        self.pruned.clear()
        if nodes:
            self.ledger.release(self.owner, nodes=nodes)


@dataclass(frozen=True, slots=True)
class SourceCarryPortsAuditSnapshot:
    """Fresh read-only evidence for the explicit source-port resource audit."""

    ledger: ResourceLedger
    source: ExactSource
    width: int
    authority: tuple[object, ...]
    cache: OwnedMemoAuditSnapshot[tuple[int, int, int], CarryFn]
    cache_identity: OwnedMemo[tuple[int, int, int], CarryFn]
    audit_cache: Mapping[tuple[int, int, int], CarryFn | object]
    workspace_owner: int
    workspace_authority: int
    closed: bool


class SourceCarryPorts:
    """Memoize dyadic spatial carry actions, never pair or carry rows."""

    __slots__ = (
        "__weakref__",
        "_audit_cache",
        "_authority",
        "_cache",
        "_cache_owner",
        "_closed",
        "_ledger",
        "_source",
        "_width",
        "_workspace_authority",
        "_workspace_owner",
    )

    def __init__(self, source: ExactSource, ledger: ResourceLedger) -> None:
        if type(source) is not ExactSource or type(ledger) is not ResourceLedger:
            raise TypeError("source carry ports require an exact source and ledger")
        coordinates = 2 * len(source.digits)
        ledger.bump(
            _reverse_add_keys.REVERSE_SOURCE_VALIDATION_COORDINATES, coordinates
        )
        ledger.bump(
            _reverse_add_keys.REVERSE_SOURCE_PORTS_VALIDATION_COORDINATES,
            coordinates,
        )
        # Keep the established source-pullback metrics present while the new
        # interval implementation records the same work at its actual leaves.
        ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PULLBACK_PAIR_READS, 0)
        ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PULLBACK_PREDECESSOR_SEARCH, 0)
        ledger.bump(_reverse_add_keys.REVERSE_SOURCE_LENGTH_PAIR_READS, 0)
        source.__post_init__()
        if not source.digits:
            raise ValueError("source carry ports require nonempty original digits")
        cache_owner = ledger.register(
            f"reverse-source-ports-{ledger.owner_count}",
            "reverse_source_carry_interval",
        )
        workspace_owner = ledger.register(
            f"reverse-source-ports-workspace-{ledger.owner_count}",
            "reverse_source_carry_workspace",
        )
        cache: OwnedMemo[tuple[int, int, int], CarryFn] = OwnedMemo(
            ledger,
            cache_owner,
            nodes_per_entry=1,
            composition_entries=True,
        )
        self._source = source
        self._ledger = ledger
        self._width = len(source.digits)
        # Preserve the established seven ExactSource fields for read-only audit.
        self._authority = (
            source,
            source.digits,
            source.base,
            source.orbit,
            source.blank,
            source.extent,
            source.alphabet_size,
            ledger,
            cache,
            cache_owner,
        )
        self._cache = cache
        self._cache_owner = cache_owner
        self._audit_cache = cache._data
        self._workspace_owner = workspace_owner
        self._workspace_authority = workspace_owner
        self._closed = False
        ledger.register_execution_root(self)
        from number_compiler.resources.payload_contracts import (
            PayloadAuditStoreBinding,
        )
        from number_compiler.sequences.reverse_add.source_payload_audit import (
            audit_reverse_source_owner,
        )

        ledger.register_payload_audit_contract(
            self,
            "reverse_add",
            (
                PayloadAuditStoreBinding(
                    cache_owner,
                    "_audit_cache",
                    "reverse_source_carry_interval",
                ),
            ),
            audit_reverse_source_owner,
        )

    @property
    def source(self) -> ExactSource:
        self._check_open()
        return self._source

    @property
    def ledger(self) -> ResourceLedger:
        self._check_open()
        return self._ledger

    @property
    def resource_ledger(self) -> ResourceLedger:
        """Return immutable ledger ownership metadata, including after close."""
        return self._ledger

    @property
    def width(self) -> int:
        self._check_open()
        return self._width

    def audit_snapshot(self) -> SourceCarryPortsAuditSnapshot:
        """Return current source/cache bindings without exposing writable fields."""
        cache = self._cache.audit_snapshot()
        return SourceCarryPortsAuditSnapshot(
            self._ledger,
            self._source,
            self._width,
            self._authority,
            cache,
            self._cache,
            self._audit_cache,
            self._workspace_owner,
            self._workspace_authority,
            self._closed,
        )

    def _check_open(self) -> None:
        if self._closed:
            raise ValueError("disposed source carry ports")
        self.check_source(self._source)

    def check_source(self, source: ExactSource) -> None:
        """Authenticate the exact original object and immutable binding in O(1)."""
        if self._closed:
            raise ValueError("disposed source carry ports")
        if type(source) is not ExactSource:
            raise TypeError("source carry ports require an exact source")
        authority = self._authority
        if (
            source is not authority[0]
            or source.digits is not authority[1]
            or source.base != authority[2]
            or source.orbit != authority[3]
            or source.blank != authority[4]
            or source.extent != authority[5]
            or source.alphabet_size != authority[6]
            or self._ledger is not authority[7]
            or self._cache is not authority[8]
            or self._cache.owner != authority[9]
            or self._cache.ledger is not self._ledger
            or self._source is not authority[0]
            or self._width != len(authority[1])
            or self._workspace_owner != self._workspace_authority
        ):
            raise ValueError("source carry port binding was altered or is foreign")
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_BINDING_CHECKS)

    def _raw_first_pair(self, position: int) -> int:
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_SOURCE_READS, 2)
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PULLBACK_PAIR_READS)
        digits = self._source.digits
        return digits[position] + digits[self._width - 1 - position]

    def first_pair(self, position: int) -> int:
        self._check_open()
        if type(position) is not int or not 0 <= position < self._width:
            raise IndexError(position)
        return self._raw_first_pair(position)

    def pair(self, position: int) -> int:
        return self.first_pair(position)

    def _exact_cached(self, key: tuple[int, int, int]) -> CarryFn | None:
        found = self._cache.get(key)
        if found is not None:
            if type(found) is not CarryFn:
                raise ValueError("source carry interval cache was altered")
            self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_INTERVAL_HITS)
            return found
        return None

    def _cached(
        self,
        key: tuple[int, int, int],
        extent: int,
    ) -> CarryFn | None:
        found = self._exact_cached(key)
        if found is not None:
            return found

        layer, start, span = key
        parent_span = span << 1
        while parent_span <= extent:
            parent_start = start - start % parent_span
            if parent_start + parent_span > extent:
                break
            self._ledger.bump(
                _reverse_add_keys.REVERSE_SOURCE_PORTS_IDENTITY_ANCESTOR_PROBES
            )
            ancestor = self._cache.get((layer, parent_start, parent_span))
            if ancestor is not None:
                if type(ancestor) is not CarryFn:
                    raise ValueError("source carry interval cache was altered")
                if ancestor is CarryFn.ID:
                    self._ledger.bump(
                        _reverse_add_keys.REVERSE_SOURCE_PORTS_IDENTITY_ANCESTOR_HITS
                    )
                    return CarryFn.ID
                # A reset summary says nothing about a proper subinterval. A
                # valid identity ancestor cannot exist above a reset interval.
                self._ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PORTS_RESET_ANCESTOR_REJECTIONS
                )
                break
            parent_span <<= 1
        return None

    def _publish(
        self,
        workspace: _QueryWorkspace,
        key: tuple[int, int, int],
        result: CarryFn,
    ) -> None:
        workspace.record(key)
        try:
            self._cache[key] = result
        except BaseException:
            workspace.forget(key)
            raise
        if result is CarryFn.ID and key[2] > 1:
            half = key[2] // 2
            children = ((key[0], key[1], half), (key[0], key[1] + half, half))
            for child in children:
                found = self._cache.get(child)
                if found is None:
                    continue
                if type(found) is not CarryFn or found is not CarryFn.ID:
                    raise ValueError("identity carry interval has a nonidentity child")
                workspace.prune(child)
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_INTERVAL_PUBLICATIONS)

    def _first_interval(self, start: int, span: int) -> CarryFn:
        return self._carry_interval(
            1,
            start,
            span,
            self._width,
            lambda position: value_carry_fn(
                self._raw_first_pair(position), self._source.base
            ),
            "first",
        )

    def _carry_interval(
        self,
        stage: int,
        start: int,
        span: int,
        extent: int,
        leaf: Callable[[int], CarryFn],
        label: str,
    ) -> CarryFn:
        root = stage, start, span
        found = self._cached(root, extent)
        if found is not None:
            return found
        workspace = _QueryWorkspace(self._ledger, self._workspace_owner)
        try:
            workspace.push(_IntervalFrame(root))
            while workspace.stack:
                frame = workspace.stack[-1]
                cached = self._exact_cached(frame.key)
                if cached is not None:
                    workspace.pop()
                    continue
                _, current_start, current_span = frame.key
                self._ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PORTS_POSTORDER_FRAMES
                )
                if current_span == 1:
                    result = leaf(current_start)
                    self._publish(workspace, frame.key, result)
                    workspace.pop()
                    continue
                half = current_span // 2
                left = stage, current_start, half
                right = stage, current_start + half, half
                if not frame.expanded:
                    frame.expanded = True
                    if self._exact_cached(right) is None:
                        workspace.push(_IntervalFrame(right))
                    continue
                after = self._exact_cached(right)
                if after is None:
                    raise AssertionError("right carry interval was not constructed")
                if after is CarryFn.ID:
                    before = self._exact_cached(left)
                    if before is None:
                        workspace.push(_IntervalFrame(left))
                        continue
                    result = compose_carry_fn(after, before)
                else:
                    result = after
                    self._ledger.bump(
                        _reverse_add_keys.REVERSE_SOURCE_PORTS_RESET_SHORTCUTS
                    )
                self._publish(workspace, frame.key, result)
                self._ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PORTS_INTERVAL_COMPOSITIONS
                )
                workspace.pop()
            workspace.commit_pruning(self._cache)
        except BaseException:
            while workspace.created:
                key = workspace.pop_created()
                del self._cache[key]
            self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_FAILED_QUERIES)
            raise
        finally:
            workspace.close()
        published = self._exact_cached(root)
        if published is None:
            raise AssertionError(f"{label} carry interval was not published")
        return published

    def _first_range(self, start: int, stop: int) -> CarryFn:
        effect = CarryFn.ID
        for position, span in right_dyadic_blocks(start, stop):
            effect = compose_carry_fn(effect, self._first_interval(position, span))
            self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_PREFIX_BLOCKS)
            if effect is not CarryFn.ID:
                self._ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PORTS_PREFIX_RESET_SHORTCUTS
                )
                break
        return effect

    def _first_prefix(self, boundary: int) -> int:
        if type(boundary) is not int or not 0 <= boundary <= self._width:
            raise IndexError(boundary)
        effect = self._first_range(0, boundary)
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_LAYER_1_CARRY_QUERIES)
        return apply_carry_fn(effect, 0)

    def carry(self, boundary: int) -> int:
        self._check_open()
        return self._first_prefix(boundary)

    @property
    def terminal(self) -> int:
        self._check_open()
        return self._first_prefix(self._width)

    def iter_first_ports(
        self, *, reflected: bool = False
    ) -> Generator[tuple[int, int], None, None]:
        """Stream physical incoming/outgoing carries in either coordinate order.

        Reflection changes traversal order only. Each right child receives the
        left child's forward carry effect; no reverse carry law is introduced.
        The charged stack retains logarithmically many region contexts, not rows.
        """
        self._check_open()
        stack: list[tuple[int, int, int, bool]] = []

        def push(start: int, span: int, incoming: int, neutral: bool) -> None:
            self._ledger.reserve(self._workspace_owner, nodes=1)
            try:
                stack.append((start, span, incoming, neutral))
            except BaseException:
                self._ledger.release(self._workspace_owner, nodes=1)
                raise

        root_span = 1 << (self._width - 1).bit_length()
        root_neutral = (
            root_span == self._width
            and self._exact_cached((1, 0, root_span)) is CarryFn.ID
        )
        push(0, root_span, 0, root_neutral)
        try:
            while stack:
                self._check_open()
                start, span, incoming, neutral = stack.pop()
                self._ledger.release(self._workspace_owner, nodes=1)
                if start >= self._width:
                    continue
                self._ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PORTS_STREAM_REGION_VISITS
                )
                if not neutral and start + span <= self._width:
                    neutral = self._exact_cached((1, start, span)) is CarryFn.ID
                if span == 1:
                    effect = (
                        CarryFn.ID if neutral else self._first_interval(start, span)
                    )
                    yield incoming, apply_carry_fn(effect, incoming)
                    continue
                half = span // 2
                left_effect = (
                    CarryFn.ID
                    if neutral
                    else (
                        self._first_interval(start, half)
                        if start + half <= self._width
                        else self._first_range(start, self._width)
                    )
                )
                middle = apply_carry_fn(left_effect, incoming)
                if reflected:
                    push(start, half, incoming, left_effect is CarryFn.ID)
                    push(start + half, half, middle, neutral)
                else:
                    push(start + half, half, middle, neutral)
                    push(start, half, incoming, left_effect is CarryFn.ID)
        finally:
            if stack:
                self._ledger.release(self._workspace_owner, nodes=len(stack))
                stack.clear()

    def _raw_second_pair(self, position: int, growth: int) -> int:
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_LENGTH_PAIR_READS)
        base = self._source.base
        if base == 10:
            domain, alpha, epsilon, _ = self._second_decimal_cocycle(position, growth)
            result = decimal_cocycle_value(domain, alpha, epsilon)
        elif growth and position in (0, self._width):
            result = pair_growth_edge(
                self._raw_first_pair(0), self._first_prefix(1), base
            )
        elif growth:
            result = pair_growth_interior(
                self._raw_first_pair(position),
                self._raw_first_pair(position - 1),
                self._first_prefix(position),
                self._first_prefix(position + 1),
                self._first_prefix(self._width - position),
                self._first_prefix(self._width - position + 1),
                base,
            )
        else:
            result = pair_no_growth(
                self._raw_first_pair(position),
                self._first_prefix(position),
                self._first_prefix(position + 1),
                self._first_prefix(self._width - 1 - position),
                self._first_prefix(self._width - position),
                base,
            )
        if not 0 <= result <= 2 * base - 2:
            raise ValueError("second source pair left its radix")
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_SECOND_PAIR_QUERIES)
        return result

    def _first_output_channels(self, position: int, growth: int) -> tuple[int, int]:
        """Exact normalized F5/parity digit channels in the output chart.

        Only the forward incoming carry is demanded. Decimal wrap is already
        encoded by CRT; there is no second outgoing carry or digit renderer.
        """
        if growth and position == self._width:
            return 1, 1
        symbol = self._raw_first_pair(position)
        return decimal_normalize_cocycle(
            symbol % 5, symbol % 2, self._first_prefix(position)
        )

    def _second_decimal_cocycle(
        self, position: int, growth: int
    ) -> tuple[CarryFn, int, int, int]:
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_CRT_THRESHOLD_QUERIES)
        return decimal_add_cocycle(
            self._first_output_channels(position, growth),
            self._first_output_channels(self._width + growth - 1 - position, growth),
        )

    def second_pair(self, position: int) -> int:
        self._check_open()
        if type(position) is not int:
            raise IndexError(position)
        growth = self._first_prefix(self._width)
        extent = self._width + growth
        if type(position) is not int or not 0 <= position < extent:
            raise IndexError(position)
        return self._raw_second_pair(position, growth)

    def _iter_first_decimal_channels(
        self, growth: int, *, reflected: bool = False
    ) -> Generator[tuple[int, int], None, None]:
        """Consume the original carry tree without a midpoint digit word."""
        with closing_output_stream(
            self.iter_first_ports(reflected=reflected)
        ) as physical:
            if growth and reflected:
                yield 1, 1
            for index, (incoming, _) in enumerate(physical):
                self._check_open()
                position = self._width - 1 - index if reflected else index
                pair = self._raw_first_pair(position)
                yield decimal_normalize_cocycle(pair % 5, pair % 2, incoming)
            if growth and not reflected:
                yield 1, 1

    def iter_second_pairs(self) -> Iterator[int]:
        """Stream the pulled pair field with one authenticated growth choice.

        Decimal streams share regional physical carry contexts in forward and
        reflected coordinates. They retain neither a midpoint nor carry rows.
        """
        self._check_open()
        growth = self._first_prefix(self._width)
        if self._source.base != 10:
            for position in range(self._width + growth):
                self._check_open()
                yield self._raw_second_pair(position, growth)
            return
        with (
            closing_output_stream(self._iter_first_decimal_channels(growth)) as forward,
            closing_output_stream(
                self._iter_first_decimal_channels(growth, reflected=True)
            ) as reflected,
        ):
            for left, right in zip(forward, reflected, strict=True):
                self._check_open()
                domain, alpha, epsilon, _ = decimal_add_cocycle(left, right)
                self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_LENGTH_PAIR_READS)
                self._ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PORTS_CRT_THRESHOLD_QUERIES
                )
                self._ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PORTS_SECOND_PAIR_QUERIES
                )
                yield decimal_cocycle_value(domain, alpha, epsilon)

    def _second_interval(self, start: int, span: int, extent: int) -> CarryFn:
        growth = extent - self._width

        def leaf(position: int) -> CarryFn:
            return (
                self._second_decimal_cocycle(position, growth)[0]
                if self._source.base == 10
                else value_carry_fn(
                    self._raw_second_pair(position, growth), self._source.base
                )
            )

        return self._carry_interval(2, start, span, extent, leaf, "second")

    def _second_range(self, start: int, stop: int, extent: int) -> CarryFn:
        effect = CarryFn.ID
        for position, span in right_dyadic_blocks(start, stop):
            effect = compose_carry_fn(
                effect, self._second_interval(position, span, extent)
            )
            self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_PREFIX_BLOCKS)
            if effect is not CarryFn.ID:
                self._ledger.bump(
                    _reverse_add_keys.REVERSE_SOURCE_PORTS_PREFIX_RESET_SHORTCUTS
                )
                break
        return effect

    def _second_prefix(self, boundary: int, extent: int) -> int:
        if type(boundary) is not int or not 0 <= boundary <= extent:
            raise IndexError(boundary)
        effect = self._second_range(0, boundary, extent)
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_LAYER_2_CARRY_QUERIES)
        return apply_carry_fn(effect, 0)

    def range_transfer(
        self, layer: int, start: int, stop: int, chart: CylinderChart | None = None
    ) -> CarryFn:
        """Consume an oriented interval lens over an admitted pair field.

        M is the original digit width. G is zero for the first field and the
        admitted first growth for the second. Both pair fields are palindromic,
        so a descending image is reflected once into a forward range; no
        reverse scan or second copy of the carry tree is needed. This range
        operation does not admit additional temporal layers.
        """
        self._check_open()
        if type(layer) is not int or layer not in (1, 2):
            raise ValueError("source carry ranges support only admitted layers 1 and 2")
        if chart is None:
            chart = CylinderChart()
        if type(chart) is not CylinderChart:
            raise TypeError("source carry range requires a cylinder chart")
        # Validate the symbolic geometry before discovering any growth.
        chart.image(start, stop, self._width, 0)
        growth = 0 if layer == 1 else self._first_prefix(self._width)
        extent = self._width + growth
        low, high = chart.image(start, stop, self._width, growth)
        if not 0 <= low <= high <= extent:
            raise IndexError((low, high))
        if chart.slope == -1:
            low, high = extent - high, extent - low
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_RANGE_QUERIES)
        if layer == 1:
            return self._first_range(low, high)
        return self._second_range(low, high, extent)

    def second_carry(self, boundary: int) -> int:
        self._check_open()
        extent = self._width + self._first_prefix(self._width)
        return self._second_prefix(boundary, extent)

    def second_width(self) -> int:
        self._check_open()
        first_width = self._width + self._first_prefix(self._width)
        result = first_width + self._second_prefix(first_width, first_width)
        self._ledger.bump(_reverse_add_keys.REVERSE_SOURCE_PORTS_SECOND_WIDTH_QUERIES)
        return result

    def dispose(self) -> None:
        if self._closed:
            return
        self._cache.dispose()
        self._ledger.mark_disposed(self._workspace_owner)
        self._closed = True


__all__ = ["SourceCarryPorts"]
