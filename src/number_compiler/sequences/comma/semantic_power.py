"""Ledger-owned powered application for comma semantic continuations."""

from __future__ import annotations

from _thread import LockType
from collections.abc import Callable, Iterator
from contextlib import ExitStack, contextmanager
from dataclasses import dataclass
from math import lcm
from threading import Lock
from typing import Self, cast

from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.fused_traversal_workspace import (
    FusedTraversalWorkspace,
    fused_traversal_workspace_owner_names,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.comma.boundary_chart import PERIOD, BoundaryChart
from number_compiler.sequences.comma.domain import canonical_offset_orbit
from number_compiler.sequences.comma.return_mdd import (
    canonical_return_template,
    evaluate_return_column,
    substitute_return_column,
    translate_return_columns,
    union_return_columns,
)
from number_compiler.sequences.comma.return_scopes import (
    B1ReturnPartitionRecord,
    ReturnColumnKey,
    ReturnMDDPartition,
    continuation_return_partition,
    return_partition_node_cost,
    return_template_node_cost,
)
from number_compiler.sequences.comma.semantic_continuation import (
    ContinuationID,
    DecadeSummary,
    SemanticAction,
    SemanticContinuation,
    SourceState,
    TerminalWeight,
    normalize_source,
)


@dataclass(frozen=True, slots=True)
class _ReturnPowerBinding:
    """Unlabeled geometry plus exact output and clock occurrence transport."""

    columns: tuple[ReturnColumnKey, ...]
    labels: tuple[int, ...]
    return_shift: int
    period: int


def _power_binding_cost(_key: tuple[int, int], value: _ReturnPowerBinding) -> int:
    # The shared column graph belongs to the ColumnCID store. This account owns
    # the occurrence record and label tuple, not another copy of that graph.
    return 2 + len(value.labels)


def _translated_template_cost(
    _key: tuple[tuple[ReturnColumnKey, ...], int],
    value: tuple[ReturnColumnKey, ...],
) -> int:
    return return_template_node_cost(value, value)


def _column_node_cost(key: ReturnColumnKey, value: ReturnColumnKey) -> int:
    if key != value:
        raise ValueError("comma ColumnCID cache key and value must match")
    return return_template_node_cost((key,), value)


@contextmanager
def _workspace_reservation(
    ledger: ResourceLedger, owner: int
) -> Iterator[tuple[Callable[[int], None], Callable[[int], None]]]:
    """Account temporary MDD work once and release it on every exit path."""
    held = 0

    def reserve(nodes: int) -> None:
        nonlocal held
        ledger.reserve(owner, nodes=nodes)
        held += nodes

    def release(nodes: int) -> None:
        nonlocal held
        if type(nodes) is not int or not 0 <= nodes <= held:
            raise ValueError("comma workspace release exceeds its reservation")
        if nodes:
            ledger.release(owner, nodes=nodes)
            held -= nodes

    try:
        yield reserve, release
    finally:
        if held:
            ledger.release(owner, nodes=held)


@contextmanager
def _dispose_on_exit(dispose: Callable[[], None]) -> Iterator[None]:
    """Keep attempting later cleanup actions when one disposer raises."""
    try:
        yield
    finally:
        dispose()


class SymbolicDecadePowers:
    """Square completed B1 returns on CRT columns, without phase-row sampling.

    This is the symbolic action consumer of the existing continuation owner.
    B1 alone is common-shift normalized. Higher powers preserve their exact
    completed columns and output bindings; Stop weights and clock transport
    remain occurrence payload. This owner does not infer infinite branch
    safety; public prefix admission uses a separately registered global
    FutureCID provider when available and retains finite forest admission
    otherwise.
    """

    def __init__(self, view: SemanticContinuation) -> None:
        roots = view.roots
        if len(roots) != 46 or any(
            source.kind != "entry"
            or source.leading != 1
            or source.delta != 0
            or canonical_offset_orbit(source.coordinate) != index
            for index, source in enumerate(roots)
        ):
            raise ValueError("symbolic powers require the 46 ordered canonical roots")
        ledger = view.ledger
        prefix = f"comma-symbolic-powers-{ledger.owner_count}"
        owner_names = (
            prefix + "-base",
            prefix + "-columns",
            prefix + "-bindings",
            prefix + "-input-templates",
            prefix + "-composition-workspace",
        )
        ledger.require_fresh_owner_names(owner_names)
        self.view = view
        self._closed = False
        self._closing = False
        base_owner = ledger.register(prefix + "-base", "semantic_return_partition")
        self._base: OwnedMemo[ContinuationID, B1ReturnPartitionRecord] = OwnedMemo(
            ledger, base_owner, node_cost=return_partition_node_cost
        )
        column_owner = view.ledger.register(
            prefix + "-columns", "semantic_return_column"
        )
        self._columns: OwnedMemo[ReturnColumnKey, ReturnColumnKey] = OwnedMemo(
            ledger, column_owner, node_cost=_column_node_cost
        )
        power_owner = view.ledger.register(
            prefix + "-bindings", "semantic_return_power"
        )
        self._powers: OwnedMemo[tuple[int, int], _ReturnPowerBinding] = OwnedMemo(
            ledger,
            power_owner,
            node_cost=_power_binding_cost,
            composition_entries=True,
        )
        input_owner = view.ledger.register(
            prefix + "-input-templates", "semantic_return_input_template"
        )
        self._input_templates: OwnedMemo[
            tuple[tuple[ReturnColumnKey, ...], int], tuple[ReturnColumnKey, ...]
        ] = OwnedMemo(ledger, input_owner, node_cost=_translated_template_cost)
        self._composition_workspace_owner = ledger.register(
            prefix + "-composition-workspace", "semantic_return_composition_workspace"
        )
        self._completed_level = -1

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(self, _exc_type: object, _exc: object, _tb: object) -> None:
        self.close()

    def close(self) -> None:
        """Drop occurrence references before their shared template graphs."""
        if not self._closed:
            self._closing = True
            with ExitStack() as cleanup:
                cleanup.enter_context(
                    _dispose_on_exit(
                        lambda: self.view.ledger.mark_disposed(
                            self._composition_workspace_owner
                        )
                    )
                )
                cleanup.enter_context(_dispose_on_exit(self._base.dispose))
                cleanup.enter_context(_dispose_on_exit(self._columns.dispose))
                cleanup.enter_context(_dispose_on_exit(self._powers.dispose))
                cleanup.enter_context(_dispose_on_exit(self._input_templates.dispose))
            self._closed = True
            self._closing = False

    def _check_open(self) -> None:
        if self._closed or self._closing:
            raise RuntimeError("symbolic decade powers are closing or closed")

    def _publish(self, level: int, root: int, partition: ReturnMDDPartition) -> None:
        with _workspace_reservation(
            self.view.ledger, self._composition_workspace_owner
        ) as (reserve, release):
            if level == 0:
                template = canonical_return_template(
                    partition,
                    charge=self.view.ledger.bump,
                    reserve_workspace=reserve,
                    release_workspace=release,
                )
                raw_columns = template.columns
                labels = template.labels
                return_shift = template.return_shift
                period = template.period
            else:
                labels = tuple(label for label, _ in partition.columns)
                raw_columns = tuple(column for _, column in partition.columns)
                return_shift = 0
                period = partition.period
            columns_list: list[ReturnColumnKey] = []
            for column in raw_columns:
                interned = self._columns.get(column)
                if interned is None:
                    self.view.ledger.bump("comma_power_column_id_misses")
                    self._columns[column] = column
                    interned = column
                else:
                    self.view.ledger.bump("comma_power_column_id_hits")
                columns_list.append(interned)
            columns = tuple(columns_list)
            self._powers[level, root] = _ReturnPowerBinding(
                columns, labels, return_shift, period
            )
            self.view.ledger.bump("comma_power_publications")

    def _input_columns(
        self, binding: _ReturnPowerBinding
    ) -> tuple[tuple[int, ReturnColumnKey], ...]:
        shift = binding.return_shift % PERIOD
        if shift == 0:
            translated_columns = binding.columns
        else:
            key = binding.columns, shift
            cached_columns = self._input_templates.get(key)
            if cached_columns is None:
                self.view.ledger.bump("comma_power_input_template_misses")
                with _workspace_reservation(
                    self.view.ledger, self._composition_workspace_owner
                ) as (reserve, release):
                    translated_columns = translate_return_columns(
                        binding.columns,
                        shift,
                        charge=self.view.ledger.bump,
                        reserve_workspace=reserve,
                        release_workspace=release,
                    )
                    self._input_templates[key] = translated_columns
            else:
                self.view.ledger.bump("comma_power_input_template_hits")
                translated_columns = cached_columns
        return tuple(zip(binding.labels, translated_columns, strict=True))

    def _square(self, level: int, root: int) -> tuple[ReturnMDDPartition, int]:
        first = self._powers[level - 1, root]
        half = 1 << (level - 1)
        columns: dict[int, ReturnColumnKey] = {}
        period = first.period
        reserved_nodes = 0

        def reserve_scratch(nodes: int) -> None:
            nonlocal reserved_nodes
            self.view.ledger.reserve(self._composition_workspace_owner, nodes=nodes)
            reserved_nodes += nodes

        def release_scratch(nodes: int) -> None:
            nonlocal reserved_nodes
            self.view.ledger.release(self._composition_workspace_owner, nodes=nodes)
            reserved_nodes -= nodes

        def charge_aggregation(operation: str, amount: int) -> None:
            self.view.ledger.bump(operation, amount)
            if operation == "comma_output_template_mdd_union_nodes":
                reserve_scratch(amount)

        try:
            for label, left in self._input_columns(first):
                if label >= 46:
                    self.view.ledger.bump("comma_power_absorbing_terminal_copies")
                    contributions: tuple[tuple[int, ReturnColumnKey], ...] = (
                        (label, left),
                    )
                else:
                    second = self._powers[level - 1, label]
                    period = lcm(period, second.period)
                    # Reserve the sorted binding list and tuple before either
                    # allocation. The right column graph is shared unchanged.
                    continuation_nodes = 2 + 2 * len(second.labels)
                    reserve_scratch(continuation_nodes)
                    try:
                        continuation = tuple(
                            sorted(
                                (
                                    output if output < 46 else output + 9 * half,
                                    column,
                                )
                                for output, column in zip(
                                    second.labels, second.columns, strict=True
                                )
                            )
                        )
                        contributions = substitute_return_column(
                            left,
                            continuation,
                            shift=second.return_shift + half,
                            charge=self.view.ledger.bump,
                            reserve_workspace=reserve_scratch,
                            release_workspace=release_scratch,
                        )
                    finally:
                        release_scratch(continuation_nodes)
                for output, column in contributions:
                    previous = columns.get(output)
                    if previous is None:
                        reserve_scratch(1)
                        columns[output] = column
                    else:
                        columns[output] = union_return_columns(
                            previous, column, charge=charge_aggregation
                        )
            return ReturnMDDPartition(
                period, tuple(sorted(columns.items()))
            ), reserved_nodes
        except BaseException:
            if reserved_nodes:
                release_scratch(reserved_nodes)
            raise

    def construct(self, level: int) -> None:
        """Publish B(2**level) from the previous completed symbolic action."""
        self._check_open()
        if type(level) is not int or level < 0:
            raise ValueError("symbolic decade level must be nonnegative")
        if level <= self._completed_level:
            self.view.ledger.bump("comma_power_completed_hits")
            return
        for current in range(self._completed_level + 1, level + 1):
            for root, source in enumerate(self.view.roots):
                # A failed publication can be retried; only fully published
                # roots survive, and no half-level is advertised as complete.
                if (current, root) in self._powers:
                    continue
                workspace_nodes = 0
                if current == 0:
                    identifier, _ = self.view.source_address(source)
                    base = continuation_return_partition(
                        self.view, identifier, self._base, charge=self.view.ledger.bump
                    )
                    # Fixed encoding at every level: Live i is i<46, Stop D
                    # is 46+D. Time never changes the meaning of a Live label.
                    partition = ReturnMDDPartition(
                        base.period,
                        tuple(
                            (label - 9 if label >= 9 else 46 + label, column)
                            for label, column in base.columns
                        ),
                    )
                else:
                    partition, workspace_nodes = self._square(current, root)
                try:
                    self._publish(current, root, partition)
                finally:
                    if workspace_nodes:
                        self.view.ledger.release(
                            self._composition_workspace_owner, nodes=workspace_nodes
                        )
            self._completed_level = current

    def evaluate(self, level: int, root: int, phase: int) -> tuple[str, int]:
        """Demand a point from the completed power; no temporal replay."""
        if type(root) is not int or not 0 <= root < 46:
            raise ValueError("symbolic decade root must be in 0..45")
        if type(phase) is not int or not 0 <= phase < PERIOD:
            raise ValueError("symbolic decade phase must be in 0..923")
        self.construct(level)
        binding = self._powers[level, root]
        clock = (phase + binding.return_shift) % PERIOD
        for label, column in zip(binding.labels, binding.columns, strict=True):
            if evaluate_return_column(column, clock, charge=self.view.ledger.bump):
                self.view.ledger.bump("comma_power_point_requests")
                return ("live", label) if label < 46 else ("stop", label - 46)
        raise AssertionError("completed symbolic power did not cover its clock")


@dataclass(frozen=True, slots=True)
class _BlockResult:
    """A control-only block with the next effective occurrence clock.

    This clock includes the actual source exponent shift. It must never be
    confused with a symbolic return template's inverse clock translation.
    Exact weighted occurrence fragments are owned separately by the source.
    """

    span: int
    action: SemanticAction
    terminal: TerminalWeight | None
    stop_offset: int
    next_source: SourceState | None
    next_effective_phase: int | None
    next_delta: int | None


class PoweredDecadeApplication:
    """Memoized parent-first dyadic B1 application for one root binding.

    The memo key carries the normalized source, effective external clock
    phase, dyadic level, and this application binding token.  Raw occurrence
    deltas remain in source transition payloads.  No scalar ``refold`` is
    claimed: each parent is composed from two independently memoized child
    blocks, and a Stop carries its exact offset through the composition law.
    """

    def __init__(
        self,
        view: SemanticContinuation,
        source_for_live_root: Callable[[int], SourceState],
    ) -> None:
        if not callable(source_for_live_root):
            raise TypeError("comma live root resolver must be callable")
        self.view = view
        self._source_for_live_root: Callable[[int], SourceState] | None = (
            source_for_live_root
        )
        self.binding = ArenaToken("comma-powered-decade-binding")
        prefix = f"comma-semantic-powered-{view.ledger.owner_count}"
        owner_names = (
            prefix,
            prefix + "-roots",
            *fused_traversal_workspace_owner_names(prefix),
        )
        view.ledger.require_fresh_owner_names(owner_names)
        owner = view.ledger.register(prefix, "semantic_dyadic_application")
        binding_owner = view.ledger.register(
            prefix + "-roots", "semantic_live_root_binding"
        )
        self._memo: OwnedMemo[
            tuple[ArenaToken, SourceState, int, int], _BlockResult
        ] = OwnedMemo(
            view.ledger,
            owner,
            nodes_per_entry=1,
            composition_entries=True,
        )
        self._root_bindings: OwnedMemo[int, SourceState] = OwnedMemo(
            view.ledger, binding_owner, nodes_per_entry=1
        )
        self._workspace = FusedTraversalWorkspace(view.ledger, prefix)
        self._operation_lock: LockType = Lock()
        self._active = False
        self.requests = 0
        self.hits = 0
        self.misses = 0
        self._closed = False
        self._closing = False

    def _check_open(self) -> None:
        if self._closed or self._closing:
            raise RuntimeError("comma powered application is closing or closed")

    def _begin_operation(self, *, active: bool = True) -> None:
        if not self._operation_lock.acquire(blocking=False):
            raise RuntimeError("comma powered application is already active")
        if self._closed or self._closing:
            self._operation_lock.release()
            raise RuntimeError("comma powered application is closing or closed")
        self._active = active

    def _end_operation(self) -> None:
        self._active = False
        self._operation_lock.release()

    def __enter__(self) -> Self:
        self._check_open()
        return self

    def __exit__(self, _exc_type: object, _exc: object, _tb: object) -> None:
        self.close()

    def close(self) -> None:
        """Release the dyadic memo while retaining the immutable CID view."""
        if not self._operation_lock.acquire(blocking=False):
            raise RuntimeError("cannot close an active comma powered application")
        try:
            if not self._closed:
                self._closing = True
                self._source_for_live_root = None

                with ExitStack() as cleanup:
                    cleanup.enter_context(_dispose_on_exit(self._workspace.dispose))
                    cleanup.enter_context(_dispose_on_exit(self._root_bindings.dispose))
                    cleanup.enter_context(_dispose_on_exit(self._memo.dispose))
                self._closed = True
                self._closing = False
        finally:
            self._operation_lock.release()

    def _memo_lookup(
        self, key: tuple[ArenaToken, SourceState, int, int]
    ) -> _BlockResult | None:
        """Count raw retrievals, including reads within the current application.

        A retrieval hit alone is not evidence of prior-request warm reuse.
        """
        self.requests += 1
        value = self._memo.get(key)
        if value is None:
            self.misses += 1
        else:
            self.hits += 1
        return value

    def _key(
        self, source: SourceState, phase: int, delta: int, level: int
    ) -> tuple[ArenaToken, SourceState, int, int]:
        # Every admitted source period divides 924, so control depends on the
        # effective clock only.  The raw occurrence delta remains in the
        # source/transition payload and is intentionally absent from this
        # control memo key.
        return self.binding, source, (phase + delta) % PERIOD, level

    def _next_live(self, action: SemanticAction) -> tuple[SourceState, int, int]:
        root = action.live_root
        if root is None:
            raise AssertionError("Live action lost its root binding")
        resolver = self._source_for_live_root
        if resolver is None:
            raise RuntimeError("comma live root resolver is not bound")
        next_source = self._root_bindings.get(root)
        if next_source is None:
            next_source = resolver(root)
            if type(next_source) is not BoundaryChart:
                raise TypeError("comma live root resolver returned a non-chart value")
            # Publish one immutable, ledger-owned binding per root.  Future
            # dyadic cache hits cannot observe a mutable callback's changed
            # answer under the same application token.
            normalized, _ = normalize_source(next_source)
            if (
                normalized.kind != "entry"
                or normalized.leading != 1
                or canonical_offset_orbit(normalized.coordinate)
                != canonical_offset_orbit(root)
            ):
                raise ValueError("comma live root resolver changed the canonical orbit")
            self._root_bindings[root] = next_source
        normalized, delta = normalize_source(next_source)
        if normalized not in self.view.source_ids:
            raise KeyError("live root resolver returned an uncompiled source")
        return normalized, delta % PERIOD, action.exponent_advance

    def _one(self, source: SourceState, phase: int, delta: int) -> _BlockResult:
        result = self.view.evaluate(source, phase, delta=delta)
        if result.action.kind == "stop":
            terminal = result.terminal_weight
            if terminal is None:
                raise AssertionError("Stop action lost its local terminal weight")
            return _BlockResult(1, result.action, terminal, 0, None, None, None)
        next_source, next_delta, advance = self._next_live(result.action)
        return _BlockResult(
            1,
            result.action,
            None,
            1,
            next_source,
            (phase + delta + advance) % PERIOD,
            next_delta,
        )

    def _combine(
        self, first: _BlockResult, second: _BlockResult, half: int
    ) -> _BlockResult:
        if first.terminal is not None:
            return _BlockResult(
                half * 2,
                first.action,
                first.terminal,
                first.stop_offset,
                None,
                None,
                None,
            )
        if second.terminal is not None:
            return _BlockResult(
                half * 2,
                second.action,
                second.terminal.after_complete_decades(half),
                half + second.stop_offset,
                None,
                None,
                None,
            )
        return _BlockResult(
            half * 2,
            second.action,
            None,
            half * 2,
            second.next_source,
            second.next_effective_phase,
            second.next_delta,
        )

    def _block(
        self, source: SourceState, phase: int, delta: int, level: int
    ) -> _BlockResult:
        """Evaluate one dyadic block with an explicit postorder worklist.

        The continuation DAG is finite, but its depth is input-dependent.  A
        Python call stack would make the application depend on the recursion
        limit; this worklist preserves parent-after-children composition while
        keeping the owned memo as the only retained result store.
        """
        self._check_open()
        if type(level) is not int or level < 0:
            raise ValueError("comma dyadic level must be nonnegative")
        initial = self._key(source, phase, delta, level)
        # (stage, source, phase, delta, level, first-child result).  A visit
        # computes a leaf or schedules its first child.  The first stage
        # either absorbs a terminal or schedules the second child.  The second
        # stage composes both completed children.
        with self._workspace.scope(level, 1):
            self._workspace.append_frame(("visit", source, phase, delta, level, None))
            while self._workspace.frames:
                (
                    stage,
                    current_source,
                    current_phase,
                    current_delta,
                    current_level,
                    first,
                ) = cast(
                    tuple[str, SourceState, int, int, int, _BlockResult | None],
                    self._workspace.pop_frame(),
                )
                key = self._key(
                    current_source, current_phase, current_delta, current_level
                )
                if stage == "visit":
                    cached = self._memo_lookup(key)
                    if cached is not None:
                        continue
                    if current_level == 0:
                        self._memo[key] = self._one(
                            current_source, current_phase, current_delta
                        )
                        continue
                    self._workspace.append_frame(
                        (
                            "first",
                            current_source,
                            current_phase,
                            current_delta,
                            current_level,
                            None,
                        )
                    )
                    self._workspace.append_frame(
                        (
                            "visit",
                            current_source,
                            current_phase,
                            current_delta,
                            current_level - 1,
                            None,
                        )
                    )
                    continue
                half = 1 << (current_level - 1)
                first_key = self._key(
                    current_source, current_phase, current_delta, current_level - 1
                )
                first_result = self._memo_lookup(first_key)
                if first_result is None:
                    raise AssertionError("comma first dyadic child was not completed")
                if stage == "first":
                    if first_result.terminal is not None:
                        self._memo[key] = _BlockResult(
                            1 << current_level,
                            first_result.action,
                            first_result.terminal,
                            first_result.stop_offset,
                            None,
                            None,
                            None,
                        )
                        continue
                    if (
                        first_result.next_source is None
                        or first_result.next_effective_phase is None
                        or first_result.next_delta is None
                    ):
                        raise AssertionError(
                            "live dyadic block lost its next occurrence"
                        )
                    self._workspace.append_frame(
                        (
                            "second",
                            current_source,
                            current_phase,
                            current_delta,
                            current_level,
                            first_result,
                        )
                    )
                    self._workspace.append_frame(
                        (
                            "visit",
                            first_result.next_source,
                            first_result.next_effective_phase,
                            first_result.next_delta,
                            current_level - 1,
                            None,
                        )
                    )
                    continue
                if first is None:
                    raise AssertionError(
                        "comma second dyadic child lost its first result"
                    )
                if (
                    first.next_source is None
                    or first.next_effective_phase is None
                    or first.next_delta is None
                ):
                    raise AssertionError(
                        "comma second dyadic child lost its occurrence"
                    )
                second = self._memo_lookup(
                    self._key(
                        first.next_source,
                        first.next_effective_phase,
                        first.next_delta,
                        current_level - 1,
                    )
                )
                if second is None:
                    raise AssertionError("comma second dyadic child was not completed")
                self._memo[key] = self._combine(first, second, half)
            result = self._memo_lookup(initial)
            if result is None:
                raise AssertionError("comma dyadic worklist lost its root result")
            return result

    def apply(
        self,
        source: SourceState,
        phase: int,
        count: int,
        *,
        delta: int = 0,
    ) -> DecadeSummary:
        """Apply through this manual owner's warm memo, rejecting reentry."""
        self._begin_operation()
        try:
            return self._apply_active(source, phase, count, delta=delta)
        finally:
            self._end_operation()

    def _apply_rebound(
        self,
        source: SourceState,
        phase: int,
        count: int,
        *,
        source_for_live_root: Callable[[int], SourceState],
        delta: int = 0,
    ) -> DecadeSummary:
        """Run one callback-scoped request, discarding all request-local work."""
        if not callable(source_for_live_root):
            raise TypeError("comma live root resolver must be callable")
        self._begin_operation(active=False)
        try:
            self._clear_request_state()
            self.binding = ArenaToken("comma-powered-decade-binding")
            self._source_for_live_root = source_for_live_root
            self.requests = self.hits = self.misses = 0
            self._active = True
            return self._apply_active(source, phase, count, delta=delta)
        finally:
            try:
                self._active = False
                self._clear_request_state()
            finally:
                self.binding = ArenaToken("comma-powered-decade-binding")
                self._source_for_live_root = None
                self._end_operation()

    def _clear_request_state(self) -> None:
        try:
            self._memo.clear()
        finally:
            self._root_bindings.clear()

    def _apply_active(
        self,
        source: SourceState,
        phase: int,
        count: int,
        *,
        delta: int = 0,
    ) -> DecadeSummary:
        self._check_open()
        if type(count) is not int or count < 0:
            raise ValueError("comma decade count must be a nonnegative integer")
        normalized, source_delta = normalize_source(source)
        if type(phase) is not int or not 0 <= phase < PERIOD:
            raise ValueError("comma continuation phase must be in 0..923")
        if type(delta) is not int or delta < 0:
            raise ValueError("comma occurrence delta must be nonnegative")
        if normalized not in self.view.source_ids:
            raise KeyError("source is outside the compiled continuation closure")
        current_source = normalized
        current_phase = phase
        current_delta = (source_delta + delta) % PERIOD
        if count == 0:
            return DecadeSummary(SemanticAction("identity"), None, 0, 0)
        remaining = count
        elapsed = 0
        final_action: SemanticAction | None = None
        while remaining:
            level = remaining.bit_length() - 1
            block = self._block(current_source, current_phase, current_delta, level)
            if block.terminal is not None:
                stop_offset = elapsed + block.stop_offset
                return DecadeSummary(
                    block.action,
                    block.terminal.after_complete_decades(elapsed),
                    stop_offset,
                    stop_offset,
                )
            if (
                block.next_source is None
                or block.next_effective_phase is None
                or block.next_delta is None
            ):
                raise AssertionError("live dyadic result lost its next occurrence")
            final_action = block.action
            current_source = block.next_source
            current_phase = block.next_effective_phase
            current_delta = block.next_delta
            elapsed += block.span
            remaining -= block.span
        if final_action is None:
            raise AssertionError("comma dyadic application had no action")
        return DecadeSummary(final_action, None, elapsed, elapsed)
