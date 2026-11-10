"""Scoped comma continuations; source transitions and arithmetic stay occurrence data."""

from __future__ import annotations

from _thread import LockType
from collections.abc import Callable, Iterator, Mapping, MutableMapping
from dataclasses import dataclass, field, replace
from threading import Lock
from types import MappingProxyType
from typing import TYPE_CHECKING, Any, Literal, Self

from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import comma as _comma_keys
from number_compiler.resources.stores import LedgerDict
from number_compiler.sequences.comma.arithmetic import (
    CycleTransfer,
    NearPortOccurrence,
    NearPortReturn,
    NearResidualPort,
    classify_near_occurrence,
    classify_near_port,
    cycle_residue_period,
    cycle_transfer,
    entry_headroom_from_validated_transfer,
    near_port_occurrence,
)
from number_compiler.sequences.comma.boundary_chart import (
    PERIOD,
    BoundaryChart,
    ChartMove,
    chart_step,
)
from number_compiler.sequences.comma.domain import (
    canonical_entry_coordinate,
    decade_root_coordinate,
)

if TYPE_CHECKING:
    from number_compiler.sequences.comma.semantic_power import (
        PoweredDecadeApplication,
        PoweredDecadeApplicationAuditSnapshot,
    )

ActionKind = Literal["goto", "live", "stop", "identity"]
SourceState = BoundaryChart


class ContinuationID(ArenaHandle):
    """A semantic continuation identity scoped to one arena lifetime."""


@dataclass(frozen=True, slots=True)
class TerminalWeight:
    """Weighted terminal position ``D = 9*H + J``; H stays occurrence data."""

    d: int

    def __post_init__(self) -> None:
        if type(self.d) is not int or self.d < 0:
            raise ValueError("comma terminal weight must be a nonnegative integer")

    @classmethod
    def local(cls, stop_j: int) -> Self:
        if type(stop_j) is not int or not 0 <= stop_j <= 8:
            raise ValueError("comma local terminal J must be in 0..8")
        return cls(stop_j)

    @property
    def height(self) -> int:
        return self.d // 9

    @property
    def stop_j(self) -> int:
        return self.d % 9

    @property
    def is_landmine(self) -> bool:
        return self.stop_j == 8

    @property
    def fork_a(self) -> int | None:
        return None if self.is_landmine else self.stop_j + 2

    def after_complete_decades(self, count: int) -> TerminalWeight:
        if type(count) is not int or count < 0:
            raise ValueError("complete decade count must be nonnegative")
        return TerminalWeight(self.d + 9 * count)


@dataclass(frozen=True, slots=True)
class OccurrenceWeight:
    """Exact per-source arithmetic fragments, excluded from CID interning."""

    entry_period: int
    entry_displacement: int
    near_physical_steps: int
    literal_increment: int
    exponent_advance: int
    live_coordinate: int | None = None

    def __post_init__(self) -> None:
        fields = (
            self.entry_period,
            self.entry_displacement,
            self.near_physical_steps,
            self.literal_increment,
            self.exponent_advance,
        )
        if any(type(value) is not int or value < 0 for value in fields):
            raise ValueError("comma occurrence weight fields must be nonnegative ints")
        if self.live_coordinate is not None and (
            type(self.live_coordinate) is not int
            or not decade_root_coordinate(1, self.live_coordinate)
        ):
            raise ValueError("invalid comma live crossing coordinate")


@dataclass(frozen=True, slots=True)
class SemanticAction:
    """A CID action with no source/scope/phase/rank identity."""

    kind: ActionKind
    target: ContinuationID | None = None
    live_root: int | None = None
    stop_j: int | None = None
    exponent_advance: int = 0

    def __post_init__(self) -> None:
        if type(self.exponent_advance) is not int:
            raise ValueError("comma exponent advance must be an exact integer")
        if self.kind == "goto":
            if (
                type(self.target) is not ContinuationID
                or any(value is not None for value in (self.live_root, self.stop_j))
                or self.exponent_advance != 0
            ):
                raise ValueError("invalid comma Goto action")
        elif self.kind == "live":
            if (
                self.target is not None
                or type(self.live_root) is not int
                or self.stop_j is not None
                or self.exponent_advance != 1
            ):
                raise ValueError("invalid comma Live action")
        elif self.kind == "stop":
            if (
                self.target is not None
                or self.live_root is not None
                or type(self.stop_j) is not int
                or not 0 <= self.stop_j <= 8
                or self.exponent_advance != 0
            ):
                raise ValueError("invalid comma Stop action")
        elif self.kind == "identity":
            if (
                any(
                    value is not None
                    for value in (self.target, self.live_root, self.stop_j)
                )
                or self.exponent_advance != 0
            ):
                raise ValueError("invalid comma identity action")
        else:
            raise ValueError("unknown comma semantic action")

    def key(self) -> tuple[object, ...]:
        return (
            self.kind,
            self.target,
            self.live_root,
            self.stop_j,
            self.exponent_advance,
        )


@dataclass(frozen=True, slots=True)
class WeightedAction:
    control: SemanticAction
    occurrence: OccurrenceWeight
    child: SourceState | None = None


class _PeriodView(Mapping[SourceState, int]):
    """A charged-store view of row periods without copying the source graph."""

    __slots__ = ("_rows",)

    def __init__(self, rows: Mapping[SourceState, tuple[WeightedAction, ...]]) -> None:
        self._rows = rows

    def __getitem__(self, source: SourceState) -> int:
        return len(self._rows[source])

    def __iter__(self) -> Iterator[SourceState]:
        return iter(self._rows)

    def __len__(self) -> int:
        return len(self._rows)


@dataclass(frozen=True, slots=True)
class SemanticResult:
    """One control result; source-bound weights remain in the transition row."""

    action: SemanticAction

    @property
    def terminal_weight(self) -> TerminalWeight | None:
        return (
            None
            if self.action.kind != "stop" or self.action.stop_j is None
            else TerminalWeight.local(self.action.stop_j)
        )


@dataclass(frozen=True, slots=True)
class DecadeSummary:
    """Result of applying complete decades through the semantic owner."""

    action: SemanticAction
    terminal: TerminalWeight | None
    complete_decades: int
    exponent_advance: int


@dataclass(frozen=True, slots=True)
class MooreRefinement:
    """Independent refinement classes for a compiled CID arena."""

    classes: Mapping[ContinuationID, int]
    rounds: int

    @property
    def class_count(self) -> int:
        return len(set(self.classes.values()))


@dataclass(frozen=True, slots=True)
class SemanticContinuationPoweredAuditSnapshot:
    """Read-only lifecycle view of the reusable powered application owner."""

    closed: bool
    application: PoweredDecadeApplicationAuditSnapshot | None


@dataclass(frozen=True, slots=True)
class SemanticContinuation:
    """Read-only application view published by ``SemanticContinuationArena``."""

    ledger: ResourceLedger
    owner: ArenaToken
    roots: tuple[SourceState, ...]
    periods: Mapping[SourceState, int]
    transitions: Mapping[SourceState, tuple[WeightedAction, ...]]
    source_ids: Mapping[SourceState, ContinuationID]
    actions_by_id: Mapping[ContinuationID, tuple[SemanticAction, ...]]
    _convenience_application: PoweredDecadeApplication | None = field(
        default=None,
        init=False,
        repr=False,
        compare=False,
        hash=False,
    )
    _convenience_closed: bool = field(
        default=False,
        init=False,
        repr=False,
        compare=False,
        hash=False,
    )
    _convenience_lock: LockType = field(
        default_factory=Lock,
        init=False,
        repr=False,
        compare=False,
        hash=False,
    )

    def validate_id(self, identifier: ContinuationID) -> ContinuationID:
        identifier.validate(
            self.owner, "comma-continuation", size=len(self.actions_by_id)
        )
        if identifier not in self.actions_by_id:
            raise KeyError("unknown comma continuation ID")
        return identifier

    def _normalize(self, source: SourceState) -> tuple[SourceState, int]:
        return normalize_source(source)

    def source_address(
        self, source: SourceState, *, delta: int = 0
    ) -> tuple[ContinuationID, int]:
        """Return ``(CID, external clock shift)`` for one occurrence."""
        normalized, source_delta = self._normalize(source)
        if type(delta) is not int or delta < 0:
            raise ValueError("comma occurrence delta must be nonnegative")
        identifier = self.source_ids.get(normalized)
        if identifier is None:
            raise KeyError("source is outside the compiled continuation closure")
        return identifier, source_delta + delta

    def evaluate_id(self, identifier: ContinuationID, phase: int) -> SemanticAction:
        """Apply a completed CID with an external cyclotomic phase."""
        self.validate_id(identifier)
        if type(phase) is not int or not 0 <= phase < PERIOD:
            raise ValueError("comma continuation phase must be in 0..923")
        current = identifier
        while True:
            actions = self.actions_by_id.get(self.validate_id(current))
            if actions is None or not actions:
                raise ValueError("comma continuation action row is empty")
            action = actions[phase % len(actions)]
            if action.kind != "goto":
                return action
            target = action.target
            if target is None or target.local_id >= current.local_id:
                raise ValueError("comma Goto does not descend in the CID DAG")
            current = target

    def evaluate(
        self, source: SourceState, phase: int, *, delta: int = 0
    ) -> SemanticResult:
        """Apply a source occurrence while carrying ``delta`` outside its CID."""
        normalized, source_shift = self._normalize(source)
        if type(delta) is not int or delta < 0:
            raise ValueError("comma occurrence delta must be nonnegative")
        if type(phase) is not int or not 0 <= phase < PERIOD:
            raise ValueError("comma continuation phase must be in 0..923")
        self.source_address(source, delta=delta)
        current_source = normalized
        shift = source_shift + delta
        while True:
            row = self.transitions.get(current_source)
            if row is None or not row:
                raise ValueError("source occurrence has an empty weighted row")
            self.ledger.bump(_comma_keys.COMMA_SEMANTIC_OCCURRENCE_VISITS)
            weighted = row[(phase + shift) % len(row)]
            action = weighted.control
            if action.kind != "goto":
                return SemanticResult(action)
            target_source = weighted.child
            child_id = action.target
            if child_id is None or target_source is None:
                raise ValueError("Goto action lost its child CID/source")
            if self.source_ids.get(target_source) != child_id:
                raise ValueError("Goto action child binding disagrees with its CID")
            current_source = target_source

    def powered_application(
        self,
        *,
        source_for_live_root: Callable[[int], SourceState],
    ) -> PoweredDecadeApplication:
        """Create a ledger-owned memoized dyadic application view."""
        from number_compiler.sequences.comma.semantic_power import (
            PoweredDecadeApplication,
        )

        return PoweredDecadeApplication(self, source_for_live_root)

    def _reusable_powered_application(
        self,
        source_for_live_root: Callable[[int], SourceState],
    ) -> PoweredDecadeApplication:
        with self._convenience_lock:
            if self._convenience_closed:
                raise RuntimeError("comma continuation convenience owner is closed")
            application = self._convenience_application
            if application is None:
                from number_compiler.sequences.comma.semantic_power import (
                    PoweredDecadeApplication,
                )

                application = PoweredDecadeApplication(self, source_for_live_root)
                object.__setattr__(self, "_convenience_application", application)
            return application

    def close(self) -> None:
        """Dispose the reusable convenience owner, retaining manual apps."""
        with self._convenience_lock:
            if self._convenience_closed:
                return
            application = self._convenience_application
            if application is not None:
                application.close()
            object.__setattr__(self, "_convenience_application", None)
            object.__setattr__(self, "_convenience_closed", True)

    def powered_audit_snapshot(self) -> SemanticContinuationPoweredAuditSnapshot:
        """Observe the convenience application's lifecycle without its stores."""
        with self._convenience_lock:
            application = self._convenience_application
            return SemanticContinuationPoweredAuditSnapshot(
                closed=self._convenience_closed,
                application=(
                    None if application is None else application.audit_snapshot()
                ),
            )

    def apply_decades(
        self,
        source: SourceState,
        phase: int,
        count: int,
        *,
        source_for_live_root: Callable[[int], SourceState],
        delta: int = 0,
    ) -> DecadeSummary:
        """Apply complete B1 blocks through the memoized dyadic owner."""
        return self.apply_decades_powered(
            source,
            phase,
            count,
            source_for_live_root=source_for_live_root,
            delta=delta,
        )

    def apply_decades_powered(
        self,
        source: SourceState,
        phase: int,
        count: int,
        *,
        source_for_live_root: Callable[[int], SourceState],
        delta: int = 0,
    ) -> DecadeSummary:
        """Apply exactly ``count`` B1 blocks by memoized dyadic composition."""
        application = self._reusable_powered_application(source_for_live_root)
        return application.apply_rebound(
            source,
            phase,
            count,
            source_for_live_root=source_for_live_root,
            delta=delta,
        )

    def refine_moore(self) -> MooreRefinement:
        """Return a structural diagnostic over stored controls and children.

        This deliberately treats an internal ``goto`` row as a symbol.  Its
        classes can therefore over-distinguish complete B1 observations; they
        are not a claim of the minimized future-output quotient.
        """
        identifiers = tuple(self.actions_by_id)
        classes = {identifier: 0 for identifier in identifiers}
        rounds = 0
        while True:
            keys: dict[tuple[object, ...], int] = {}
            next_classes: dict[ContinuationID, int] = {}
            for identifier in identifiers:
                row = self.actions_by_id[identifier]
                key = tuple(
                    (
                        action.kind,
                        action.live_root,
                        action.stop_j,
                        action.exponent_advance,
                        None if action.target is None else classes[action.target],
                    )
                    for action in row
                )
                next_classes[identifier] = keys.setdefault(key, len(keys))
            rounds += 1
            if all(next_classes[item] == classes[item] for item in identifiers):
                return MooreRefinement(MappingProxyType(next_classes), rounds)
            classes = next_classes


@dataclass(frozen=True, slots=True)
class _RawAction:
    kind: ActionKind
    child: SourceState | None
    live_root: int | None
    stop_j: int | None
    exponent_advance: int
    occurrence: OccurrenceWeight


def normalize_source(source: SourceState) -> tuple[SourceState, int]:
    """Remove chart delta from a key and return it as an occurrence shift."""
    if type(source) is not BoundaryChart:
        raise TypeError("comma semantic source requires an exact BoundaryChart")
    if (
        source.kind not in ("entry", "near")
        or type(source.leading) is not int
        or type(source.delta) is not int
        or type(source.coordinate) is not int
        or not 1 <= source.leading <= 9
        or source.delta < 0
        or source.kind == "entry"
        and not canonical_entry_coordinate(source.leading, source.coordinate)
        or source.kind == "near"
        and not 1 <= source.coordinate <= 540
    ):
        raise ValueError("invalid comma semantic source")
    return BoundaryChart(
        source.kind, source.leading, 0, source.coordinate
    ), source.delta


def _source_cycle(source: SourceState) -> tuple[CycleTransfer | None, int]:
    if source.kind == "near":
        return None, 1
    transfer: CycleTransfer = cycle_transfer(source.leading, source.coordinate % 10)
    return transfer, cycle_residue_period(transfer.displacement)


def _selected_target(
    source: SourceState,
    phase: int,
    transfer: CycleTransfer | None,
    near_occurrence: NearPortOccurrence | None = None,
) -> tuple[BoundaryChart, NearPortReturn, int, int]:
    if source.kind == "entry":
        if transfer is None:
            raise ArithmeticError("comma Entry action is missing its source transfer")
        headroom = entry_headroom_from_validated_transfer(
            source.leading, source.coordinate, phase, transfer
        )
        entry_period = transfer.period
        entry_displacement = transfer.displacement
        near_return = classify_near_port(source.leading, headroom)
    else:
        if transfer is not None:
            raise ArithmeticError("comma Near action received an Entry transfer")
        headroom = source.coordinate
        entry_period = 1
        entry_displacement = 0
        if near_occurrence is None:
            near_return = classify_near_port(source.leading, headroom)
        else:
            if (
                near_occurrence.port.leading != source.leading
                or near_occurrence.headroom != headroom
            ):
                raise ValueError("Near occurrence does not bind to its source chart")
            near_return = classify_near_occurrence(
                near_occurrence, charge_work=None, charge_bits=None
            )
    return (
        BoundaryChart("near", source.leading, 0, near_return.terminal_headroom),
        near_return,
        entry_period,
        entry_displacement,
    )


def _raw_action(
    source: SourceState,
    phase: int,
    transfer: CycleTransfer | None,
    near_occurrence: NearPortOccurrence | None = None,
) -> _RawAction:
    target, near_return, entry_period, entry_displacement = _selected_target(
        source, phase, transfer, near_occurrence
    )
    move: ChartMove = chart_step(phase, target)
    live_coordinate = (
        move.next_chart.coordinate
        if move.next_chart is not None
        and move.next_chart.kind == "entry"
        and move.next_chart.delta == 1
        else None
    )
    if live_coordinate is not None and not decade_root_coordinate(1, live_coordinate):
        raise ArithmeticError("comma live crossing left the canonical root domain")
    occurrence = OccurrenceWeight(
        entry_period,
        entry_displacement,
        near_return.physical_steps,
        move.literal_increment,
        int(live_coordinate is not None),
        live_coordinate,
    )
    if live_coordinate is not None:
        return _RawAction("live", None, live_coordinate, None, 1, occurrence)
    if move.next_chart is None:
        if move.fork_a is None:
            return _RawAction("stop", None, None, 8, 0, occurrence)
        if not 2 <= move.fork_a <= 9:
            raise ArithmeticError("comma fork coefficient left its admitted domain")
        return _RawAction("stop", None, None, move.fork_a - 2, 0, occurrence)
    normalized, child_delta = normalize_source(move.next_chart)
    if child_delta != 0 or normalized.leading <= source.leading:
        raise ArithmeticError("comma source continuation did not advance its sector")
    return _RawAction("goto", normalized, None, None, 0, occurrence)


def _minimal_period(actions: tuple[SemanticAction, ...]) -> int:
    period = len(actions)
    for candidate in range(1, period + 1):
        if period % candidate == 0 and all(
            actions[index] == actions[index % candidate] for index in range(period)
        ):
            return candidate
    raise AssertionError("comma semantic action period normalization failed")


class SemanticContinuationArena:
    """Instance-scoped bottom-up CID compiler with no eager phase table."""

    def __init__(self, ledger: ResourceLedger | None = None) -> None:
        self.ledger = ResourceLedger() if ledger is None else ledger
        self.ledger.register_execution_root(self)
        self.owner = ArenaToken("comma-semantic-continuations")
        prefix = f"comma-semantic-{self.ledger.owner_count}"
        self._raw_owner = self.ledger.register(prefix + "-raw", "semantic_raw_source")
        self._transition_owner = self.ledger.register(
            prefix + "-transitions", "semantic_transition"
        )
        self._source_id_owner = self.ledger.register(
            prefix + "-source-ids", "semantic_source_id"
        )
        self._action_owner = self.ledger.register(
            prefix + "-actions", "semantic_action"
        )
        self._near_operator_owner = self.ledger.register(
            prefix + "-near-operators", "semantic_near_operator"
        )
        self._key_owner = self.ledger.register(prefix + "-keys", "semantic_interner")
        self._raw: LedgerDict[SourceState, tuple[_RawAction, ...]] = (
            self.ledger.make_dict(self._raw_owner, nodes_per_entry=1)
        )
        self._transitions: LedgerDict[SourceState, tuple[WeightedAction, ...]] = (
            self.ledger.make_dict(self._transition_owner, nodes_per_entry=1)
        )
        self._source_ids: LedgerDict[SourceState, ContinuationID] = (
            self.ledger.make_dict(self._source_id_owner, nodes_per_entry=1)
        )
        self._actions: LedgerDict[ContinuationID, tuple[SemanticAction, ...]] = (
            self.ledger.make_dict(self._action_owner, nodes_per_entry=1)
        )
        self._near_operators: LedgerDict[NearResidualPort, _RawAction] = (
            self.ledger.make_dict(self._near_operator_owner, nodes_per_entry=1)
        )
        self._signatures: LedgerDict[
            tuple[int, tuple[tuple[object, ...], ...]], ContinuationID
        ] = self.ledger.make_dict(self._key_owner)
        self._next_id = 0

    def _store(
        self,
        mapping: MutableMapping[Any, Any],
        owner: int,
        key: object,
        value: object,
        *,
        nodes: int = 1,
    ) -> None:
        if key in mapping:
            mapping[key] = value
            return
        self.ledger.reserve(owner, entries=1, nodes=nodes)
        try:
            mapping[key] = value
        except BaseException:
            self.ledger.release(owner, entries=1, nodes=nodes)
            raise

    def _remove(
        self,
        mapping: MutableMapping[Any, Any],
        owner: int,
        key: object,
        *,
        nodes: int,
    ) -> None:
        if key not in mapping:
            return
        del mapping[key]
        self.ledger.release(owner, entries=1, nodes=nodes)

    def _id(self, local_id: int) -> ContinuationID:
        return ContinuationID(self.owner, "comma-continuation", local_id)

    @staticmethod
    def _signature_nodes(signature: tuple[int, tuple[tuple[object, ...], ...]]) -> int:
        _period, keys = signature
        return 1 + sum(len(key) for key in keys)

    def _rollback_sources(
        self, sources: tuple[SourceState, ...] | list[SourceState], *, remove_raw: bool
    ) -> None:
        for item in sources:
            if remove_raw:
                raw = self._raw.get(item)
                if raw is not None:
                    self._remove(self._raw, self._raw_owner, item, nodes=len(raw))
            transitions = self._transitions.get(item)
            if transitions is not None:
                self._remove(
                    self._transitions,
                    self._transition_owner,
                    item,
                    nodes=len(transitions),
                )
            if item in self._source_ids:
                self._remove(self._source_ids, self._source_id_owner, item, nodes=1)

    def compile(self, source: SourceState) -> ContinuationID:
        normalized, _ = normalize_source(source)
        found = self._source_ids.get(normalized)
        if found is not None:
            return found
        discovered, added_near_operators = self._discover(normalized)
        try:
            self._intern_new_sources(discovered)
        except BaseException:
            self._rollback_sources(discovered, remove_raw=True)
            self._rollback_near_operators(added_near_operators)
            raise
        identifier = self._source_ids.get(normalized)
        if identifier is None:
            raise AssertionError("comma source publication lost its root")
        return identifier

    def _rollback_near_operators(self, keys: tuple[NearResidualPort, ...]) -> None:
        for key in keys:
            self._remove(
                self._near_operators,
                self._near_operator_owner,
                key,
                nodes=1,
            )

    @staticmethod
    def _bind_near_occurrence(
        operator: _RawAction, occurrence: NearPortOccurrence
    ) -> _RawAction:
        steps = (
            operator.occurrence.near_physical_steps
            + occurrence.cycle_quotient * occurrence.cycle_length
        )
        return replace(
            operator,
            occurrence=replace(operator.occurrence, near_physical_steps=steps),
        )

    def _near_action(
        self,
        source: SourceState,
        occurrence: NearPortOccurrence,
        added_keys: list[NearResidualPort],
    ) -> _RawAction:
        # A Near chart action ignores the external clock; its row has period 1.
        key = occurrence.port
        cached = self._near_operators.get(key)
        if cached is not None:
            return self._bind_near_occurrence(cached, occurrence)
        action = _raw_action(source, 0, None, occurrence)
        repeated_steps = occurrence.cycle_quotient * occurrence.cycle_length
        residual_steps = action.occurrence.near_physical_steps - repeated_steps
        if not 0 <= residual_steps < occurrence.cycle_length:
            raise ArithmeticError("Near action has an invalid residual-time cocycle")
        operator = replace(
            action,
            occurrence=replace(action.occurrence, near_physical_steps=residual_steps),
        )
        added_keys.append(key)
        self._store(
            self._near_operators,
            self._near_operator_owner,
            key,
            operator,
        )
        return action

    def _intern_new_sources(self, discovered: tuple[SourceState, ...]) -> None:
        ordered = sorted(
            discovered, key=lambda item: (-item.leading, item.kind, item.coordinate)
        )
        published_sources: list[SourceState] = []
        touched_sources: list[SourceState] = []
        added_signatures: list[tuple[int, tuple[tuple[object, ...], ...]]] = []
        added_identifiers: list[ContinuationID] = []
        starting_next_id = self._next_id
        try:
            for item in ordered:
                controls: list[SemanticAction] = []
                weighted: list[WeightedAction] = []
                for raw in self._raw[item]:
                    target = (
                        None if raw.child is None else self._source_ids.get(raw.child)
                    )
                    if raw.kind == "goto" and target is None:
                        raise AssertionError("comma child was not interned bottom-up")
                    action = SemanticAction(
                        raw.kind,
                        target,
                        raw.live_root,
                        raw.stop_j,
                        raw.exponent_advance,
                    )
                    controls.append(action)
                    weighted.append(WeightedAction(action, raw.occurrence, raw.child))
                full_controls = tuple(controls)
                period = _minimal_period(full_controls)
                signature = (
                    period,
                    tuple(action.key() for action in full_controls[:period]),
                )
                identifier = self._signatures.get(signature)
                if identifier is None:
                    identifier = self._id(self._next_id)
                    self._next_id += 1
                    self._store(
                        self._signatures,
                        self._key_owner,
                        signature,
                        identifier,
                        nodes=self._signature_nodes(signature),
                    )
                    added_signatures.append(signature)
                    added_identifiers.append(identifier)
                    self._store(
                        self._actions,
                        self._action_owner,
                        identifier,
                        full_controls[:period],
                        nodes=period,
                    )
                touched_sources.append(item)
                self._store(
                    self._source_ids,
                    self._source_id_owner,
                    item,
                    identifier,
                )
                self._store(
                    self._transitions,
                    self._transition_owner,
                    item,
                    tuple(weighted),
                    nodes=len(weighted),
                )
                published_sources.append(item)
            self.ledger.bump(
                _comma_keys.COMMA_SEMANTIC_SOURCE_PUBLICATIONS,
                len(published_sources),
            )
        except BaseException:
            self._rollback_sources(touched_sources, remove_raw=False)
            for signature in added_signatures:
                self._remove(
                    self._signatures,
                    self._key_owner,
                    signature,
                    nodes=self._signature_nodes(signature),
                )
            for identifier in added_identifiers:
                actions = self._actions.get(identifier)
                if actions is not None:
                    self._remove(
                        self._actions,
                        self._action_owner,
                        identifier,
                        nodes=len(actions),
                    )
            self._next_id = starting_next_id
            self.ledger.bump(
                _comma_keys.COMMA_SEMANTIC_FAILED_SOURCE_PUBLICATIONS,
                len(touched_sources),
            )
            raise

    def _discover(
        self, root: SourceState
    ) -> tuple[tuple[SourceState, ...], tuple[NearResidualPort, ...]]:
        pending = [root]
        pending_set = {root}
        discovered: list[SourceState] = []
        added_near_operators: list[NearResidualPort] = []
        try:
            while pending:
                source = pending.pop()
                pending_set.remove(source)
                if source in self._raw:
                    continue
                transfer, period = _source_cycle(source)
                if transfer is not None:
                    self.ledger.bump(_comma_keys.COMMA_SEMANTIC_CYCLE_TRANSFER_BUILDS)
                near_occurrence = (
                    None
                    if source.kind != "near"
                    else near_port_occurrence(source.leading, source.coordinate)
                )
                if near_occurrence is not None and period != 1:
                    raise ArithmeticError("Near residual operator requires unit period")
                actions: list[_RawAction] = []
                for phase in range(period):
                    self.ledger.bump(_comma_keys.COMMA_SEMANTIC_ACTION_REQUESTS)
                    try:
                        if near_occurrence is None:
                            actions.append(_raw_action(source, phase, transfer))
                        else:
                            action = self._near_action(
                                source, near_occurrence, added_near_operators
                            )
                            actions.append(action)
                    except BaseException:
                        self.ledger.bump(_comma_keys.COMMA_SEMANTIC_ACTION_FAILURES)
                        raise
                self.ledger.bump(_comma_keys.COMMA_SEMANTIC_ACTION_EVALUATIONS, period)
                full_actions = tuple(actions)
                self._store(
                    self._raw,
                    self._raw_owner,
                    source,
                    full_actions,
                    nodes=len(full_actions),
                )
                discovered.append(source)
                for action in full_actions:
                    child = action.child
                    if (
                        child is not None
                        and child not in self._raw
                        and child not in pending_set
                    ):
                        pending_set.add(child)
                        pending.append(child)
        except BaseException:
            for source in discovered:
                raw = self._raw.get(source)
                if raw is not None:
                    self._remove(self._raw, self._raw_owner, source, nodes=len(raw))
            self._rollback_near_operators(tuple(added_near_operators))
            raise
        return tuple(discovered), tuple(added_near_operators)

    def compile_many(
        self, sources: tuple[SourceState, ...]
    ) -> tuple[ContinuationID, ...]:
        return tuple(self.compile(source) for source in sources)

    def publish(self, roots: tuple[SourceState, ...] = ()) -> SemanticContinuation:
        normalized = tuple(normalize_source(root)[0] for root in roots)
        if any(root not in self._source_ids for root in normalized):
            raise KeyError("published root was not compiled")
        return SemanticContinuation(
            self.ledger,
            self.owner,
            normalized,
            _PeriodView(self._transitions),
            MappingProxyType(self._transitions),
            MappingProxyType(self._source_ids),
            MappingProxyType(self._actions),
        )

    def refinement(self) -> MooreRefinement:
        """Run an independent Moore refinement over published CID controls."""
        return self.publish().refine_moore()


def build_semantic_continuation(
    roots: tuple[SourceState, ...],
) -> SemanticContinuation:
    """Compile and publish a caller-selected root closure."""
    arena = SemanticContinuationArena()
    arena.compile_many(roots)
    return arena.publish(roots)


__all__ = [
    "ActionKind",
    "ContinuationID",
    "DecadeSummary",
    "MooreRefinement",
    "OccurrenceWeight",
    "SemanticAction",
    "SemanticContinuation",
    "SemanticContinuationArena",
    "SemanticResult",
    "TerminalWeight",
    "WeightedAction",
    "build_semantic_continuation",
    "normalize_source",
]
