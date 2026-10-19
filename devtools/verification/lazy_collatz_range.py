"""Dyadic carry observers evaluated directly over source-backed Collatz DAGs.

Only complete functions on the three carry inputs are retained, together with
first/last witnesses. No point result or one-cell occurrence is memoized. These
spatial observers do not establish temporal successor closure.
"""

from __future__ import annotations

from collections.abc import Generator, Iterator, MutableMapping, MutableSequence
from dataclasses import dataclass
from importlib import import_module
from typing import TYPE_CHECKING, Literal, cast

from devtools.verification.collatz_carry_ranges import (
    CarryRangeSummary,
    CarryRangeTransfer,
)
from devtools.verification.lazy_collatz import (
    _Mul3Port,
    _ShiftPort,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.resources.proof_payload_admission import (
    register_proof_geometry_fields,
)


@dataclass(frozen=True, slots=True)
class CollatzRangeEffect:
    transfer: CarryRangeTransfer
    first_one: int | None
    last_one: int | None

    def __post_init__(self) -> None:
        if type(self.transfer) is not CarryRangeTransfer:
            raise ValueError("range effects require complete finite carry transfers")
        if (self.first_one is None) != (self.last_one is None):
            raise ValueError("range witnesses must agree on emptiness")
        if any(
            point is not None
            and (type(point) is not int or not 0 <= point < self.length)
            for point in (self.first_one, self.last_one)
        ):
            raise ValueError("range witnesses must be bounded coordinates")
        if (
            self.first_one is not None
            and self.last_one is not None
            and self.first_one > self.last_one
        ):
            raise ValueError("range witnesses must be ordered")

    @property
    def length(self) -> int:
        return self.transfer.length

    def then(self, following: CollatzRangeEffect) -> CollatzRangeEffect:
        return CollatzRangeEffect(
            self.transfer.compose(following.transfer),
            self.first_one
            if self.first_one is not None
            else (
                None
                if following.first_one is None
                else self.length + following.first_one
            ),
            self.last_one
            if following.last_one is None
            else self.length + following.last_one,
        )


@dataclass(frozen=True, slots=True)
class _RangeKey:
    program: ActionProgramID
    start: int
    length: int


@dataclass(frozen=True, slots=True)
class _CompositionKey:
    left: TransferSummaryID
    right: TransferSummaryID


@dataclass(frozen=True, slots=True)
class _SourceTileKey:
    tile: ArenaHandle
    length: int


@dataclass(frozen=True, slots=True)
class _Request:
    kind: Literal["point", "range", "event"]
    program: ActionProgramID
    start: int
    length: int = 0


_Value = int | CollatzRangeEffect | CarryRangeSummary
_Computation = Generator[_Request, _Value, _Value]


class CollatzRangeEvaluator:
    """One application scope: canonical effects and evictable range bindings."""

    def __init__(self, application: LazyCollatzApplication) -> None:
        self.application = application
        self.ledger = application.ledger
        self.ledger.register_execution_root(self)
        self.owner = application.token
        self.action_owner = ArenaToken("collatz-range-effects")
        prefix = f"collatz-dyadic-{len(self.ledger.inventory())}"
        kernel_owner = self.ledger.register(prefix + "-kernel", "finite_port")
        self._atoms = tuple(
            CollatzRangeEffect(
                CarryRangeTransfer.bit(bit), 0 if bit else None, 0 if bit else None
            )
            for bit in (0, 1)
        )
        self._empty = CollatzRangeEffect(
            CarryRangeTransfer.bit(0).repeat(0), None, None
        )
        kernel = (*self._atoms, self._empty)
        self.ledger.reserve(kernel_owner, entries=3, nodes=3)
        self.ledger.register_container(
            kernel_owner, kernel, node_count=lambda: 3, payloads=lambda: kernel
        )
        effect_owner = self.ledger.register(prefix + "-effects", "canonical_transfer")
        interner_owner = self.ledger.register(prefix + "-interner", "transfer_interner")
        range_owner = self.ledger.register(prefix + "-ranges", "spatial_binding")
        tile_owner = self.ledger.register(prefix + "-source-tiles", "spatial_binding")
        event_owner = self.ledger.register(
            prefix + "-event-witnesses", "spatial_binding"
        )
        compose_owner = self.ledger.register(prefix + "-compositions", "query_memo")
        self._effect_owner, self._interner_owner = effect_owner, interner_owner
        self._effects: MutableSequence[CollatzRangeEffect] = self.ledger.make_list(
            effect_owner
        )
        self._ids: MutableMapping[CollatzRangeEffect, TransferSummaryID] = (
            self.ledger.make_dict(interner_owner)
        )
        self._ranges: OwnedMemo[_RangeKey, TransferSummaryID] = OwnedMemo(
            self.ledger, range_owner, evictable=True
        )
        self._source_tiles: OwnedMemo[_SourceTileKey, TransferSummaryID] = OwnedMemo(
            self.ledger, tile_owner, evictable=True
        )
        self._events: OwnedMemo[_RangeKey, CarryRangeSummary] = OwnedMemo(
            self.ledger, event_owner, nodes_per_entry=1, evictable=True
        )
        self._compositions: OwnedMemo[_CompositionKey, TransferSummaryID] = OwnedMemo(
            self.ledger,
            compose_owner,
            evictable=True,
            composition_entries=True,
        )

    def _handle(self, index: int) -> TransferSummaryID:
        return TransferSummaryID(self.action_owner, "collatz-range-effect", index)

    def effect(self, action: TransferSummaryID) -> CollatzRangeEffect:
        if type(action) is not TransferSummaryID:
            raise TypeError("expected a scoped Collatz range action")
        action.validate(
            self.action_owner, "collatz-range-effect", size=len(self._effects)
        )
        return self._effects[action.local_id]

    def _intern(self, effect: CollatzRangeEffect) -> TransferSummaryID:
        found = self._ids.get(effect)
        if found is not None:
            return found
        self.ledger.reserve_many(
            ((self._effect_owner, 1, 1), (self._interner_owner, 1, 0))
        )
        action = self._handle(len(self._effects))
        self._effects.append(effect)
        self._ids[effect] = action
        return action

    def compose(
        self, left: TransferSummaryID, right: TransferSummaryID
    ) -> TransferSummaryID:
        first, second = self.effect(left), self.effect(right)
        self.ledger.bump("collatz_range_composition_requests")
        self.ledger.bump("composition_requests")
        key = _CompositionKey(left, right)
        found = self._compositions.get(key)
        if found is not None:
            self.ledger.bump("collatz_range_composition_hits")
            self.ledger.bump("composition_cache_hits")
            return found
        result = self._intern(first.then(second))
        self._compositions[key] = result
        self.ledger.bump("collatz_range_composition_evaluations")
        self.ledger.bump("composition_evaluations")
        return result

    def _atom(self, bit: int) -> CollatzRangeEffect:
        self.ledger.bump("collatz_leaf_symbol_classifications")
        return self._atoms[bit]

    def _zero(self, length: int) -> CollatzRangeEffect:
        if not length:
            return self._empty
        self.ledger.bump("collatz_zero_range_evaluations")
        return CollatzRangeEffect(
            CarryRangeTransfer(
                (
                    CarryRangeSummary(length, 0, None, None),
                    CarryRangeSummary(length, 0, 0, 0),
                    CarryRangeSummary(
                        length,
                        int(length == 1),
                        1 if length > 1 else None,
                        1 if length > 1 else None,
                    ),
                )
            ),
            None,
            None,
        )

    def _leaf_stream(self, program: ActionProgramID) -> Iterator[int]:
        """Finite live ports for one leaf scan; no retained operation expansion."""
        pending = [program]
        ports: list[_Mul3Port | _ShiftPort] = []
        while pending:
            stack_peak = self.ledger.counters.get(
                "collatz_leaf_dag_stack_peak_frames", 0
            )
            self.ledger.bump(
                "collatz_leaf_dag_stack_peak_frames", max(0, len(pending) - stack_peak)
            )
            reference = pending.pop()
            node = self.application._programs[reference.local_id]
            self.ledger.bump("collatz_leaf_dag_visits")
            if node.kind == "compose":
                pending.extend(
                    (
                        ActionProgramID(self.owner, "program", node.right),
                        ActionProgramID(self.owner, "program", node.left),
                    )
                )
            elif node.kind == "mul3":
                ports.append(_Mul3Port(reference))
                if node.shift:
                    ports.append(_ShiftPort(reference, node.shift))
            elif node.kind == "shift":
                ports.append(_ShiftPort(reference, node.shift))
        peak = self.ledger.counters.get("collatz_leaf_peak_ports", 0)
        self.ledger.bump("collatz_leaf_peak_ports", max(0, len(ports) - peak))
        capacity = 2 * sum(isinstance(port, _Mul3Port) for port in ports)
        capacity_peak = self.ledger.counters.get(
            "collatz_leaf_peak_carry_payload_bits", 0
        )
        self.ledger.bump(
            "collatz_leaf_peak_carry_payload_bits", max(0, capacity - capacity_peak)
        )
        cursor = 0
        while True:
            bit = 0
            if cursor < len(self.application._source):
                geometry = self.application.source_geometry
                bit = (
                    self.application._source[cursor]
                    if geometry is None
                    else geometry.read(cursor)
                )
                self.ledger.bump("collatz_source_reads")
            cursor += 1
            for port in ports:
                if isinstance(port, _ShiftPort):
                    if port.remaining:
                        port.remaining -= 1
                        break
                else:
                    bit = port.advance(bit, self.ledger)
                    self.application.carry_cell_evaluations += 1
                    self.application.maximum_carry = max(
                        self.application.maximum_carry, int(port.state)
                    )
            else:
                self.ledger.bump("collatz_leaf_emitted_bits")
                yield bit

    def _leaf_scan(
        self,
        program: ActionProgramID,
        start: int,
        length: int,
        requested: int | None = None,
    ) -> tuple[CollatzRangeEffect, int | None]:
        if not 0 <= length <= 8:
            raise ValueError(
                "finite leaf observations cover at most eight output cells"
            )
        self.ledger.bump("collatz_leaf_evaluations")
        result, answer = self._empty, None
        for offset in range(length):
            bit = self.application.program_bit(program, start + offset)
            result = result.then(self._atom(bit))
            self.ledger.bump("collatz_range_small_compositions")
            if start + offset == requested:
                answer = bit
        return result, answer

    def _input(self, program: ActionProgramID) -> tuple[ActionProgramID, str, int]:
        program.validate(self.owner, "program", size=len(self.application._programs))
        self.ledger.bump("collatz_dag_visits")
        node = self.application._programs[program.local_id]
        before = ActionProgramID(self.owner, "program", 0)
        if node.kind == "compose":
            before = ActionProgramID(self.owner, "program", node.left)
            node = self.application._programs[node.right]
            if node.kind == "compose":
                raise ValueError("Collatz programs require an atomic right action")
        return before, node.kind, node.shift

    def _point(self, request: _Request) -> _Computation:
        _before, kind, _shift = self._input(request.program)
        if kind != "identity":
            raise AssertionError(
                "only original source leaves bypass the finite leaf kernel"
            )
        position = request.start
        self.ledger.bump("collatz_source_reads")
        if position >= len(self.application._source):
            return 0
        yield from ()
        geometry = self.application.source_geometry
        return (
            self.application._source[position]
            if geometry is None
            else geometry.read(position)
        )

    def _event(self, request: _Request) -> _Computation:
        """Unresolved event fallback still scans the complete finite width.

        It retains bounded eight-cell transfer effects, never emitted tapes.
        This measured linear branch discovery is not a temporal HashLife jump.
        """
        self.ledger.bump("collatz_event_edge_requests")
        carry, first, last = 1, None, None
        block = self._empty
        for position in range(request.length + 2):
            self.ledger.bump("collatz_event_scanned_cells")
            bit = (
                self.application.program_bit(request.program, position)
                if position < request.length
                else 0
            )
            if position < request.length:
                block = block.then(self._atom(bit))
                self.ledger.bump("collatz_range_small_compositions")
                if block.length == 8:
                    self._store_range(
                        _Request("range", request.program, position - 7, 8), block
                    )
                    block = self._empty
            value = self.ledger.observe_arithmetic(3 * bit + carry)
            carry = value >> 1
            self.application.maximum_carry = max(self.application.maximum_carry, carry)
            if value & 1:
                if first is None:
                    first = position
                last = position
        self.application._finish_program_scan(request.program, request.length)
        yield from ()  # This finite leaf kernel needs no child requests.
        return CarryRangeSummary(request.length + 2, carry, first, last)

    def _range(self, request: _Request) -> _Computation:
        before, kind, shift = self._input(request.program)
        start, length = request.start, request.length
        if not length:
            return self._zero(0)
        if kind == "shift":
            return (yield _Request("range", before, start + shift, length))
        if kind == "identity" and start >= len(self.application._source):
            return self._zero(length)
        if kind != "identity" and length <= 8:
            return self._leaf_scan(request.program, start, length)[0]
        if length == 1:
            bit = cast(int, (yield _Request("point", request.program, start)))
            return self._atom(bit)
        # Largest aligned dyadic child; arbitrary prefix queries reuse those
        # same parent bindings instead of rescanning their individual points.
        split = 1 << (length.bit_length() - 1)
        if split == length:
            split >>= 1
        if start:
            split = min(split, start & -start)
        left = cast(
            CollatzRangeEffect, (yield _Request("range", request.program, start, split))
        )
        right = cast(
            CollatzRangeEffect,
            (yield _Request("range", request.program, start + split, length - split)),
        )
        if left.length >= 8 and right.length >= 8:
            return self.effect(self.compose(self._intern(left), self._intern(right)))
        self.ledger.bump("collatz_range_small_compositions")
        return left.then(right)

    @staticmethod
    def _cacheable(request: _Request) -> bool:
        length = request.length
        return (
            request.kind == "range"
            and length >= 8
            and length & (length - 1) == 0
            and request.start % length == 0
        )

    def _remember(self, request: _Request, value: _Value) -> None:
        if self._cacheable(request):
            self._store_range(request, cast(CollatzRangeEffect, value))

    def _store_range(self, request: _Request, value: CollatzRangeEffect) -> None:
        key = _RangeKey(request.program, request.start, request.length)
        action = self._intern(value)
        tile = self._source_tile(request)
        if tile is None:
            self._ranges[key] = action
        else:
            self._source_tiles[tile] = action
        self.ledger.bump("collatz_range_evaluations")
        self.ledger.bump("summary_evaluations")

    def _source_tile(self, request: _Request) -> _SourceTileKey | None:
        geometry = self.application.source_geometry
        if (
            geometry is None
            or request.program.local_id != 0
            or request.start + request.length > len(self.application._source)
        ):
            return None
        tile = geometry.tile_at(request.start, request.length.bit_length() - 1)
        if tile is None:
            return None
        return _SourceTileKey(
            ArenaHandle(geometry.token, "source-tile", tile.node_id), request.length
        )

    def _evaluate(self, request: _Request) -> _Value:
        stack: list[tuple[_Request, _Computation]] = []
        pending: _Request | None = request
        result: _Value = 0
        while True:
            self.ledger.bump("collatz_evaluator_transitions")
            if pending is not None:
                if self._cacheable(pending):
                    self.ledger.bump("collatz_range_requests")
                    key = _RangeKey(pending.program, pending.start, pending.length)
                    tile = self._source_tile(pending)
                    found = (
                        self._ranges.get(key)
                        if tile is None
                        else self._source_tiles.get(tile)
                    )
                    if found is not None:
                        self.ledger.bump("collatz_range_hits")
                        self.ledger.bump("summary_cache_hits")
                        if tile is not None:
                            self.ledger.bump("collatz_source_tile_effect_hits")
                        result, pending = self.effect(found), None
                if pending is not None:
                    if pending.kind == "point":
                        computation = self._point(pending)
                    elif pending.kind == "event":
                        computation = self._event(pending)
                    else:
                        computation = self._range(pending)
                    stack.append((pending, computation))
                    peak = self.ledger.counters.get(
                        "collatz_evaluator_stack_peak_frames", 0
                    )
                    self.ledger.bump(
                        "collatz_evaluator_stack_peak_frames", max(0, len(stack) - peak)
                    )
                    try:
                        pending = next(computation)
                        continue
                    except StopIteration as done:
                        result = cast(_Value, done.value)
                        finished, _ = stack.pop()
                        self._remember(finished, result)
                        pending = None
            if not stack:
                return result
            finished, computation = stack[-1]
            try:
                pending = computation.send(result)
            except StopIteration as done:
                result = cast(_Value, done.value)
                stack.pop()
                self._remember(finished, result)
                pending = None

    def point(self, program: ActionProgramID, position: int) -> int:
        if type(program) is not ActionProgramID:
            raise TypeError("expected a scoped Collatz action program")
        program.validate(self.owner, "program", size=len(self.application._programs))
        if type(position) is not int:
            raise TypeError("Collatz point coordinate must be an exact integer")
        if position < 0:
            return 0
        start = position // 8 * 8
        key = _RangeKey(program, start, 8)
        self.ledger.bump("collatz_point_parent_requests")
        found = self._ranges.get(key)
        if found is not None:
            effect = self.effect(found)
            coordinate = position - start
            if (
                effect.first_one is None
                or coordinate < effect.first_one
                or coordinate > cast(int, effect.last_one)
            ):
                self.ledger.bump("collatz_point_parent_hits")
                return 0
            if coordinate in (effect.first_one, effect.last_one):
                self.ledger.bump("collatz_point_parent_hits")
                return 1
        effect, answer = self._leaf_scan(program, start, 8, position)
        if found is None:
            self._store_range(_Request("range", program, start, 8), effect)
        assert answer is not None
        return answer

    def range_effect(
        self, program: ActionProgramID, start: int, length: int
    ) -> CollatzRangeEffect:
        if type(program) is not ActionProgramID:
            raise TypeError("expected a scoped Collatz action program")
        program.validate(self.owner, "program", size=len(self.application._programs))
        if type(start) is not int or type(length) is not int:
            raise TypeError("Collatz range geometry requires exact integers")
        if start < 0 or length < 0:
            raise ValueError("negative Collatz range")
        return cast(
            CollatzRangeEffect,
            self._evaluate(_Request("range", program, start, length)),
        )

    def event_summary(self, program: ActionProgramID, width: int) -> CarryRangeSummary:
        if type(program) is not ActionProgramID:
            raise TypeError("expected a scoped Collatz action program")
        if type(width) is not int or width <= 0:
            raise ValueError("Collatz event extent must be positive")
        program.validate(self.owner, "program", size=len(self.application._programs))
        self.ledger.bump("collatz_event_summary_requests")
        key = _RangeKey(program, 0, width)
        # Future arbitrary-prefix witnesses can collectively reveal a word;
        # only original-source prefix observations may own a response binding.
        cacheable = program.local_id == 0
        found = self._events.get(key) if cacheable else None
        if found is not None:
            self.ledger.bump("collatz_event_summary_hits")
            return found
        self.ledger.bump("collatz_event_summary_evaluations")
        cover = max(8, 1 << (width - 1).bit_length())
        parent = self._ranges.get(_RangeKey(program, 0, cover))
        effect = None if parent is None else self.effect(parent)
        if effect is not None and (effect.last_one is None or effect.last_one < width):
            row = effect.transfer.compose(self._zero(2).transfer).rows[1]
            result = CarryRangeSummary(
                width + 2, row.exit_carry, row.first_one, row.last_one
            )
            self.ledger.bump("collatz_event_parent_hits")
        else:
            result = cast(
                CarryRangeSummary, self._evaluate(_Request("event", program, 0, width))
            )
        if cacheable:
            self._events[key] = result
        return result

    def retained_entries(self) -> int:
        return (
            3
            + len(self._effects)
            + len(self._ids)
            + len(self._ranges)
            + len(self._source_tiles)
            + len(self._compositions)
            + len(self._events)
        )


register_proof_geometry_fields(
    {
        CollatzRangeEffect: frozenset(("first_one", "last_one")),
        _RangeKey: frozenset(("start", "length")),
        _CompositionKey: frozenset(),
        _Request: frozenset(("start", "length")),
        _SourceTileKey: frozenset(("length",)),
    }
)

# Import the independent relation auditor only after this proof executor is
# fully defined.  Ordinary production metrics never load either module; an
# explicitly constructed legacy Collatz proof application loads the range
# evaluator and thereby opts its retained key/value relations into auditing.
_lazy_observation_payload = import_module(
    "devtools.verification.lazy_observation_payload"
)

if TYPE_CHECKING:
    from devtools.verification.lazy_collatz import LazyCollatzApplication
