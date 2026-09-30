"""Source-backed reverse/add programs with bounded carry observations.

No future digit, pair, carry-row, or offset tape is allocated here. Spatial
memo entries bind canonical joint effects to demanded dyadic intervals
with disjoint two-cell leaves:
forward/backward carry functions and a capped reset-count port. They forget
interior outputs. Point work uses
one transient scan cursor per side and live stage, bounded by the event horizon.
A cursor replaces its previous position; no emitted carry-word cache exists.
Even-width range coordinates are canonicalized modulo reflection before work.

The program identity is structural, not a successor-closed temporal quotient.
Cold nonlinear branch discovery remains linear in the requested generation.
"""

from __future__ import annotations

from collections import OrderedDict
from collections.abc import (
    Generator,
    Iterator,
    MutableMapping,
    MutableSequence,
    Sequence,
)
from dataclasses import dataclass
from typing import Literal, cast, overload

from devtools.verification.carry_interval_effects import CarryActionQuotientArena
from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
    ExactSource,
    LazyFieldRef,
    TransferSummaryID,
)
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan, DyadicTile
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.proof_payload_admission import (
    register_proof_geometry_fields,
)


@dataclass(frozen=True, slots=True)
class ReverseRangeKey:
    generation: int
    stop: int
    level: int = 1


@dataclass(frozen=True, slots=True)
class ReverseRangeRequest:
    generation: int
    stop: int
    level: int = 1


@dataclass(frozen=True, slots=True)
class OffsetProgram:
    """A symbolic affine offset; references are local indexes, never digits."""

    kind: Literal["zero", "event", "transport", "add"]
    left: int = 0
    right: int = 0
    q: int = 0
    r: int = 0


@dataclass(frozen=True, slots=True)
class ReverseProgram:
    before: int
    offset: int
    q: int
    r: int
    width: int
    growth: int


@dataclass(frozen=True, slots=True)
class CarryRangeSummary:
    """Boundary function on [stop-2, stop), without its emitted carry word."""

    program: int
    stop: int
    action: TransferSummaryID
    level: int = 1

    def __post_init__(self) -> None:
        if (
            type(self.program) is not int
            or self.program < 0
            or type(self.stop) is not int
            or type(self.level) is not int
            or self.level < 1
            or self.level >= self.stop.bit_length()
            or self.stop % (1 << self.level)
            or type(self.action) is not TransferSummaryID
            or self.action.kind != "carry-interval-effect"
        ):
            raise ValueError(
                "carry summary requires a disjoint interval and scoped joint effect"
            )


@dataclass(frozen=True, slots=True)
class LazyReverseMetrics:
    family: str
    temporal_state_classes: int
    temporal_action_classes: int
    exact_spatial_occurrences: int
    symbolic_action_nodes: int
    jump_entries: int
    primitive_step_evaluations: int
    query_requests: int
    quotient_builds: int
    residual_physical_steps: int = 0
    action_compositions: int = 0
    action_applications: int = 0
    nonlinear_branch_evaluations: int = 0
    exact_endpoint_entries: int = 0
    workspace_peak: int = 0


_ScalarRequest = tuple[Literal["coefficient", "carry"] | int, int, int]
_Request = _ScalarRequest | ReverseRangeRequest
_Result = int | TransferSummaryID
_Computation = Generator[_Request, _Result, _Result]
# Keys select a stage and its left/right port, never a spatial cell. Each
# port replaces its scalar cursor; the total live workspace is capped at 2H.
_Cursors = OrderedDict[tuple[int, int], tuple[int, int]]


def _transport_weights(
    r: int,
    q: int,
    bits: int,
    ledger: ResourceLedger | None = None,
    *,
    limit: int | None = None,
) -> Iterator[int]:
    """Stream 2**q binomial coefficients modulo 2**bits with bounded limbs."""
    modulus = 1 << bits
    odd = 1
    valuation = 0
    for shift in range((r if limit is None else min(r, limit)) + 1):
        if shift:
            numerator, denominator = r - shift + 1, shift
            numerator_twos = (numerator & -numerator).bit_length() - 1
            denominator_twos = (denominator & -denominator).bit_length() - 1
            valuation += numerator_twos - denominator_twos
            product = odd * ((numerator >> numerator_twos) % modulus)
            if ledger is not None:
                ledger.observe_arithmetic(product)
            odd = product % modulus
            product = odd * pow(
                (denominator >> denominator_twos) % modulus, -1, modulus
            )
            if ledger is not None:
                ledger.observe_arithmetic(product)
            odd = product % modulus
        product = 0 if q + valuation >= bits else odd << (q + valuation)
        if ledger is not None:
            ledger.observe_arithmetic(product)
        if ledger is not None:
            ledger.bump("reverse_transport_terms")
        yield product % modulus


class LazyReverseApplication:
    """Apply a reverse-pair program lazily, then normalize requested digits."""

    def __init__(
        self,
        base: int,
        blank: int,
        steps: int,
        source: Sequence[int],
        ledger: ResourceLedger | None = None,
        *,
        source_geometry: SourceGeometry | None = None,
    ) -> None:
        if base < 2 or steps < 0:
            raise ValueError((base, steps))
        digits = tuple(map(int, source))
        if not digits or digits != digits[::-1]:
            raise ValueError("reverse/add requires a nonempty symmetric pair source")
        self.base, self.blank, self.steps = base, blank, steps
        self.ledger = ledger if ledger is not None else ResourceLedger()
        if source_geometry is not None:
            if source_geometry.ledger is not self.ledger:
                raise ValueError("source geometry belongs to another resource context")
            source_geometry.require_source(digits, blank)
        self.ledger.register_execution_root(self)
        self.owner = ArenaToken("lazy-reverse")
        prefix = f"lazy-reverse-{id(self)}"
        self._source_account = self.ledger.register(prefix + ":source", "exact-source")
        self._program_account = self.ledger.register(
            prefix + ":program", "action-program"
        )
        self._offset_account = self.ledger.register(
            prefix + ":offset", "symbolic-offset-program"
        )
        self._offset_key_account = self.ledger.register(
            prefix + ":offset-key", "symbolic-offset-interner"
        )
        self._summary_account = self.ledger.register(
            prefix + ":summary", "spatial_binding"
        )
        self._source_action_account = self.ledger.register(
            prefix + ":source-actions", "spatial_binding"
        )
        self._source_actions: OwnedMemo[ArenaHandle, TransferSummaryID] = OwnedMemo(
            self.ledger,
            self._source_action_account,
            evictable=True,
        )
        exact_source = ExactSource(
            digits, base, "reverse-pair", alphabet_size=2 * base - 1
        )
        self.ledger.reserve(self._source_account, entries=1, nodes=1)
        self.source = exact_source
        self.source_geometry = source_geometry
        self._sources = (self.source,)
        self.ledger.register_container(
            self._source_account,
            self._sources,
            node_count=lambda: 1,
            payloads=lambda: self._sources,
        )
        self.source_ref = ArenaHandle(self.owner, "source", 0)
        self.ledger.register_root(self._source_account, self.source_ref)
        self._offsets: MutableSequence[OffsetProgram] = self.ledger.make_list(
            self._offset_account
        )
        self._offset_keys: MutableMapping[OffsetProgram, int] = self.ledger.make_dict(
            self._offset_key_account
        )
        self._programs: MutableSequence[ReverseProgram] = self.ledger.make_list(
            self._program_account
        )
        self._ranges: MutableMapping[ReverseRangeKey, CarryRangeSummary] = (
            self.ledger.make_dict(self._summary_account, nodes_per_entry=1)
        )
        self.ledger.register_container(
            self._program_account,
            self._programs,
            node_count=lambda: len(self._programs),
            payloads=lambda: self._programs,
        )
        self.ledger.register_container(
            self._offset_account,
            self._offsets,
            node_count=lambda: len(self._offsets),
            payloads=lambda: self._offsets,
        )
        self.ledger.register_container(
            self._offset_key_account,
            self._offset_keys,
            node_count=lambda: 0,
            payloads=lambda: self._offset_keys.keys(),
        )
        self.ledger.register_container(
            self._summary_account,
            self._ranges,
            node_count=lambda: len(self._ranges),
            payloads=lambda: self._ranges.values(),
            evict=self._evict_ranges,
        )
        self.port_actions = CarryActionQuotientArena(self.ledger)
        self.carry_port = PortVariable(0, 0, "carry", 0)
        self._bits = (2 * (base - 1)).bit_length()
        self._modulus = 1 << self._bits
        self.horizon = 4 * self._bits
        self.workspace_limit = 2 * self.horizon
        self.workspace_peak = 0
        self._requests = 0
        self._built = False
        self._width: int | None = None
        self._branches = 0
        self._ranges_evicted = False
        zero = self._offset(OffsetProgram("zero"))
        self._append_program(ReverseProgram(0, zero, 0, 0, len(digits), 0))
        # Register defined instrumentation only after constructor admission and
        # all initial reservations succeeded. Zero does not reset a shared ledger.
        for counter in (
            "reverse_coefficient_requests",
            "reverse_offset_dag_visits",
            "reverse_transport_terms",
            "reverse_carry_interval_visits",
            "reverse_carry_function_classifications",
            "reverse_evaluator_transitions",
            "reverse_evaluator_requests",
            "reverse_growth_queries",
            "reverse_range_requests",
            "reverse_range_leaf_evaluations",
            "reverse_range_parent_evaluations",
            "reverse_range_parent_compositions",
            "reverse_range_parent_cache_hits",
            "reverse_source_reads",
            "reverse_source_tile_action_requests",
            "reverse_source_tile_action_cache_hits",
            "reverse_source_tile_action_visits",
            "reverse_source_action_stack_peak",
            "reverse_evaluator_stack_peak",
            "reverse_offset_stack_peak",
            "reverse_coefficient_dependencies_peak",
            "reverse_carry_workspace_peak",
        ):
            self.ledger.bump(counter, 0)

    def _evict_ranges(self) -> None:
        size = len(self._ranges)
        self._ranges.clear()
        self.ledger.release(self._summary_account, entries=size, nodes=size)
        self._ranges_evicted = True

    def _source_digit(self, position: int) -> int:
        self.ledger.bump("reverse_source_reads")
        if self.source_geometry is not None:
            return self.source_geometry.read(position)
        return self.source.digits[position]

    def _peak(self, name: str, value: int) -> None:
        previous = self.ledger.counters.get(name, 0)
        if value > previous:
            self.ledger.bump(name, value - previous)

    def _arithmetic(self, value: int) -> None:
        self.ledger.observe_arithmetic(value)

    def _offset(self, node: OffsetProgram) -> int:
        found = self._offset_keys.get(node)
        if found is not None:
            return found
        self.ledger.reserve_many(
            ((self._offset_account, 1, 1), (self._offset_key_account, 1, 0))
        )
        index = len(self._offsets)
        self._offsets.append(node)
        self._offset_keys[node] = index
        return index

    def _append_program(self, node: ReverseProgram) -> None:
        self.ledger.reserve(self._program_account, entries=1, nodes=1)
        self._programs.append(node)

    def _coefficient(
        self, generation: int, position: int, bits: int | None = None
    ) -> _Computation:
        """One modular coefficient as a scalar linear form in bounded carries."""
        self.ledger.bump("reverse_coefficient_requests")
        bits = self._bits if bits is None else bits
        modulus = 1 << bits
        width = self._programs[generation].width
        if position < 0 or position >= width:
            return 0
        position = min(position, width - 1 - position)
        if not generation:
            return self.ledger.observe_arithmetic(
                self._source_digit(position) % modulus
            )
        terms: dict[tuple[int, int], int] = {}
        constant = 0
        program = self._programs[generation]
        pending = [(program.offset, 0, 0)]
        while pending:
            self._peak("reverse_offset_stack_peak", len(pending))
            self.ledger.bump("reverse_offset_dag_visits")
            offset, q, r = pending.pop()
            if q >= bits:
                continue
            node = self._offsets[offset]
            if node.kind == "zero":
                continue
            if node.kind == "add":
                pending.extend(((node.left, q, r), (node.right, q, r)))
                continue
            if node.kind == "transport":
                pending.append((node.left, q + node.q, r + node.r))
                continue
            event = node.left
            step = self._programs[event + 1]
            old_width = self._programs[event].width
            for shift, weight in enumerate(
                _transport_weights(r, q, bits, self.ledger, limit=position)
            ):
                coordinate = position - shift
                if not 0 <= coordinate < step.width:
                    continue
                if not weight:
                    continue
                refs: tuple[tuple[int, int], ...]
                if step.growth and coordinate in (0, old_width):
                    constant = (
                        self.ledger.observe_arithmetic(constant + weight) % modulus
                    )
                    refs = ((1, -self.base),)
                elif step.growth:
                    refs = (
                        (coordinate, 1),
                        (old_width - coordinate, 1),
                        (coordinate + 1, -self.base),
                        (old_width - coordinate + 1, -self.base),
                    )
                else:
                    refs = (
                        (coordinate, 1),
                        (old_width - coordinate - 1, 1),
                        (coordinate + 1, -self.base),
                        (old_width - coordinate, -self.base),
                    )
                for boundary, multiplier in refs:
                    if boundary:
                        key = event, boundary
                        terms[key] = (
                            self.ledger.observe_arithmetic(
                                terms.get(key, 0) + weight * multiplier
                            )
                            % modulus
                        )
        q, r = program.q, program.r
        if q < bits:
            for shift, weight in enumerate(
                _transport_weights(r, q, bits, self.ledger, limit=position)
            ):
                coordinate = position - shift
                if 0 <= coordinate < len(self.source.digits):
                    constant = (
                        self.ledger.observe_arithmetic(
                            constant + weight * self._source_digit(coordinate)
                        )
                        % modulus
                    )
        self._peak("reverse_coefficient_dependencies_peak", len(terms))
        for (event, boundary), weight in sorted(
            terms.items(),
            key=lambda item: (
                item[0][0],
                int(item[0][1] > self._programs[item[0][0]].width // 2),
                min(item[0][1], self._programs[item[0][0]].width - item[0][1]),
            ),
        ):
            if weight:
                carry = cast(int, (yield "carry", event, boundary))
                constant = (
                    self.ledger.observe_arithmetic(constant + weight * carry) % modulus
                )
        return constant % modulus

    def _range_key(
        self, generation: int, stop: int, level: int = 1
    ) -> tuple[ReverseRangeKey, bool]:
        """Fold only when reflection preserves this dyadic interval grid."""
        width = self._programs[generation].width
        if type(level) is not int or level < 1 or level >= stop.bit_length():
            raise ValueError("carry range level must fit its extent")
        size = 1 << level
        if stop < size or stop % size or stop > width:
            raise ValueError("carry range must be an aligned interior interval")
        mirror = width + size - stop
        reflected = width % size == 0 and mirror < stop
        return ReverseRangeKey(
            generation, mirror if reflected else stop, level
        ), reflected

    def _range_action(
        self, generation: int, stop: int, level: int = 1
    ) -> TransferSummaryID | None:
        key, reflected = self._range_key(generation, stop, level)
        self.ledger.bump("reverse_summary_lookup_requests")
        summary = self._ranges.get(key)
        if summary is None:
            self.ledger.bump("reverse_summary_lookup_misses")
            return None
        self.ledger.bump("summary_cache_hits")
        self.ledger.bump("reverse_summary_lookup_hits")
        if level > 1:
            self.ledger.bump("reverse_range_parent_cache_hits")
        if reflected:
            self.ledger.bump("reverse_summary_reflection_hits")
            return self.port_actions.reflect_interval(summary.action)
        return summary.action

    def _store_range(
        self, generation: int, stop: int, level: int, action: TransferSummaryID
    ) -> None:
        """Bind a demanded interval only; never promote unrequested ancestors."""
        key, reflected = self._range_key(generation, stop, level)
        canonical = self.port_actions.reflect_interval(action) if reflected else action
        found = self._ranges.get(key)
        if found is not None:
            if found.action != canonical:
                raise AssertionError("dyadic range effects disagree")
            return
        self.ledger.reserve(self._summary_account, entries=1, nodes=1)
        self._ranges[key] = CarryRangeSummary(generation, key.stop, canonical, level)
        self.ledger.bump("summary_evaluations")

    def _source_tile_action(self, tile: DyadicTile) -> TransferSummaryID:
        """Compose original-source subtrees before considering their leaves."""
        if self.source_geometry is None:
            raise ValueError("source tile actions require original-source geometry")
        owner = self.source_geometry.token
        self.ledger.bump("reverse_source_tile_action_requests")
        found = self._source_actions.get(
            ArenaHandle(owner, "source-tile", tile.node_id)
        )
        if found is not None:
            self.ledger.bump("reverse_source_tile_action_cache_hits")
            return found
        stack = [(tile, False)]
        while stack:
            self._peak("reverse_source_action_stack_peak", len(stack))
            node, ready = stack.pop()
            if ArenaHandle(owner, "source-tile", node.node_id) in self._source_actions:
                continue
            self.ledger.bump("reverse_source_tile_action_visits")
            if node.level == 0:
                if node.symbol is None:
                    raise AssertionError("original source leaf lacks a symbol")
                self.ledger.bump("reverse_source_reads")
                self._source_actions[
                    ArenaHandle(owner, "source-tile", node.node_id)
                ] = self.port_actions.interval_symbol(
                    node.symbol,
                    base=self.base,
                    port=self.carry_port,
                )
                continue
            left, right = node.left, node.right
            if left is None or right is None:
                raise AssertionError("original source parent lacks children")
            if not ready:
                stack.append((node, True))
                if (
                    ArenaHandle(owner, "source-tile", right.node_id)
                    not in self._source_actions
                ):
                    stack.append((right, False))
                if (
                    left.node_id != right.node_id
                    and ArenaHandle(owner, "source-tile", left.node_id)
                    not in self._source_actions
                ):
                    stack.append((left, False))
                continue
            self._source_actions[ArenaHandle(owner, "source-tile", node.node_id)] = (
                self.port_actions.compose_intervals(
                    self._source_actions[
                        ArenaHandle(owner, "source-tile", left.node_id)
                    ],
                    self._source_actions[
                        ArenaHandle(owner, "source-tile", right.node_id)
                    ],
                    self.carry_port,
                )
            )
        return self._source_actions[ArenaHandle(owner, "source-tile", tile.node_id)]

    def _range(self, request: ReverseRangeRequest) -> _Computation:
        """Demand a complete parent effect using only child ActionIDs."""
        generation, stop, level = request.generation, request.stop, request.level
        self.ledger.bump("reverse_range_requests")
        found = self._range_action(generation, stop, level)
        if found is not None:
            return found
        key, reflected = self._range_key(generation, stop, level)
        source_tile = (
            self.source_geometry.tile_at(key.stop - (1 << level), level)
            if generation == 0 and self.source_geometry is not None
            else None
        )
        if source_tile is not None:
            action = self._source_tile_action(source_tile)
        elif level == 1:
            self.ledger.bump("reverse_range_leaf_evaluations")
            action = self.port_actions.interval_identity(self.carry_port)
            for position in range(key.stop - 2, key.stop):
                value = cast(int, (yield "coefficient", generation, position))
                self._arithmetic(value + 1)
                atom = self.port_actions.interval_symbol(
                    value, base=self.base, port=self.carry_port
                )
                action = self.port_actions.compose_intervals(
                    action, atom, self.carry_port
                )
        else:
            self.ledger.bump("reverse_range_parent_evaluations")
            middle = key.stop - (1 << (level - 1))
            left = cast(
                TransferSummaryID,
                (yield ReverseRangeRequest(generation, middle, level - 1)),
            )
            right = cast(
                TransferSummaryID,
                (yield ReverseRangeRequest(generation, key.stop, level - 1)),
            )
            self.ledger.bump("reverse_range_parent_compositions")
            action = self.port_actions.compose_intervals(left, right, self.carry_port)
        self._store_range(generation, key.stop, level, action)
        return self.port_actions.reflect_interval(action) if reflected else action

    def _carry_code_from_summary(self, summary: TransferSummaryID) -> int:
        effect = self.port_actions.interval_effect(summary)
        return self.port_actions.carry_code(effect.forward, self.carry_port)

    def _carry(self, generation: int, position: int, cursors: _Cursors) -> _Computation:
        if not position:
            return 0
        side = int(position > self._programs[generation].width // 2)
        cursor = cursors.get((generation, side))
        while position:
            if cursor is not None and cursor[0] == position:
                return cursor[1]
            self.ledger.bump("reverse_carry_interval_visits")
            summary = None
            level = 1
            if position % 2 == 0:
                # A reset in the final leaf already answers this carry port.
                # Parent descent is needed only across an identity suffix.
                summary = self._range_action(generation, position)
                if summary is None:
                    summary = cast(
                        TransferSummaryID,
                        (yield ReverseRangeRequest(generation, position)),
                    )
            if summary is not None:
                code = self._carry_code_from_summary(summary)
                if code != 1:
                    return code // 2
                # The identity suffix proves that its left sibling matters.
                # Demand their parent now, rather than publishing ancestors
                # whenever unrelated leaf occurrences happen to be known.
                while position % (1 << (level + 1)) == 0:
                    parent = cast(
                        TransferSummaryID,
                        (yield ReverseRangeRequest(generation, position, level + 1)),
                    )
                    code = self._carry_code_from_summary(parent)
                    if code != 1:
                        return code // 2
                    level += 1
                position -= 1 << level
                continue
            if position % 2:
                folded = (
                    cast(
                        TransferSummaryID,
                        (yield ReverseRangeRequest(generation, position + 1)),
                    )
                    if position < self._programs[generation].width
                    else None
                )
                if folded is not None:
                    effect = self.port_actions.interval_effect(folded)
                    forward = self.port_actions.carry_code(
                        effect.forward, self.carry_port
                    )
                    backward = self.port_actions.carry_code(
                        effect.backward, self.carry_port
                    )
                    if forward == 1:
                        position -= 1  # Both cells are identity.
                        continue
                    if effect.reset_count == 2 or backward != forward:
                        return backward // 2  # The first cell is a known reset.
                    incoming = cast(int, (yield "carry", generation, position - 1))
                    if incoming == forward // 2:
                        return incoming
                    # [ID, C] and [C, ID] remain aliased. Query only the
                    # source-backed residue bits needed to distinguish ID.
                    for bits in range(1, self._bits + 1):
                        residue = cast(int, (yield bits, generation, position - 1))
                        if residue != (self.base - 1) % (1 << bits):
                            return forward // 2
                    return incoming
            # Only a final unpaired cell is observed. A reset destroys all
            # earlier carry input; no interior carry word is emitted or saved.
            coefficient = cast(int, (yield "coefficient", generation, position - 1))
            self._arithmetic(coefficient + 1)
            if coefficient != self.base - 1:
                return int(coefficient >= self.base)
            position -= 1
        return 0

    @overload
    def _evaluate(self, request: _ScalarRequest, workspace: _Cursors) -> int: ...

    @overload
    def _evaluate(
        self, request: ReverseRangeRequest, workspace: _Cursors
    ) -> TransferSummaryID: ...

    def _evaluate(self, request: _Request, workspace: _Cursors) -> _Result:
        """One iterative trampoline for scalar observations and dyadic actions."""
        stack: list[tuple[_Request, _Computation]] = []
        pending: _Request | None = request
        result: _Result = 0
        while True:
            self.ledger.bump("reverse_evaluator_transitions")
            if pending is not None:
                self.ledger.bump("reverse_evaluator_requests")
                if isinstance(pending, ReverseRangeRequest):
                    computation = self._range(pending)
                else:
                    kind, generation, position = pending
                    side = int(position > self._programs[generation].width // 2)
                    cursor_key = generation, side
                    cursor = workspace.get(cursor_key) if kind == "carry" else None
                    if cursor is not None and cursor[0] == position:
                        workspace.move_to_end(cursor_key)
                        result = cursor[1]
                        pending = None
                        continue
                    computation = (
                        self._carry(generation, position, workspace)
                        if kind == "carry"
                        else self._coefficient(
                            generation,
                            position,
                            None if kind == "coefficient" else kind,
                        )
                    )
                stack.append((pending, computation))
                self._peak("reverse_evaluator_stack_peak", len(stack))
                try:
                    pending = next(computation)
                    continue
                except StopIteration as done:
                    result = cast(_Result, done.value)
                    pending = None
                    finished, _ = stack.pop()
                    if not isinstance(finished, ReverseRangeRequest):
                        self._remember(workspace, finished, cast(int, result))
            if not stack:
                return result
            completed, current = stack[-1]
            try:
                pending = current.send(result)
            except StopIteration as done:
                result = cast(_Result, done.value)
                stack.pop()
                if not isinstance(completed, ReverseRangeRequest):
                    self._remember(workspace, completed, cast(int, result))
                pending = None

    def _remember(
        self, workspace: _Cursors, request: _ScalarRequest, result: int
    ) -> None:
        if request[0] != "carry" or request[2] % 2 == 0:
            return
        summary = (
            self._range_action(request[1], request[2] + 1)
            if request[2] < self._programs[request[1]].width
            else None
        )
        if (
            summary is not None
            and self.port_actions.interval_effect(summary).reset_count != 1
        ):
            return
        key = request[1], int(request[2] > self._programs[request[1]].width // 2)
        if key not in workspace and len(workspace) == self.workspace_limit:
            workspace.popitem(last=False)
        workspace[key] = request[2], result
        workspace.move_to_end(key)
        if len(workspace) > self.workspace_peak:
            self.ledger.bump(
                "reverse_carry_workspace_peak", len(workspace) - self.workspace_peak
            )
            self.workspace_peak = len(workspace)

    def _scan(self, generation: int, workspace: _Cursors) -> int:
        """Demand only the terminal carry cone; no full-width successor scan."""
        self.ledger.bump("reverse_growth_queries")
        position = self._programs[generation].width
        while position and position % 2 == 0:
            found = None
            for level in range((position & -position).bit_length() - 1, 0, -1):
                found = self._range_action(generation, position, level)
                if found is not None:
                    code = self.port_actions.carry_code(
                        self.port_actions.interval_effect(found).forward,
                        self.carry_port,
                    )
                    if code != 1:
                        return code // 2
                    position -= 1 << level
                    break
            if found is None:
                break
        if not position:
            return 0
        return self._evaluate(("carry", generation, position), workspace)

    def _ensure_program(self) -> None:
        if self._built:
            if self._ranges_evicted:
                self._ranges_evicted = False
            return
        workspace: _Cursors = OrderedDict()
        while len(self._programs) <= self.steps:
            before = len(self._programs) - 1
            previous = self._programs[before]
            growth = self._scan(before, workspace)
            event = self._offset(OffsetProgram("event", left=before))
            transport = self._offset(
                OffsetProgram("transport", left=previous.offset, q=1 - growth, r=growth)
            )
            offset = self._offset(OffsetProgram("add", left=transport, right=event))
            self._append_program(
                ReverseProgram(
                    before,
                    offset,
                    min(self._bits, previous.q + 1 - growth),
                    previous.r + growth,
                    previous.width + growth,
                    growth,
                )
            )
            self._branches += 1
            self.ledger.bump("reverse_nonlinear_branch_evaluations")
        pair_width = self._programs[-1].width
        terminal_carry = self._scan(self.steps, workspace)
        width = pair_width + terminal_carry
        if not terminal_carry:
            while width > 1:
                coefficient = self._evaluate(
                    ("coefficient", self.steps, width - 1), workspace
                )
                carry = self._evaluate(("carry", self.steps, width - 1), workspace)
                if (coefficient + carry) % self.base:
                    break
                width -= 1
        self._width = width
        self._built = True

    @property
    def field(self) -> LazyFieldRef:
        self._ensure_program()
        return LazyFieldRef(
            self.source_ref,
            ActionProgramID(self.owner, "reverse-program", self.steps),
            extent=self._programs[self.steps].width,
        )

    @source_reads_only
    def point(self, position: int) -> int:
        self._requests += 1
        self._ensure_program()
        if position < 0 or position >= self.active_width():
            return self.blank
        width = self._programs[self.steps].width
        if position == width:
            return 1
        workspace: _Cursors = OrderedDict()
        coefficient = self._evaluate(("coefficient", self.steps, position), workspace)
        carry = self._evaluate(("carry", self.steps, position), workspace)
        return (coefficient + carry) % self.base

    @source_reads_only
    def active_width(self) -> int:
        self._ensure_program()
        assert self._width is not None
        return self._width

    def retained_spans(self) -> tuple[DyadicSpan, ...]:
        # Original source storage is ExactSource, not a second dyadic copy.
        return ()

    def retained_entries(self) -> int:
        accounts = {
            self._source_account,
            self._program_account,
            self._summary_account,
            self._offset_account,
            self._offset_key_account,
            self._source_action_account,
        }
        return (
            sum(
                item.entries
                for item in self.ledger.inventory()
                if item.owner in accounts
            )
            + self.port_actions.retained_entries()
        )

    def metrics(self) -> LazyReverseMetrics:
        # These are observed finite boundary functions and structural program
        # nodes respectively; neither count proves temporal successor closure.
        classes = len({summary.action for summary in self._ranges.values()})
        nodes = len(self._programs) + len(self._offsets)
        return LazyReverseMetrics(
            "reverse-add-lazy-symbolic",
            classes,
            nodes,
            1,
            nodes,
            0,
            self._branches,
            self._requests,
            int(self._built),
            action_compositions=self._branches,
            nonlinear_branch_evaluations=self._branches,
            workspace_peak=self.workspace_peak,
        )


register_proof_geometry_fields(
    {
        OffsetProgram: frozenset(("left", "right", "q", "r")),
        ReverseProgram: frozenset(("before", "offset", "q", "r", "width")),
        CarryRangeSummary: frozenset(("program", "stop", "level")),
        ReverseRangeKey: frozenset(("generation", "stop", "level")),
    }
)
