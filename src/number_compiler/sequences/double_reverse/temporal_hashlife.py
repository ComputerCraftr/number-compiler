"""Source guarded Hashlife actions for the decimal ``2 * reverse`` map.

One cellular step is the exact two generation map ``F = T²``.  Only words
whose complete two digit borders satisfy the checked four phase cylinder are
powered here.  The engine returns source bound actions over the existing SLP
arena; it neither expands decimal words nor chooses a successor from a border
clock alone.
"""

from __future__ import annotations

from collections.abc import Callable, Iterator
from typing import cast

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.contracts.scoped_handles import ArenaToken
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import (
    double_reverse as _double_reverse_keys,
)
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditStoreBinding,
)
from number_compiler.sequences.double_reverse.boundary_cycles import (
    candidate_component,
)
from number_compiler.sequences.double_reverse.stencil_moore import (
    DIGIT_STENCIL_MOORE,
    stencil_cell,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_audit import (
    audit_double_reverse_temporal_actions,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_slp import (
    _existing_symbol_at,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
    DoubleReversePortAction,
    DoubleReverseSLPID,
    DoubleReverseSourcePrefix,
    IssuedDoubleReversePortAction,
    IssuedDoubleReverseSourcePrefix,
    PointedDigitStencil,
    UncertifiedPointedStencilError,
    source_prefix_binding,
    temporal_action_binding,
)


def two_step_cell(left: int, digit: int, right: int) -> int:
    """Exact local carry law for two physical reverse/double transitions."""
    return stencil_cell(left, digit, right)


def edge_phase(upper: tuple[int, int], lower: tuple[int, int]) -> int | None:
    """Classify a source by its exact two digit borders."""
    if upper == (1, 7):
        if lower == (4, 2):
            return 1
        if lower in ((6, 8), (8, 8)):
            return 0
    elif upper in ((4, 8), (4, 9)):
        if lower == (4, 2):
            return 2
        if lower in ((6, 8), (8, 8)):
            return 3
    return None


def growth_ports(phase: int, steps: int) -> tuple[int, int]:
    """Return exact left/right cell births after ``steps`` applications of F."""
    if type(phase) is not int or phase not in (0, 1, 2, 3):
        raise ValueError("invalid 2rev10 border phase")
    if type(steps) is not int or steps < 0:
        raise ValueError("2rev10 F-step count must be nonnegative")
    low = steps // 2
    high = (steps + 1) // 2
    return (
        high if phase in (2, 3) else low,
        high if phase in (0, 3) else low,
    )


def _audit_temporal_hashlife_payloads(
    ledger: object, root: object
) -> PayloadAuditContribution:
    return audit_double_reverse_temporal_actions(
        ledger, root, DoubleReverseTemporalHashlife
    )


class DoubleReverseTemporalHashlife:
    """Ledger memoized dyadic cones and source aligned temporal actions."""

    __slots__ = (
        "__weakref__",
        "_actions",
        "_audit_actions",
        "_audit_cones",
        "_audit_prefixes",
        "_audit_slices",
        "_cone",
        "_prefix_binding_snapshot",
        "_prefix_issued",
        "_prefixes",
        "_slices",
        "_source_advancer",
        "arena",
        "issuer",
        "ledger",
        "max_steps",
        "prefix_limit",
        "scratch_owner",
        "source_root",
    )

    def __init__(
        self,
        arena: LedgerSLPArena,
        ledger: ResourceLedger,
        issuer: ArenaToken,
        scratch_owner: int,
        cone_memo: OwnedMemo[tuple[int, int], int],
        slice_memo: OwnedMemo[tuple[int, int, int], int],
        action_memo: OwnedMemo[tuple[int, int, int], IssuedDoubleReversePortAction],
        source_prefix_memo: OwnedMemo[int, IssuedDoubleReverseSourcePrefix],
        source_root: int,
        max_steps: int,
    ) -> None:
        self.arena = arena
        self.ledger = ledger
        self.issuer = issuer
        self.scratch_owner = scratch_owner
        self.max_steps = max_steps
        self.prefix_limit = min(32, max_steps)
        self.source_root = source_root
        self._cone = cone_memo
        self._slices = slice_memo
        self._actions = action_memo
        self._prefixes = source_prefix_memo
        self._source_advancer: Callable[[int], int] | None = None
        self._prefix_issued: IssuedDoubleReverseSourcePrefix | None = None
        self._prefix_binding_snapshot: tuple[int | str | None, ...] | None = None
        self._audit_actions = action_memo._data
        self._audit_cones = cone_memo._data
        self._audit_slices = slice_memo._data
        self._audit_prefixes = source_prefix_memo._data
        ledger.register_execution_root(self)
        ledger.register_payload_audit_contract(
            self,
            "double_reverse",
            (
                PayloadAuditStoreBinding(
                    action_memo.owner,
                    "_audit_actions",
                    "double_reverse_temporal_memo",
                ),
                PayloadAuditStoreBinding(
                    cone_memo.owner,
                    "_audit_cones",
                    "double_reverse_temporal_memo",
                ),
                PayloadAuditStoreBinding(
                    slice_memo.owner,
                    "_audit_slices",
                    "double_reverse_temporal_memo",
                ),
                PayloadAuditStoreBinding(
                    source_prefix_memo.owner,
                    "_audit_prefixes",
                    "double_reverse_temporal_memo",
                ),
            ),
            _audit_temporal_hashlife_payloads,
        )

    def admit_extended_prefix(self, limit: int) -> None:
        """Allow a bounded exact one-T admission scan, only on explicit demand.

        This does not broaden any border-cylinder theorem: every extra step
        is the existing owner-issued chronological source transition.  The
        original 32-tick horizon remains the default for other observers.
        """
        if type(limit) is not int or not 0 <= limit <= min(512, self.max_steps):
            raise ValueError("extended exact 2rev10 prefix exceeds its budget")
        self.prefix_limit = max(self.prefix_limit, limit)

    def dispose_audit_contract(self) -> None:
        """Retire issuer validation before the associated action memo closes."""
        self.ledger.remove_payload_audit_contract(self, "double_reverse")
        self._source_advancer = None

    def _handle(self, root: int) -> DoubleReverseSLPID:
        return DoubleReverseSLPID(self.issuer, "double_reverse_slp", root)

    def _root(self, handle: DoubleReverseSLPID) -> int:
        if type(handle) is not DoubleReverseSLPID:
            raise ValueError("temporal action has a malformed SLP handle")
        return handle.validate(
            self.issuer, "double_reverse_slp", size=len(self.arena.nodes)
        ).local_id

    def root_of(self, handle: DoubleReverseSLPID) -> int:
        """Resolve a local root handle after checking its arena generation."""
        return self._root(handle)

    def source_prefix(self) -> DoubleReverseSourcePrefix | None:
        """Return this owner's latest exact prefix cursor, if one was issued."""
        issued = self._prefixes.get(self.source_root)
        if issued is None:
            return None
        if issued is not self._prefix_issued:
            raise ValueError("2rev10 source-prefix cursor is not owner-issued")
        return self.validate_source_prefix(issued.entry)

    def validate_source_prefix(self, entry: object) -> DoubleReverseSourcePrefix:
        """Accept only the exact, sealed cursor previously issued by this owner."""
        issued = self._prefixes.get(self.source_root)
        if (
            type(entry) is not DoubleReverseSourcePrefix
            or issued is None
            or issued is not self._prefix_issued
            or issued.entry is not entry
        ):
            raise ValueError("2rev10 source-prefix cursor is not owner-issued")
        self._validate_source_prefix(issued)
        return issued.entry

    def _bind_source_advancer(self, advance: Callable[[int], int]) -> None:
        """Bind the source adapter's exact one-T transition during construction."""
        if not callable(advance) or self._source_advancer is not None:
            raise ValueError("2rev10 source transition owner is already bound")
        self._source_advancer = advance

    def advance_source_root(self, root: int) -> int:
        """Apply the already-bound exact physical T map to one arena root.

        This is used only to inspect the physical midpoint of an owner-issued
        T-squared action. The returned root carries no temporal-action
        authority; endpoint actions remain the checked records from this
        engine's Hashlife issuer.
        """
        if type(root) is not int or not 0 <= root < len(self.arena.nodes):
            raise ValueError("2rev10 physical source root is outside its arena")
        advance = self._source_advancer
        if advance is None:
            raise ValueError("2rev10 source transition owner is unavailable")
        target_root = advance(root)
        if type(target_root) is not int or not 0 <= target_root < len(self.arena.nodes):
            raise ValueError("2rev10 source transition returned an invalid root")
        return target_root

    def _advance_source_prefix(self) -> DoubleReverseSourcePrefix:
        """Issue the initial cursor or advance it through the bound exact T map."""
        current = self.source_prefix()
        if current is None:
            target_root = self.source_root
            physical_steps = 0
        else:
            physical_steps = current.physical_steps + 1
            if physical_steps > self.prefix_limit:
                raise ValueError("2rev10 source-prefix cursor exceeds its horizon")
            if self._source_advancer is None:
                raise ValueError("2rev10 source transition owner is unavailable")
            previous_root = self._root(current.target)
            target_root = self._source_advancer(previous_root)
            if type(target_root) is not int or not 0 <= target_root < len(
                self.arena.nodes
            ):
                raise ValueError("2rev10 source transition returned an invalid root")
        certified_phase = self.certify(target_root)
        entry = DoubleReverseSourcePrefix(
            self._handle(self.source_root),
            self._handle(target_root),
            physical_steps,
            certified_phase,
        )
        issued = IssuedDoubleReverseSourcePrefix(entry, source_prefix_binding(entry))
        self._prefixes[self.source_root] = issued
        self._prefix_issued = issued
        self._prefix_binding_snapshot = issued.binding
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_POINTED_BORDER_PREFIX_CURSOR_PUBLICATIONS
        )
        return entry

    def _validate_source_prefix(self, issued: IssuedDoubleReverseSourcePrefix) -> None:
        if type(issued) is not IssuedDoubleReverseSourcePrefix:
            raise ValueError("malformed 2rev10 source-prefix owner record")
        entry = issued.entry
        if (
            type(entry) is not DoubleReverseSourcePrefix
            or self._root(entry.source) != self.source_root
            or type(entry.physical_steps) is not int
            or not 0 <= entry.physical_steps <= self.prefix_limit
            or entry.certified_phase is not None
            and (
                type(entry.certified_phase) is not int
                or entry.certified_phase not in (0, 1, 2, 3)
            )
            or issued.binding != source_prefix_binding(entry)
            or issued.binding != self._prefix_binding_snapshot
        ):
            raise ValueError("2rev10 source-prefix cursor binding is stale")
        self._root(entry.target)

    def validate_action(self, action: DoubleReversePortAction) -> None:
        """Validate an action at the scheduler payload trust boundary."""
        self._validate_action(action)

    def _validate_action(
        self, action: DoubleReversePortAction, *, audit: bool = False
    ) -> None:
        if type(action) is not DoubleReversePortAction:
            raise ValueError("temporal action is foreign or malformed")
        source = self._root(action.source)
        key = (source, action.steps, action.phase_in)
        self._validate_issued_action(action, self._actions.get(key), audit=audit)

    def _validate_issued_action(
        self,
        action: DoubleReversePortAction,
        issued: object,
        *,
        audit: bool = False,
    ) -> None:
        if type(action) is not DoubleReversePortAction:
            raise ValueError("temporal action is foreign or malformed")
        # Shape checks alone are not authority: a forged action can preserve
        # both border pairs and width while naming an incorrect interior.
        # The cache wrapper also seals nested handle fields. A frozen action
        # can otherwise be changed through object.__setattr__ on its handles.
        if (
            type(issued) is not IssuedDoubleReversePortAction
            or issued.action is not action
            or issued.binding != temporal_action_binding(action)
        ):
            raise ValueError("temporal action was not published by this owner")
        self._validate_action_shape(action, audit=audit)

    def _issue_action(
        self, key: tuple[int, int, int], action: DoubleReversePortAction
    ) -> None:
        """Publish one action together with its immutable issue-time binding."""
        issued = IssuedDoubleReversePortAction(action, temporal_action_binding(action))
        if key != (action.source.local_id, action.steps, action.phase_in):
            raise ValueError("temporal action key does not match its source")
        self._validate_action_shape(action)
        self._actions[key] = issued

    def _validate_action_shape(
        self, action: DoubleReversePortAction, *, audit: bool = False
    ) -> None:
        if type(action) is not DoubleReversePortAction:
            raise ValueError("temporal action is foreign or malformed")
        source = self._root(action.source)
        target = self._root(action.target)
        if (
            type(action.steps) is not int
            or action.steps < 1
            or type(action.phase_in) is not int
            or type(action.phase_out) is not int
            or action.phase_in not in (0, 1, 2, 3)
            or action.phase_out != (action.phase_in + 2 * action.steps) % 4
            or type(action.left_births) is not int
            or type(action.right_births) is not int
            or min(action.left_births, action.right_births) < 0
            or growth_ports(action.phase_in, action.steps)
            != (action.left_births, action.right_births)
            or self.arena.nodes[target].length
            != self.arena.nodes[source].length
            + action.left_births
            + action.right_births
            or self._certify(source, audit=audit) != action.phase_in
            or self._certify(target, audit=audit) != action.phase_out
        ):
            raise ValueError("temporal action ports do not match its source and target")

    def certify(self, root: int) -> int | None:
        """Recognize the closed cylinder from both exact borders."""
        return self._certify(root, audit=False)

    def edge_signature(self, root: int) -> tuple[int, int, int, int] | None:
        """Read the two-cell boundary without assigning it temporal authority."""
        if type(root) is not int or not 0 <= root < len(self.arena.nodes):
            raise ValueError("invalid double-reverse SLP root")
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_BOUNDARY_CANDIDATE_CLASSIFICATIONS
        )
        return self._edge_signature(root, audit=False)

    def candidate_cycle(self, root: int) -> int | None:
        """Return a candidate SCC index for diagnostics only."""
        signature = self.edge_signature(root)
        return None if signature is None else candidate_component(signature)

    def _edge_signature(
        self, root: int, *, audit: bool
    ) -> tuple[int, int, int, int] | None:
        width = self.arena.nodes[root].length
        if width < 5:
            return None
        if audit:
            values = (
                _existing_symbol_at(
                    self.arena,
                    root,
                    0,
                    on_visit=self._payload_audit_boundary_visit,
                ),
                _existing_symbol_at(
                    self.arena,
                    root,
                    1,
                    on_visit=self._payload_audit_boundary_visit,
                ),
                _existing_symbol_at(
                    self.arena,
                    root,
                    width - 2,
                    on_visit=self._payload_audit_boundary_visit,
                ),
                _existing_symbol_at(
                    self.arena,
                    root,
                    width - 1,
                    on_visit=self._payload_audit_boundary_visit,
                ),
            )
            if any(value is None for value in values):
                return None
            return cast(tuple[int, int, int, int], values)
        on_visit = self._boundary_visit
        return (
            symbol_at(self.arena, root, 0, on_visit=on_visit),
            symbol_at(self.arena, root, 1, on_visit=on_visit),
            symbol_at(self.arena, root, width - 2, on_visit=on_visit),
            symbol_at(self.arena, root, width - 1, on_visit=on_visit),
        )

    def _certify(self, root: int, *, audit: bool) -> int | None:
        """Classify a cylinder while isolating explicit audit counters."""
        if type(root) is not int or not 0 <= root < len(self.arena.nodes):
            raise ValueError("invalid double-reverse SLP root")
        if audit:
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_PAYLOAD_AUDIT_BOUNDARY_CLASSIFICATIONS
            )
        else:
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_BOUNDARY_CLASSIFICATIONS
            )
        signature = self._edge_signature(root, audit=audit)
        return None if signature is None else edge_phase(signature[:2], signature[2:])

    def _boundary_visit(self) -> None:
        """Count each SLP node read while classifying a cylinder boundary."""
        self.ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_BOUNDARY_NODE_VISITS)

    def _payload_audit_boundary_visit(self) -> None:
        """Separate explicit audit traversal from production execution work."""
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_PAYLOAD_AUDIT_BOUNDARY_VISITS
        )

    def part(self, root: int, begin: int, end: int) -> int:
        """Iteratively slice a compressed SLP without spelling repeats."""
        if type(root) is not int or not 0 <= root < len(self.arena.nodes):
            raise ValueError("invalid double-reverse SLP root")
        if type(begin) is not int or type(end) is not int:
            raise TypeError("SLP slice coordinates must be exact integers")
        node = self.arena.nodes[root]
        if not 0 <= begin <= end <= node.length:
            raise ValueError("hashlife substring outside source")
        if begin == end:
            return self.arena.empty_id
        if begin == 0 and end == node.length:
            return root
        key = (root, begin, end)
        found = self._slices.get(key)
        if found is not None:
            return found
        tasks: list[tuple[int, int, int]] = []
        fragments: list[int] = []
        retained_tasks = 0

        def push_task(task: tuple[int, int, int]) -> None:
            nonlocal retained_tasks
            self.ledger.reserve(self.scratch_owner, entries=1, nodes=1)
            try:
                tasks.append(task)
            except BaseException as error:
                try:
                    self.ledger.release(self.scratch_owner, entries=1, nodes=1)
                except BaseException as cleanup_error:
                    raise error from cleanup_error
                raise
            retained_tasks += 1

        def keep_fragment(fragment: int) -> None:
            self.ledger.reserve(self.scratch_owner, entries=1, nodes=1)
            try:
                fragments.append(fragment)
            except BaseException as error:
                try:
                    self.ledger.release(self.scratch_owner, entries=1, nodes=1)
                except BaseException as cleanup_error:
                    raise error from cleanup_error
                raise

        try:
            push_task((root, begin, end))
            while tasks:
                child, lo, hi = tasks.pop()
                retained_tasks -= 1
                self.ledger.release(self.scratch_owner, entries=1, nodes=1)
                current = self.arena.nodes[child]
                if lo == hi:
                    continue
                if lo == 0 and hi == current.length:
                    keep_fragment(child)
                elif current.kind == "CONCAT":
                    pivot = self.arena.nodes[current.left].length
                    if hi > pivot:
                        push_task((current.right, max(0, lo - pivot), hi - pivot))
                    if lo < pivot:
                        push_task((current.left, lo, min(hi, pivot)))
                elif current.kind == "REPEAT":
                    child_length = self.arena.nodes[current.child].length
                    if child_length == 0:
                        raise AssertionError("empty repeated child")
                    first, first_pos = divmod(lo, child_length)
                    last, last_pos = divmod(hi, child_length)
                    if first == last:
                        push_task((current.child, first_pos, last_pos))
                    else:
                        if last_pos:
                            push_task((current.child, 0, last_pos))
                        copies = last - first - int(first_pos != 0)
                        if copies:
                            repeated = self.arena.repeat(current.child, copies)
                            push_task((repeated, 0, copies * child_length))
                        if first_pos:
                            push_task((current.child, first_pos, child_length))
                else:
                    raise AssertionError("partial terminal or empty grammar")
            # concat_many holds a row and its next pairwise level at once.
            with self.ledger.reservation(
                self.scratch_owner,
                entries=2 * len(fragments),
                nodes=2 * len(fragments),
            ):
                result = self.arena.concat_many(fragments)
        finally:
            if fragments:
                self.ledger.release(
                    self.scratch_owner,
                    entries=len(fragments),
                    nodes=len(fragments),
                )
                fragments.clear()
            if retained_tasks:
                self.ledger.release(
                    self.scratch_owner,
                    entries=retained_tasks,
                    nodes=retained_tasks,
                )
        if self.arena.nodes[result].length != end - begin:
            raise AssertionError("hashlife SLP slice lost a decimal cell")
        self._slices[key] = result
        return result

    def _cone_step(self, root: int, steps: int) -> int:
        """Iterative memoized dyadic space-time cone composition."""
        if type(steps) is not int or steps < 1 or steps & (steps - 1):
            raise ValueError("hashlife cone requires a positive power of two")
        if self.arena.nodes[root].length != 4 * steps:
            raise ValueError("hashlife cone requires a complete causal halo")
        # Depth-first ternary subdivision keeps the work stack logarithmic.
        # Charge a conservative fixed multiple of that depth before allocating
        # either Python list; all grammar nodes remain charged by the arena.
        work = max(16, 8 * steps.bit_length() + 8)
        with self.ledger.reservation(self.scratch_owner, entries=work, nodes=work):
            tasks = [("visit", root, steps)]
            values: list[int] = []
            while tasks:
                tag, block, time_steps = tasks.pop()
                key = (block, time_steps)
                if tag == "visit":
                    cached = self._cone.get(key)
                    if cached is not None:
                        values.append(cached)
                        self.ledger.bump(
                            _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_CONE_HITS
                        )
                        continue
                    self.ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_CONES)
                    if time_steps == 1:
                        a, b, c, d = (symbol_at(self.arena, block, i) for i in range(4))
                        result = self.arena.word(
                            (two_step_cell(a, b, c), two_step_cell(b, c, d))
                        )
                        self._cone[key] = result
                        values.append(result)
                        continue
                    half = time_steps // 2
                    tasks.append(("first_join", block, time_steps))
                    tasks.append(
                        (
                            "visit",
                            self.part(block, 2 * time_steps, 4 * time_steps),
                            half,
                        )
                    )
                    tasks.append(
                        (
                            "visit",
                            self.part(block, time_steps, 3 * time_steps),
                            half,
                        )
                    )
                    tasks.append(("visit", self.part(block, 0, 2 * time_steps), half))
                elif tag == "first_join":
                    right = values.pop()
                    middle = values.pop()
                    left = values.pop()
                    half = time_steps // 2
                    tasks.append(("finish", block, time_steps))
                    tasks.append(("visit", self.arena.concat(middle, right), half))
                    tasks.append(("visit", self.arena.concat(left, middle), half))
                elif tag == "finish":
                    right = values.pop()
                    left = values.pop()
                    result = self.arena.concat(left, right)
                    self._cone[key] = result
                    values.append(result)
                else:
                    raise AssertionError("unknown Hashlife cone task")
            if len(values) != 1:
                raise AssertionError("Hashlife cone tasks left extra results")
            return values[0]

    def _power_of_two(self, root: int, steps: int, phase: int) -> int:
        """Produce the physical SLP from a guarded F^steps causal cone."""
        width = self.arena.nodes[root].length
        zero = self.arena.terminal(0)
        pad = self.arena.repeat(zero, 2 * steps)
        padded = self.arena.concat_many((pad, root, self.arena.repeat(zero, 4 * steps)))
        span = 2 * steps
        requested = width + 2 * steps
        count = (requested + span - 1) // span

        def select_tiles() -> Iterator[int]:
            for tile_index in range(count):
                self.ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_TILE_SELECTIONS
                )
                block = self.part(
                    padded,
                    tile_index * span,
                    tile_index * span + 4 * steps,
                )
                yield self._cone_step(block, steps)

        tiles = select_tiles()
        # The output can contain one tile per spatial chunk. Charge its held
        # roots and concat_many's temporary pairwise rows before consuming it.
        tile_roots: list[int] = []
        try:
            for tile in tiles:
                self.ledger.reserve(self.scratch_owner, entries=1, nodes=1)
                try:
                    tile_roots.append(tile)
                except BaseException as error:
                    try:
                        self.ledger.release(self.scratch_owner, entries=1, nodes=1)
                    except BaseException as cleanup_error:
                        raise error from cleanup_error
                    raise
            with self.ledger.reservation(
                self.scratch_owner,
                entries=2 * len(tile_roots),
                nodes=2 * len(tile_roots),
            ):
                full = self.arena.concat_many(tile_roots)
        finally:
            if tile_roots:
                self.ledger.release(
                    self.scratch_owner,
                    entries=len(tile_roots),
                    nodes=len(tile_roots),
                )
                tile_roots.clear()
        left, right = growth_ports(phase, steps)
        result = self.part(full, steps - left, steps + width + right)
        expected_phase = (phase + 2 * steps) % 4
        if self.certify(result) != expected_phase:
            raise AssertionError("2rev10 temporal cone lost its certified border")
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWERED_T2_STEPS, steps
        )
        self.ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWER_CHUNKS)
        return result

    def _power_action(
        self, root: int, steps: int, phase: int
    ) -> DoubleReversePortAction:
        """Return one memoized dyadic action with authenticated endpoint roots."""
        if (
            type(phase) is not int
            or phase not in (0, 1, 2, 3)
            or type(steps) is not int
            or steps < 1
            or steps > self.max_steps
            or steps & (steps - 1)
        ):
            raise ValueError("temporal port action requires a power of two")
        key = (root, steps, phase)
        issued = self._actions.get(key)
        if issued is not None:
            if type(issued) is not IssuedDoubleReversePortAction:
                raise ValueError("temporal action memo payload is malformed")
            cached = issued.action
            self._validate_issued_action(cached, issued)
            if cached.source != self._handle(root) or cached.phase_in != phase:
                raise ValueError("cached 2rev10 action belongs to another source")
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_PORT_ACTION_CACHE_HITS
            )
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWERED_T2_STEPS, steps
            )
            self.ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWER_CHUNKS)
            return cached
        if self.certify(root) != phase:
            raise ValueError("uncertified source for temporal port action")
        result = self._power_of_two(root, steps, phase)
        left, right = growth_ports(phase, steps)
        action = DoubleReversePortAction(
            self._handle(root),
            self._handle(result),
            steps,
            phase,
            (phase + 2 * steps) % 4,
            left,
            right,
        )
        self._issue_action(key, action)
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_PORT_ACTION_PUBLICATIONS
        )
        return action

    def advance_action(
        self, root: int, steps: int, phase: int
    ) -> DoubleReversePortAction:
        """Compose exact source-root actions over the binary expansion of time."""
        if (
            type(phase) is not int
            or phase not in (0, 1, 2, 3)
            or type(steps) is not int
            or steps < 1
            or steps > self.max_steps
            or self.certify(root) != phase
        ):
            raise ValueError("uncertified 2rev10 source cylinder")
        key = (root, steps, phase)
        issued = self._actions.get(key)
        if issued is not None:
            if type(issued) is not IssuedDoubleReversePortAction:
                raise ValueError("temporal action memo payload is malformed")
            cached = issued.action
            self._validate_issued_action(cached, issued)
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_PORT_ACTION_CACHE_HITS
            )
            self.ledger.bump(
                _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWERED_T2_STEPS, steps
            )
            self.ledger.bump(_double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWER_CHUNKS)
            return cached
        combined = DoubleReversePortAction(
            self._handle(root), self._handle(root), 0, phase, phase, 0, 0
        )
        for bit in range(steps.bit_length() - 1, -1, -1):
            power = 1 << bit
            if steps & power:
                next_action = self._power_action(
                    self._root(combined.target), power, combined.phase_out
                )
                combined = combined.then(next_action)
        if combined.steps != steps:
            raise AssertionError("powered action does not represent requested span")
        existing = self._actions.get(key)
        if existing is not None:
            if type(existing) is not IssuedDoubleReversePortAction:
                raise ValueError("temporal action memo payload is malformed")
            self._validate_issued_action(existing.action, existing)
            if existing.action != combined:
                raise AssertionError(
                    "cached powered action differs from its composition"
                )
            return existing.action
        self._issue_action(key, combined)
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_TEMPORAL_PORT_ACTION_PUBLICATIONS
        )
        return combined

    def advance(self, root: int, steps: int, phase: int) -> int:
        """Return only the endpoint grammar from the complete action."""
        return self._root(self.advance_action(root, steps, phase).target)

    def _pointed_source_window(self, root: int, origin: int, radius: int) -> int:
        """Build the exact zero-extended causal interval around one source cell."""
        width = self.arena.nodes[root].length
        length = 2 * radius + 1
        begin = origin - radius
        end = begin + length
        left_zeros = min(length, max(0, -begin))
        right_zeros = min(length - left_zeros, max(0, end - width))
        middle = length - left_zeros - right_zeros
        with self.ledger.reservation(self.scratch_owner, entries=8, nodes=8):
            fragments: list[int] = []
            zero = self.arena.terminal(0)
            if left_zeros:
                fragments.append(self.arena.repeat(zero, left_zeros))
            if middle:
                first = max(0, begin)
                fragments.append(self.part(root, first, first + middle))
            if right_zeros:
                fragments.append(self.arena.repeat(zero, right_zeros))
            window = self.arena.concat_many(fragments)
        if self.arena.nodes[window].length != length:
            raise AssertionError("pointed stencil window omitted its causal halo")
        return window

    def _advance_pointed_window(self, window: int, steps: int) -> int:
        """Apply one dyadic F chunk and retain only its exact future cone."""
        width = self.arena.nodes[window].length
        if steps < 1 or steps & (steps - 1) or width <= 2 * steps:
            raise ValueError("pointed stencil needs a complete dyadic causal halo")
        output_width = width - 2 * steps
        span = 2 * steps
        count = (output_width + span - 1) // span
        if count > 32:
            raise ValueError("pointed temporal interval exceeds 32 causal tiles")
        reservations = 8 + 4 * max(0, count - 2)
        with self.ledger.reservation(
            self.scratch_owner, entries=reservations, nodes=reservations
        ):
            zero_pad = self.arena.repeat(self.arena.terminal(0), 2 * steps)
            padded = self.arena.concat(window, zero_pad)
            tile_roots: list[int] = []
            for tile_index in range(count):
                block = self.part(
                    padded, tile_index * span, tile_index * span + 4 * steps
                )
                tile_roots.append(self._cone_step(block, steps))
                self.ledger.bump(
                    _double_reverse_keys.DOUBLE_REVERSE_POINTED_STENCIL_TILES
                )
            joined = self.arena.concat_many(tile_roots)
            result = self.part(joined, 0, output_width)
        if self.arena.nodes[result].length != output_width:
            raise AssertionError("pointed stencil lost requested coordinates")
        return result

    def _pointed_causal_window(
        self, root: int, steps: int, phase: int, msd_start: int, count: int
    ) -> tuple[int, ...]:
        """Share one complete source cone across a bounded output interval."""
        left, right = growth_ports(phase, steps)
        width = self.arena.nodes[root].length + left + right
        if msd_start < 0 or msd_start + count > width:
            raise IndexError("pointed temporal row outside the normalized output")
        if steps == 0:
            values = tuple(
                symbol_at(self.arena, root, msd_start + i) for i in range(count)
            )
        else:
            # The centered input cone for an even row contains one surplus
            # cell on its left. Crop that cell after the causal evolution.
            left_padding = int(count % 2 == 0)
            center = msd_start - left + (count - 1) // 2
            radius = steps + count // 2
            window = self._pointed_source_window(root, center, radius)
            for bit in range(steps.bit_length() - 1, -1, -1):
                chunk = 1 << bit
                if steps & chunk:
                    window = self._advance_pointed_window(window, chunk)
                    self.ledger.bump(
                        _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWERED_T2_STEPS,
                        chunk,
                    )
                    self.ledger.bump(
                        _double_reverse_keys.DOUBLE_REVERSE_HASHLIFE_POWER_CHUNKS
                    )
            if self.arena.nodes[window].length != count + left_padding:
                raise AssertionError("pointed causal cone lost its complete row")
            values = tuple(
                symbol_at(self.arena, window, left_padding + i) for i in range(count)
            )
        self.ledger.bump(
            _double_reverse_keys.DOUBLE_REVERSE_POINTED_STENCIL_PUBLICATIONS,
            count,
        )
        return values

    def pointed_window(
        self, root: int, steps: int, phase: int, msd_start: int, count: int
    ) -> tuple[int, ...]:
        """Read a short exact row through one shared source-root causal cone."""
        if (
            type(root) is not int
            or not 0 <= root < len(self.arena.nodes)
            or type(steps) is not int
            or not 0 <= steps <= self.max_steps // 2
            or type(phase) is not int
            or phase not in (0, 1, 2, 3)
            or type(msd_start) is not int
            or type(count) is not int
            or not 1 <= count <= 18
            or self.certify(root) != phase
        ):
            raise ValueError("pointed temporal row needs a certified bounded source")
        return self._pointed_causal_window(root, steps, phase, msd_start, count)

    def pointed_stencil(
        self, root: int, steps: int, phase: int, msd_index: int
    ) -> PointedDigitStencil:
        """Return one exact output cell without producing its full endpoint."""
        if (
            type(root) is not int
            or not 0 <= root < len(self.arena.nodes)
            or type(steps) is not int
            or not 1 <= steps <= self.max_steps // 2
            or type(phase) is not int
            or phase not in (0, 1, 2, 3)
            or type(msd_index) is not int
            or self.certify(root) != phase
        ):
            raise ValueError("pointed stencil requires a certified source cylinder")
        digit = self._pointed_causal_window(root, steps, phase, msd_index, 1)[0]
        width = self.arena.nodes[root].length + sum(growth_ports(phase, steps))
        return PointedDigitStencil(
            self._handle(root),
            steps,
            phase,
            (phase + 2 * steps) % 4,
            width,
            msd_index,
            digit,
            int(digit >= 5),
            digit % 5,
            DIGIT_STENCIL_MOORE["joint"].classes[digit],
        )


__all__ = [
    "DoubleReversePortAction",
    "DoubleReverseSLPID",
    "DoubleReverseTemporalHashlife",
    "PointedDigitStencil",
    "UncertifiedPointedStencilError",
    "edge_phase",
    "growth_ports",
    "two_step_cell",
]
