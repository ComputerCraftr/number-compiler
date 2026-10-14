"""Source guarded Hashlife actions for the decimal ``2 * reverse`` map.

One cellular step is the exact two generation map ``F = T²``.  Only words
whose complete two digit borders satisfy the checked four phase cylinder are
powered here.  The engine returns source bound actions over the existing SLP
arena; it neither expands decimal words nor chooses a successor from a border
clock alone.
"""

from __future__ import annotations

from collections.abc import Iterator
from dataclasses import dataclass
from typing import TypeVar, cast

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.automata.slp_walks import symbol_at
from number_compiler.arithmetic.contracts.scoped_handles import ArenaHandle, ArenaToken
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
    PayloadAuditStoreBinding,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_slp import (
    _existing_concat,
    _existing_part,
    _existing_symbol_at,
)

_Key = TypeVar("_Key")
_Value = TypeVar("_Value")


def two_step_cell(left: int, digit: int, right: int) -> int:
    """Exact local carry law for two physical reverse/double transitions."""
    first_carry = int(left >= 5)
    second_carry = int((2 * right + int(digit >= 5)) % 10 >= 5)
    return (4 * digit + 2 * first_carry + second_carry) % 10


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


@dataclass(frozen=True, slots=True)
class DoubleReverseSLPID(ArenaHandle):
    """Typed root handle for one double-reverse SLP arena generation."""

    def __post_init__(self) -> None:
        ArenaHandle.__post_init__(self)
        if self.kind != "double_reverse_slp":
            raise ValueError("invalid double-reverse SLP handle kind")


@dataclass(frozen=True, slots=True)
class DoubleReversePortAction:
    """A powered output grammar and its exact source and boundary seams."""

    source: DoubleReverseSLPID
    target: DoubleReverseSLPID
    steps: int
    phase_in: int
    phase_out: int
    left_births: int
    right_births: int

    def then(self, other: DoubleReversePortAction) -> DoubleReversePortAction:
        """Compose only actions whose exact output root feeds the next input."""
        if type(other) is not DoubleReversePortAction:
            raise TypeError("temporal composition requires a guarded port action")
        if self.target != other.source:
            raise ValueError("temporal action source-root seam mismatch")
        if self.phase_out != other.phase_in:
            raise ValueError("temporal action border-phase seam mismatch")
        return DoubleReversePortAction(
            self.source,
            other.target,
            self.steps + other.steps,
            self.phase_in,
            other.phase_out,
            self.left_births + other.left_births,
            self.right_births + other.right_births,
        )


def temporal_action_node_cost(key: object, action: object) -> int:
    """Charge exact integer limbs for the retained action and its scoped key."""
    if type(key) is not tuple or len(key) != 3:
        raise ValueError("malformed temporal action memo entry")
    coordinates = cast(tuple[object, ...], key)
    if any(type(value) is not int or value < 0 for value in coordinates):
        raise ValueError("malformed temporal action memo key")
    exact_coordinates = cast(tuple[int, int, int], coordinates)
    if type(action) is not DoubleReversePortAction:
        raise ValueError("malformed temporal action memo payload")
    exact_action = action
    integers = (
        *exact_coordinates,
        exact_action.source.local_id,
        exact_action.target.local_id,
        exact_action.steps,
        exact_action.phase_in,
        exact_action.phase_out,
        exact_action.left_births,
        exact_action.right_births,
    )
    if any(type(value) is not int or value < 0 for value in integers):
        raise ValueError("malformed temporal action coordinates")
    return 8 + sum(max(1, (value.bit_length() + 63) // 64) for value in integers)


def _memo_account_is_exact(
    ledger: ResourceLedger,
    memo: OwnedMemo[_Key, _Value],
    owner: int,
    container: object,
    *,
    role: str,
) -> bool:
    account = ledger._account(owner)
    return (
        memo.ledger is ledger
        and memo.owner == owner
        and memo._data is container
        and account.container is container
        and account.role == role
        and not account.disposed
        and memo.nodes_per_entry == 1
        and memo.node_cost is None
        and memo._dynamic_nodes == 0
        and account.entries == len(memo)
        and account.nodes == len(memo)
    )


def _audit_temporal_slice_store(
    root: DoubleReverseTemporalHashlife,
) -> tuple[list[PayloadAuditEntry], list[PayloadAuditEntry]]:
    memo = root._slices
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    container = root._audit_slices
    if not _memo_account_is_exact(
        root.ledger, memo, memo.owner, container, role="double_reverse_temporal_memo"
    ):
        raise ValueError("2rev10 temporal slice owner is invalid")
    for key, value in memo.items():
        valid = (
            type(key) is tuple
            and len(key) == 3
            and all(type(item) is int for item in key)
            and type(value) is int
        )
        if valid:
            source, begin, end = key
            valid = (
                0 <= source < len(root.arena.nodes)
                and 0 <= begin < end <= root.arena.nodes[source].length
                and not (begin == 0 and end == root.arena.nodes[source].length)
                and 0 <= value < len(root.arena.nodes)
            )
            if valid:
                expected = _existing_part(root.arena, source, begin, end)
                valid = (
                    expected == value and root.arena.nodes[value].length == end - begin
                )
        destination = approved if valid else invalid
        destination.extend(
            (
                PayloadAuditEntry(memo.owner, key),
                PayloadAuditEntry(memo.owner, value),
            )
        )
    return approved, invalid


def _audit_temporal_cone_store(
    root: DoubleReverseTemporalHashlife,
) -> tuple[list[PayloadAuditEntry], list[PayloadAuditEntry]]:
    memo = root._cone
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    if not _memo_account_is_exact(
        root.ledger,
        memo,
        memo.owner,
        root._audit_cones,
        role="double_reverse_temporal_memo",
    ):
        raise ValueError("2rev10 temporal cone owner is invalid")

    rows = list(memo.items())
    rows.sort(
        key=lambda row: (
            row[0][1]
            if type(row[0]) is tuple and len(row[0]) == 2 and type(row[0][1]) is int
            else -1,
            row[0][0]
            if type(row[0]) is tuple and len(row[0]) == 2 and type(row[0][0]) is int
            else -1,
        )
    )
    verified: dict[tuple[int, int], int] = {}
    for key, value in rows:
        valid = (
            type(key) is tuple
            and len(key) == 2
            and all(type(item) is int for item in key)
            and type(value) is int
        )
        if valid:
            block, steps = key
            valid = (
                0 <= block < len(root.arena.nodes)
                and type(steps) is int
                and steps > 0
                and steps <= root.max_steps
                and steps & (steps - 1) == 0
                and root.arena.nodes[block].length == 4 * steps
                and 0 <= value < len(root.arena.nodes)
                and root.arena.nodes[value].length == 2 * steps
            )
            if valid and steps == 1:
                read_digits = tuple(
                    _existing_symbol_at(
                        root.arena,
                        block,
                        index,
                        on_visit=root._payload_audit_boundary_visit,
                    )
                    for index in range(4)
                )
                valid = all(
                    type(digit) is int and 0 <= digit <= 9 for digit in read_digits
                )
                digits = cast(tuple[int, int, int, int], read_digits)
                left = (
                    root.arena._term.get(two_step_cell(digits[0], digits[1], digits[2]))
                    if valid
                    else None
                )
                right = (
                    root.arena._term.get(two_step_cell(digits[1], digits[2], digits[3]))
                    if valid
                    else None
                )
                expected = (
                    None
                    if left is None or right is None
                    else _existing_concat(root.arena, left, right)
                )
                valid = expected == value
            elif valid:
                half = steps // 2
                child_blocks = (
                    _existing_part(root.arena, block, 0, 2 * steps),
                    _existing_part(root.arena, block, steps, 3 * steps),
                    _existing_part(root.arena, block, 2 * steps, 4 * steps),
                )
                child_outputs: list[int] = []
                for child_block in child_blocks:
                    if child_block is None:
                        valid = False
                        break
                    child_key = (child_block, half)
                    child_output = verified.get(child_key)
                    if child_output is None:
                        valid = False
                        break
                    child_outputs.append(child_output)
                if valid:
                    left_middle = _existing_concat(
                        root.arena, child_outputs[0], child_outputs[1]
                    )
                    middle_right = _existing_concat(
                        root.arena, child_outputs[1], child_outputs[2]
                    )
                    if left_middle is None or middle_right is None:
                        valid = False
                    else:
                        left_result = verified.get((left_middle, half))
                        right_result = verified.get((middle_right, half))
                        expected = (
                            None
                            if left_result is None or right_result is None
                            else _existing_concat(root.arena, left_result, right_result)
                        )
                        valid = expected == value
        if valid:
            verified[key] = value
        destination = approved if valid else invalid
        destination.extend(
            (
                PayloadAuditEntry(memo.owner, key),
                PayloadAuditEntry(memo.owner, value),
            )
        )
    return approved, invalid


def audit_double_reverse_temporal_actions(
    ledger_value: object, root_value: object
) -> PayloadAuditContribution:
    """Validate action records and the exact dynamic accounting of their memo."""
    if type(ledger_value) is not ResourceLedger:
        raise TypeError("2rev10 temporal auditor received a foreign ledger")
    if type(root_value) is not DoubleReverseTemporalHashlife:
        raise TypeError("2rev10 temporal auditor received a foreign owner")
    ledger = ledger_value
    root = root_value
    memo = root._actions
    account = ledger._account(memo.owner)
    cost_nodes = 0
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []
    valid_owner = (
        root.ledger is ledger
        and memo.ledger is ledger
        and memo._data is root._audit_actions
        and account.container is root._audit_actions
        and account.role == "double_reverse_temporal_memo"
        and not account.disposed
        and memo.node_cost is temporal_action_node_cost
        and memo.nodes_per_entry == 0
        and memo._dynamic_nodes == account.nodes
        and account.entries == len(memo)
    )
    if not valid_owner:
        raise ValueError("2rev10 temporal action owner is invalid")

    for key, action in memo.items():
        valid = (
            type(key) is tuple
            and len(key) == 3
            and all(type(value) is int and value >= 0 for value in key)
            and type(action) is DoubleReversePortAction
            and key == (action.source.local_id, action.steps, action.phase_in)
        )
        if valid:
            try:
                root._validate_action(action, audit=True)
                cost_nodes += memo._entry_nodes(key, action)
            except (
                ArithmeticError,
                AttributeError,
                IndexError,
                KeyError,
                TypeError,
                ValueError,
            ):
                valid = False
        destination = approved if valid else invalid
        destination.extend(
            (
                PayloadAuditEntry(memo.owner, key),
                PayloadAuditEntry(memo.owner, action),
            )
        )
    if cost_nodes != account.nodes:
        raise ValueError("2rev10 temporal action accounting is inconsistent")
    slice_approved, slice_invalid = _audit_temporal_slice_store(root)
    cone_approved, cone_invalid = _audit_temporal_cone_store(root)
    approved.extend(slice_approved)
    approved.extend(cone_approved)
    invalid.extend(slice_invalid)
    invalid.extend(cone_invalid)
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


class DoubleReverseTemporalHashlife:
    """Ledger memoized dyadic cones and source aligned temporal actions."""

    __slots__ = (
        "__weakref__",
        "_actions",
        "_audit_actions",
        "_audit_cones",
        "_audit_slices",
        "_cone",
        "_slices",
        "arena",
        "issuer",
        "ledger",
        "max_steps",
        "scratch_owner",
    )

    def __init__(
        self,
        arena: LedgerSLPArena,
        ledger: ResourceLedger,
        issuer: ArenaToken,
        scratch_owner: int,
        cone_memo: OwnedMemo[tuple[int, int], int],
        slice_memo: OwnedMemo[tuple[int, int, int], int],
        action_memo: OwnedMemo[tuple[int, int, int], DoubleReversePortAction],
        max_steps: int,
    ) -> None:
        self.arena = arena
        self.ledger = ledger
        self.issuer = issuer
        self.scratch_owner = scratch_owner
        self.max_steps = max_steps
        self._cone = cone_memo
        self._slices = slice_memo
        self._actions = action_memo
        self._audit_actions = action_memo._data
        self._audit_cones = cone_memo._data
        self._audit_slices = slice_memo._data
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
            ),
            audit_double_reverse_temporal_actions,
        )

    def dispose_audit_contract(self) -> None:
        """Retire issuer validation before the associated action memo closes."""
        self.ledger.remove_payload_audit_contract(self, "double_reverse")

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
        # Shape checks alone are not authority: a forged action can preserve
        # both border pairs and width while naming an incorrect interior.
        # Only the exact frozen object published by this owner is admissible.
        if self._actions.get(key) is not action:
            raise ValueError("temporal action was not published by this owner")
        self._validate_action_shape(action, audit=audit)

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

    def _certify(self, root: int, *, audit: bool) -> int | None:
        """Classify a cylinder while isolating explicit audit counters."""
        if type(root) is not int or not 0 <= root < len(self.arena.nodes):
            raise ValueError("invalid double-reverse SLP root")
        if audit:
            self.ledger.bump("double_reverse_payload_audit_boundary_classifications")
            on_visit = self._payload_audit_boundary_visit
        else:
            self.ledger.bump("double_reverse_boundary_classifications")
            on_visit = self._boundary_visit
        width = self.arena.nodes[root].length
        if width < 5:
            return None
        if audit:
            upper_left = _existing_symbol_at(
                self.arena, root, 0, on_visit=self._payload_audit_boundary_visit
            )
            upper_right = _existing_symbol_at(
                self.arena, root, 1, on_visit=self._payload_audit_boundary_visit
            )
            lower_left = _existing_symbol_at(
                self.arena,
                root,
                width - 2,
                on_visit=self._payload_audit_boundary_visit,
            )
            lower_right = _existing_symbol_at(
                self.arena,
                root,
                width - 1,
                on_visit=self._payload_audit_boundary_visit,
            )
            if any(
                digit is None
                for digit in (upper_left, upper_right, lower_left, lower_right)
            ):
                return None
            return edge_phase(
                (cast(int, upper_left), cast(int, upper_right)),
                (cast(int, lower_left), cast(int, lower_right)),
            )
        upper = (
            symbol_at(self.arena, root, 0, on_visit=on_visit),
            symbol_at(self.arena, root, 1, on_visit=on_visit),
        )
        lower = (
            symbol_at(self.arena, root, width - 2, on_visit=on_visit),
            symbol_at(self.arena, root, width - 1, on_visit=on_visit),
        )
        return edge_phase(upper, lower)

    def _boundary_visit(self) -> None:
        """Count each SLP node read while classifying a cylinder boundary."""
        self.ledger.bump("double_reverse_boundary_node_visits")

    def _payload_audit_boundary_visit(self) -> None:
        """Separate explicit audit traversal from production execution work."""
        self.ledger.bump("double_reverse_payload_audit_boundary_visits")

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
                        self.ledger.bump("double_reverse_hashlife_cone_hits")
                        continue
                    self.ledger.bump("double_reverse_hashlife_cones")
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
                self.ledger.bump("double_reverse_hashlife_tile_selections")
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
        self.ledger.bump("double_reverse_hashlife_powered_t2_steps", steps)
        self.ledger.bump("double_reverse_hashlife_power_chunks")
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
        cached = self._actions.get(key)
        if cached is not None:
            self._validate_action(cached)
            if cached.source != self._handle(root) or cached.phase_in != phase:
                raise ValueError("cached 2rev10 action belongs to another source")
            self.ledger.bump("double_reverse_temporal_port_action_cache_hits")
            self.ledger.bump("double_reverse_hashlife_powered_t2_steps", steps)
            self.ledger.bump("double_reverse_hashlife_power_chunks")
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
        self._actions[key] = action
        self._validate_action(action)
        self.ledger.bump("double_reverse_temporal_port_action_publications")
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
        cached = self._actions.get((root, steps, phase))
        if cached is not None:
            self._validate_action(cached)
            self.ledger.bump("double_reverse_temporal_port_action_cache_hits")
            self.ledger.bump("double_reverse_hashlife_powered_t2_steps", steps)
            self.ledger.bump("double_reverse_hashlife_power_chunks")
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
        self._validate_action_shape(combined)
        if combined.steps != steps:
            raise AssertionError("powered action does not represent requested span")
        action_was_published = self._actions.get((root, steps, phase)) is not None
        self._actions[(root, steps, phase)] = combined
        self._validate_action(combined)
        if not action_was_published:
            self.ledger.bump("double_reverse_temporal_port_action_publications")
        return combined

    def advance(self, root: int, steps: int, phase: int) -> int:
        """Return only the endpoint grammar from the complete action."""
        return self._root(self.advance_action(root, steps, phase).target)
