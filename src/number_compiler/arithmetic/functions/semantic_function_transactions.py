"""Transient reduced-function construction and atomic publication."""

from __future__ import annotations

from collections.abc import Callable
from typing import TYPE_CHECKING, Self, TypeVar

from number_compiler.arithmetic.contracts.iterative_queries import split_choice
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
    SemanticNode,
    SemanticRequest,
    SemanticTerminal,
    base_port_variable,
    union_inputs,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.resources.metric_keys import (
    arithmetic_functions as _functions_keys,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.semantic_functions import (
        SemanticFunctionArena,
    )

_K = TypeVar("_K")
_V = TypeVar("_V")


class _Transaction:
    """Transient reductions; publish only nodes reachable from the final root."""

    def __init__(
        self, arena: SemanticFunctionArena, request: SemanticRequest | None = None
    ) -> None:
        self.arena = arena
        self.request = request
        self.base = len(arena.nodes)
        self.staged: list[SemanticNode] = []
        self.keys: dict[SemanticNode, int] = {}
        self.choices: dict[tuple[int, int, int], int] = {}
        # Only canonical operands may escape this construction transaction.
        # Promotion is bounded; publication never retains an intermediate DAG
        # merely to populate this optional reduction memo.
        self.choice_requests: set[tuple[int, int, int]] = set()
        self.restricted: dict[tuple[int, PortVariable, int], int] = {}
        self._resigned: dict[tuple[int, FunctionSignature], int] = {}
        # Transient proof facts about canonical nodes. A total condition can
        # erase an identical branch without traversing that branch's DAG.
        self._total: dict[int, bool] = {}
        self._workspace_entries = 0
        self._workspace_nodes = 0
        self._staged_entries = 0
        self._staged_nodes = 0
        self._closed = False

    @property
    def is_open(self) -> bool:
        """Whether the transaction still owns its construction workspace."""
        return not self._closed

    def __enter__(self) -> Self:
        if self._closed:
            raise RuntimeError("closed semantic construction transaction")
        return self

    def __exit__(self, *_error: object) -> None:
        self.close()

    @property
    def workspace_charge(self) -> tuple[int, int, int]:
        return (
            self.arena.workspace_owner,
            self._workspace_entries,
            self._workspace_nodes,
        )

    @property
    def staged_charge(self) -> tuple[int, int]:
        return self._staged_entries, self._staged_nodes

    def reserve_workspace(self, *, entries: int = 0, nodes: int = 0) -> None:
        if self._closed:
            raise RuntimeError("closed semantic construction transaction")
        try:
            self.arena.ledger.reserve(
                self.arena.workspace_owner, entries=entries, nodes=nodes
            )
        except BaseException:
            self.close()
            raise
        self.arena.workspace.entries += entries
        self.arena.workspace.nodes += nodes
        self._workspace_entries += entries
        self._workspace_nodes += nodes
        ledger = self.arena.ledger
        ledger.bump(
            _functions_keys.SEMANTIC_FUNCTION_WORKSPACE_ALLOCATED_ENTRIES,
            entries,
        )
        ledger.bump(
            _functions_keys.SEMANTIC_FUNCTION_WORKSPACE_ALLOCATED_NODES,
            nodes,
        )
        for name, value in (
            ("entries", self._workspace_entries),
            ("nodes", self._workspace_nodes),
        ):
            counter = "semantic_function_workspace_peak_" + name
            ledger.bump(counter, max(0, value - ledger.counters.get(counter, 0)))

    def reserve_staged(self, *, entries: int, nodes: int) -> None:
        """Charge construction objects which may become canonical on publication."""
        self.reserve_workspace(entries=entries, nodes=nodes)
        self._staged_entries += entries
        self._staged_nodes += nodes

    def remember(self, mapping: dict[_K, _V], key: _K, value: _V) -> None:
        """Charge a transaction-lifetime memo entry before retaining it."""
        if key not in mapping:
            self.reserve_workspace(entries=1)
        mapping[key] = value

    def remember_choice_request(self, key: tuple[int, int, int]) -> None:
        """Charge an optional canonical-reduction request before retaining it."""
        if key not in self.choice_requests:
            self.reserve_workspace(entries=1)
            self.choice_requests.add(key)

    def release_workspace(self, *, entries: int = 0, nodes: int = 0) -> None:
        if entries > self._workspace_entries or nodes > self._workspace_nodes:
            raise ValueError("semantic workspace release exceeds its transaction")
        self.arena.ledger.release(
            self.arena.workspace_owner, entries=entries, nodes=nodes
        )
        self.arena.workspace.entries -= entries
        self.arena.workspace.nodes -= nodes
        self._workspace_entries -= entries
        self._workspace_nodes -= nodes

    def reassign_staged(
        self,
        reservations: tuple[tuple[int, int, int], ...],
    ) -> None:
        """Atomically convert staged semantic nodes into retained ownership."""
        self.arena.ledger.reassign_many(
            (
                (
                    self.arena.workspace_owner,
                    self._staged_entries,
                    self._staged_nodes,
                ),
            ),
            reservations,
        )
        self.arena.workspace.entries -= self._staged_entries
        self.arena.workspace.nodes -= self._staged_nodes
        self._workspace_entries -= self._staged_entries
        self._workspace_nodes -= self._staged_nodes
        self._staged_entries = self._staged_nodes = 0

    def restore_staged(self, *, entries: int, nodes: int) -> None:
        """Restore local ownership after a failed pre-publication conversion."""
        if self._closed:
            raise RuntimeError("closed semantic construction transaction")
        self.arena.workspace.entries += entries
        self.arena.workspace.nodes += nodes
        self._workspace_entries += entries
        self._workspace_nodes += nodes
        self._staged_entries += entries
        self._staged_nodes += nodes

    def close(self) -> None:
        if self._closed:
            return
        if self._workspace_entries or self._workspace_nodes:
            self.arena.ledger.release(
                self.arena.workspace_owner,
                entries=self._workspace_entries,
                nodes=self._workspace_nodes,
            )
            self.arena.workspace.entries -= self._workspace_entries
            self.arena.workspace.nodes -= self._workspace_nodes
        self._workspace_entries = self._workspace_nodes = 0
        self._staged_entries = self._staged_nodes = 0
        self.staged.clear()
        self.keys.clear()
        self.choices.clear()
        self.choice_requests.clear()
        self.restricted.clear()
        self._resigned.clear()
        self._total.clear()
        self._closed = True

    def node(self, identity: int) -> SemanticNode:
        if type(identity) is not int or identity < 0:
            raise ValueError("semantic construction identity requires an integer")
        if self._closed:
            raise RuntimeError("closed semantic construction transaction")
        return (
            self.arena.nodes[identity]
            if identity < self.base
            else self.staged[identity - self.base]
        )

    def intern(self, node: SemanticNode) -> int:
        if self._closed:
            raise RuntimeError("closed semantic construction transaction")
        found = self.arena.keys.get(node)
        if found is None:
            found = self.keys.get(node)
        if found is not None:
            self.arena.ledger.bump(_functions_keys.SEMANTIC_FUNCTION_INTERN_HITS)
            return found
        result = self.base + len(self.staged)
        try:
            self.reserve_staged(entries=2, nodes=1)
        except BaseException:
            self.close()
            raise
        try:
            self.staged.append(node)
            self.keys[node] = result
        except BaseException:
            if len(self.staged) > result - self.base:
                self.staged.pop()
            self.keys.pop(node, None)
            self.release_workspace(entries=2, nodes=1)
            self._staged_entries -= 2
            self._staged_nodes -= 1
            raise
        if node.terminal is not None:
            self.remember(self._total, result, node.terminal.kind != "invalid")
        elif node.low in self._total and node.high in self._total:
            self.remember(
                self._total,
                result,
                self._total[node.low] and self._total[node.high],
            )
        self.arena.ledger.bump(_functions_keys.SEMANTIC_FUNCTION_STAGED_NODES)
        return result

    def _total_condition(self, root: int) -> bool:
        """Prove definedness on every encoded assignment, including padding.

        This deliberately proves more than admissible-input totality: erasing
        an undefined condition would otherwise change partial ITE semantics.
        """
        if root in self._total:
            self.arena.ledger.bump(_functions_keys.SEMANTIC_TOTAL_CONDITION_HITS)
            return self._total[root]
        pending = [(root, False)]
        while pending:
            identity, ready = pending.pop()
            self.arena.ledger.bump(_functions_keys.SEMANTIC_TOTAL_CONDITION_FRAMES)
            if identity in self._total:
                continue
            node = self.node(identity)
            if node.terminal is not None:
                self.remember(self._total, identity, node.terminal.kind != "invalid")
            elif ready:
                self.remember(
                    self._total,
                    identity,
                    self._total[node.low] and self._total[node.high],
                )
            else:
                pending.extend(
                    ((identity, True), (node.high, False), (node.low, False))
                )
            self.arena.ledger.bump(
                _functions_keys.SEMANTIC_TOTAL_CONDITION_WORKSPACE_PEAK,
                max(
                    0,
                    len(pending)
                    + len(self._total)
                    - self.arena.ledger.counters.get(
                        _functions_keys.SEMANTIC_TOTAL_CONDITION_WORKSPACE_PEAK,
                        0,
                    ),
                ),
            )
        return self._total[root]

    def terminal(self, signature: FunctionSignature, value: SemanticTerminal) -> int:
        return self.intern(SemanticNode(signature, terminal=value))

    def decision(
        self, signature: FunctionSignature, variable: PortVariable, low: int, high: int
    ) -> int:
        self.arena.ledger.bump(_functions_keys.SEMANTIC_DECISION_REQUESTS)
        if low == high:
            return low
        a, b = self.node(low), self.node(high)
        if (
            a.signature is not signature
            and a.signature != signature
            or b.signature is not signature
            and b.signature != signature
        ):
            raise AssertionError("decision child signatures differ")
        # Children already have ordered canonical descendants. Their first
        # variable suffices for construction admission; the independent audit
        # still checks the complete support inventories.
        if (
            a.variable is not None
            and a.variable <= variable
            or b.variable is not None
            and b.variable <= variable
        ):
            raise AssertionError("decision ordering violation")
        key = SemanticNode(signature, variable, low, high)
        found = self.arena.keys.get(key)
        if found is None:
            found = self.keys.get(key)
        if found is not None:
            self.arena.ledger.bump(_functions_keys.SEMANTIC_DECISION_EARLY_HITS)
            return found
        support = self._decision_support(variable, a.support, b.support)
        return self.intern(
            SemanticNode(signature, variable, low, high, support=support)
        )

    def _decision_support(
        self,
        variable: PortVariable,
        left: tuple[PortVariable, ...],
        right: tuple[PortVariable, ...],
    ) -> tuple[PortVariable, ...]:
        self.arena.ledger.bump(_functions_keys.SEMANTIC_DECISION_SUPPORT_BUILDS)
        self.arena.ledger.bump(
            _functions_keys.SEMANTIC_DECISION_SUPPORT_INPUT_REFERENCES,
            len(left) + len(right),
        )
        if not left or left == right:
            return (variable, *right)
        if not right:
            return (variable, *left)
        return (variable, *sorted(set(left + right)))

    def rebuilt_decision(
        self, signature: FunctionSignature, variable: PortVariable, low: int, high: int
    ) -> int:
        """Preserve an ordered split without replaying a generic substitution.

        Replacements may move a child variable ahead of this split. Only that
        case needs Shannon reordering; an unchanged ordered graph can be
        hash-consed directly, including identical-branch elimination.
        """
        left, right = self.node(low), self.node(high)
        if (
            (left.signature is signature or left.signature == signature)
            and (right.signature is signature or right.signature == signature)
            and (left.variable is None or variable < left.variable)
            and (right.variable is None or variable < right.variable)
        ):
            self.arena.ledger.bump(_functions_keys.SEMANTIC_DIRECT_DECISION_REBUILDS)
            return self.decision(signature, variable, low, high)
        self.arena.ledger.bump(_functions_keys.SEMANTIC_REORDERED_DECISION_REBUILDS)
        return self.choose(self.bit(signature.inputs, variable), high, low)

    def choose(self, condition: int, yes: int, no: int) -> int:
        root = condition, yes, no
        if root in self.choices:
            self.arena.ledger.bump(_functions_keys.SEMANTIC_ITE_TRANSACTION_HITS)
            return self.choices[root]
        if self.arena.cache_construction_reductions and all(
            0 <= identity < self.base for identity in root
        ):
            request = SemanticRequest(
                "construction-ite",
                tuple(
                    self.arena.candidate_handle(
                        identity, base=self.base, candidate_count=0
                    )
                    for identity in root
                ),
            )
            self.arena.ledger.bump(_functions_keys.SEMANTIC_ITE_CANONICAL_REQUESTS)
            cached = self.arena.memo.get(request)
            if cached is not None:
                self.arena.resolve(cached)
                self.remember(self.choices, root, cached.local_id)
                self.arena.ledger.bump(
                    _functions_keys.SEMANTIC_ITE_CANONICAL_EARLY_HITS
                )
                return cached.local_id
            if len(self.choice_requests) < 256:
                self.remember_choice_request(root)
        pending = [(root, False)]
        children: dict[
            tuple[int, int, int],
            tuple[PortVariable, tuple[int, int, int], tuple[int, int, int]],
        ] = {}
        while pending:
            key, ready = pending.pop()
            if key in self.choices:
                continue
            c, a, b = (self.node(item) for item in key)
            self.arena.ledger.bump(_functions_keys.SEMANTIC_FUNCTION_ITE_FRAMES)
            if c.terminal is not None:
                self.remember(
                    self.choices,
                    key,
                    self.terminal(a.signature, SemanticTerminal("invalid"))
                    if c.terminal.kind == "invalid"
                    else key[1]
                    if c.terminal.value
                    else key[2],
                )
            elif key[1] == key[2] and self._total_condition(key[0]):
                self.remember(self.choices, key, key[1])
                self.arena.ledger.bump(
                    _functions_keys.SEMANTIC_IDENTICAL_BRANCH_REDUCTIONS
                )
            elif (
                c.signature == a.signature == b.signature
                and c.signature.output == BOOL
                and (
                    (
                        (
                            key[0] == key[1]
                            or a.terminal is not None
                            and a.terminal.kind == "atom"
                            and a.terminal.value == 1
                        )
                        and b.terminal is not None
                        and b.terminal.kind == "atom"
                        and b.terminal.value == 0
                    )
                    or (
                        a.terminal is not None
                        and a.terminal.kind == "atom"
                        and a.terminal.value == 1
                        and key[0] == key[2]
                    )
                )
            ):
                # ITE(c,1,0), ITE(c,c,0), ITE(c,1,c) are c even when
                # c is undefined. This preserves partial-function semantics.
                self.remember(self.choices, key, key[0])
                self.arena.ledger.bump(
                    _functions_keys.SEMANTIC_BOOLEAN_IDENTITY_REDUCTIONS
                )
            elif ready:
                variable, low, high = children[key]
                self.remember(
                    self.choices,
                    key,
                    self.decision(
                        a.signature, variable, self.choices[low], self.choices[high]
                    ),
                )
            else:
                variable = min(
                    v
                    for n in (c, a, b)
                    for v in (() if n.variable is None else (n.variable,))
                )
                low_key = tuple(
                    n.low if n.variable == variable else identity
                    for n, identity in zip((c, a, b), key, strict=True)
                )
                high_key = tuple(
                    n.high if n.variable == variable else identity
                    for n, identity in zip((c, a, b), key, strict=True)
                )
                split_choice(pending, children, key, variable, low_key, high_key)
        return self.choices[root]

    def map_terminals(
        self,
        root: int,
        signature: FunctionSignature,
        transform: Callable[[SemanticTerminal], int],
    ) -> int:
        pending = [(root, False)]
        done: dict[int, int] = {}
        while pending:
            current, ready = pending.pop()
            if current in done:
                continue
            node = self.node(current)
            self.arena.ledger.bump(_functions_keys.SEMANTIC_FUNCTION_REWRITE_FRAMES)
            if node.terminal is not None:
                done[current] = transform(node.terminal)
            elif ready:
                assert node.variable is not None
                done[current] = self.rebuilt_decision(
                    signature, node.variable, done[node.low], done[node.high]
                )
            else:
                pending.extend(((current, True), (node.high, False), (node.low, False)))
        return done[root]

    def resign(self, root: int, signature: FunctionSignature) -> int:
        ledger = self.arena.ledger
        ledger.bump(_functions_keys.SEMANTIC_FUNCTION_RESIGN_REQUESTS)
        if self.node(root).signature == signature:
            ledger.bump(_functions_keys.SEMANTIC_FUNCTION_RESIGN_IDENTITY_HITS)
            return root
        target = root, signature
        if target in self._resigned:
            ledger.bump(_functions_keys.SEMANTIC_FUNCTION_RESIGN_CACHE_HITS)
            return self._resigned[target]
        # One transaction imports several output bits and validity roots under
        # the same declaration. Share their complete child DAGs before walking
        # them again; these are construction references, not observations.
        ledger.bump(_functions_keys.SEMANTIC_FUNCTION_RESIGN_EVALUATIONS)
        pending = [(root, False)]
        while pending:
            ledger.bump(
                _functions_keys.SEMANTIC_FUNCTION_RESIGN_WORKSPACE_PEAK,
                max(
                    0,
                    len(pending)
                    + len(self._resigned)
                    - ledger.counters.get(
                        _functions_keys.SEMANTIC_FUNCTION_RESIGN_WORKSPACE_PEAK,
                        0,
                    ),
                ),
            )
            current, ready = pending.pop()
            key = current, signature
            if key in self._resigned:
                ledger.bump(_functions_keys.SEMANTIC_FUNCTION_RESIGN_SHARED_CHILD_HITS)
                continue
            node = self.node(current)
            ledger.bump(_functions_keys.SEMANTIC_FUNCTION_RESIGN_FRAMES)
            if node.signature == signature:
                self.remember(self._resigned, key, current)
            elif node.terminal is not None:
                self.remember(
                    self._resigned, key, self.terminal(signature, node.terminal)
                )
            elif ready:
                assert node.variable is not None
                self.remember(
                    self._resigned,
                    key,
                    self.rebuilt_decision(
                        signature,
                        node.variable,
                        self._resigned[node.low, signature],
                        self._resigned[node.high, signature],
                    ),
                )
            else:
                pending.extend(((current, True), (node.high, False), (node.low, False)))
        return self._resigned[target]

    def bit(self, inputs: tuple[FinitePort, ...], variable: PortVariable) -> int:
        signature = FunctionSignature(inputs, BOOL)
        return self.decision(
            signature,
            variable,
            self.terminal(signature, SemanticTerminal("atom", 0)),
            self.terminal(signature, SemanticTerminal("atom", 1)),
        )

    def admissible(self, root: int) -> int:
        signature = self.node(root).signature
        invalid = self.terminal(signature, SemanticTerminal("invalid"))
        result = root
        # Binary less-than a cardinality, using O(bits) comparator nodes.
        for port in reversed(signature.inputs):
            if port.cardinality == 1 << port.bits:
                continue
            condition_signature = FunctionSignature(signature.inputs, BOOL)
            condition = self.terminal(condition_signature, SemanticTerminal("atom", 0))
            one = self.terminal(condition_signature, SemanticTerminal("atom", 1))
            zero = self.terminal(condition_signature, SemanticTerminal("atom", 0))
            for bit in range(port.bits):
                variable = PortVariable(
                    port.variable.time, port.variable.side, port.variable.role, bit
                )
                test = self.bit(signature.inputs, variable)
                condition = self.choose(
                    test,
                    condition if (port.cardinality >> bit) & 1 else zero,
                    one if (port.cardinality >> bit) & 1 else condition,
                )
            result = self.choose(condition, result, invalid)
        return result

    def restrict(self, root: int, variable: PortVariable, value: int) -> int:
        target = root, variable, value
        pending = [(root, False)]
        while pending:
            current, ready = pending.pop()
            key = current, variable, value
            if key in self.restricted:
                continue
            node = self.node(current)
            if node.variable is None or node.variable > variable:
                self.remember(self.restricted, key, current)
            elif node.variable == variable:
                self.remember(self.restricted, key, node.high if value else node.low)
            elif ready:
                self.remember(
                    self.restricted,
                    key,
                    self.decision(
                        node.signature,
                        node.variable,
                        self.restricted[node.low, variable, value],
                        self.restricted[node.high, variable, value],
                    ),
                )
            else:
                pending.extend(((current, True), (node.high, False), (node.low, False)))
        return self.restricted[target]

    def zip_product(self, roots: tuple[int, ...], signature: FunctionSignature) -> int:
        pending = [(roots, False)]
        done: dict[tuple[int, ...], int] = {}
        children: dict[
            tuple[int, ...], tuple[PortVariable, tuple[int, ...], tuple[int, ...]]
        ] = {}
        while pending:
            key, ready = pending.pop()
            if key in done:
                continue
            nodes = tuple(self.node(item) for item in key)
            if all(node.terminal is not None for node in nodes):
                if any(
                    node.terminal is not None and node.terminal.kind == "invalid"
                    for node in nodes
                ):
                    terminal = SemanticTerminal("invalid")
                else:
                    components = tuple(
                        self.terminal(
                            FunctionSignature((), node.signature.output), node.terminal
                        )
                        for node in nodes
                        if node.terminal is not None
                    )
                    terminal = SemanticTerminal("product", references=components)
                done[key] = self.terminal(signature, terminal)
            elif ready:
                variable, low, high = children[key]
                done[key] = self.decision(signature, variable, done[low], done[high])
            else:
                variable = min(
                    node.variable for node in nodes if node.variable is not None
                )
                low = tuple(
                    node.low if node.variable == variable else identity
                    for node, identity in zip(nodes, key, strict=True)
                )
                high = tuple(
                    node.high if node.variable == variable else identity
                    for node, identity in zip(nodes, key, strict=True)
                )
                children[key] = variable, low, high
                pending.extend(((key, True), (high, False), (low, False)))
        return done[roots]

    def substitution(
        self, root: int, replacements: tuple[tuple[FinitePort, int], ...]
    ) -> int:
        original = self.node(root).signature
        removed = {port.variable for port, _ in replacements}
        inputs = union_inputs(
            tuple(port for port in original.inputs if port.variable not in removed),
            *(self.node(item).signature.inputs for _, item in replacements),
        )
        signature = FunctionSignature(inputs, original.output)
        replacement_by_name = {port.variable: item for port, item in replacements}
        bits: dict[PortVariable, int] = {}
        pending = [(root, False)]
        done: dict[int, int] = {}
        while pending:
            current, ready = pending.pop()
            if current in done:
                continue
            node = self.node(current)
            if node.terminal is not None:
                done[current] = self.terminal(signature, node.terminal)
            elif ready:
                variable = node.variable
                assert variable is not None
                condition = bits.get(variable)
                if condition is None:
                    replacement = replacement_by_name.get(base_port_variable(variable))
                    if replacement is None:
                        condition = self.bit(inputs, variable)
                    else:

                        def extract(
                            terminal: SemanticTerminal, bit: int = variable.bit
                        ) -> int:
                            value = (
                                terminal
                                if terminal.kind == "invalid"
                                else SemanticTerminal(
                                    "atom", (terminal.value >> bit) & 1
                                )
                            )
                            return self.terminal(FunctionSignature(inputs, BOOL), value)

                        condition = self.map_terminals(
                            replacement, FunctionSignature(inputs, BOOL), extract
                        )
                    bits[variable] = condition
                done[current] = self.choose(condition, done[node.high], done[node.low])
            else:
                pending.extend(((current, True), (node.high, False), (node.low, False)))
        return done[root]

    def finish(self, root: int) -> SemanticFunctionID:
        from number_compiler.hashlife.interfaces.semantic_publication import (
            prepare_functions,
        )

        prepared = None
        try:
            prepared = prepare_functions(self, (root,))
            prepared.reserve_with(
                ((self.arena.memo_owner, int(self.request is not None), 0),)
            )
            prepared.publish_reserved()
            result = prepared.roots[0]
            if self.request is not None:
                self.arena.memo[self.request] = result
            return result
        finally:
            if prepared is None:
                self.close()
            else:
                prepared.cancel()


__all__ = ["_Transaction"]
