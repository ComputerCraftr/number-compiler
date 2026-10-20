"""Reduced ordered Boolean port functions, with factored multi-port cuts.

Variables are ordered by time, side, role, and bit.  Spatial transfer functions
can share these canonical decision nodes without enumerating the product of
all cut states.  This algebra supplies no arithmetic successor-closure proof.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING, cast

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.iterative_queries import split_choice
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import (
    arithmetic_functions as _functions_keys,
)
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.stores import LedgerDict, LedgerList

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_port_substitution import (
        FinitePortSubstitution,
    )


@dataclass(frozen=True, slots=True, order=True)
class PortVariable:
    time: int
    side: int
    role: str
    bit: int

    def __post_init__(self) -> None:
        if (
            type(self.time) is not int
            or self.time < 0
            or type(self.side) is not int
            or self.side < 0
            or type(self.bit) is not int
            or self.bit < 0
            or type(self.role) is not str
            or not self.role
        ):
            raise ValueError("invalid finite port coordinate")


_SubstitutionInputs = tuple[tuple[PortVariable, int], ...]
_SubstitutionState = tuple[int, _SubstitutionInputs]
_SubstitutionStageKey = tuple[PortVariable, int, int]


def _validate_ports(*handles: TransferSummaryID) -> None:
    for handle in handles:
        if (
            type(handle) is not TransferSummaryID
            or handle.kind != "finite-port-function"
        ):
            raise ValueError("finite port components require transfer handles")
        if handle.owner is not handles[0].owner:
            raise ValueError("finite port components must belong to one arena")


@dataclass(frozen=True, slots=True)
class DecisionKey:
    variable: PortVariable
    low: TransferSummaryID
    high: TransferSummaryID

    def __post_init__(self) -> None:
        if type(self.variable) is not PortVariable:
            raise ValueError("invalid decision port")
        _validate_ports(self.low, self.high)


@dataclass(frozen=True, slots=True)
class DecisionIndexKey:
    """Canonical decision indices used after public handles are validated."""

    variable: PortVariable
    low: int
    high: int


@dataclass(frozen=True, slots=True)
class ChoiceKey:
    condition: TransferSummaryID
    yes: TransferSummaryID
    no: TransferSummaryID

    def __post_init__(self) -> None:
        _validate_ports(self.condition, self.yes, self.no)


@dataclass(frozen=True, slots=True)
class ChoiceIndexKey:
    """Canonical ITE identity after public handles have been validated."""

    condition: int
    yes: int
    no: int


@dataclass(frozen=True, slots=True)
class PortCompositionKey:
    before: TransferSummaryID
    after: TransferSummaryID
    port: PortVariable

    def __post_init__(self) -> None:
        if type(self.port) is not PortVariable:
            raise ValueError("invalid composition port")
        _validate_ports(self.before, self.after)


@dataclass(frozen=True, slots=True)
class FinitePortDecisionRecord:
    variable: PortVariable | None
    low: int = 0
    high: int = 0


@dataclass(frozen=True, slots=True)
class FinitePortActionAuditSnapshot:
    """Detached rows and exact registered-store identities for payload audits."""

    ledger: ResourceLedger
    owner: ArenaToken
    node_owner: int
    node_store_identity: int
    nodes: tuple[FinitePortDecisionRecord, ...]
    key_owner: int
    key_store_identity: int
    key_rows: tuple[tuple[object, object], ...]
    choice_owner: int
    choice_store_identity: int
    choice_rows: tuple[tuple[object, object], ...]
    substitution_owner: int
    substitution_store_identity: int
    substitution_rows: tuple[tuple[object, object], ...]
    support_owner: int
    support_store_identity: int
    support_rows: tuple[tuple[object, object], ...]


@dataclass(frozen=True, slots=True)
class PortDecision:
    """Authenticated finite-port node with scoped child references."""

    variable: PortVariable | None
    low: TransferSummaryID
    high: TransferSummaryID


@dataclass(frozen=True, slots=True)
class PortComponent:
    variable: PortVariable
    function: TransferSummaryID

    def __post_init__(self) -> None:
        if type(self.variable) is not PortVariable:
            raise ValueError("invalid component port")
        _validate_ports(self.function)


@dataclass(frozen=True, slots=True)
class FoldedPortCut:
    """Separate Boolean output components, never a dense joint-state table."""

    components: tuple[PortComponent, ...]

    def __post_init__(self) -> None:
        if type(self.components) is not tuple or any(
            type(component) is not PortComponent for component in self.components
        ):
            raise ValueError("folded cuts contain only symbolic port components")
        _validate_ports(*(component.function for component in self.components))
        variables = tuple(component.variable for component in self.components)
        if variables != tuple(sorted(set(variables))):
            raise ValueError("folded cut ports must be unique and ordered")


class FinitePortActionArena:
    def __init__(self, ledger: ResourceLedger | None = None) -> None:
        self.ledger = ResourceLedger() if ledger is None else ledger
        self.ledger.register_execution_root(self)
        self.owner = ArenaToken("finite-port-actions")
        prefix = f"finite-port-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(prefix + "-nodes", "canonical_transfer")
        self._key_owner = self.ledger.register(
            prefix + "-interner", "transfer_interner"
        )
        cache_owner = self.ledger.register(prefix + "-ite", "query_memo")
        compose_owner = self.ledger.register(prefix + "-composition", "query_memo")
        self._nodes: LedgerList[FinitePortDecisionRecord] = self.ledger.make_list(
            self._node_owner
        )
        self._keys: LedgerDict[DecisionIndexKey, int] = self.ledger.make_dict(
            self._key_owner
        )
        self._ite: OwnedMemo[ChoiceIndexKey, int] = OwnedMemo(
            self.ledger,
            cache_owner,
            evictable=True,
            composition_entries=True,
        )
        self._compositions: OwnedMemo[PortCompositionKey, TransferSummaryID] = (
            OwnedMemo(
                self.ledger, compose_owner, evictable=True, composition_entries=True
            )
        )
        self.ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=lambda: self._nodes,
        )
        self.ledger.register_container(
            self._key_owner,
            self._keys,
            node_count=lambda: 0,
            payloads=lambda: self._keys.items(),
        )
        self.ledger.reserve(self._node_owner, entries=2, nodes=2)
        self._nodes.extend(
            (FinitePortDecisionRecord(None), FinitePortDecisionRecord(None))
        )
        from number_compiler.arithmetic.functions.finite_port_substitution import (
            FinitePortSubstitution,
        )

        self._substitution = FinitePortSubstitution(self)

    def scoped_handle(self, index: int) -> TransferSummaryID:
        return TransferSummaryID(self.owner, "finite-port-function", index)

    def resolve_index(self, handle: TransferSummaryID) -> int:
        if type(handle) is not TransferSummaryID:
            raise ValueError("expected a finite-port transfer handle")
        handle.validate(self.owner, "finite-port-function")
        if handle.local_id >= len(self._nodes):
            raise ValueError("invalid finite-port transfer handle")
        return handle.local_id

    def decision_at(self, identity: int) -> FinitePortDecisionRecord:
        """Read one retained decision by its already resolved local identity."""
        return self._nodes[identity]

    def decision_record(self, handle: TransferSummaryID) -> FinitePortDecisionRecord:
        """Read the immutable backing record for an authenticated handle."""
        return self._nodes[self.resolve_index(handle)]

    def audit_snapshot(self) -> FinitePortActionAuditSnapshot:
        """Capture exact stores as immutable rows for the resource auditor."""
        from number_compiler.resources.payload_containers import audit_mapping_items

        substitution = self._substitution
        choice_store = self._ite.audit_snapshot().container
        return FinitePortActionAuditSnapshot(
            ledger=self.ledger,
            owner=self.owner,
            node_owner=self._node_owner,
            node_store_identity=id(self._nodes),
            nodes=tuple(self._nodes.audit_view()),
            key_owner=self._key_owner,
            key_store_identity=id(self._keys),
            key_rows=audit_mapping_items(cast(Mapping[object, object], self._keys)),
            choice_owner=self._ite.owner,
            choice_store_identity=id(choice_store),
            choice_rows=audit_mapping_items(
                cast(Mapping[object, object], choice_store)
            ),
            substitution_owner=substitution.memo_owner,
            substitution_store_identity=id(substitution.memo),
            substitution_rows=audit_mapping_items(
                cast(Mapping[object, object], substitution.memo)
            ),
            support_owner=substitution.support_owner,
            support_store_identity=id(substitution.supports),
            support_rows=audit_mapping_items(
                cast(Mapping[object, object], substitution.supports)
            ),
        )

    def node(self, handle: TransferSummaryID) -> PortDecision:
        """Resolve one node after authenticating its arena-scoped handle."""
        index = self.resolve_index(handle)
        record = self._nodes[index]
        return PortDecision(
            record.variable,
            self.scoped_handle(record.low),
            self.scoped_handle(record.high),
        )

    def constant(self, value: bool) -> TransferSummaryID:
        if type(value) is not bool:
            raise TypeError("finite-port constants require a Boolean")
        return self.scoped_handle(int(value))

    def intern_record(self, variable: PortVariable, low: int, high: int) -> int:
        if type(variable) is not PortVariable:
            raise ValueError("invalid finite decision variable")
        if (
            type(variable.time) is not int
            or variable.time < 0
            or type(variable.side) is not int
            or variable.side < 0
            or type(variable.bit) is not int
            or variable.bit < 0
            or type(variable.role) is not str
            or not variable.role
        ):
            raise ValueError("invalid finite port coordinate")
        nodes = self._nodes.audit_view()
        node_count = len(nodes)
        if (
            type(low) is not int
            or not 0 <= low < node_count
            or type(high) is not int
            or not 0 <= high < node_count
        ):
            raise ValueError("invalid finite decision child")
        if low == high:
            self.ledger.bump(_functions_keys.FINITE_DECISION_INTERNER_REQUESTS)
            self.ledger.bump(_functions_keys.FINITE_DECISION_IDENTITY_REDUCTIONS)
            return low
        for child in (low, high):
            child_variable = nodes[child].variable
            if child_variable is not None and child_variable <= variable:
                raise ValueError("decision variables are not strictly ordered")
        key = DecisionIndexKey(variable, low, high)
        # This is a private read after validation. Publication still passes
        # through the ledger-owned stores and their reservation checks.
        found = self._keys.audit_view().get(key)
        self.ledger.bump(_functions_keys.FINITE_DECISION_INTERNER_REQUESTS)
        if found is not None:
            self.ledger.bump(_functions_keys.FINITE_DECISION_INTERNER_HITS)
            return found
        self.ledger.bump(_functions_keys.FINITE_DECISION_INTERNER_EVALUATIONS)
        try:
            self.ledger.reserve_many(
                ((self._node_owner, 1, 1), (self._key_owner, 1, 0))
            )
        except BlockContextBudgetExceeded:
            self.ledger.bump(_functions_keys.FINITE_DECISION_PUBLICATION_REJECTIONS)
            raise
        index = len(self._nodes)
        self._nodes.append(FinitePortDecisionRecord(variable, low, high))
        self._keys[key] = index
        self.ledger.bump(_functions_keys.FINITE_DECISION_PUBLISHED_NODES)
        return index

    def variable(self, variable: PortVariable) -> TransferSummaryID:
        return self.scoped_handle(self.intern_record(variable, 0, 1))

    def unary(self, variable: PortVariable, low: bool, high: bool) -> TransferSummaryID:
        if type(low) is not bool or type(high) is not bool:
            raise TypeError("finite-port branches require Booleans")
        return self.scoped_handle(self.intern_record(variable, int(low), int(high)))

    @staticmethod
    def _terminal(key: tuple[int, int, int]) -> int | None:
        condition, yes, no = key
        if condition < 2:
            return yes if condition else no
        if yes == no:
            return yes
        if yes == 1 and no == 0:
            return condition
        return None

    def choose(
        self,
        condition: TransferSummaryID,
        yes: TransferSummaryID,
        no: TransferSummaryID,
    ) -> TransferSummaryID:
        """Canonical if-then-else, using an explicit Shannon expansion stack."""
        root = (
            self.resolve_index(condition),
            self.resolve_index(yes),
            self.resolve_index(no),
        )
        self.ledger.bump(_shared_keys.COMPOSITION_REQUESTS)
        root_key = ChoiceIndexKey(*root)
        cached_root = self._ite.get(root_key)
        if cached_root is not None:
            if type(cached_root) is not int or not 0 <= cached_root < len(self._nodes):
                raise ValueError("cached finite choice has an invalid private identity")
            self.ledger.bump(_shared_keys.COMPOSITION_CACHE_HITS)
            return self.scoped_handle(cached_root)
        self.ledger.bump(_shared_keys.COMPOSITION_EVALUATIONS)
        results: dict[tuple[int, int, int], int] = {}
        frames: list[tuple[tuple[int, int, int], bool]] = [(root, False)]
        splits: dict[
            tuple[int, int, int],
            tuple[PortVariable, tuple[int, int, int], tuple[int, int, int]],
        ] = {}
        while frames:
            key, ready = frames.pop()
            if key in results:
                continue
            terminal = self._terminal(key)
            if terminal is not None:
                results[key] = terminal
                continue
            memo_key = ChoiceIndexKey(*key)
            found = self._ite.get(memo_key)
            if found is not None:
                if type(found) is not int or not 0 <= found < len(self._nodes):
                    raise ValueError(
                        "cached finite choice has an invalid private identity"
                    )
                results[key] = found
                continue
            if not ready:
                variable = min(
                    node.variable
                    for index in key
                    if (node := self._nodes[index]).variable is not None
                )
                lower = tuple(
                    self._nodes[index].low
                    if self._nodes[index].variable == variable
                    else index
                    for index in key
                )
                upper = tuple(
                    self._nodes[index].high
                    if self._nodes[index].variable == variable
                    else index
                    for index in key
                )
                split_choice(frames, splits, key, variable, lower, upper)
                continue
            variable, low_key, high_key = splits[key]
            result = self.intern_record(variable, results[low_key], results[high_key])
            self._ite[memo_key] = result
            results[key] = result
            self.ledger.bump(_functions_keys.DECISION_SUBPROBLEM_EVALUATIONS)
        return self.scoped_handle(results[root])

    def negate(self, function: TransferSummaryID) -> TransferSummaryID:
        return self.choose(function, self.constant(False), self.constant(True))

    def compile_substitution(
        self,
        work: FinitePortSubstitution,
        function: TransferSummaryID,
        substitutions: Mapping[PortVariable, TransferSummaryID],
    ) -> TransferSummaryID:
        """Compile inside the decision owner using the caller's charged memo."""
        from number_compiler.arithmetic.functions.finite_port_substitution import (
            FinitePortSubstitution,
            PortIndexComponent,
            SubstitutionIndexKey,
        )

        if type(work) is not FinitePortSubstitution or work.arena is not self:
            raise ValueError("substitution workspace belongs to another arena")
        arena = self
        root = arena.resolve_index(function)
        for variable, value in substitutions.items():
            if type(variable) is not PortVariable:
                raise ValueError("substitution keys must be port variables")
            arena.resolve_index(value)
        # All scoped inputs are now validated. Internal dependency frames use
        # only canonical local IDs, so read the arena's owned append-only list
        # directly instead of re-entering its public sequence facade millions
        # of times during exhaustive proof compilation.
        nodes = arena._nodes.audit_view()
        work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_REQUESTS)
        # Constants and identity substitutions require no memo allocation.
        while root >= 2:
            node = nodes[root]
            assert node.variable is not None
            condition = substitutions.get(node.variable)
            if condition is None or condition.local_id >= 2:
                break
            work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_CONSTANT_PRUNES)
            work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_VISITS)
            root = node.high if condition.local_id else node.low
        if root < 2 or not substitutions:
            work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_DIRECT_RESULTS)
            return arena.scoped_handle(root)
        local_support: dict[int, frozenset[PortVariable]] = {
            0: frozenset(),
            1: frozenset(),
        }

        support_members = 0

        def support(index: int) -> frozenset[PortVariable]:
            nonlocal support_members
            frames = [(index, False)]
            while frames:
                work.record_peak(
                    "finite_port_substitution_support_frames_peak", len(frames)
                )
                current, ready = frames.pop()
                work.ledger.bump(
                    _functions_keys.FINITE_PORT_SUBSTITUTION_SUPPORT_FRAME_POPS
                )
                if current in local_support:
                    continue
                work.ledger.bump(
                    _functions_keys.FINITE_PORT_SUBSTITUTION_SUPPORT_VISITS
                )
                decision = nodes[current]
                assert decision.variable is not None
                if not ready:
                    frames.extend(
                        ((current, True), (decision.high, False), (decision.low, False))
                    )
                else:
                    local_support[current] = (
                        local_support[decision.low]
                        | local_support[decision.high]
                        | {decision.variable}
                    )
                    support_members += len(local_support[current])
                    work.record_peak(
                        "finite_port_substitution_support_members_peak", support_members
                    )
                    work.record_peak(
                        "finite_port_substitution_support_nodes_peak",
                        len(local_support),
                    )
            return local_support[index]

        ordered = work.supports.get(root)
        if ordered is None:
            ordered = tuple(sorted(support(root)))
        # Ignore unused substitutions and explicit identity substitutions.
        components: list[PortIndexComponent] = []
        for variable in ordered:
            replacement_handle = substitutions.get(variable)
            if replacement_handle is None:
                continue
            decision = nodes[replacement_handle.local_id]
            if (
                decision.variable == variable
                and decision.low == 0
                and decision.high == 1
            ):
                continue
            components.append(PortIndexComponent(variable, replacement_handle.local_id))
        if not components:
            work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_DIRECT_RESULTS)
            return arena.scoped_handle(root)
        work.record_peak("finite_port_substitution_components_peak", len(components))
        key = SubstitutionIndexKey(root, tuple(components))
        cached = work.memo.get(key)
        if cached is not None:
            if type(cached) is not int or not 0 <= cached < len(nodes):
                raise ValueError("cached substitution has an invalid private identity")
            work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_CACHE_HITS)
            return arena.scoped_handle(cached)
        # Every nontrivial cold query needs a root memo slot, even if its final
        # function aliases an existing node. Reject an exhausted entry budget
        # before Shannon expansion; a full node budget can still admit aliases.
        if (
            work.ledger.max_cache_entries is not None
            and work.ledger.entries >= work.ledger.max_cache_entries
        ):
            work.ledger.bump(
                _functions_keys.FINITE_PORT_SUBSTITUTION_PREFLIGHT_REJECTIONS
            )
            raise BlockContextBudgetExceeded(
                "finite port substitution memo budget exhausted"
            )
        work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_EVALUATIONS)
        replacements = {part.variable: part.function for part in components}
        work.record_peak(
            "finite_port_substitution_replacements_peak", len(replacements)
        )
        initial: _SubstitutionState = (
            root,
            tuple((variable, replacements.get(variable, -1)) for variable in ordered),
        )
        results: dict[_SubstitutionState, int] = {}
        splits: dict[
            _SubstitutionState,
            tuple[PortVariable, _SubstitutionState, _SubstitutionState],
        ] = {}
        pending = [(initial, False)]
        results_input_count = splits_input_count = 0
        staged: list[_SubstitutionStageKey] = []
        stage_keys: dict[_SubstitutionStageKey, int] = {}

        def normalize(index: int, inputs: _SubstitutionInputs) -> _SubstitutionState:
            conditions = dict(inputs)
            work.record_peak(
                "finite_port_substitution_normalization_inputs_peak", len(inputs)
            )
            work.record_peak(
                "finite_port_substitution_normalization_map_peak", len(conditions)
            )
            while index >= 2:
                node = nodes[index]
                assert node.variable is not None
                value = conditions[node.variable]
                if value not in (0, 1):
                    break
                work.ledger.bump(
                    _functions_keys.FINITE_PORT_SUBSTITUTION_CONSTANT_PRUNES
                )
                index = node.high if value else node.low
            if index < 2:
                return index, ()
            needed = support(index)
            return index, tuple(
                (variable, value) for variable, value in inputs if variable in needed
            )

        def intern(variable: PortVariable, low: int, high: int) -> int:
            if low == high:
                work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_LATE_ALIASES)
                return low
            if low >= 0 and high >= 0:
                found = arena._keys.get(DecisionIndexKey(variable, low, high))
                if found is not None:
                    work.ledger.bump(
                        _functions_keys.FINITE_PORT_SUBSTITUTION_LATE_ALIASES
                    )
                    return found
            stage_key = variable, low, high
            found_index = stage_keys.get(stage_key)
            if found_index is not None:
                work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_LATE_ALIASES)
                return found_index
            staged.append(stage_key)
            index = -len(staged)
            stage_keys[stage_key] = index
            work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_STAGED_NODES)
            return index

        while pending:
            work.record_peak("finite_port_substitution_peak_frames", len(pending))
            work.record_peak("finite_port_substitution_results_peak", len(results))
            work.record_peak(
                "finite_port_substitution_shannon_storage_peak",
                len(pending)
                + len(results)
                + len(splits)
                + len(staged)
                + len(stage_keys),
            )
            work.record_peak(
                "finite_port_substitution_stage_keys_peak", len(stage_keys)
            )
            work.record_peak("finite_port_substitution_splits_peak", len(splits))
            work.record_peak(
                "finite_port_substitution_state_inputs_peak",
                results_input_count + splits_input_count,
            )
            state, ready = pending.pop()
            work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_VISITS)
            if state in results:
                continue
            index, inputs = state
            if index < 2:
                results[state] = index
                results_input_count += len(inputs)
                continue
            if ready:
                variable, lower_state, upper_state = splits.pop(state)
                splits_input_count -= len(inputs)
                results_input_count += len(inputs)
                results[state] = intern(
                    variable, results[lower_state], results[upper_state]
                )
                continue
            work.ledger.bump(_functions_keys.FINITE_PORT_SUBSTITUTION_COFACTOR_TASKS)
            candidates: list[PortVariable] = []
            for original, replacement in inputs:
                top = original if replacement == -1 else nodes[replacement].variable
                if top is not None:
                    candidates.append(top)
            work.record_peak(
                "finite_port_substitution_candidates_peak", len(candidates)
            )
            variable = min(candidates)
            low_inputs: list[tuple[PortVariable, int]] = []
            high_inputs: list[tuple[PortVariable, int]] = []
            for original, replacement in inputs:
                if replacement == -1:
                    low, high = (0, 1) if original == variable else (-1, -1)
                else:
                    decision = nodes[replacement]
                    low, high = (
                        (decision.low, decision.high)
                        if decision.variable == variable
                        else (replacement, replacement)
                    )
                low_inputs.append((original, low))
                high_inputs.append((original, high))
            work.record_peak(
                "finite_port_substitution_branch_inputs_peak",
                len(low_inputs) + len(high_inputs),
            )
            low_state = normalize(index, tuple(low_inputs))
            high_state = normalize(index, tuple(high_inputs))
            splits[state] = variable, low_state, high_state
            splits_input_count += len(inputs)
            pending.extend(((state, True), (high_state, False), (low_state, False)))
        work.record_peak("finite_port_substitution_results_peak", len(results))
        work.record_peak("finite_port_substitution_stage_keys_peak", len(stage_keys))
        work.record_peak(
            "finite_port_substitution_state_inputs_peak",
            results_input_count + splits_input_count,
        )
        work.record_peak(
            "finite_port_substitution_shannon_storage_peak",
            len(results) + len(splits) + len(staged) + len(stage_keys),
        )
        result = results[initial]
        # Local postorder IDs are topological. Mark only the final result's DAG;
        # Shannon subproblems reduced out of the root are discarded, not interned.
        reachable: set[int] = set()
        scan = [result]
        while scan:
            work.record_peak(
                "finite_port_substitution_publication_scan_peak", len(scan)
            )
            work.record_peak("finite_port_substitution_reachable_peak", len(reachable))
            work.ledger.bump(
                _functions_keys.FINITE_PORT_SUBSTITUTION_PUBLICATION_VISITS
            )
            index = scan.pop()
            if index >= 0 or index in reachable:
                continue
            reachable.add(index)
            _, low, high = staged[-index - 1]
            scan.extend((low, high))
        work.record_peak("finite_port_substitution_reachable_peak", len(reachable))
        count = len(reachable)
        support_new = root not in work.supports
        try:
            work.ledger.reserve_many(
                (
                    (arena._node_owner, count, count),
                    (arena._key_owner, count, 0),
                    (work.memo_owner, 1, 0),
                    (work.support_owner, int(support_new), 0),
                )
            )
        except BlockContextBudgetExceeded:
            work.ledger.bump(
                _functions_keys.FINITE_PORT_SUBSTITUTION_PUBLICATION_REJECTIONS
            )
            raise
        published: dict[int, int] = {}
        for offset, (variable, low, high) in enumerate(staged):
            local = -offset - 1
            if local not in reachable:
                continue
            low = low if low >= 0 else published[low]
            high = high if high >= 0 else published[high]
            index = len(arena._nodes)
            arena._nodes.append(FinitePortDecisionRecord(variable, low, high))
            arena._keys[DecisionIndexKey(variable, low, high)] = index
            published[local] = index
            work.record_peak(
                "finite_port_substitution_published_map_peak", len(published)
            )
        output = result if result >= 0 else published[result]
        if support_new:
            work.supports[root] = ordered
        work.memo[key] = output
        work.ledger.bump(
            _functions_keys.FINITE_PORT_SUBSTITUTION_PUBLISHED_NODES,
            count,
        )
        work.ledger.bump(
            _functions_keys.FINITE_PORT_SUBSTITUTION_DISCARDED_NODES,
            len(staged) - count,
        )
        return arena.scoped_handle(output)

    def substitute(
        self,
        function: TransferSummaryID,
        substitutions: Mapping[PortVariable, TransferSummaryID],
    ) -> TransferSummaryID:
        """Simultaneous, fused cofactoring; replacements are not substituted."""
        return self._substitution.apply(function, substitutions)

    def compose(
        self, before: TransferSummaryID, after: TransferSummaryID, port: PortVariable
    ) -> TransferSummaryID:
        """Chronological unary port composition: after(before(input))."""
        self.resolve_index(before)
        self.resolve_index(after)
        key = PortCompositionKey(before, after, port)
        self.ledger.bump(_shared_keys.COMPOSITION_REQUESTS)
        found = self._compositions.get(key)
        if found is not None:
            self.ledger.bump(_shared_keys.COMPOSITION_CACHE_HITS)
            return found
        result = self.substitute(after, {port: before})
        self._compositions[key] = result
        self.ledger.bump(_shared_keys.COMPOSITION_EVALUATIONS)
        return result

    def apply(
        self, function: TransferSummaryID, inputs: Mapping[PortVariable, bool]
    ) -> bool:
        index = self.resolve_index(function)
        if any(type(value) is not bool for value in inputs.values()):
            raise TypeError("finite-port observations require Boolean values")
        self.ledger.bump(_functions_keys.FINITE_PORT_APPLICATIONS)
        while index >= 2:
            self.ledger.bump(_functions_keys.FINITE_PORT_DECISION_VISITS)
            node = self._nodes[index]
            if node.variable is None:
                raise AssertionError(index)
            index = node.high if inputs[node.variable] else node.low
        return bool(index)

    def permute(
        self,
        function: TransferSummaryID,
        permutation: Mapping[PortVariable, PortVariable],
    ) -> TransferSummaryID:
        if set(permutation) != set(permutation.values()):
            raise ValueError("port symmetry must be a bijection")
        self.resolve_index(function)
        return self.substitute(
            function, {old: self.variable(new) for old, new in permutation.items()}
        )

    def cut(self, outputs: Mapping[PortVariable, TransferSummaryID]) -> FoldedPortCut:
        for function in outputs.values():
            self.resolve_index(function)
        return FoldedPortCut(
            tuple(
                PortComponent(variable, outputs[variable])
                for variable in sorted(outputs)
            )
        )

    def compose_cut(self, before: FoldedPortCut, after: FoldedPortCut) -> FoldedPortCut:
        substitutions = {
            component.variable: component.function for component in before.components
        }
        for component in (*before.components, *after.components):
            self.resolve_index(component.function)
        return self.cut(
            {
                component.variable: self.substitute(component.function, substitutions)
                for component in after.components
            }
        )

    @property
    def node_count(self) -> int:
        return len(self._nodes)

    def retained_entries(self) -> int:
        return (
            len(self._nodes)
            + len(self._keys)
            + len(self._ite)
            + len(self._compositions)
            + len(self._substitution.memo)
            + len(self._substitution.supports)
        )
