"""Simultaneous port substitution with a transactionally published reduced DAG.

Only Boolean functions are staged. Cofactor states contain original decision
IDs and replacement decision IDs, never sampled values of a spatial field.
"""

from __future__ import annotations

from collections.abc import Mapping, MutableMapping
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_port_action import (
    PortComponent,
    PortVariable,
    _Decision,
    _DecisionIndexKey,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.functions.finite_port_action import (
        FinitePortActionArena,
    )


@dataclass(frozen=True, slots=True)
class SubstitutionKey:
    function: TransferSummaryID
    components: tuple[PortComponent, ...]

    def __post_init__(self) -> None:
        if (
            type(self.function) is not TransferSummaryID
            or self.function.kind != "finite-port-function"
        ):
            raise ValueError("invalid substitution function")
        if type(self.components) is not tuple or any(
            type(part) is not PortComponent for part in self.components
        ):
            raise ValueError("invalid substitution components")
        variables = tuple(part.variable for part in self.components)
        if variables != tuple(sorted(set(variables))):
            raise ValueError("substitution components must be ordered and unique")
        for part in self.components:
            part.function.validate(self.function.owner, "finite-port-function")


@dataclass(frozen=True, slots=True)
class _PortIndexComponent:
    variable: PortVariable
    function: int


@dataclass(frozen=True, slots=True)
class _SubstitutionIndexKey:
    function: int
    components: tuple[_PortIndexComponent, ...]


# -1 is an implicit identity variable, not a Boolean decision ID.
_Inputs = tuple[tuple[PortVariable, int], ...]
_State = tuple[int, _Inputs]
_StageKey = tuple[PortVariable, int, int]


class FinitePortSubstitution:
    def __init__(self, arena: FinitePortActionArena) -> None:
        self.arena = arena
        self.ledger = arena.ledger
        prefix = f"finite-port-substitution-{len(self.ledger.inventory())}"
        self.memo_owner = self.ledger.register(prefix, "query_memo")
        self.support_owner = self.ledger.register(prefix + "-support", "query_memo")
        self.memo: MutableMapping[_SubstitutionIndexKey, int] = self.ledger.make_dict(
            self.memo_owner
        )
        self.supports: MutableMapping[int, tuple[PortVariable, ...]] = (
            self.ledger.make_dict(self.support_owner)
        )
        self.ledger.register_container(
            self.memo_owner,
            self.memo,
            node_count=lambda: 0,
            payloads=lambda: self.memo.items(),
            evict=self.clear,
            composition_count=lambda: len(self.memo),
        )
        self.ledger.register_container(
            self.support_owner,
            self.supports,
            node_count=lambda: 0,
            payloads=lambda: self.supports.items(),
        )

    def clear(self) -> None:
        entries, supports = len(self.memo), len(self.supports)
        self.memo.clear()
        self.supports.clear()
        self.ledger.release(self.memo_owner, entries=entries)
        self.ledger.release(self.support_owner, entries=supports)

    def _peak(self, name: str, size: int) -> None:
        self.ledger.bump(name, max(0, size - self.ledger.counters.get(name, 0)))

    def apply(
        self,
        function: TransferSummaryID,
        substitutions: Mapping[PortVariable, TransferSummaryID],
    ) -> TransferSummaryID:
        arena = self.arena
        root = arena._resolve(function)
        for variable, value in substitutions.items():
            if type(variable) is not PortVariable:
                raise ValueError("substitution keys must be port variables")
            arena._resolve(value)
        # All scoped inputs are now validated. Internal dependency frames use
        # only canonical local IDs, so read the arena's owned append-only list
        # directly instead of re-entering its public sequence facade millions
        # of times during exhaustive proof compilation.
        nodes = arena._nodes._data
        self.ledger.bump("finite_port_substitution_requests")
        # Constants and identity substitutions require no memo allocation.
        while root >= 2:
            node = nodes[root]
            assert node.variable is not None
            condition = substitutions.get(node.variable)
            if condition is None or condition.local_id >= 2:
                break
            self.ledger.bump("finite_port_substitution_constant_prunes")
            self.ledger.bump("finite_port_substitution_visits")
            root = node.high if condition.local_id else node.low
        if root < 2 or not substitutions:
            self.ledger.bump("finite_port_substitution_direct_results")
            return arena._handle(root)
        local_support: dict[int, frozenset[PortVariable]] = {
            0: frozenset(),
            1: frozenset(),
        }

        support_members = 0

        def support(index: int) -> frozenset[PortVariable]:
            nonlocal support_members
            frames = [(index, False)]
            while frames:
                self._peak("finite_port_substitution_support_frames_peak", len(frames))
                current, ready = frames.pop()
                self.ledger.bump("finite_port_substitution_support_frame_pops")
                if current in local_support:
                    continue
                self.ledger.bump("finite_port_substitution_support_visits")
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
                    self._peak(
                        "finite_port_substitution_support_members_peak", support_members
                    )
                    self._peak(
                        "finite_port_substitution_support_nodes_peak",
                        len(local_support),
                    )
            return local_support[index]

        ordered = self.supports.get(root)
        if ordered is None:
            ordered = tuple(sorted(support(root)))
        # Ignore unused substitutions and explicit identity substitutions.
        components = []
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
            components.append(
                _PortIndexComponent(variable, replacement_handle.local_id)
            )
        if not components:
            self.ledger.bump("finite_port_substitution_direct_results")
            return arena._handle(root)
        self._peak("finite_port_substitution_components_peak", len(components))
        key = _SubstitutionIndexKey(root, tuple(components))
        cached = self.memo.get(key)
        if cached is not None:
            if type(cached) is not int or not 0 <= cached < len(nodes):
                raise ValueError("cached substitution has an invalid private identity")
            self.ledger.bump("finite_port_substitution_cache_hits")
            return arena._handle(cached)
        # Every nontrivial cold query needs a root memo slot, even if its final
        # function aliases an existing node. Reject an exhausted entry budget
        # before Shannon expansion; a full node budget can still admit aliases.
        if (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries >= self.ledger.max_cache_entries
        ):
            self.ledger.bump("finite_port_substitution_preflight_rejections")
            raise BlockContextBudgetExceeded(
                "finite port substitution memo budget exhausted"
            )
        self.ledger.bump("finite_port_substitution_evaluations")
        replacements = {part.variable: part.function for part in components}
        self._peak("finite_port_substitution_replacements_peak", len(replacements))
        initial: _State = (
            root,
            tuple((variable, replacements.get(variable, -1)) for variable in ordered),
        )
        results: dict[_State, int] = {}
        splits: dict[_State, tuple[PortVariable, _State, _State]] = {}
        pending = [(initial, False)]
        results_input_count = splits_input_count = 0
        staged: list[_StageKey] = []
        stage_keys: dict[_StageKey, int] = {}

        def normalize(index: int, inputs: _Inputs) -> _State:
            conditions = dict(inputs)
            self._peak(
                "finite_port_substitution_normalization_inputs_peak", len(inputs)
            )
            self._peak(
                "finite_port_substitution_normalization_map_peak", len(conditions)
            )
            while index >= 2:
                node = nodes[index]
                assert node.variable is not None
                value = conditions[node.variable]
                if value not in (0, 1):
                    break
                self.ledger.bump("finite_port_substitution_constant_prunes")
                index = node.high if value else node.low
            if index < 2:
                return index, ()
            needed = support(index)
            return index, tuple(
                (variable, value) for variable, value in inputs if variable in needed
            )

        def intern(variable: PortVariable, low: int, high: int) -> int:
            if low == high:
                self.ledger.bump("finite_port_substitution_late_aliases")
                return low
            if low >= 0 and high >= 0:
                found = arena._keys.get(_DecisionIndexKey(variable, low, high))
                if found is not None:
                    self.ledger.bump("finite_port_substitution_late_aliases")
                    return found
            stage_key = variable, low, high
            found_index = stage_keys.get(stage_key)
            if found_index is not None:
                self.ledger.bump("finite_port_substitution_late_aliases")
                return found_index
            staged.append(stage_key)
            index = -len(staged)
            stage_keys[stage_key] = index
            self.ledger.bump("finite_port_substitution_staged_nodes")
            return index

        while pending:
            self._peak("finite_port_substitution_peak_frames", len(pending))
            self._peak("finite_port_substitution_results_peak", len(results))
            self._peak(
                "finite_port_substitution_shannon_storage_peak",
                len(pending)
                + len(results)
                + len(splits)
                + len(staged)
                + len(stage_keys),
            )
            self._peak("finite_port_substitution_stage_keys_peak", len(stage_keys))
            self._peak("finite_port_substitution_splits_peak", len(splits))
            self._peak(
                "finite_port_substitution_state_inputs_peak",
                results_input_count + splits_input_count,
            )
            state, ready = pending.pop()
            self.ledger.bump("finite_port_substitution_visits")
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
            self.ledger.bump("finite_port_substitution_cofactor_tasks")
            candidates = []
            for original, replacement in inputs:
                top = original if replacement == -1 else nodes[replacement].variable
                if top is not None:
                    candidates.append(top)
            self._peak("finite_port_substitution_candidates_peak", len(candidates))
            variable = min(candidates)
            low_inputs, high_inputs = [], []
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
            self._peak(
                "finite_port_substitution_branch_inputs_peak",
                len(low_inputs) + len(high_inputs),
            )
            low_state = normalize(index, tuple(low_inputs))
            high_state = normalize(index, tuple(high_inputs))
            splits[state] = variable, low_state, high_state
            splits_input_count += len(inputs)
            pending.extend(((state, True), (high_state, False), (low_state, False)))
        self._peak("finite_port_substitution_results_peak", len(results))
        self._peak("finite_port_substitution_stage_keys_peak", len(stage_keys))
        self._peak(
            "finite_port_substitution_state_inputs_peak",
            results_input_count + splits_input_count,
        )
        self._peak(
            "finite_port_substitution_shannon_storage_peak",
            len(results) + len(splits) + len(staged) + len(stage_keys),
        )
        result = results[initial]
        # Local postorder IDs are topological. Mark only the final result's DAG;
        # Shannon subproblems reduced out of the root are discarded, not interned.
        reachable: set[int] = set()
        scan = [result]
        while scan:
            self._peak("finite_port_substitution_publication_scan_peak", len(scan))
            self._peak("finite_port_substitution_reachable_peak", len(reachable))
            self.ledger.bump("finite_port_substitution_publication_visits")
            index = scan.pop()
            if index >= 0 or index in reachable:
                continue
            reachable.add(index)
            _, low, high = staged[-index - 1]
            scan.extend((low, high))
        self._peak("finite_port_substitution_reachable_peak", len(reachable))
        count = len(reachable)
        support_new = root not in self.supports
        try:
            self.ledger.reserve_many(
                (
                    (arena._node_owner, count, count),
                    (arena._key_owner, count, 0),
                    (self.memo_owner, 1, 0),
                    (self.support_owner, int(support_new), 0),
                )
            )
        except BlockContextBudgetExceeded:
            self.ledger.bump("finite_port_substitution_publication_rejections")
            raise
        published: dict[int, int] = {}
        for offset, (variable, low, high) in enumerate(staged):
            local = -offset - 1
            if local not in reachable:
                continue
            low = low if low >= 0 else published[low]
            high = high if high >= 0 else published[high]
            index = len(arena._nodes)
            arena._nodes.append(_Decision(variable, low, high))
            arena._keys[_DecisionIndexKey(variable, low, high)] = index
            published[local] = index
            self._peak("finite_port_substitution_published_map_peak", len(published))
        output = result if result >= 0 else published[result]
        if support_new:
            self.supports[root] = ordered
        self.memo[key] = output
        self.ledger.bump("finite_port_substitution_published_nodes", count)
        self.ledger.bump(
            "finite_port_substitution_discarded_nodes", len(staged) - count
        )
        return arena._handle(output)
