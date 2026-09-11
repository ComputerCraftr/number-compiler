"""Reduced ordered Boolean port functions, with factored multi-port cuts.

Variables are ordered by time, side, role, and bit.  Spatial transfer functions
can share these canonical decision nodes without enumerating the product of
all cut states.  This algebra supplies no arithmetic successor-closure proof.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
    TransferSummaryID,
)
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.stores import LedgerDict, LedgerList


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
class _DecisionIndexKey:
    """Arena-private canonical indices; public APIs still admit scoped handles."""

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
class _ChoiceIndexKey:
    """Arena-private ITE identity after all public handles are validated."""

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
class _Decision:
    variable: PortVariable | None
    low: int = 0
    high: int = 0


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
        self._nodes: LedgerList[_Decision] = self.ledger.make_list(self._node_owner)
        self._keys: LedgerDict[_DecisionIndexKey, int] = self.ledger.make_dict(
            self._key_owner
        )
        self._ite: OwnedMemo[_ChoiceIndexKey, int] = OwnedMemo(
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
        self._nodes.extend((_Decision(None), _Decision(None)))
        from number_compiler.arithmetic.functions.finite_port_substitution import (
            FinitePortSubstitution,
        )

        self._substitution = FinitePortSubstitution(self)

    def _handle(self, index: int) -> TransferSummaryID:
        return TransferSummaryID(self.owner, "finite-port-function", index)

    def _resolve(self, handle: TransferSummaryID) -> int:
        if type(handle) is not TransferSummaryID:
            raise ValueError("expected a finite-port transfer handle")
        handle.validate(self.owner, "finite-port-function")
        if handle.local_id >= len(self._nodes):
            raise ValueError("invalid finite-port transfer handle")
        return handle.local_id

    def constant(self, value: bool) -> TransferSummaryID:
        if type(value) is not bool:
            raise TypeError("finite-port constants require a Boolean")
        return self._handle(int(value))

    def _intern(self, variable: PortVariable, low: int, high: int) -> int:
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
        nodes = self._nodes._data
        node_count = len(nodes)
        if (
            type(low) is not int
            or not 0 <= low < node_count
            or type(high) is not int
            or not 0 <= high < node_count
        ):
            raise ValueError("invalid finite decision child")
        if low == high:
            self.ledger.bump("finite_decision_interner_requests")
            self.ledger.bump("finite_decision_identity_reductions")
            return low
        for child in (low, high):
            child_variable = nodes[child].variable
            if child_variable is not None and child_variable <= variable:
                raise ValueError("decision variables are not strictly ordered")
        key = _DecisionIndexKey(variable, low, high)
        # This is a private read after validation. Publication still passes
        # through the ledger-owned stores and their reservation checks.
        found = self._keys._data.get(key)
        self.ledger.bump("finite_decision_interner_requests")
        if found is not None:
            self.ledger.bump("finite_decision_interner_hits")
            return found
        self.ledger.bump("finite_decision_interner_evaluations")
        try:
            self.ledger.reserve_many(
                ((self._node_owner, 1, 1), (self._key_owner, 1, 0))
            )
        except BlockContextBudgetExceeded:
            self.ledger.bump("finite_decision_publication_rejections")
            raise
        index = len(self._nodes)
        self._nodes.append(_Decision(variable, low, high))
        self._keys[key] = index
        self.ledger.bump("finite_decision_published_nodes")
        return index

    def variable(self, variable: PortVariable) -> TransferSummaryID:
        return self._handle(self._intern(variable, 0, 1))

    def unary(self, variable: PortVariable, low: bool, high: bool) -> TransferSummaryID:
        if type(low) is not bool or type(high) is not bool:
            raise TypeError("finite-port branches require Booleans")
        return self._handle(self._intern(variable, int(low), int(high)))

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
        root = self._resolve(condition), self._resolve(yes), self._resolve(no)
        self.ledger.bump("composition_requests")
        root_key = _ChoiceIndexKey(*root)
        cached_root = self._ite.get(root_key)
        if cached_root is not None:
            if type(cached_root) is not int or not 0 <= cached_root < len(self._nodes):
                raise ValueError("cached finite choice has an invalid private identity")
            self.ledger.bump("composition_cache_hits")
            return self._handle(cached_root)
        self.ledger.bump("composition_evaluations")
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
            memo_key = _ChoiceIndexKey(*key)
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
                low_key = lower[0], lower[1], lower[2]
                high_key = upper[0], upper[1], upper[2]
                splits[key] = variable, low_key, high_key
                frames.extend(((key, True), (high_key, False), (low_key, False)))
                continue
            variable, low_key, high_key = splits[key]
            result = self._intern(variable, results[low_key], results[high_key])
            self._ite[memo_key] = result
            results[key] = result
            self.ledger.bump("decision_subproblem_evaluations")
        return self._handle(results[root])

    def negate(self, function: TransferSummaryID) -> TransferSummaryID:
        return self.choose(function, self.constant(False), self.constant(True))

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
        self._resolve(before)
        self._resolve(after)
        key = PortCompositionKey(before, after, port)
        self.ledger.bump("composition_requests")
        found = self._compositions.get(key)
        if found is not None:
            self.ledger.bump("composition_cache_hits")
            return found
        result = self.substitute(after, {port: before})
        self._compositions[key] = result
        self.ledger.bump("composition_evaluations")
        return result

    def apply(
        self, function: TransferSummaryID, inputs: Mapping[PortVariable, bool]
    ) -> bool:
        index = self._resolve(function)
        if any(type(value) is not bool for value in inputs.values()):
            raise TypeError("finite-port observations require Boolean values")
        self.ledger.bump("finite_port_applications")
        while index >= 2:
            self.ledger.bump("finite_port_decision_visits")
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
        self._resolve(function)
        return self.substitute(
            function, {old: self.variable(new) for old, new in permutation.items()}
        )

    def cut(self, outputs: Mapping[PortVariable, TransferSummaryID]) -> FoldedPortCut:
        for function in outputs.values():
            self._resolve(function)
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
            self._resolve(component.function)
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
