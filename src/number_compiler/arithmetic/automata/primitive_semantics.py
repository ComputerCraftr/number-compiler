"""Complete primitive transfer/output functions, not spatial macro quotients.

Only an already admitted primitive interface is expanded. Semantic decisions
contain no source, coordinate, output word, or retained evaluation callback.
"""

from __future__ import annotations

from array import array
from dataclasses import dataclass
from typing import Literal

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
    BlockEffect,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import FiniteBlockEffect
from number_compiler.arithmetic.contracts.kernel_admission import immutable_atom
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
    SemanticTerminal,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_function_transactions import (
    _Transaction,
)
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    PrimitiveKernel,
)
from number_compiler.hashlife.interfaces.semantic_publication import prepare_functions
from number_compiler.resources.ledger import OwnedMemo


@dataclass(frozen=True, slots=True)
class PrimitiveSemantics:
    """Source-free primitive laws with the original kernel interpretation.

    Blank tails are definition metadata, not a derived macrocell halo proof.
    The output function includes the blank symbol and every primitive state.
    """

    kernel: ActionProgramID
    ports: tuple[FinitePort, FinitePort, FinitePort]
    left_sort: AtomSort
    symbol_sort: AtomSort
    right_sort: AtomSort
    initial_left: int
    initial_right: int
    base: int
    blank: int
    blank_left_tail: int
    blank_right_tail: int
    stable_blank_output: bool
    advance_left: SemanticFunctionID
    advance_right: SemanticFunctionID
    emit: SemanticFunctionID


class PrimitiveSemanticsAdapter:
    """Compile fixed primitive kernels into one shared semantic function arena."""

    def __init__(
        self, kernels: DiamondKernelArena, functions: SemanticFunctionArena
    ) -> None:
        if kernels.ledger is not functions.ledger:
            raise ValueError("primitive and semantic arenas must share one ledger")
        self.kernels, self.functions, self.ledger = kernels, functions, kernels.ledger
        self.ledger.register_execution_root(self)
        prefix = f"primitive-semantics-{len(self.ledger.inventory())}"
        self.records: OwnedMemo[ActionProgramID, PrimitiveSemantics] = OwnedMemo(
            self.ledger, self.ledger.register(prefix, "primitive_semantics")
        )

    def compile(self, effect: BlockEffect | ActionProgramID) -> PrimitiveSemantics:
        if isinstance(effect, ActionProgramID):
            kernel = self.kernels.kernel(effect)
            handle = effect
        else:
            definition = immutable_atom(effect)
            handle = self.kernels.intern(definition)
            kernel = self.kernels.kernel(handle)
        found = self.records.get(handle)
        if found is not None:
            self.ledger.bump("primitive_semantics_cache_hits")
            return found
        # A record needs one entry even when every function already exists.
        # This read-only preflight preserves rejection before avoidable work.
        limit = self.ledger.max_cache_entries
        if limit is not None and self.ledger.entries >= limit:
            raise BlockContextBudgetExceeded(
                "primitive semantics needs one record entry"
            )
        ports = (
            FinitePort(PortVariable(0, 0, "primitive-left", 0), kernel.left_count),
            FinitePort(PortVariable(0, 0, "primitive-symbol", 0), kernel.blank + 1),
            FinitePort(PortVariable(0, 1, "primitive-right", 0), kernel.right_count),
        )
        left = AtomSort("primitive-left-state", kernel.left_count)
        symbol = AtomSort("primitive-symbol", kernel.blank + 1)
        right = AtomSort("primitive-right-state", kernel.right_count)
        transaction = _Transaction(self.functions)
        prepared = None
        try:
            roots = (
                self._build(transaction, kernel, ports, left, "left"),
                self._build(transaction, kernel, ports, right, "right"),
                self._build(transaction, kernel, ports, symbol, "emit"),
            )
            prepared = prepare_functions(transaction, roots)
            advance_left, advance_right, emit = prepared.roots
            record = PrimitiveSemantics(
                handle,
                ports,
                left,
                symbol,
                right,
                kernel.initial(BoundarySide.LEFT),
                kernel.initial(BoundarySide.RIGHT),
                kernel.base,
                kernel.blank,
                kernel.effect.blank_left_tail,
                kernel.effect.blank_right_tail,
                kernel.effect.stable_blank_output,
                advance_left,
                advance_right,
                emit,
            )
            prepared.reserve_with(((self.records.owner, 1, 0),))
            prepared.publish_reserved()
            self.records._data[handle] = record
            self.ledger.bump("primitive_semantics_compilations")
            return record
        finally:
            if prepared is None:
                transaction.close()
            else:
                prepared.cancel()

    def _build(
        self,
        transaction: _Transaction,
        kernel: PrimitiveKernel,
        ports: tuple[FinitePort, FinitePort, FinitePort],
        output: AtomSort,
        operation: Literal["left", "right", "emit"],
    ) -> int:
        active = (
            (0, 1)
            if operation == "left"
            else (1, 2)
            if operation == "right"
            else (0, 1, 2)
        )
        bits = tuple(
            (index, bit) for index in active for bit in range(ports[index].bits)
        )
        variables = tuple(
            PortVariable(
                ports[index].variable.time,
                ports[index].variable.side,
                ports[index].variable.role,
                bit,
            )
            for index, bit in bits
        )
        signature = FunctionSignature(ports, output)
        pending = [(0, (0, 0, 0), False)]
        results: list[int] = []
        terminals: dict[SemanticTerminal, int] = {}
        peak = 1
        while pending:
            depth, values, ready = pending.pop()
            self.ledger.bump("primitive_semantics_synthesis_frames")
            if ready:
                high, low = results.pop(), results.pop()
                results.append(
                    transaction.decision(signature, variables[depth], low, high)
                )
            elif depth == len(bits):
                if any(values[index] >= ports[index].cardinality for index in active):
                    terminal = SemanticTerminal("invalid")
                else:
                    left, symbol, right = values
                    if operation == "left":
                        value = kernel.advance(BoundarySide.LEFT, left, symbol)
                    elif operation == "right":
                        value = kernel.advance(BoundarySide.RIGHT, right, symbol)
                    else:
                        value = kernel.emit(left, symbol, right)
                    terminal = SemanticTerminal("atom", value)
                    self.ledger.bump("primitive_semantics_admissible_evaluations")
                terminal_id = terminals.get(terminal)
                if terminal_id is None:
                    terminal_id = transaction.terminal(signature, terminal)
                    terminals[terminal] = terminal_id
                else:
                    self.ledger.bump("primitive_semantics_terminal_hits")
                results.append(terminal_id)
            else:
                index, bit = bits[depth]
                updated = tuple(
                    value | (1 << bit) if item == index else value
                    for item, value in enumerate(values)
                )
                higher = (updated[0], updated[1], updated[2])
                pending.extend(
                    (
                        (depth, values, True),
                        (depth + 1, higher, False),
                        (depth + 1, values, False),
                    )
                )
            peak = max(peak, len(pending) + len(results))
        result = transaction.admissible(results[0])
        self.ledger.bump(
            "primitive_semantics_workspace_peak",
            max(
                0,
                peak
                - self.ledger.counters.get("primitive_semantics_workspace_peak", 0),
            ),
        )
        self.ledger.bump(
            "primitive_semantics_staged_nodes_peak",
            max(
                0,
                len(transaction.staged)
                - self.ledger.counters.get("primitive_semantics_staged_nodes_peak", 0),
            ),
        )
        return result


def division_witness(radix: int) -> FiniteBlockEffect:
    """Fixed small-radix binary division, scanning right-to-left on LSD cells.

    Symbols 2 and blank 3 pass through and preserve the carry. These witnesses
    prove primitive equations only; they are not general radix query routing.
    """
    if type(radix) is not int or radix not in (3, 6, 12):
        raise ValueError("division witnesses support exactly radix 3, 6, or 12")
    right = array(
        "I",
        (
            (2 * carry + symbol) % radix if symbol < 2 else carry
            for carry in range(radix)
            for symbol in range(4)
        ),
    )
    outputs = bytes(
        (2 * carry + symbol) // radix if symbol < 2 else symbol
        for symbol in range(4)
        for carry in range(radix)
    )
    return FiniteBlockEffect(
        base=2,
        exponent=1,
        left_count=1,
        right_count=radix,
        alphabet_size=4,
        initial_left=0,
        initial_right=0,
        left_transitions=array("I", [0] * 4),
        right_transitions=right,
        outputs=outputs,
        kernel_name=f"binary-division-{radix}",
        storage_bytes=0,
        uncompressed_bytes=0,
        blank_left_tail=0,
        blank_right_tail=0,
        stable_blank_output=True,
    )
