"""Complete binary division actions fused with an original source or one C step.

The interface has a physical carry, one formal carry per division, and a
coordinate. Spatial composition substitutes entire Boolean functions. No
realized division-state vector or array of future output functions is retained.
"""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import dataclass

from number_compiler.arithmetic.functions.finite_function_types import (
    FinitePort,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)
from number_compiler.hashlife.interfaces.semantic_bits import BooleanCircuit
from number_compiler.hashlife.interfaces.semantic_publication import prepare_functions
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import projection as _projection_keys


@dataclass(frozen=True, slots=True)
class FusedRadixBindingKey:
    index: int

    def __post_init__(self) -> None:
        if type(self.index) is not int or not 0 <= self.index < 4:
            raise ValueError("fused division binding requires a supported digit index")


@dataclass(frozen=True, slots=True)
class FusedDivisionAction:
    radix: int
    stages: int
    level: int
    physical: bool
    ports: tuple[FinitePort, ...]
    physical_exit: tuple[SemanticFunctionID, ...]
    division_exit: tuple[tuple[SemanticFunctionID, ...], ...]
    output: SemanticFunctionID
    active: SemanticFunctionID
    valid: SemanticFunctionID


@dataclass(frozen=True, slots=True)
class _BuildingAction:
    level: int
    physical_exit: tuple[int, ...]
    division_exit: tuple[tuple[int, ...], ...]
    output: int
    active: int


class FusedRadixArena:
    """One ledger-owned semantic arena; source association stays in its caller."""

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.functions = SemanticFunctionArena(ledger)
        self.owner = ledger.register(
            f"fused-radix-{len(ledger.inventory())}", "radix_fused_action"
        )
        self.actions: MutableMapping[FusedDivisionAction, FusedDivisionAction] = (
            ledger.make_dict(self.owner, nodes_per_entry=1)
        )
        ledger.register_execution_root(self)

    def compile(
        self,
        source: tuple[int, ...],
        *,
        radix: int,
        stages: int,
        physical: bool,
        shift: int = 0,
    ) -> FusedDivisionAction:
        if (
            type(source) is not tuple
            or not source
            or any(type(bit) is not int or bit not in (0, 1) for bit in source)
            or type(radix) is not int
            or not 2 <= radix <= 12
            or type(stages) is not int
            or not 1 <= stages <= 4
            or type(physical) is not bool
            or type(shift) is not int
            or shift not in (0, 1)
            or (physical and shift)
        ):
            raise ValueError("unsupported fused original-source division interface")
        level = (len(source) + 1).bit_length()
        count = 1 << level
        ports = (
            FinitePort(PortVariable(0, 0, "radix-physical", 0), 3),
            *(
                FinitePort(PortVariable(stage + 1, 1, "radix-carry", 0), radix)
                for stage in range(stages)
            ),
            FinitePort(PortVariable(stages + 1, 0, "radix-coordinate", 0), count),
        )
        circuit = BooleanCircuit(self.functions, ports)
        variables = tuple(
            tuple(
                circuit.tx.bit(
                    ports,
                    PortVariable(
                        port.variable.time, port.variable.side, port.variable.role, bit
                    ),
                )
                for bit in range(port.bits)
            )
            for port in ports
        )
        carry, divisions = variables[0], variables[1:-1]
        leaves: dict[int, _BuildingAction] = {}
        joins: dict[tuple[_BuildingAction, _BuildingAction], _BuildingAction] = {}
        stack: list[_BuildingAction] = []
        # These are original-source reads, not a physical generation loop.
        for position in range(count):
            source_position = position + shift
            self.ledger.bump(_projection_keys.RADIX_FUSED_SPATIAL_LEAF_VISITS)
            if source_position < len(source):
                self.ledger.bump(_projection_keys.RADIX_FUSED_ORIGINAL_SOURCE_READS)
            symbol = source[source_position] if source_position < len(source) else 0
            leaf = leaves.get(symbol)
            if leaf is None:
                leaf = self._leaf(circuit, symbol, physical, radix, carry, divisions)
                leaves[symbol] = leaf
            stack.append(leaf)
            while len(stack) >= 2 and stack[-1].level == stack[-2].level:
                right, left = stack.pop(), stack.pop()
                key = (left, right)
                parent = joins.get(key)
                if parent is None:
                    parent = self._join(circuit, ports, left, right)
                    joins[key] = parent
                else:
                    self.ledger.bump(
                        _projection_keys.RADIX_FUSED_PARENT_CONSTRUCTION_HITS
                    )
                stack.append(parent)
            self.ledger.bump(
                _projection_keys.RADIX_FUSED_PARENT_RECORDS_PEAK,
                max(
                    0,
                    len(stack)
                    + len(joins)
                    + len(leaves)
                    - self.ledger.counters.get(
                        _projection_keys.RADIX_FUSED_PARENT_RECORDS_PEAK, 0
                    ),
                ),
            )
            self.ledger.bump(
                _projection_keys.RADIX_FUSED_PARENT_STACK_PEAK,
                max(
                    0,
                    len(stack)
                    - self.ledger.counters.get(
                        _projection_keys.RADIX_FUSED_PARENT_STACK_PEAK, 0
                    ),
                ),
            )
        result = stack[0]
        valid = circuit.admitted()
        raw = (
            *result.physical_exit,
            *(bit for component in result.division_exit for bit in component),
            result.output,
            result.active,
        )
        roots = (*tuple(circuit.conjunction(valid, bit) for bit in raw), valid)
        prepared = None
        try:
            prepared = prepare_functions(circuit.tx, roots)
            offset = 2
            physical_exit = prepared.roots[:offset]
            division_exit: list[tuple[SemanticFunctionID, ...]] = []
            for port in ports[1:-1]:
                division_exit.append(prepared.roots[offset : offset + port.bits])
                offset += port.bits
            record = FusedDivisionAction(
                radix,
                stages,
                level,
                physical,
                ports,
                physical_exit,
                tuple(division_exit),
                prepared.roots[-3],
                prepared.roots[-2],
                prepared.roots[-1],
            )
            existing = self.actions.get(record)
            if existing is not None:
                return existing
            prepared.reserve_with(((self.owner, 1, 1),))
            prepared.publish_reserved()
            self.actions[record] = record
            self.ledger.bump(_projection_keys.RADIX_FUSED_ACTIONS_PUBLISHED)
            return record
        finally:
            if prepared is None:
                circuit.tx.close()
            else:
                prepared.cancel()

    def _leaf(
        self,
        c: BooleanCircuit,
        symbol: int,
        physical: bool,
        radix: int,
        carry: tuple[int, ...],
        divisions: tuple[tuple[int, ...], ...],
    ) -> _BuildingAction:
        if physical:
            add = 3 * symbol
            pending = c.zero
            total: list[int] = []
            for bit in range(3):
                left = carry[bit] if bit < 2 else c.zero
                right = c.one if (add >> bit) & 1 else c.zero
                parity = c.xor(left, right)
                total.append(c.xor(parity, pending))
                pending = c.choose(parity, pending, left)
            output, physical_exit = total[0], tuple(total[1:])
        else:
            output, physical_exit = c.one if symbol else c.zero, carry
        exits: list[tuple[int, ...]] = []
        active = output
        for incoming in divisions:
            active = output
            total_bits = (output, *incoming)
            difference, below = c.subtract_constant(total_bits, radix)
            quotient = c.negate(below)
            exits.append(
                tuple(
                    c.choose(quotient, difference[bit], total_bits[bit])
                    for bit in range(len(incoming))
                )
            )
            output = quotient
        self.ledger.bump(_projection_keys.RADIX_FUSED_LEAF_COMPILATIONS)
        return _BuildingAction(0, physical_exit, tuple(exits), output, active)

    def _join(
        self,
        c: BooleanCircuit,
        ports: tuple[FinitePort, ...],
        left: _BuildingAction,
        right: _BuildingAction,
    ) -> _BuildingAction:
        replacements = self._bindings(ports[:1], (left.physical_exit,))
        right_roots = self._substitute(
            c,
            (
                *right.physical_exit,
                *(bit for component in right.division_exit for bit in component),
                right.output,
                right.active,
            ),
            replacements,
        )
        right_physical = right_roots[:2]
        width = len(right.division_exit[0])
        right_divisions = tuple(
            right_roots[2 + index * width : 2 + (index + 1) * width]
            for index in range(len(right.division_exit))
        )
        right_output, right_active = right_roots[-2:]
        left_bindings = self._bindings(ports[1:-1], right_divisions)
        left_roots = self._substitute(
            c,
            (
                *(bit for component in left.division_exit for bit in component),
                left.output,
                left.active,
            ),
            left_bindings,
        )
        exits = tuple(
            left_roots[index * width : (index + 1) * width]
            for index in range(len(left.division_exit))
        )
        left_output, left_active = left_roots[-2:]
        coordinate = ports[-1].variable
        select = c.tx.bit(
            ports,
            PortVariable(coordinate.time, coordinate.side, coordinate.role, left.level),
        )
        output = c.choose(select, right_output, left_output)
        active = c.choose(right_active, c.one, left_active)
        self.ledger.bump(_projection_keys.RADIX_FUSED_PARENT_COMPOSITIONS)
        return _BuildingAction(left.level + 1, right_physical, exits, output, active)

    def _substitute(
        self,
        c: BooleanCircuit,
        roots: tuple[int, ...],
        replacements: dict[PortVariable, int],
    ) -> tuple[int, ...]:
        pending = [(root, False) for root in roots]
        done: dict[int, int] = {}
        while pending:
            self.ledger.bump(
                _projection_keys.RADIX_FUSED_SUBSTITUTION_WORKSPACE_PEAK,
                max(
                    0,
                    len(pending)
                    + len(done)
                    - self.ledger.counters.get(
                        _projection_keys.RADIX_FUSED_SUBSTITUTION_WORKSPACE_PEAK, 0
                    ),
                ),
            )
            identity, ready = pending.pop()
            self.ledger.bump(_projection_keys.RADIX_FUSED_SUBSTITUTION_FRAMES)
            if identity in done:
                continue
            node = c.tx.node(identity)
            self.ledger.bump(_projection_keys.RADIX_FUSED_SUBSTITUTION_VISITS)
            if node.terminal is not None:
                done[identity] = identity
                continue
            assert node.variable is not None
            condition = replacements.get(node.variable)
            if condition is None:
                condition = c.tx.bit(c.inputs, node.variable)
            if condition in (c.zero, c.one):
                child = node.high if condition == c.one else node.low
                if child in done:
                    done[identity] = done[child]
                else:
                    pending.extend(((identity, True), (child, False)))
            elif ready:
                done[identity] = c.choose(condition, done[node.high], done[node.low])
            else:
                pending.extend(
                    ((identity, True), (node.high, False), (node.low, False))
                )
        return tuple(done[root] for root in roots)

    @staticmethod
    def _bindings(
        ports: tuple[FinitePort, ...], components: tuple[tuple[int, ...], ...]
    ) -> dict[PortVariable, int]:
        return {
            PortVariable(
                port.variable.time, port.variable.side, port.variable.role, bit
            ): value
            for port, component in zip(ports, components, strict=True)
            for bit, value in enumerate(component)
        }

    def digit(self, action: FusedDivisionAction) -> int:
        if (
            type(action) is not FusedDivisionAction
            or self.actions.get(action) is not action
        ):
            raise ValueError("fused action belongs to another arena")
        inputs = {port.variable: 0 for port in action.ports}
        inputs[action.ports[0].variable] = int(action.physical)
        self.ledger.bump(_projection_keys.RADIX_FUSED_DIGIT_QUERIES)
        if not self.functions.evaluate(action.active, inputs).value:
            raise IndexError(action.stages - 1)
        result = 0
        for bit, function in enumerate(action.division_exit[-1]):
            shifted = self.ledger.observe_arithmetic(
                self.functions.evaluate(function, inputs).value << bit
            )
            result = self.ledger.observe_arithmetic(result | shifted)
        return result


__all__ = ["FusedDivisionAction", "FusedRadixArena", "FusedRadixBindingKey"]
