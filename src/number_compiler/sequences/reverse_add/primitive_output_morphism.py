"""Bind decimal kernel ports to executable output and next-carry functions."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.carry.reverse_port_functions import ReversePortCodec
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.sequences.reverse_add.active_output import (
    CARRY_ACTION,
    PAIR,
    ReverseActiveOutputArena,
)

CELL = AtomSort("reverse-decimal-cell", 20)
LEFT = FinitePort(PortVariable(0, 0, "reverse-producer-left", 0), 43)
RIGHT = FinitePort(PortVariable(0, 1, "reverse-producer-right", 0), 5)
PORTS = (LEFT, RIGHT)
CARRIES = (CarryFn.CONST0, CarryFn.ID, CarryFn.CONST1)


class ReversePrimitiveOutputMorphism:
    """One source-free local law per bounded source symbol, including blank.

    All producer ports remain parameters. Growth, its edge, and the reflected
    carry response use the existing exact decimal output/control algebra.
    """

    def __init__(
        self, bits: BitFunctionArena, kernel: PrimitiveKernel | None = None
    ) -> None:
        if kernel is not None and (
            type(kernel) is not PrimitiveKernel
            or kernel.ledger is not bits.ledger
            or type(kernel.effect) is not BaseBlockEffect
            or kernel.base != 10
        ):
            raise ValueError("output binding requires this ledger's decimal kernel")
        self.bits = bits
        self.kernel = kernel
        self.active = ReverseActiveOutputArena(bits)
        self.ledger = bits.ledger
        self.ledger.register_execution_root(self)
        owner = self.ledger.register(
            f"reverse-primitive-output-{len(self.ledger.inventory())}", "query_memo"
        )
        self._leaves: OwnedMemo[int, FactoredFunctionID] = OwnedMemo(
            self.ledger, owner, evictable=True
        )

    def bind(self, symbol: int, ports: tuple[int, int]) -> FactoredFunctionID:
        """Specialize known producer ports before building a decision function.

        The scalar finite kernel is the canonical evaluator of the same local
        law (checked exhaustively against ``leaf``). Its result is one bounded
        local literal; no intermediate row or producer recipe is retained.
        """
        if type(ports) is not tuple or len(ports) != 2:
            raise TypeError("output morphism binding requires two finite ports")
        if self.kernel is None:
            raise ValueError("output binding requires an admitted primitive evaluator")
        value = self.kernel.emit(ports[0], symbol, ports[1])
        self.ledger.bump("reverse_primitive_output_morphism_bindings")
        if value == 19:
            return self.bits.constant(FunctionSignature((), CELL), 19)
        output = self.active.resolve(self.active.constant(value))
        return self.bits.map_atoms(output, CELL, tuple(range(19)))

    def constant(self, sort: AtomSort, value: int) -> FactoredFunctionID:
        return self.bits.constant(FunctionSignature(PORTS, sort), value)

    def port_map(
        self, port: FinitePort, sort: AtomSort, law: Callable[[int], int]
    ) -> FactoredFunctionID:
        source = self.bits.variable(PORTS, port)
        return self.bits.map_atoms(
            source, sort, tuple(law(i) for i in range(port.cardinality))
        )

    def leaf(self, symbol: int) -> FactoredFunctionID:
        if type(symbol) is not int or not 0 <= symbol <= 19:
            raise ValueError("decimal output morphism requires a source cell")
        cached = self._leaves.get(symbol)
        if cached is not None:
            return cached
        bits, active, codec = self.bits, self.active, ReversePortCodec(10)
        zero = self.constant(BOOL, 0)
        one = self.constant(PAIR, 1)
        blank = self.constant(CELL, 19)
        previous = self.port_map(
            LEFT, PAIR, lambda i: max(0, codec.decode_left(i).previous_pair)
        )
        if symbol == 19:
            live = self.port_map(
                LEFT,
                BOOL,
                lambda i: int(
                    not codec.decode_left(i).sink
                    and not codec.decode_left(i).blank_seen
                    and codec.decode_left(i).previous_pair >= 0
                    and codec.decode_left(i).carry == 1
                ),
            )
            edge = active.resolve(active.pair(previous, zero, one, zero))
            value = bits.select(
                live, bits.map_atoms(edge, CELL, tuple(range(19))), blank
            )
        else:
            source = self.constant(PAIR, symbol)
            carry = self.port_map(LEFT, BOOL, lambda i: codec.decode_left(i).carry)
            forward = self.port_map(
                RIGHT,
                CARRY_ACTION,
                lambda i: CARRIES.index(codec.decode_right(i).forward_suffix),
            )
            backward = self.port_map(
                RIGHT,
                CARRY_ACTION,
                lambda i: CARRIES.index(codec.decode_right(i).backward_suffix),
            )
            action = active.carry_action(active.intern(source))
            final = active.carry_apply(forward, active.carry_apply(action, carry))
            reflected = active.carry_apply(backward, zero)
            reflected_previous = active.carry_apply(
                active.carry_then(backward, action), zero
            )
            no_growth = active.resolve(active.pair(source, carry, source, reflected))
            interior = active.resolve(
                active.pair(source, carry, previous, reflected_previous)
            )
            edge = active.resolve(active.pair(source, zero, one, zero))
            has_previous = self.port_map(
                LEFT, BOOL, lambda i: int(codec.decode_left(i).previous_pair >= 0)
            )
            pair = bits.select(
                final, bits.select(has_previous, interior, edge), no_growth
            )
            sink = self.port_map(LEFT, BOOL, lambda i: int(codec.decode_left(i).sink))
            value = bits.select(
                sink, blank, bits.map_atoms(pair, CELL, tuple(range(19)))
            )
        self._leaves[symbol] = value
        self.ledger.bump("reverse_primitive_output_morphism_compilations")
        return value
