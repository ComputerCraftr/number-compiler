"""Bind decimal kernel ports to executable output and next-carry functions."""

from __future__ import annotations

from collections.abc import Callable

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReverseRightTransfer,
)
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
SYMBOL = FinitePort(PortVariable(0, 0, "reverse-producer-symbol", 0), 20)
LEFT_STATE = AtomSort("primitive-left-state", 43)
RIGHT_STATE = AtomSort("primitive-right-state", 5)
CHANNEL_SYMBOL = AtomSort("primitive-symbol", 20)
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
        self._channel_templates: OwnedMemo[int, tuple[FactoredFunctionID, ...]] = (
            OwnedMemo(
                self.ledger,
                self.ledger.register(
                    f"reverse-symbolic-channels-{len(self.ledger.inventory())}",
                    "query_memo",
                ),
                evictable=True,
            )
        )
        self._channel_seals: OwnedMemo[int, tuple[FactoredFunctionID, ...]] = OwnedMemo(
            self.ledger,
            self.ledger.register(
                f"reverse-symbolic-channel-seals-{len(self.ledger.inventory())}",
                "query_memo",
            ),
            evictable=True,
        )

    def pullback_channels(
        self,
        symbol: FactoredFunctionID,
        left: FactoredFunctionID,
        right: FactoredFunctionID,
    ) -> tuple[FactoredFunctionID, ...]:
        """Substitute a symbolic cell and both ports through all local channels.

        The argument functions share a frozen source environment; no argument
        is evaluated or substituted into another. The result order is
        ``COMPONENT_ROLES`` for the existing reverse leaf contract. In this
        local contract extent/growth are activity predicates, not whole-word
        lengths or accumulated temporal growth. This is local semantic closure,
        not a constructor for recursive temporal intervals.
        """
        for function, sort in (
            (symbol, CHANNEL_SYMBOL),
            (left, LEFT_STATE),
            (right, RIGHT_STATE),
        ):
            if self.bits.resolve(function).signature.output != sort:
                raise ValueError("symbolic reverse pullback has another channel sort")
        return self.bits.substitute_many(
            self._symbolic_channels(),
            {SYMBOL.variable: symbol, LEFT.variable: left, RIGHT.variable: right},
        )

    def _symbolic_channels(self) -> tuple[FactoredFunctionID, ...]:
        """Lift the bounded primitive alphabet without enumerating source states."""
        cached = self._channel_templates.get(0)
        seal = self._channel_seals.get(0)
        if (cached is None) != (seal is None):
            raise ValueError(
                "symbolic reverse channel template has incomplete publication"
            )
        if cached is not None:
            if cached != seal:
                raise ValueError(
                    "symbolic reverse channel template changed after publication"
                )
            for function in cached:
                self.bits.resolve(function)
            return cached
        bits, codec = self.bits, ReversePortCodec(10)
        inputs = tuple(sorted((*PORTS, SYMBOL), key=lambda port: port.variable))
        symbol = bits.variable(inputs, SYMBOL, CHANNEL_SYMBOL)
        left_port = bits.variable(PORTS, LEFT, LEFT_STATE)
        right_port = bits.variable(PORTS, RIGHT, RIGHT_STATE)
        # Each branch is one existing primitive law. Only the fixed alphabet
        # and the two unary boundary domains are inspected, never their product
        # or the caller's source assignments.
        roots: tuple[FactoredFunctionID, ...] = ()
        for value in reversed(range(20)):
            self.ledger.bump("reverse_symbolic_channel_alphabet_branches")
            left = ReverseLeftTransfer.leaf(10, value)
            right = ReverseRightTransfer.leaf(10, value)
            branches = (
                bits.map_atoms(
                    left_port,
                    LEFT_STATE,
                    tuple(
                        codec.encode_left(left.apply(codec.decode_left(i)))
                        for i in range(43)
                    ),
                ),
                bits.map_atoms(
                    right_port,
                    RIGHT_STATE,
                    tuple(
                        codec.encode_right(right.apply(codec.decode_right(i)))
                        for i in range(5)
                    ),
                ),
                bits.map_atoms(
                    self._compile_leaf(value), CHANNEL_SYMBOL, tuple(range(20))
                ),
            )
            condition = bits.map_atoms(
                symbol, BOOL, tuple(int(i == value) for i in range(20))
            )
            if not roots:
                # Import the full three-port domain even for constant branches.
                roots = tuple(bits.select(condition, f, f) for f in branches)
            else:
                roots = tuple(
                    bits.select(condition, f, other)
                    for f, other in zip(branches, roots, strict=True)
                )
        forward, backward, output = roots
        active = bits.map_atoms(output, BOOL, tuple(int(i != 19) for i in range(20)))
        inactive = bits.map_atoms(active, BOOL, (1, 0))
        zero = bits.constant(FunctionSignature(inputs, BOOL), 0)
        result = (
            forward,
            backward,
            output,
            active,
            active,
            active,
            active,
            output,
            output,
            active,
            inactive,
            zero,
            zero,
        )
        try:
            # Copy handle metadata: mutating a supposedly frozen cached handle
            # must not also mutate its publication witness through aliasing.
            self._channel_seals[0] = tuple(
                FactoredFunctionID(f.owner, f.kind, f.local_id) for f in result
            )
            self._channel_templates[0] = result
        except BaseException:
            self._channel_seals.clear()
            raise
        return result

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
        value = self._compile_leaf(symbol)
        self._leaves[symbol] = value
        self.ledger.bump("reverse_primitive_output_morphism_compilations")
        return value

    def _compile_leaf(self, symbol: int) -> FactoredFunctionID:
        """Build the shared local law without retaining an alphabet lookup table."""
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
        return value
