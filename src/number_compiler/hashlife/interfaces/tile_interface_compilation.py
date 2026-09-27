"""Store-free tile interface compilation operations."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockEffect,
    BoundarySide,
    _effect_key,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.radix_division import (
    SymbolicBinaryDivisionEffect,
    certified_binary_division_radix,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.tile_fused_kernel import (
    leaf_product as _leaf_product,
)
from number_compiler.hashlife.interfaces.diamond_kernel import (
    PrimitiveKernel,
)
from number_compiler.hashlife.interfaces.diamond_quotient import (
    LocalInterfaceID,
    MacroInterface,
)
from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
    differs_from_constant,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    FactoredFunctionID,
    _Circuit,
)
from number_compiler.hashlife.tiles.tile_context import TemporalCocycle
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import (
    PoweredInterfaceKey,
)
from number_compiler.hashlife.tiles.tiles import (
    TileID,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )


def _tabulated(
    self: PrimitiveTileKernelAdapter,
    ports: tuple[FinitePort, ...],
    output: AtomSort,
    active: tuple[FinitePort, ...],
    table: tuple[int, ...],
) -> FactoredFunctionID:
    """Compile one source-bound finite law without a whole alphabet product."""
    expected = 1
    for port in active:
        expected *= port.cardinality
    if len(table) != expected:
        raise ValueError("finite source-bound table has another domain")
    circuit = _Circuit(self.quotients.functions, ports)
    variables = tuple(
        PortVariable(port.variable.time, port.variable.side, port.variable.role, bit)
        for port in active
        for bit in range(port.bits)
    )
    pending: list[tuple[int, tuple[int, ...], bool]] = [
        (
            0,
            (0,) * len(active),
            False,
        )
    ]
    values: list[tuple[int, ...]] = []
    while pending:
        depth, inputs, ready = pending.pop()
        if depth == len(variables):
            if any(
                value >= port.cardinality
                for value, port in zip(inputs, active, strict=True)
            ):
                values.append(
                    tuple(
                        circuit.zero
                        for _ in range((output.cardinality - 1).bit_length())
                    )
                )
            else:
                index = 0
                for value, port in zip(inputs, active, strict=True):
                    index = index * port.cardinality + value
                answer = table[index]
                values.append(
                    tuple(
                        circuit.one if answer & (1 << bit) else circuit.zero
                        for bit in range((output.cardinality - 1).bit_length())
                    )
                )
            continue
        if ready:
            high, low = values.pop(), values.pop()
            values.append(
                tuple(
                    circuit.tx.decision(circuit.signature, variables[depth], a, b)
                    for a, b in zip(low, high, strict=True)
                )
            )
            continue
        port_index = next(
            index
            for index, port in enumerate(active)
            if port.variable.side == variables[depth].side
            and port.variable.role == variables[depth].role
        )
        updated = tuple(
            value | (1 << variables[depth].bit) if index == port_index else value
            for index, value in enumerate(inputs)
        )
        pending.extend(
            (
                (depth, inputs, True),
                (depth + 1, updated, False),
                (depth + 1, inputs, False),
            )
        )
    if len(values) != 1:
        raise AssertionError("source-bound function produced multiple roots")
    result = circuit.normalized(
        FunctionSignature(ports, output),
        values[0],
        circuit.admitted(),
    )
    return self.bits._publish(circuit, (result,))[0]


def _leaf_components(
    self: PrimitiveTileKernelAdapter,
    kernel: PrimitiveKernel,
    symbol: int,
) -> tuple[FactoredFunctionID, ...]:
    from number_compiler.hashlife.execution.tile_kernel import _LEFT, _RIGHT

    if certified_binary_division_radix(kernel.effect) is not None:
        raise TypeError("radix leaves require the bounded arithmetic interface")

    ports = self._ports(kernel)
    left_port = next(port for port in ports if port.variable == _LEFT)
    right_port = next(port for port in ports if port.variable == _RIGHT)
    left_sort, right_sort, symbol_sort = self._output_sorts(kernel)[:3]
    assert type(left_sort) is AtomSort and type(right_sort) is AtomSort
    assert type(symbol_sort) is AtomSort
    advance_left = self._tabulated(
        ports,
        left_sort,
        (left_port,),
        tuple(
            kernel.advance(BoundarySide.LEFT, state, symbol)
            for state in range(kernel.left_count)
        ),
    )
    advance_right = self._tabulated(
        ports,
        right_sort,
        (right_port,),
        tuple(
            kernel.advance(BoundarySide.RIGHT, state, symbol)
            for state in range(kernel.right_count)
        ),
    )
    if type(kernel.effect) is CollatzPhysicalBlockEffect:
        from number_compiler.sequences.collatz.physical_output_quotient import (
            collatz_physical_leaf_output,
        )

        output = collatz_physical_leaf_output(
            self.bits,
            kernel,
            symbol,
            ports,
            left_port,
            right_port,
            symbol_sort,
        )
    elif type(kernel.effect) is BaseBlockEffect and kernel.effect.base == 10:
        from number_compiler.hashlife.interfaces.tile_decimal_functions import (
            decimal_leaf_output,
        )

        output = decimal_leaf_output(
            self.bits,
            kernel,
            symbol,
            ports,
            left_port,
            right_port,
            symbol_sort,
        )
        self.ledger.bump("decimal_tile_factored_output_compilations")
    else:
        output = self._tabulated(
            ports,
            symbol_sort,
            (left_port, right_port),
            tuple(
                kernel.emit(left, symbol, right)
                for left in range(kernel.left_count)
                for right in range(kernel.right_count)
            ),
        )
    return self._finish(
        kernel,
        advance_left,
        advance_right,
        output,
        self._nonblank(output, kernel.blank),
    )


def _parent_components(
    self: PrimitiveTileKernelAdapter,
    kernel: PrimitiveKernel,
    left_interface: LocalInterfaceID,
    right_interface: LocalInterfaceID,
) -> tuple[FactoredFunctionID, ...]:
    from number_compiler.hashlife.execution.tile_kernel import _LEFT, _RIGHT

    ports = self._ports(kernel)
    left_sort, right_sort = self._output_sorts(kernel)[:2]
    assert type(left_sort) is AtomSort and type(right_sort) is AtomSort
    incoming_left = self._variable(ports, _LEFT, left_sort)
    incoming_right = self._variable(ports, _RIGHT, right_sort)
    aa0, bb0 = self._components(left_interface), self._components(right_interface)

    def lift(
        function: FactoredFunctionID,
        low: FactoredFunctionID,
        high: FactoredFunctionID,
    ) -> FactoredFunctionID:
        # Small primitive interfaces have at most nine Boolean inputs.
        # Ordinary reduced-BDD substitution avoids constructing correlated
        # environments there; it does not enumerate the finite domain.
        # Larger interfaces retain joint cofactoring to control temporary
        # ITE growth. Both routes publish the same extensional function.
        return self.bits.substitute(
            function,
            {_LEFT: low, _RIGHT: high},
            # Division's 64-bit remainder law is already a compact arithmetic
            # circuit. Joint cofactoring treats its correlated bit-vector as
            # a Cartesian truth domain and causes exponential construction.
            # Ordinary reduced-DAG substitution preserves the same function.
            joint=(
                certified_binary_division_radix(kernel.effect) is None
                and sum(port.bits for port in ports) > 9
            ),
        )

    # Both midpoint maps already use this parent's unbound input ports.
    # Substituting the identity variables rebuilds exactly these functions,
    # including their validity masks, before discovering the same canonical ID.
    # Check their complete signatures and reuse them before that work.
    if self.bits.resolve(aa0[0]).signature != FunctionSignature(
        ports, left_sort
    ) or self.bits.resolve(bb0[1]).signature != FunctionSignature(ports, right_sort):
        raise ValueError("spatial midpoint function has another port signature")
    left_mid, right_mid = aa0[0], bb0[1]
    self.ledger.bump("tile_spatial_identity_substitutions_elided", 2)
    # Only seven child channels survive the parent projection.  Rewriting
    # all thirteen channels used to perform nineteen discarded decision-
    # DAG substitutions per new spatial effect.
    a_right = lift(aa0[1], incoming_left, right_mid)
    a_output = lift(aa0[2], incoming_left, right_mid)
    a_active = lift(aa0[3], incoming_left, right_mid)
    a_halo_left = lift(aa0[7], incoming_left, right_mid)
    b_left = lift(bb0[0], left_mid, incoming_right)
    b_active = lift(bb0[3], left_mid, incoming_right)
    b_halo_right = lift(bb0[8], left_mid, incoming_right)
    one = self._constant(ports, BOOL, 1)
    active = self.bits.select(a_active, one, b_active)
    # The scalar output channel denotes the left edge for an interval;
    # exact interval output is exclusively the CompletedResult TileID.
    return self._finish(
        kernel,
        b_left,
        a_right,
        a_output,
        active,
        a_halo_left,
        b_halo_right,
        a_active,
        b_active,
    )


def _compile_interface(
    self: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    source: TileID,
    wiring: ResultWiring,
) -> LocalInterfaceID:
    record = self._action(action)
    if record.children is not None:
        raise ValueError("composed tile actions require the complete temporal executor")
    if (
        wiring.signature != record.signature
        or wiring.orientation != 0
        or wiring.phase != 0
    ):
        raise ValueError("primitive tile adapter supports its forward wiring")
    results = self._require_results()
    root_key = PoweredInterfaceKey(action, source, wiring)
    found = results.lookup_interface(root_key)
    if found is not None:
        return found
    kernel = self.kernels.kernel(record.kernel)
    stack: list[tuple[TileID, bool]] = [(source, False)]
    built: dict[TileID, LocalInterfaceID] = {}
    while stack:
        current, ready = stack.pop()
        if current in built:
            continue
        key = PoweredInterfaceKey(action, current, wiring)
        cached = results.lookup_interface(key)
        if cached is not None:
            built[current] = cached
            continue
        node = self.tiles.resolve(current)
        if node.level and not ready:
            if node.left is None or node.right is None:
                raise ValueError("malformed canonical tile parent")
            stack.extend(((current, True), (node.right, False), (node.left, False)))
            continue
        if node.level:
            assert node.left is not None and node.right is not None
            from number_compiler.hashlife.execution.tile_causal_interfaces import (
                combine_local_interfaces,
            )

            # The shared composer owns both the early probe and publication.
            # Publishing again counted our own fresh result as a late alias.
            interface = combine_local_interfaces(
                results,
                action,
                built[node.left],
                built[node.right],
                wiring,
            )
        else:
            if node.symbol is None:
                raise ValueError("malformed canonical tile leaf")
            alphabet = self.tiles.alphabet(node.alphabet)
            if (
                alphabet.symbol_count != kernel.blank + 1
                or alphabet.blank != kernel.blank
                or alphabet.radix != kernel.base
            ):
                raise ValueError("tile alphabet differs from primitive kernel")
            interface = _leaf_product(self, action, node.symbol, wiring)
        published = results.publish_interface(key, interface)
        built[current] = published
        self.ledger.bump("primitive_tile_interface_publications")
    return built[source]


def _signature(
    self: PrimitiveTileKernelAdapter,
    kernel: PrimitiveKernel,
    effect: BlockEffect,
) -> PortSignatureID:
    from number_compiler.hashlife.execution.tile_kernel import _CONTRACT

    ports = self._ports(kernel)
    outputs = self._output_sorts(kernel)
    division_radix = certified_binary_division_radix(effect)
    behavior = (
        _CONTRACT,
        SymbolicBinaryDivisionEffect(division_radix).canonical_key()
        if division_radix is not None
        else _effect_key(effect),
    )
    identity = SemanticIdentity("tile-interface", behavior)
    admissible = self.quotients.functions.atom(
        FunctionSignature(ports, BOOL),
        1,
    )
    return self.quotients.intern_interface(
        MacroInterface(
            identity,
            ports,
            outputs,
            admissible,
            orientations=(0,),
        )
    )


def _output_sorts(kernel: PrimitiveKernel) -> tuple[AtomSort, ...]:
    left = AtomSort("primitive-left-state", kernel.left_count)
    right = AtomSort("primitive-right-state", kernel.right_count)
    symbol = AtomSort("primitive-symbol", kernel.blank + 1)
    return (
        left,
        right,
        symbol,
        BOOL,
        BOOL,
        BOOL,
        BOOL,
        symbol,
        symbol,
        BOOL,
        BOOL,
        BOOL,
        BOOL,
    )


def _nonblank(
    self: PrimitiveTileKernelAdapter,
    function: FactoredFunctionID,
    blank: int,
) -> FactoredFunctionID:
    return differs_from_constant(self.bits, function, blank)


def _finish(
    self: PrimitiveTileKernelAdapter,
    kernel: PrimitiveKernel,
    left: FactoredFunctionID,
    right: FactoredFunctionID,
    output: FactoredFunctionID,
    active: FactoredFunctionID,
    halo_left: FactoredFunctionID | None = None,
    halo_right: FactoredFunctionID | None = None,
    first_active: FactoredFunctionID | None = None,
    last_active: FactoredFunctionID | None = None,
) -> tuple[FactoredFunctionID, ...]:
    ports = self._ports(kernel)
    zero_bool = self._constant(ports, BOOL, 0)
    one_bool = self._constant(ports, BOOL, 1)
    left_halo = output if halo_left is None else halo_left
    right_halo = output if halo_right is None else halo_right
    first = active if first_active is None else first_active
    last = active if last_active is None else last_active
    termination = self.bits.select(active, zero_bool, one_bool)
    return (
        left,
        right,
        output,
        active,
        first,
        last,
        active,
        left_halo,
        right_halo,
        active,
        termination,
        zero_bool,
        zero_bool,
    )


def _ports(kernel: PrimitiveKernel) -> tuple[FinitePort, ...]:
    from number_compiler.hashlife.execution.tile_kernel import _LEFT, _RIGHT

    return tuple(
        sorted(
            (
                FinitePort(_LEFT, kernel.left_count),
                FinitePort(_RIGHT, kernel.right_count),
            ),
            key=lambda item: item.variable,
        )
    )


def leaf_interface_symbol(
    self: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    symbol: int,
    ports: tuple[int, ...],
    wiring: ResultWiring,
) -> tuple[int, LocalInterfaceID, TemporalCocycle]:
    """Execute one bounded local law without constructing an output tile."""
    self._require_results().validate_shape(action, ports, wiring)
    interface = _leaf_product(self, action, symbol, wiring)
    output = self._observe(interface, "output", ports)
    return (
        output,
        interface,
        self._symbol_observation(action, symbol, interface, ports),
    )


def _symbol_observation(
    self: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    symbol: int,
    interface: LocalInterfaceID,
    ports: tuple[int, ...],
) -> TemporalCocycle:
    record = self._action(action)
    if record.children is not None:
        raise ValueError("leaf observations require one primitive action")
    if self.quotients.resolve(interface).signature != record.signature:
        raise ValueError("leaf observation has another interface signature")
    kernel = self.kernels.kernel(record.kernel)
    if len(ports) != 2:
        raise ValueError("leaf observation has another port tuple")
    if type(kernel.effect) is not CollatzPhysicalBlockEffect:
        return TemporalCocycle()
    odd = int(ports[0] == kernel.initial(BoundarySide.LEFT) and symbol == 1)
    return TemporalCocycle(0, odd, 0)
