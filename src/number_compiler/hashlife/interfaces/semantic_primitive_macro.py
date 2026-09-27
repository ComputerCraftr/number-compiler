"""Complete primitive behavior for the explicit fixed-padded-cell-v1 adapter.

The thirteen channels mean: complete directional exits; output at coordinate;
any nonblank output; first/last nonblank (width sentinel); active extent;
first/last EDGE SYMBOLS (the channels called halos); signed active-extent change
encoded with bias=width; all-output-blank termination; unchanged output symbols
as normalization; unchanged coordinate as frame. No arithmetic-family trimming,
halting, causal-radius, or normalization certificate is implied by this adapter.

Spatial composition substitutes both midpoint boundaries into child functions.
It never constructs an output word or evaluates a future symbol for a leaf.
"""

from __future__ import annotations

from collections.abc import Generator
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.primitive_semantics import (
    PrimitiveSemantics,
    PrimitiveSemanticsAdapter,
)
from number_compiler.arithmetic.contracts.block_effect import _effect_key
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.diamond_actions import CellID, ImageCellArena
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
    DiamondQuotientID,
    MacroComponents,
    MacroInterface,
)
from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
    differs_from_constant,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    FactoredFunctionID,
    _Circuit,
)
from number_compiler.hashlife.interfaces.semantic_primitive_tasks import (
    PrimitiveMacroKey,
    PrimitiveMacroObservation,
    PrimitiveMacroTask,
)
from number_compiler.resources.ledger import OwnedMemo

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )
    from number_compiler.hashlife.execution.continuations.diamond_tasks import (
        Result,
        Task,
    )


CONTRACT = (
    "fixed-padded-cell-v1",
    "boundary-exits",
    "coordinate-output",
    "nonblank-activity",
    "first-last:width-sentinel",
    "extent:last+1-or-zero",
    "halos:edge-output-symbols",
    "growth:output-extent-minus-source-extent,bias=width",
    "termination:all-blank",
    "normalization:preserve-symbols-no-trim",
    "frame:identity-coordinate",
)
_LEFT = PortVariable(0, 0, "macro-left", 0)
_RIGHT = PortVariable(0, 1, "macro-right", 0)
_COORDINATE = PortVariable(0, 0, "macro-coordinate", 0)


@dataclass(frozen=True, slots=True)
class PrimitiveMacroBinding:
    quotient: DiamondQuotientID
    original_extent: int  # Original-source metadata; never an observed output.


class PrimitiveMacroArena:
    """Opt-in producer; ordinary family certificates cannot select this contract."""

    def __init__(
        self, runtime: DiamondRuntime, quotients: DiamondQuotientArena
    ) -> None:
        kernels = runtime.kernels
        if (
            runtime.semantic_quotients is not quotients
            or runtime.primitive_macros is not None
        ):
            raise ValueError("primitive macro producer must be the runtime-owned arena")
        if (
            type(quotients) is not DiamondQuotientArena
            or type(kernels) is not DiamondKernelArena
        ):
            raise TypeError("primitive macro needs exact owned semantic arenas")
        if quotients.cells is None or kernels.ledger is not quotients.ledger:
            raise ValueError("primitive macro needs source cells and one owning ledger")
        self.runtime = runtime
        self.quotients, self.kernels, self.cells = quotients, kernels, quotients.cells
        self.structures, self.bits = quotients.structures, quotients.structures.bits
        self.ledger = quotients.ledger
        self.primitives = PrimitiveSemanticsAdapter(kernels, quotients.functions)
        self.bindings: OwnedMemo[PrimitiveMacroKey, PrimitiveMacroBinding] = OwnedMemo(
            self.ledger,
            self.ledger.register(
                f"primitive-macro-bindings-{len(self.ledger.inventory())}",
                "spatial_parent_memo",
            ),
            evictable=True,
        )
        self.ledger.register_execution_root(self)

    def _ports(
        self, primitive: PrimitiveSemantics, width: int
    ) -> tuple[FinitePort, ...]:
        return tuple(
            sorted(
                (
                    FinitePort(_LEFT, primitive.left_sort.cardinality),
                    FinitePort(_RIGHT, primitive.right_sort.cardinality),
                    FinitePort(_COORDINATE, width),
                ),
                key=lambda port: port.variable,
            )
        )

    def _constant(
        self, ports: tuple[FinitePort, ...], output: AtomSort, value: int
    ) -> FactoredFunctionID:
        return self.bits.constant(FunctionSignature(ports, output), value)

    def _variable(
        self, ports: tuple[FinitePort, ...], name: PortVariable, output: AtomSort
    ) -> FactoredFunctionID:
        return self.bits.variable(
            ports, next(port for port in ports if port.variable == name), output
        )

    def _retag(
        self, function: FactoredFunctionID, output: AtomSort
    ) -> FactoredFunctionID:
        node = self.bits.resolve(function)
        circuit = _Circuit(self.quotients.functions, node.signature.inputs)
        roots, valid = circuit.imported(node)
        width = (output.cardinality - 1).bit_length()
        if len(roots) > width:
            raise ValueError("primitive macro numeric conversion would discard bits")
        pending = circuit.normalized(
            FunctionSignature(node.signature.inputs, output),
            roots + (circuit.zero,) * (width - len(roots)),
            valid,
        )
        return self.bits._publish(circuit, (pending,))[0]

    def _offset(
        self, function: FactoredFunctionID, offset: int, output: AtomSort
    ) -> FactoredFunctionID:
        ports = self.bits.resolve(function).signature.inputs
        return self.bits.add(
            self._retag(function, output), self._constant(ports, output, offset), output
        )

    def _nonblank(self, function: FactoredFunctionID, blank: int) -> FactoredFunctionID:
        return differs_from_constant(self.bits, function, blank)

    def _components(
        self, quotient: DiamondQuotientID
    ) -> tuple[FactoredFunctionID, ...]:
        result = []
        for reference in self.quotients.resolve(quotient).components.functions():
            from number_compiler.hashlife.interfaces.semantic_structures import (
                StructureID,
            )

            if type(reference) is not StructureID:
                raise AssertionError(
                    "primitive producer did not publish factored structures"
                )
            atom = self.structures.resolve(reference).atom
            if atom is None:
                raise AssertionError("primitive macro channel is not numeric")
            result.append(atom)
        return tuple(result)

    def compile(self, kernel: ActionProgramID, source: CellID) -> DiamondQuotientID:
        if self.runtime.primitive_macros is not self:
            raise ValueError(
                "primitive macro requests require the runtime-owned producer"
            )
        return self.runtime.compile_primitive_macro(kernel, source)

    def validate_task(self, task: PrimitiveMacroTask) -> None:
        if type(task) is PrimitiveMacroKey:
            validate_primitive_request(self.kernels, self.cells, task)
        elif type(task) is PrimitiveMacroObservation:
            self._observation(task)
        else:
            raise TypeError("unknown primitive macro task")

    def probe(self, task: PrimitiveMacroTask) -> DiamondQuotientID | None:
        self.validate_task(task)
        if type(task) is PrimitiveMacroObservation:
            self.ledger.bump("primitive_macro_observation_requests")
            return None
        assert isinstance(task, PrimitiveMacroKey)
        self.ledger.bump("primitive_macro_requests")
        cached = self.bindings.get(task)
        if cached is not None:
            self.quotients.resolve(cached.quotient)
            self.ledger.bump("primitive_macro_early_hits")
            return cached.quotient
        return None

    def publication(self, task: PrimitiveMacroTask, result: Result) -> None:
        self.validate_task(task)
        if type(task) is PrimitiveMacroObservation:
            function, _ = self._observation(task)
            output = self.bits.resolve(function).signature.output
            if (
                type(result) is not int
                or type(output) is not AtomSort
                or not 0 <= result < output.cardinality
            ):
                raise ValueError(
                    "primitive observation returned a value outside its finite channel"
                )
            return
        assert isinstance(task, PrimitiveMacroKey)
        if type(result) is not DiamondQuotientID:
            raise ValueError("primitive macro publication needs a complete quotient ID")
        self.quotients.resolve(result)
        binding = self.bindings.get(task)
        if binding is None or binding.quotient != result:
            raise ValueError(
                "primitive macro result has not been atomically bound to this source request"
            )
        # The binding was reserved and published with its completed program.

    def program(self, task: PrimitiveMacroTask) -> Generator[Task, Result, Result]:
        self.validate_task(task)
        if type(task) is PrimitiveMacroObservation:
            function, values = self._observation(task)
            result = self.bits.evaluate(function, values)
            if result is None:
                raise AssertionError(
                    "admitted complete macro observation became undefined"
                )
            self.ledger.bump("primitive_macro_observation_evaluations")
            return result
        assert isinstance(task, PrimitiveMacroKey)
        if (
            self.ledger.max_cache_entries is not None
            and self.ledger.entries >= self.ledger.max_cache_entries
        ):
            from number_compiler.arithmetic.contracts.block_effect import (
                BlockContextBudgetExceeded,
            )

            raise BlockContextBudgetExceeded("primitive macro needs a source binding")
        self.ledger.bump("primitive_macro_evaluations")
        self.ledger.bump("primitive_macro_source_frames")
        node = self.cells.require_original(task.source)
        children: tuple[PrimitiveMacroBinding, PrimitiveMacroBinding] | None = None
        if node.level:
            left, right = self.cells.split(task.source)
            left_result = yield PrimitiveMacroKey(task.kernel, left)
            right_result = yield PrimitiveMacroKey(task.kernel, right)
            if (
                type(left_result) is not DiamondQuotientID
                or type(right_result) is not DiamondQuotientID
            ):
                raise ValueError("primitive parent needs complete child quotient IDs")
            self.quotients.resolve(left_result)
            self.quotients.resolve(right_result)
            a, b = (
                self.bindings[PrimitiveMacroKey(task.kernel, cell)]
                for cell in (left, right)
            )
            if a.quotient != left_result or b.quotient != right_result:
                raise ValueError(
                    "primitive child result belongs to another source binding"
                )
            children = a, b
        self.ledger.reserve(self.bindings.owner, entries=1)
        try:
            laws = self.primitives.compile(task.kernel)
            primitive = self.kernels.kernel(task.kernel)
            if children is None:
                channels, extent = self._leaf(
                    laws, self.cells.source_symbol(task.source)
                )
            else:
                channels, extent = self._parent(laws, node.width, *children)
            behavior = (CONTRACT, _effect_key(primitive.effect), node.width)
            identity = SemanticIdentity("primitive-macro", behavior)
            outputs = tuple(
                self.bits.resolve(channel).signature.output for channel in channels
            )
            ports = self._ports(laws, node.width)
            admissible = self.quotients.functions.atom(
                FunctionSignature(ports, BOOL), 1
            )
            interface = self.quotients.intern_interface(
                MacroInterface(identity, ports, outputs, admissible)
            )
            components = MacroComponents(
                *(self.structures.atom(channel) for channel in channels)
            )
            quotient = self.quotients.intern(interface, components)
            self.bindings._data[task] = PrimitiveMacroBinding(quotient, extent)
            self.ledger.bump("primitive_macro_compilations")
        except BaseException:
            self.ledger.release(self.bindings.owner, entries=1)
            raise
        return quotient

    def _observation(
        self, task: PrimitiveMacroObservation
    ) -> tuple[FactoredFunctionID, dict[PortVariable, int]]:
        if (
            type(task) is not PrimitiveMacroObservation
            or type(task.channel) is not str
            or task.channel not in COMPONENT_ROLES
        ):
            raise ValueError("primitive macro observation requires a declared channel")
        record = self.quotients.resolve(task.quotient)
        interface = self.quotients.interface(record.signature)
        if interface.kernel.behavior[:1] != (CONTRACT,) or len(interface.inputs) != 3:
            raise ValueError(
                "quotient does not carry the fixed padded-cell primitive contract"
            )
        values = {_LEFT: task.left, _RIGHT: task.right, _COORDINATE: task.coordinate}
        if {port.variable for port in interface.inputs} != set(values):
            raise ValueError("quotient has another primitive observation interface")
        for port in interface.inputs:
            value = values[port.variable]
            if type(value) is not int or not 0 <= value < port.cardinality:
                raise ValueError(
                    "primitive observation input is outside its finite domain"
                )
        reference = record.components.functions()[COMPONENT_ROLES.index(task.channel)]
        from number_compiler.hashlife.interfaces.semantic_structures import StructureID

        if type(reference) is not StructureID:
            raise ValueError("primitive macro channel is not a factored structure")
        node = self.structures.resolve(reference)
        if node.atom is None:
            raise ValueError("primitive macro observation channel is not scalar")
        self.bits.resolve(node.atom)
        return node.atom, values

    def _leaf(
        self, laws: PrimitiveSemantics, symbol: int
    ) -> tuple[tuple[FactoredFunctionID, ...], int]:
        ports = self._ports(laws, 1)
        left = self._variable(ports, _LEFT, laws.left_sort)
        right = self._variable(ports, _RIGHT, laws.right_sort)
        source = self._constant(ports, laws.symbol_sort, symbol)
        replacement = {
            laws.ports[0].variable: left,
            laws.ports[1].variable: source,
            laws.ports[2].variable: right,
        }
        advance_left, advance_right, output = (
            self.bits.substitute(self.bits.from_scalar(function), replacement)
            for function in (laws.advance_left, laws.advance_right, laws.emit)
        )
        active = self._nonblank(output, laws.blank)
        position = AtomSort("cell-active-position", 2)
        zero, absent = (
            self._constant(ports, position, 0),
            self._constant(ports, position, 1),
        )
        first = self.bits.select(active, zero, absent)
        extent = self._retag(active, AtomSort("cell-active-extent", 2))
        original_extent = int(symbol != laws.blank)
        return self._finish(
            laws,
            1,
            original_extent,
            advance_left,
            advance_right,
            output,
            active,
            first,
            first,
            extent,
            output,
            output,
        ), original_extent

    def _parent(
        self,
        laws: PrimitiveSemantics,
        width: int,
        left: PrimitiveMacroBinding,
        right: PrimitiveMacroBinding,
    ) -> tuple[tuple[FactoredFunctionID, ...], int]:
        self.ledger.bump("primitive_macro_spatial_compositions")
        ports, half = self._ports(laws, width), width // 2
        incoming_left = self._variable(ports, _LEFT, laws.left_sort)
        incoming_right = self._variable(ports, _RIGHT, laws.right_sort)
        coordinate = self._variable(
            ports, _COORDINATE, AtomSort("cell-coordinate", width)
        )
        circuit = _Circuit(self.quotients.functions, ports)
        coords, valid = circuit.imported(self.bits.resolve(coordinate))
        local = circuit.normalized(
            FunctionSignature(ports, AtomSort("cell-coordinate", half)),
            coords[:-1],
            valid,
        )
        branch = circuit.normalized(
            FunctionSignature(ports, BOOL), (coords[-1],), valid
        )
        child_coordinate, is_right = self.bits._publish(circuit, (local, branch))
        a, b = self._components(left.quotient), self._components(right.quotient)

        def lift(
            function: FactoredFunctionID,
            low: FactoredFunctionID,
            high: FactoredFunctionID,
        ) -> FactoredFunctionID:
            return self.bits.substitute(
                function, {_LEFT: low, _RIGHT: high, _COORDINATE: child_coordinate}
            )

        left_mid, right_mid = (
            lift(a[0], incoming_left, incoming_right),
            lift(b[1], incoming_left, incoming_right),
        )
        aa = tuple(lift(function, incoming_left, right_mid) for function in a[:9])
        bb = tuple(lift(function, left_mid, incoming_right) for function in b[:9])
        advance_left, advance_right = bb[0], aa[1]
        output = self.bits.select(is_right, bb[2], aa[2])
        active = self.bits.select(aa[3], self._constant(ports, BOOL, 1), bb[3])
        position, extent_sort = (
            AtomSort("cell-active-position", width + 1),
            AtomSort("cell-active-extent", width + 1),
        )
        absent = self._constant(ports, position, width)
        first = self.bits.select(
            aa[3],
            self._retag(aa[4], position),
            self.bits.select(bb[3], self._offset(bb[4], half, position), absent),
        )
        last = self.bits.select(
            bb[3],
            self._offset(bb[5], half, position),
            self.bits.select(aa[3], self._retag(aa[5], position), absent),
        )
        extent = self.bits.select(
            bb[3],
            self._offset(bb[6], half, extent_sort),
            self._retag(aa[6], extent_sort),
        )
        original_extent = (
            half + right.original_extent
            if right.original_extent
            else left.original_extent
        )
        return self._finish(
            laws,
            width,
            original_extent,
            advance_left,
            advance_right,
            output,
            active,
            first,
            last,
            extent,
            aa[7],
            bb[8],
        ), original_extent

    def _finish(
        self,
        laws: PrimitiveSemantics,
        width: int,
        source_extent: int,
        left: FactoredFunctionID,
        right: FactoredFunctionID,
        output: FactoredFunctionID,
        active: FactoredFunctionID,
        first: FactoredFunctionID,
        last: FactoredFunctionID,
        extent: FactoredFunctionID,
        edge_left: FactoredFunctionID,
        edge_right: FactoredFunctionID,
    ) -> tuple[FactoredFunctionID, ...]:
        ports = self._ports(laws, width)
        growth = self._offset(
            extent,
            width - source_extent,
            AtomSort("cell-growth-biased-by-width", 2 * width + 1),
        )
        termination = self.bits.select(
            active, self._constant(ports, BOOL, 0), self._constant(ports, BOOL, 1)
        )
        frame = self._variable(ports, _COORDINATE, AtomSort("cell-coordinate", width))
        return (
            left,
            right,
            output,
            active,
            first,
            last,
            extent,
            edge_left,
            edge_right,
            growth,
            termination,
            output,
            frame,
        )


def validate_primitive_request(
    kernels: DiamondKernelArena, cells: ImageCellArena, task: PrimitiveMacroKey
) -> None:
    """Read-only scope and alphabet admission, usable before arena allocation."""
    if type(task) is not PrimitiveMacroKey:
        raise TypeError("primitive macro request requires its exact task type")
    primitive = kernels.kernel(task.kernel)
    source_node = cells.require_original(task.source)
    if source_node.level >= 63:
        from number_compiler.hashlife.actions.lazy_compiler import (
            UnsupportedInterfaceError,
        )

        raise UnsupportedInterfaceError(
            "fixed padded-cell growth requires at most 64 result bits"
        )
    original = cells.source_geometry._construction.source
    if (primitive.base, primitive.blank) != (original.base, original.blank):
        raise ValueError("primitive macro alphabet differs from original source")
