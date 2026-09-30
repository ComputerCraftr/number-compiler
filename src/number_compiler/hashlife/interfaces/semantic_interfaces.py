"""Output-complete local interfaces over scoped original source cells.

This module is the production carrier for the thirteen fixed-padded-cell
channels.  It ports the primitive spatial equations out of ``DiamondRuntime``:
source occurrences are read through :class:`SourceCellArena`, while every
published result is a canonical :class:`LocalInterfaceID`.  No image cell,
future tile, emitted word, or coordinate-indexed output collection is owned by
this compiler.
"""

from __future__ import annotations

from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
    MACRO_LEFT as _LEFT,
    MACRO_RIGHT as _RIGHT,
    primitive_leaf_channels,
    retag_numeric,
)

from number_compiler.resources.stores import append_indexed_node

from collections.abc import Callable, MutableMapping, MutableSequence
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

from number_compiler.arithmetic.automata.primitive_semantics import (
    PrimitiveSemantics,
    PrimitiveSemanticsAdapter,
)
from number_compiler.arithmetic.contracts.block_effect import _effect_key
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaHandle,
    ArenaToken,
)
from number_compiler.arithmetic.contracts.semantic_identity import SemanticIdentity
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import (
    CoordinateOutputMorphismID,
    FieldCellActionID,
    FieldGeometryID,
)
from number_compiler.hashlife.execution.field_images import (
    FieldImageSummary,
    SourceBindingID,
    SourceCellArena,
    SourceCellID,
)
from number_compiler.hashlife.execution.field_transfer import FieldTransferCandidate
from number_compiler.hashlife.execution.field_transfers import FieldTransferID
from number_compiler.hashlife.interfaces.diamond_kernel import DiamondKernelArena
from number_compiler.hashlife.interfaces.diamond_quotient import (
    COMPONENT_ROLES,
    DiamondQuotientArena,
    LocalInterfaceID,
    MacroComponents,
    MacroInterface,
)
from number_compiler.hashlife.interfaces.semantic_bit_transforms import (
    differs_from_constant,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    FactoredFunctionID,
)
from number_compiler.hashlife.interfaces.semantic_structures import StructureID
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.field_transfers import FieldTransferArena


SEMANTIC_INTERFACE_CONTRACT = (
    "fixed-padded-cell-v2",
    "boundary-exits",
    "coordinate-output",
    "nonblank-activity",
    "first-last:width-sentinel",
    "extent:last+1-or-zero",
    "halos:edge-output-symbols",
    "growth:output-minus-source,bias=width",
    "termination:all-blank",
    "normalization:preserve-symbols",
    "frame:identity",
)
_COORDINATE = PortVariable(0, 0, "macro-coordinate", 0)


@dataclass(frozen=True, slots=True)
class SemanticBoundaryID(ArenaHandle):
    """A concrete two-sided boundary used only by observations."""


@dataclass(frozen=True, slots=True)
class _Boundary:
    left: int
    right: int


class SemanticBoundaryArena:
    """Scoped finite boundary bundles; values never enter image identities."""

    _KIND = "semantic-boundary"

    def __init__(self, ledger: ResourceLedger) -> None:
        self.ledger = ledger
        self.owner = ArenaToken("semantic-boundaries")
        prefix = f"semantic-boundaries-{len(ledger.inventory())}"
        self._node_owner = ledger.register(prefix + "-nodes", "observation_port_state")
        self._key_owner = ledger.register(prefix + "-keys", "observation_port_interner")
        self._nodes: MutableSequence[_Boundary] = ledger.make_list(self._node_owner)
        self._keys: MutableMapping[_Boundary, int] = ledger.make_dict(self._key_owner)
        ledger.register_execution_root(self)
        ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=lambda: self._nodes,
        )
        ledger.register_container(
            self._key_owner,
            self._keys,
            payloads=self._keys.items,
        )

    def intern(self, left: int, right: int) -> SemanticBoundaryID:
        if type(left) is not int or type(right) is not int or left < 0 or right < 0:
            raise ValueError("boundary values require nonnegative exact integers")
        record = _Boundary(left, right)
        found = self._keys.get(record)
        if found is None:
            found = append_indexed_node(
                self.ledger,
                self._nodes,
                self._keys,
                self._node_owner,
                self._key_owner,
                record,
                record,
            )
        return SemanticBoundaryID(self.owner, self._KIND, found)

    def resolve(self, reference: ArenaHandle) -> _Boundary:
        if type(reference) is not SemanticBoundaryID:
            raise TypeError("expected a semantic boundary ID")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[reference.local_id]


@dataclass(frozen=True, slots=True)
class _OutputRecord:
    interface: LocalInterfaceID
    source: SourceCellID = field(compare=False, hash=False)
    semantic_key: object


class SemanticCoordinateOutputArena:
    """Canonical coordinate functions extracted from complete interfaces."""

    _KIND = "coordinate-output-morphism"

    def __init__(self, quotients: DiamondQuotientArena) -> None:
        self.quotients = quotients
        self.ledger = quotients.ledger
        self.owner = ArenaToken("semantic-coordinate-outputs")
        prefix = f"semantic-coordinate-outputs-{len(self.ledger.inventory())}"
        self._node_owner = self.ledger.register(
            prefix + "-nodes", "coordinate_output_morphism"
        )
        self._key_owner = self.ledger.register(
            prefix + "-keys", "output_morphism_interner"
        )
        self._nodes: MutableSequence[_OutputRecord] = self.ledger.make_list(
            self._node_owner
        )
        self._keys: MutableMapping[_OutputRecord, int] = self.ledger.make_dict(
            self._key_owner
        )
        self.ledger.register_execution_root(self)
        self.ledger.register_container(
            self._node_owner,
            self._nodes,
            node_count=lambda: len(self._nodes),
            payloads=lambda: self._nodes,
        )
        self.ledger.register_container(
            self._key_owner,
            self._keys,
            payloads=self._keys.items,
        )

    def intern(
        self,
        interface: LocalInterfaceID,
        source: SourceCellID,
        *,
        source_independent: bool = False,
    ) -> CoordinateOutputMorphismID:
        """Intern a source-bound coordinate provider.

        Coordinates are geometry metadata, rather than a finite semantic port.
        The source handle is immutable original geometry; it is never a future
        tile or a coordinate-indexed output tape.
        """
        if type(source) is not SourceCellID:
            raise TypeError("coordinate output requires an original source cell")
        self.quotients.resolve(interface)
        semantic_key = (
            (interface, "source-independent")
            if source_independent
            else (interface, source)
        )
        pending = _OutputRecord(interface, source, semantic_key)
        found = self._keys.get(pending)
        if found is None:
            found = append_indexed_node(
                self.ledger,
                self._nodes,
                self._keys,
                self._node_owner,
                self._key_owner,
                pending,
                pending,
            )
            self.ledger.bump("output_morphism_nodes")
        return CoordinateOutputMorphismID(self.owner, self._KIND, found)

    def resolve(self, reference: CoordinateOutputMorphismID) -> _OutputRecord:
        if type(reference) is not CoordinateOutputMorphismID:
            raise TypeError("expected a semantic coordinate-output ID")
        reference.validate(self.owner, self._KIND, size=len(self._nodes))
        return self._nodes[reference.local_id]

    def validate(self, reference: CoordinateOutputMorphismID) -> None:
        self.resolve(reference)


@dataclass(frozen=True, slots=True)
class _Compiled:
    interface: LocalInterfaceID
    original_extent: int


class SemanticLocalInterfaceCompiler:
    """Iterative homomorphic compiler from source cells to complete effects."""

    def __init__(
        self,
        kernels: DiamondKernelArena,
        quotients: DiamondQuotientArena,
        sources: SourceCellArena,
    ) -> None:
        if (
            kernels.ledger is not quotients.ledger
            or sources.ledger is not quotients.ledger
        ):
            raise ValueError("semantic interface arenas require one index ledger")
        self.kernels = kernels
        self.quotients = quotients
        self.sources = sources
        self.ledger = quotients.ledger
        self.bits = quotients.structures.bits
        self.structures = quotients.structures
        self.primitives = PrimitiveSemanticsAdapter(kernels, quotients.functions)
        self.outputs = SemanticCoordinateOutputArena(quotients)
        prefix = f"semantic-interface-compiler-{len(self.ledger.inventory())}"
        self._source_interface_owner = self.ledger.register(
            prefix + "-source-bindings",
            "source_interface_binding",
        )
        self._default_source_owner = self.ledger.register(
            prefix + "-default-sources",
            "interface_source_binding",
        )
        self._interface_kernel_owner = self.ledger.register(
            prefix + "-interface-kernels",
            "interface_kernel_binding",
        )
        self._source_extent_owner = self.ledger.register(
            prefix + "-source-extents",
            "source_extent_memo",
        )
        self._source_interfaces: MutableMapping[
            tuple[ActionProgramID, SourceCellID], LocalInterfaceID
        ] = self.ledger.make_dict(self._source_interface_owner)
        self._default_sources: MutableMapping[LocalInterfaceID, SourceCellID] = (
            self.ledger.make_dict(self._default_source_owner)
        )
        self._interface_kernels: MutableMapping[LocalInterfaceID, ActionProgramID] = (
            self.ledger.make_dict(self._interface_kernel_owner)
        )
        self._source_extent_cache: MutableMapping[
            tuple[ActionProgramID, SourceCellID], int
        ] = self.ledger.make_dict(self._source_extent_owner)
        self._geometry_last: (
            tuple[tuple[SourceCellID, str, int, int, int], int] | None
        ) = None
        self.ledger.register_execution_root(self)

    def signature(self, kernel: ActionProgramID, level: int) -> PortSignatureID:
        laws = self.primitives.compile(kernel)
        self._validate_level(level)
        ports = self._ports(laws)
        outputs = self._output_sorts(laws)
        primitive = self.kernels.kernel(kernel)
        # Spatial level and coordinate extent belong to the source/image
        # geometry.  Including them here creates a width-sized port domain and
        # prevents equivalent local boundary actions from aliasing.
        behavior = (SEMANTIC_INTERFACE_CONTRACT, _effect_key(primitive.effect), level)
        identity = SemanticIdentity("semantic-interface", behavior)
        admissible = self.quotients.functions.atom(FunctionSignature(ports, BOOL), 1)
        return self.quotients.intern_interface(
            MacroInterface(identity, ports, outputs, admissible)
        )

    def compile(
        self, kernel: ActionProgramID, source: SourceCellID, signature: PortSignatureID
    ) -> LocalInterfaceID:
        laws = self.primitives.compile(kernel)
        root = self.sources.resolve(source)
        self._validate_source(kernel, root.level, signature)
        cached = self._source_interfaces.get((kernel, source))
        if cached is not None:
            if self.quotients.resolve(cached).signature != signature:
                raise AssertionError("cached interface has another signature")
            return cached
        stack: list[tuple[SourceCellID, bool]] = [(source, False)]
        built: dict[SourceCellID, _Compiled] = {}
        while stack:
            current, ready = stack.pop()
            if current in built:
                continue
            node = self.sources.resolve(current)
            if node.level and not ready:
                left, right = self.sources.children(current)
                stack.append((current, True))
                if right not in built:
                    stack.append((right, False))
                if left not in built:
                    stack.append((left, False))
                continue
            if node.level:
                left, right = self.sources.children(current)
                channels, extent = self._parent(
                    laws,
                    node.width,
                    built[left],
                    built[right],
                )
            else:
                channels, extent = self._leaf(laws, self.sources.symbol(current))
            local_signature = self.signature(kernel, node.level)
            components = MacroComponents(
                *(self.structures.atom(item) for item in channels)
            )
            interface = self.quotients.intern(local_signature, components)
            source_key = (kernel, current)
            reservations: list[tuple[int, int, int]] = []
            if source_key not in self._source_interfaces:
                reservations.append((self._source_interface_owner, 1, 0))
            if interface not in self._default_sources:
                reservations.append((self._default_source_owner, 1, 0))
            if interface not in self._interface_kernels:
                reservations.append((self._interface_kernel_owner, 1, 0))
            self.ledger.reserve_many(reservations)
            self._source_interfaces[source_key] = interface
            self._default_sources.setdefault(interface, current)
            self._interface_kernels.setdefault(interface, kernel)
            built[current] = _Compiled(interface, extent)
            self.ledger.bump("local_interface_compilations")
        result = built[source].interface
        if self.quotients.resolve(result).signature != signature:
            raise AssertionError("compiled interface has another signature")
        return result

    def observe(
        self,
        interface: LocalInterfaceID,
        channel: str,
        left: int,
        right: int,
        coordinate: int,
        *,
        source: SourceCellID | None = None,
    ) -> int:
        if type(channel) is not str or channel not in COMPONENT_ROLES:
            raise ValueError("unknown complete semantic channel")
        record = self.quotients.resolve(interface)
        self.quotients.interface(record.signature)
        if source is None:
            source = self._default_sources.get(interface)
        if channel in (
            "output",
            "first_active",
            "last_active",
            "extent",
            "growth",
            "halo_left",
            "halo_right",
            "termination",
            "normalization",
            "frame",
        ):
            if source is None:
                raise ValueError("coordinate geometry has no source binding")
            key = (source, channel, left, right, coordinate)
            if self._geometry_last is not None and self._geometry_last[0] == key:
                return self._geometry_last[1]
            kernel = self._interface_kernels.get(interface)
            if kernel is None:
                raise ValueError("coordinate geometry has no kernel binding")
            result = self._observe_geometry(
                source,
                kernel,
                channel,
                left,
                right,
                coordinate,
            )
            self._geometry_last = (key, result)
            return result
        evaluated = self._finite_observe(interface, channel, left, right)
        self.ledger.bump("local_interface_observations")
        return evaluated

    def _finite_observe(
        self, interface: LocalInterfaceID, channel: str, left: int, right: int
    ) -> int:
        """Evaluate a finite boundary channel without a coordinate port."""
        record = self.quotients.resolve(interface)
        declared = self.quotients.interface(record.signature)
        values = {_LEFT: left, _RIGHT: right}
        for port in declared.inputs:
            value = values.get(port.variable)
            if type(value) is not int or not 0 <= value < port.cardinality:
                raise ValueError("semantic observation lies outside its port")
        reference = record.components.functions()[COMPONENT_ROLES.index(channel)]
        if type(reference) is not StructureID:
            raise ValueError("semantic channel is not a factored structure")
        function = self.structures.resolve(reference).atom
        if function is None:
            raise ValueError("semantic channel is not scalar")
        result = self.bits.evaluate(function, values)
        if result is None:
            raise ValueError("semantic observation is inadmissible")
        return result

    def _source_extent(
        self, source: SourceCellID, laws: PrimitiveSemantics, kernel: ActionProgramID
    ) -> int:
        root_key = (kernel, source)
        cached = self._source_extent_cache.get(root_key)
        if cached is not None:
            return cached
        stack: list[tuple[SourceCellID, bool]] = [(source, False)]
        while stack:
            current, ready = stack.pop()
            current_key = (kernel, current)
            if current_key in self._source_extent_cache:
                continue
            node = self.sources.resolve(current)
            if node.level == 0:
                self.ledger.reserve(self._source_extent_owner, entries=1)
                self._source_extent_cache[current_key] = int(
                    self.sources.symbol(current) != laws.blank
                )
                continue
            left, right = self.sources.children(current)
            if not ready:
                stack.append((current, True))
                if (kernel, right) not in self._source_extent_cache:
                    stack.append((right, False))
                if (kernel, left) not in self._source_extent_cache:
                    stack.append((left, False))
                continue
            right_extent = self._source_extent_cache[(kernel, right)]
            self.ledger.reserve(self._source_extent_owner, entries=1)
            self._source_extent_cache[current_key] = (
                self.sources.resolve(left).width + right_extent
                if right_extent
                else self._source_extent_cache[(kernel, left)]
            )
        return self._source_extent_cache[root_key]

    def _output_source_independent(self, kernel: ActionProgramID) -> bool:
        """Check the finite primitive law before allowing output aliasing."""
        primitive = self.kernels.kernel(kernel)
        for left in range(primitive.left_count):
            for right in range(primitive.right_count):
                first = primitive.emit(left, 0, right)
                if any(
                    primitive.emit(left, symbol, right) != first
                    for symbol in range(1, primitive.blank + 1)
                ):
                    return False
        return True

    def _observe_geometry(
        self,
        source: SourceCellID,
        kernel: ActionProgramID,
        channel: str,
        left: int,
        right: int,
        coordinate: int,
    ) -> int:
        from number_compiler.hashlife.observation.interface_geometry import (
            _observe_geometry,
        )

        return _observe_geometry(self, source, kernel, channel, left, right, coordinate)

    def _validate_source(
        self, kernel: ActionProgramID, level: int, signature: PortSignatureID
    ) -> None:
        primitive = self.kernels.kernel(kernel)
        if (primitive.base, primitive.blank) != self.sources.alphabet():
            raise ValueError(
                "primitive interface alphabet differs from original source"
            )
        if self.quotients.interface(signature) != self.quotients.interface(
            self.signature(kernel, level)
        ):
            raise ValueError(
                "semantic interface signature differs from source geometry"
            )

    @staticmethod
    def _validate_level(level: int) -> None:
        if type(level) is not int or level < 0:
            raise ValueError(
                "semantic source level must be a nonnegative exact integer"
            )

    def _ports(self, laws: PrimitiveSemantics) -> tuple[FinitePort, ...]:
        return tuple(
            sorted(
                (
                    FinitePort(_LEFT, laws.left_sort.cardinality),
                    FinitePort(_RIGHT, laws.right_sort.cardinality),
                ),
                key=lambda item: item.variable,
            )
        )

    @staticmethod
    def _output_sorts(laws: PrimitiveSemantics) -> tuple[AtomSort, ...]:
        # Position, extent, growth, and frame are observed by the separate
        # coordinate provider.  Fixed placeholders keep the local port
        # signature finite and prevent width-sized Boolean circuits.
        return (
            laws.left_sort,
            laws.right_sort,
            laws.symbol_sort,
            BOOL,
            BOOL,
            BOOL,
            BOOL,
            laws.symbol_sort,
            laws.symbol_sort,
            BOOL,
            BOOL,
            BOOL,
            BOOL,
        )

    def _constant(
        self, ports: tuple[FinitePort, ...], output: AtomSort, value: int
    ) -> FactoredFunctionID:
        return self.bits.constant(FunctionSignature(ports, output), value)

    def _variable(
        self, ports: tuple[FinitePort, ...], variable: PortVariable, output: AtomSort
    ) -> FactoredFunctionID:
        port = next(item for item in ports if item.variable == variable)
        return self.bits.variable(ports, port, output)

    def _retag(
        self, function: FactoredFunctionID, output: AtomSort
    ) -> FactoredFunctionID:
        return retag_numeric(
            self.bits,
            function,
            output,
            "semantic numeric conversion would discard bits",
        )

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
        self, interface: LocalInterfaceID
    ) -> tuple[FactoredFunctionID, ...]:
        result: list[FactoredFunctionID] = []
        for reference in self.quotients.resolve(interface).components.functions():
            if type(reference) is not StructureID:
                raise AssertionError("semantic compiler requires factored structures")
            atom = self.structures.resolve(reference).atom
            if atom is None:
                raise AssertionError("semantic channel is not scalar")
            result.append(atom)
        return tuple(result)

    def _leaf(
        self, laws: PrimitiveSemantics, symbol: int
    ) -> tuple[tuple[FactoredFunctionID, ...], int]:
        ports = self._ports(laws)
        advance_left, advance_right, output = primitive_leaf_channels(
            self.bits, laws, ports, symbol
        )
        active = self._nonblank(output, laws.blank)
        original_extent = int(symbol != laws.blank)
        return self._finish(
            laws, advance_left, advance_right, output, active
        ), original_extent

    def _parent(
        self, laws: PrimitiveSemantics, width: int, left: _Compiled, right: _Compiled
    ) -> tuple[tuple[FactoredFunctionID, ...], int]:
        self.ledger.bump("local_interface_spatial_compositions")
        ports = self._ports(laws)
        incoming_left = self._variable(ports, _LEFT, laws.left_sort)
        incoming_right = self._variable(ports, _RIGHT, laws.right_sort)
        aa0, bb0 = self._components(left.interface), self._components(right.interface)

        def lift(
            function: FactoredFunctionID,
            low: FactoredFunctionID,
            high: FactoredFunctionID,
        ) -> FactoredFunctionID:
            return self.bits.substitute(function, {_LEFT: low, _RIGHT: high})

        left_mid = lift(aa0[0], incoming_left, incoming_right)
        right_mid = lift(bb0[1], incoming_left, incoming_right)
        aa = tuple(lift(function, incoming_left, right_mid) for function in aa0)
        bb = tuple(lift(function, left_mid, incoming_right) for function in bb0)
        active = self.bits.select(aa[3], self._constant(ports, BOOL, 1), bb[3])
        output = self._constant(ports, laws.symbol_sort, 0)
        original_extent = width
        return self._finish(
            laws, bb[0], aa[1], output, active, aa[7], bb[8]
        ), original_extent

    def _finish(
        self,
        laws: PrimitiveSemantics,
        left: FactoredFunctionID,
        right: FactoredFunctionID,
        output: FactoredFunctionID,
        active: FactoredFunctionID,
        halo_left: FactoredFunctionID | None = None,
        halo_right: FactoredFunctionID | None = None,
    ) -> tuple[FactoredFunctionID, ...]:
        ports = self._ports(laws)
        zero_bool = self._constant(ports, BOOL, 0)
        zero_symbol = self._constant(ports, laws.symbol_sort, 0)
        # Geometry channels are evaluated by the coordinate provider.  Their
        # finite placeholders keep the local interface bounded and total.
        left_halo = zero_symbol if halo_left is None else halo_left
        right_halo = zero_symbol if halo_right is None else halo_right
        termination = self.bits.select(
            active, zero_bool, self._constant(ports, BOOL, 1)
        )
        return (
            left,
            right,
            output,
            active,
            zero_bool,
            zero_bool,
            zero_bool,
            left_halo,
            right_halo,
            zero_bool,
            termination,
            zero_bool,
            zero_bool,
        )


class PrimitiveSemanticTransferAdapter:
    """Bind primitive complete effects to the shared parent-first transfer API."""

    def __init__(
        self,
        compiler: SemanticLocalInterfaceCompiler,
        boundaries: SemanticBoundaryArena,
        validate_action: Callable[[FieldCellActionID], object],
        kernel_for_action: Callable[[FieldCellActionID], ActionProgramID],
    ) -> None:
        if boundaries.ledger is not compiler.ledger:
            raise ValueError("semantic transfer adapter requires one index ledger")
        self.compiler = compiler
        self.boundaries = boundaries
        self.outputs = compiler.outputs
        self.ledger = compiler.ledger
        self._validate_action = validate_action
        self._kernel_for_action = kernel_for_action
        self.transfers: FieldTransferArena | None = None

    def attach_transfers(self, transfers: object) -> None:
        from number_compiler.hashlife.execution.field_transfers import (
            FieldTransferArena,
        )

        if (
            type(transfers) is not FieldTransferArena
            or transfers.ledger is not self.ledger
        ):
            raise ValueError("semantic adapter needs its owning transfer arena")
        self.transfers = transfers

    def validate_action(self, action: FieldCellActionID) -> None:
        self._validate_action(action)
        self.compiler.kernels.kernel(self._kernel_for_action(action))

    def validate_port(self, incoming: ArenaHandle) -> None:
        self.boundaries.resolve(incoming)

    def compile_transfer(
        self,
        action: FieldCellActionID,
        source: SourceBindingID,
        geometry: FieldGeometryID,
        signature: PortSignatureID,
    ) -> FieldTransferCandidate:
        if type(source) is not SourceCellID:
            raise TypeError("primitive semantic transfer requires a source cell")
        self.validate_action(action)
        source_record = self.compiler.sources.resolve(source)
        interface = self.compiler.compile(
            self._kernel_for_action(action), source, signature
        )
        output = self.outputs.intern(
            interface,
            source,
            source_independent=self.compiler._output_source_independent(
                self._kernel_for_action(action),
            ),
        )
        summary = self._summary_bound(source_record.width)
        return FieldTransferCandidate(interface, output, summary.extent)

    def _record(
        self, transfer: FieldTransferID
    ) -> tuple[LocalInterfaceID, _OutputRecord]:
        from number_compiler.hashlife.execution.field_transfers import (
            FieldTransferArena,
        )

        if type(self.transfers) is not FieldTransferArena:
            raise RuntimeError("semantic adapter has not been attached")
        record = self.transfers.resolve(transfer)
        return record.interface, self.outputs.resolve(record.output)

    @staticmethod
    def _summary_bound(width: int) -> FieldImageSummary:
        """Return a geometry-only admission bound without port enumeration."""
        if type(width) is not int or width < 1:
            raise ValueError("summary width must be a positive exact integer")
        return FieldImageSummary(True, 0, width - 1, width, width, False)

    def point_transfer(
        self,
        transfer: FieldTransferID,
        source: SourceBindingID,
        incoming: ArenaHandle,
        coordinate: int,
    ) -> int:
        if type(source) is not SourceCellID:
            raise TypeError("primitive semantic transfer requires a source cell")
        interface, output = self._record(transfer)
        self.compiler.sources.resolve(source)
        boundary = self.boundaries.resolve(incoming)
        if output.interface != interface:
            raise AssertionError("transfer output differs from its interface")
        self.ledger.bump("output_morphism_visits")
        return self.compiler.observe(
            interface,
            "output",
            boundary.left,
            boundary.right,
            coordinate,
            source=source,
        )

    def width_transfer(
        self, transfer: FieldTransferID, source: SourceBindingID, incoming: ArenaHandle
    ) -> int:
        if type(source) is not SourceCellID:
            raise TypeError("primitive semantic transfer requires a source cell")
        interface, _ = self._record(transfer)
        width = self.compiler.sources.resolve(source).width
        boundary = self.boundaries.resolve(incoming)
        last = self.compiler.observe(
            interface, "last_active", boundary.left, boundary.right, 0, source=source
        )
        return 0 if last == width else last + 1


__all__ = [
    "SEMANTIC_INTERFACE_CONTRACT",
    "PrimitiveSemanticTransferAdapter",
    "SemanticBoundaryArena",
    "SemanticBoundaryID",
    "SemanticCoordinateOutputArena",
    "SemanticLocalInterfaceCompiler",
]
