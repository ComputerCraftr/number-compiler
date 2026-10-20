from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.block_effect import (
    BlockEffect,
    BoundarySide,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    BaseBlockEffect,
    FiniteBlockEffect,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ActionProgramID,
    ArenaToken,
)
from number_compiler.arithmetic.fields.morphism_core import semigroup_power
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.polynomials.frobenius_sector import decimal_reverse_plan
from number_compiler.arithmetic.radix_division import (
    SymbolicBinaryDivisionEffect,
    certified_binary_division_radix,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.actions.tile_action_algebra import (
    ActionSemanticKey,
    PrimitiveTileAction,
    TileActionAlgebra,
    blank_context_metadata,
    retained_action_nodes,
    retained_reverse_plan_nodes,
)
from number_compiler.hashlife.execution.tile_boundary_transfer import (
    bind_boundaries as _bind_boundaries,
)
from number_compiler.hashlife.execution.tile_boundary_transfer import (
    transfer_view as _transfer_view,
)
from number_compiler.hashlife.execution.tile_boundary_transfer import (
    validate_boundaries as validate_boundaries,
)
from number_compiler.hashlife.execution.tile_execution_adapter import (
    FamilyTileHooks,
    FinitePairTransfer,
    is_finite_pair_transfer,
)
from number_compiler.hashlife.execution.tile_fused_kernel import (
    FusedKernelAlgorithms,
    LeafProductKey,
)
from number_compiler.hashlife.execution.tile_fused_kernel import (
    fused_child_contexts as _fused_child_contexts,
)
from number_compiler.hashlife.execution.tile_fused_kernel import (
    fused_interface as _fused_interface,
)
from number_compiler.hashlife.execution.tile_fused_kernel import (
    fused_leaf_result as _fused_leaf_result,
)
from number_compiler.hashlife.execution.tile_fused_kernel import (
    fused_output_active as _fused_output_active,
)
from number_compiler.hashlife.execution.tile_fused_kernel import (
    fused_primitive_pair as _fused_primitive_pair,
)
from number_compiler.hashlife.execution.tile_kernel_composition import (
    compose_temporal_semantics as _compose_temporal_semantics,
)
from number_compiler.hashlife.execution.tile_kernel_validation import (
    admit_family_effect as _admit_family_effect,
)
from number_compiler.hashlife.execution.tile_kernel_validation import (
    admitted_action_record as _admitted_action_record,
)
from number_compiler.hashlife.execution.tile_kernel_validation import (
    validate_fused_action as fused_action_validator,
)
from number_compiler.hashlife.execution.tile_kernel_validation import (
    validate_fused_wiring as fused_wiring_validator,
)
from number_compiler.hashlife.execution.tile_kernel_validation import (
    validate_input as input_validator,
)
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    PrimitiveKernel,
)
from number_compiler.hashlife.interfaces.diamond_quotient import DiamondQuotientArena
from number_compiler.hashlife.interfaces.primitive_behavior import (
    CertifiedLocalSymmetry,
    LocalSymmetryWitness,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    FactoredFunctionID,
)
from number_compiler.hashlife.interfaces.semantic_structures import (
    LocalInterfaceID,
    StructureID,
)
from number_compiler.hashlife.observation.diamond_observers import NonblankBlockEffect
from number_compiler.hashlife.tiles.reverse_threshold_summary import (
    observe_current_growth,
)
from number_compiler.hashlife.tiles.temporal_cocycle import TemporalCocycle
from number_compiler.hashlife.tiles.tile_boundaries import (
    BoundaryTileOperands,
    BoundaryTileView,
)
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    PrimitiveTileResult,
    ResultSemantics,
)
from number_compiler.hashlife.tiles.tile_ports import BoundPorts, ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import (
    CompletedResult,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import (
    TileAlphabet,
    TileAlphabetID,
    TileArena,
    TileID,
)
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.fused_traversal_workspace import FusedTraversalWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import shared as _shared_keys
from number_compiler.resources.stores import LedgerDict
from number_compiler.resources.tile_alphabet_contract import (
    CANONICAL_TILE_ALPHABET_VERSION,
)

if TYPE_CHECKING:
    from number_compiler.resources.causal_workspace import CausalActionAdmission
    from number_compiler.resources.tile_runtime_audit_contracts import (
        PrimitiveTileKernelAuditSnapshot,
    )


class PrimitiveTileKernelAdapter(TileActionAlgebra, FusedKernelAlgorithms):
    """Action authority and scheduler adapter for immutable primitive kernels."""

    complete_via_midpoint_tiles = True
    fused_demand_only = True
    check_two_sided_midpoints = True

    def __init__(
        self,
        tiles: TileArena,
        kernels: DiamondKernelArena,
        quotients: DiamondQuotientArena,
        *,
        family_hooks: FamilyTileHooks | None = None,
        pair_transfer: FinitePairTransfer | None = None,
    ) -> None:
        if not (tiles.ledger is kernels.ledger and kernels.ledger is quotients.ledger):
            raise ValueError("primitive tile execution requires one index ledger")
        self.tiles, self.kernels, self.quotients = tiles, kernels, quotients
        if family_hooks is not None and type(family_hooks) is not FamilyTileHooks:
            raise TypeError("primitive tile adapter requires canonical family hooks")
        if pair_transfer is not None and not is_finite_pair_transfer(pair_transfer):
            raise TypeError(type(pair_transfer))
        if pair_transfer is not None and pair_transfer.ledger is not tiles.ledger:
            raise ValueError("primitive pair transfer belongs to another ledger")
        self.family_hooks = family_hooks
        self.pair_transfer = pair_transfer
        kernels.bind_family_hooks(family_hooks)
        self.ledger: ResourceLedger = tiles.ledger
        self.bits, self.structures = quotients.structures.bits, quotients.structures
        self.owner = ArenaToken("primitive-tile-actions")
        prefix = f"primitive-tile-actions-{len(self.ledger.inventory())}"
        self._fused_workspace = FusedTraversalWorkspace(self.ledger, prefix)
        self._action_owner = self.ledger.register(prefix + "-nodes", "field_action")
        self._action_key_owner = self.ledger.register(
            prefix + "-keys",
            "field_action_interner",
        )
        self._leaf_owner = self.ledger.register(
            prefix + "-leaf-products",
            "tile_leaf_interface_binding",
        )
        self._compose_owner = self.ledger.register(
            prefix + "-compositions",
            "temporal_action_composition",
        )
        self._actions: LedgerDict[int, PrimitiveTileAction] = self.ledger.make_dict(
            self._action_owner,
            nodes_per_entry=1,
        )
        self._action_keys: LedgerDict[ActionSemanticKey, int] = self.ledger.make_dict(
            self._action_key_owner,
        )
        self._leaf_records: LedgerDict[
            LocalInterfaceID | LeafProductKey, int | LocalInterfaceID
        ] = self.ledger.make_dict(
            self._leaf_owner,
        )
        self._compositions: LedgerDict[
            tuple[FieldCellActionID, FieldCellActionID], int
        ] = self.ledger.make_dict(self._compose_owner)
        for owner, store, nodes in (
            (
                self._action_owner,
                self._actions,
                lambda: sum(
                    retained_action_nodes(record.reverse_frobenius)
                    for record in self._actions.values()
                ),
            ),
            (self._action_key_owner, self._action_keys, lambda: 0),
            (self._leaf_owner, self._leaf_records, lambda: 0),
            (self._compose_owner, self._compositions, lambda: 0),
        ):
            self.ledger.register_container(
                owner,
                store,
                payloads=store.items,
                node_count=nodes,
            )
        self._next_action = 0
        self.results: CompletedResultArena | None = None
        self.ledger.register_execution_root(self)

    def attach_results(self, results: CompletedResultArena) -> None:
        if results.tiles is not self.tiles or results.interfaces is not self.quotients:
            raise ValueError("primitive tile results belong to another runtime")
        if results.action_authority is not self:
            raise ValueError("primitive tile results have another action authority")
        if self.results is not None and self.results is not results:
            raise ValueError("primitive tile adapter has one result memo owner")
        self.results = results

    def admit(
        self,
        effect: BlockEffect,
        *,
        symmetry_witnesses: tuple[LocalSymmetryWitness, ...] | None = None,
        cocycle: TemporalCocycle | None = None,
    ) -> FieldCellActionID:
        if type(effect) not in (
            BaseBlockEffect,
            FiniteBlockEffect,
            DigitNormalizeBlockEffect,
            NonblankBlockEffect,
            SymbolicBinaryDivisionEffect,
        ):
            effect = _admit_family_effect(effect, self.family_hooks)
        division_radix = certified_binary_division_radix(effect)
        if type(effect) is SymbolicBinaryDivisionEffect and division_radix is None:
            raise ValueError("symbolic division has malformed fixed semantics")
        if division_radix is not None:
            effect = SymbolicBinaryDivisionEffect(division_radix)
        if cocycle is not None and type(cocycle) is not TemporalCocycle:
            raise TypeError("primitive action cocycle must be canonical")
        action_cocycle = (
            TemporalCocycle(effect.exponent) if cocycle is None else cocycle
        )
        kernel = self.kernels.intern(effect, symmetry_witnesses=symmetry_witnesses)
        primitive = self.kernels.kernel(kernel)
        initial_right = primitive.initial(BoundarySide.RIGHT)
        if (
            primitive.advance(BoundarySide.RIGHT, initial_right, primitive.blank)
            != initial_right
        ):
            raise ValueError(
                "primitive right boundary is not invariant under dyadic blank padding"
            )
        signature = self.signature(primitive, effect)
        semantic_key: ActionSemanticKey = "power", kernel, 1, action_cocycle
        found = self._action_keys.get(semantic_key)
        if found is not None:
            if type(found) is not int:
                raise TypeError("primitive action interner contains an integer alias")
            result = self.scoped_handle(found)
            record = self._action(result)
            if (
                record.kernel != kernel
                or record.signature != signature
                or record.children is not None
                or record.cocycle != action_cocycle
                or record.repetitions != 1
                or not record.homogeneous
                or record.spatial_events_add != self.spatial_events_add(effect)
                or blank_context_metadata(record)
                != (
                    effect.blank_left_tail,
                    effect.blank_right_tail,
                    effect.stable_blank_output,
                )
            ):
                raise ValueError("primitive action interner points to another record")
            return result
        reverse_frobenius_nodes = (
            1 + retained_reverse_plan_nodes(8)
            if type(effect) is BaseBlockEffect and effect.base == 10
            else 1
        )
        reservations = (
            (self._action_owner, 1, reverse_frobenius_nodes),
            (self._action_key_owner, 1, 0),
        )
        self.ledger.reserve_many(reservations)
        local_id = self._next_action
        self._next_action += 1
        try:
            self._actions[local_id] = PrimitiveTileAction(
                kernel,
                signature,
                None,
                action_cocycle,
                1,
                spatial_events_add=self.spatial_events_add(effect),
                blank_left_tail=effect.blank_left_tail,
                blank_right_tail=effect.blank_right_tail,
                stable_blank_output=effect.stable_blank_output,
                reverse_frobenius=(
                    decimal_reverse_plan(1)
                    if type(effect) is BaseBlockEffect and effect.base == 10
                    else None
                ),
            )
            self._action_keys[semantic_key] = local_id
        except BaseException:
            self._actions.pop(local_id, None)
            self._action_keys.pop(semantic_key, None)
            for owner, entries, nodes in reservations:
                self.ledger.release(owner, entries, nodes)
            raise
        self.ledger.bump(_shared_keys.TILE_TEMPORAL_ACTION_PUBLICATIONS)
        return self.scoped_handle(local_id)

    def spatial_events_add(self, effect: BlockEffect) -> bool:
        hooks = self.family_hooks
        return (
            hooks is not None and hooks.owns_effect(effect) and hooks.spatial_events_add
        )

    def scoped_handle(self, local_id: int) -> FieldCellActionID:
        return FieldCellActionID(self.owner, "field-cell-action", local_id)

    def validate_action(self, action: FieldCellActionID) -> None:
        from number_compiler.hashlife.execution.tile_kernel_validation import (
            validate_action,
        )

        validate_action(self, action)

    def local_symmetry(self, action: FieldCellActionID) -> CertifiedLocalSymmetry:
        return self.kernels.local_symmetry(self._action(action).kernel)

    def kernels_compatible(
        self,
        before: ActionProgramID,
        after: ActionProgramID,
    ) -> bool:
        first, second = self.kernels.kernel(before), self.kernels.kernel(after)
        return (
            first.base == second.base
            and first.blank == second.blank
            and first.blank.bit_length() == second.blank.bit_length()
        )

    def validate_input(self, action: FieldCellActionID, source: TileID) -> None:
        input_validator(self, action, source)

    def validate_output(self, action: FieldCellActionID, output: TileID) -> None:
        input_validator(self, action, output, output=True)

    def validate_boundaries(
        self,
        action: FieldCellActionID,
        boundaries: BoundaryTileOperands,
        wiring: ResultWiring,
    ) -> None:
        validate_boundaries(self, action, boundaries, wiring)

    def bind_boundaries(
        self, action: FieldCellActionID, context: BoundPorts
    ) -> BoundPorts:
        return _bind_boundaries(self, action, context)

    def transfer_view(
        self,
        action: FieldCellActionID,
        view: BoundaryTileView,
        context: BoundPorts,
        side: int,
    ) -> int:
        return _transfer_view(self, action, view, context, side)

    def validate_fused_action(self, action: FieldCellActionID) -> None:
        fused_action_validator(self, action)

    def validate_fused_wiring(
        self,
        action: FieldCellActionID,
        producer: ResultWiring,
        result: ResultWiring,
    ) -> None:
        fused_wiring_validator(self, action, producer, result)

    def _action(self, action: FieldCellActionID) -> PrimitiveTileAction:
        self.validate_action(action)
        return self._actions[action.local_id]

    def action_record(self, action: FieldCellActionID) -> PrimitiveTileAction:
        """Return the exact action row after complete semantic validation."""
        return self._action(action)

    def audit_snapshot(self) -> PrimitiveTileKernelAuditSnapshot:
        """Expose immutable rows and exact store identities to resource audits."""
        from number_compiler.hashlife.execution.tile_kernel_audit import (
            tile_kernel_audit_snapshot,
        )

        return tile_kernel_audit_snapshot(
            ledger=self.ledger,
            owner=self.owner,
            next_action=self._next_action,
            action_owner=self._action_owner,
            actions=self._actions,
            action_keys_owner=self._action_key_owner,
            action_keys=self._action_keys,
            leaf_owner=self._leaf_owner,
            leaf_records=self._leaf_records,
            compose_owner=self._compose_owner,
            compositions=self._compositions,
            fused_workspace=self._fused_workspace.audit_snapshot(),
            action_store=self._actions,
            action_key_store=self._action_keys,
            leaf_store=self._leaf_records,
            compose_store=self._compositions,
        )

    def admitted_action_record(
        self, action: FieldCellActionID, admission: CausalActionAdmission
    ) -> PrimitiveTileAction:
        """Read one row under its exact live run admission without deep replay."""
        return _admitted_action_record(self, action, admission)

    def signature_for(self, action: FieldCellActionID) -> PortSignatureID:
        self.validate_action(action)
        return self._actions[action.local_id].signature

    def validated_signature_for(self, action: FieldCellActionID) -> PortSignatureID:
        return self.signature_for(action)

    def action_children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        return self._action(action).children

    def compose(
        self,
        before: FieldCellActionID,
        after: FieldCellActionID,
    ) -> FieldCellActionID:
        self.validate_action(result := self.compose_action_records(before, after))
        return result

    def power(
        self,
        primitive: FieldCellActionID,
        exponent: int,
    ) -> FieldCellActionID:
        self.validate_action(primitive)
        if type(exponent) is not int or exponent < 1:
            raise ValueError("primitive tile power must be a positive exact integer")
        return semigroup_power(primitive, exponent, compose=self.compose)

    def action_cocycle(self, action: FieldCellActionID) -> TemporalCocycle:
        return self._action(action).cocycle

    def wiring(self, action: FieldCellActionID) -> ResultWiring:
        return ResultWiring(self.signature_for(action))

    def validate_wiring(
        self,
        action: FieldCellActionID,
        wiring: ResultWiring,
    ) -> None:
        record = self._action(action)
        if type(wiring) is not ResultWiring:
            raise TypeError("primitive tile execution requires normalized wiring")
        wiring.__post_init__()
        if (
            wiring.signature != record.signature
            or wiring.orientation != 0
            or wiring.phase != 0
        ):
            raise ValueError(
                "primitive tile kernel has no certified wiring automorphism"
            )

    def initial_ports(self, action: FieldCellActionID) -> tuple[int, int]:
        record = self._action(action)
        return self._kernel_ports(record.kernel)

    def _kernel_ports(self, kernel_id: ActionProgramID) -> tuple[int, int]:
        kernel = self.kernels.kernel(kernel_id)
        return kernel.initial(BoundarySide.LEFT), kernel.initial(BoundarySide.RIGHT)

    def primitive_law(self, action: FieldCellActionID) -> PrimitiveKernel:
        record = self._action(action)
        if record.children is not None:
            raise ValueError("a composite action cannot masquerade as a primitive law")
        return self.kernels.kernel(record.kernel)

    def alphabet(self, action: FieldCellActionID) -> TileAlphabetID:
        record = self._action(action)
        kernel = self.kernels.kernel(record.kernel)
        return self.tiles.intern_alphabet(
            TileAlphabet(
                kernel.blank + 1,
                kernel.blank,
                kernel.base,
                max(1, kernel.blank.bit_length()),
                "unsigned-radix-cell-with-explicit-blank",
                CANONICAL_TILE_ALPHABET_VERSION,
            )
        )

    def signature(
        self,
        kernel: PrimitiveKernel,
        effect: BlockEffect,
    ) -> PortSignatureID:
        from number_compiler.hashlife.interfaces.tile_interface_compilation import (
            signature,
        )

        return signature(self, kernel, effect)

    def constant_function(
        self,
        ports: tuple[FinitePort, ...],
        output: AtomSort,
        value: int,
    ) -> FactoredFunctionID:
        return self.bits.constant(FunctionSignature(ports, output), value)

    def variable_function(
        self,
        ports: tuple[FinitePort, ...],
        variable: PortVariable,
        output: AtomSort,
    ) -> FactoredFunctionID:
        port = next(item for item in ports if item.variable == variable)
        return self.bits.variable(ports, port, output)

    def nonblank(
        self,
        function: FactoredFunctionID,
        blank: int,
    ) -> FactoredFunctionID:
        from number_compiler.hashlife.interfaces.tile_interface_compilation import (
            nonblank,
        )

        return nonblank(self, function, blank)

    def interface_components(
        self,
        interface: LocalInterfaceID,
    ) -> tuple[FactoredFunctionID, ...]:
        result: list[FactoredFunctionID] = []
        for reference in self.quotients.resolve(interface).components.functions():
            if type(reference) is not StructureID:
                raise ValueError("primitive tile interface is not factored")
            atom = self.structures.resolve(reference).atom
            if atom is None:
                raise ValueError("primitive tile channel is not scalar")
            result.append(atom)
        return tuple(result)

    def finish(
        self,
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
        from number_compiler.hashlife.interfaces.tile_interface_compilation import (
            finish,
        )

        return finish(
            self,
            kernel,
            left,
            right,
            output,
            active,
            halo_left,
            halo_right,
            first_active,
            last_active,
        )

    def tabulated(
        self,
        ports: tuple[FinitePort, ...],
        output: AtomSort,
        active: tuple[FinitePort, ...],
        table: tuple[int, ...],
    ) -> FactoredFunctionID:
        from number_compiler.hashlife.interfaces.tile_interface_compilation import (
            tabulated,
        )

        return tabulated(self, ports, output, active, table)

    def leaf_components(
        self,
        kernel: PrimitiveKernel,
        symbol: int,
    ) -> tuple[FactoredFunctionID, ...]:
        from number_compiler.hashlife.interfaces.tile_interface_compilation import (
            leaf_components,
        )

        return leaf_components(self, kernel, symbol)

    def parent_components(
        self,
        kernel: PrimitiveKernel,
        left: LocalInterfaceID,
        right: LocalInterfaceID,
    ) -> tuple[FactoredFunctionID, ...]:
        from number_compiler.hashlife.interfaces.tile_interface_compilation import (
            parent_components,
        )

        return parent_components(self, kernel, left, right)

    def require_results(self) -> CompletedResultArena:
        if self.results is None:
            raise RuntimeError("primitive tile adapter has no result memo")
        return self.results

    def compile_interface(
        self,
        action: FieldCellActionID,
        source: TileID,
        wiring: ResultWiring,
    ) -> LocalInterfaceID:
        from number_compiler.hashlife.interfaces.tile_interface_compilation import (
            compile_interface,
        )

        return compile_interface(self, action, source, wiring)

    def fused_primitive_pair(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None:
        return _fused_primitive_pair(self, action)

    def fused_interface(
        self,
        action: FieldCellActionID,
        source: TileID,
        producer_ports: tuple[int, ...],
        wiring: ResultWiring,
        *,
        producer_wiring: ResultWiring | None = None,
    ) -> LocalInterfaceID:
        return _fused_interface(
            self,
            action,
            source,
            producer_ports,
            wiring,
            producer_wiring=producer_wiring,
        )

    def fused_child_contexts(
        self,
        action: FieldCellActionID,
        parent: TileID,
        producer_ports: tuple[int, ...],
        consumer_ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
        *,
        producer_wiring: ResultWiring | None = None,
    ) -> tuple[ChildContext, ChildContext]:
        return _fused_child_contexts(
            self,
            action,
            parent,
            producer_ports,
            consumer_ports,
            wiring,
            side,
            producer_wiring=producer_wiring,
        )

    def fused_leaf_result(
        self,
        action: FieldCellActionID,
        source: TileID,
        producer_ports: tuple[int, ...],
        consumer_ports: tuple[int, ...],
        wiring: ResultWiring,
        *,
        producer_wiring: ResultWiring | None = None,
    ) -> PrimitiveTileResult:
        return _fused_leaf_result(
            self,
            action,
            source,
            producer_ports,
            consumer_ports,
            wiring,
            producer_wiring=producer_wiring,
        )

    def fused_output_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        producer_ports: tuple[int, ...],
        consumer_ports: tuple[int, ...],
        wiring: ResultWiring,
        *,
        producer_wiring: ResultWiring | None = None,
    ) -> bool:
        return _fused_output_active(
            self,
            action,
            source,
            producer_ports,
            consumer_ports,
            wiring,
            producer_wiring=producer_wiring,
        )

    def leaf_interface(
        self,
        action: FieldCellActionID,
        source: TileID,
        wiring: ResultWiring,
    ) -> LocalInterfaceID:
        if self.tiles.resolve(source).level:
            raise ValueError("leaf interface requires one tile symbol")
        return self.compile_interface(action, source, wiring)

    def observe(
        self,
        interface: LocalInterfaceID,
        channel: str,
        ports: tuple[int, ...],
    ) -> int:
        from number_compiler.hashlife.observation.interface_channel import (
            observe_channel,
        )

        return observe_channel(self, interface, channel, ports)

    def apply_leaf(
        self,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> PrimitiveTileResult:
        binding = self._leaf_records.get(interface)
        if type(binding) is not int:
            raise ValueError("leaf interface has no primitive tile binding")
        output = self.observe(interface, "output", ports)
        outgoing = (
            self.observe(interface, "boundary_left", ports),
            self.observe(interface, "boundary_right", ports),
        )
        return PrimitiveTileResult(
            output,
            ResultSemantics(
                interface,
                outgoing,
                relative_extent=int(output != binding),
                observed_input_ports=ports,
            ),
        )

    def leaf_observation(
        self,
        action: FieldCellActionID,
        source: TileID,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> TemporalCocycle:
        node = self.tiles.resolve(source)
        if node.level or node.symbol is None:
            raise ValueError("leaf observations require one source symbol")
        return self.symbol_observation(action, node.symbol, interface, ports)

    def symbol_observation(
        self,
        action: FieldCellActionID,
        symbol: int,
        interface: LocalInterfaceID,
        ports: tuple[int, ...],
    ) -> TemporalCocycle:
        from number_compiler.hashlife.interfaces.tile_interface_compilation import (
            symbol_observation,
        )

        return symbol_observation(self, action, symbol, interface, ports)

    def leaf_interface_symbol(
        self,
        action: FieldCellActionID,
        symbol: int,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> tuple[int, LocalInterfaceID, TemporalCocycle]:
        from number_compiler.hashlife.interfaces.tile_interface_compilation import (
            leaf_interface_symbol,
        )

        return leaf_interface_symbol(self, action, symbol, ports, wiring)

    def child_context(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
    ) -> ChildContext:
        if type(side) is not int:
            raise TypeError("child side requires an exact integer")
        if side not in (0, 1):
            raise ValueError("child side must be zero or one")
        node = self.tiles.resolve(parent)
        if node.left != left or node.right != right:
            raise ValueError("child context does not match its canonical parent")
        if len(ports) != 2:
            raise ValueError("primitive tile execution requires two boundary ports")
        sibling = right if side == 0 else left
        interface = self.compile_interface(action, sibling, wiring)
        channel = "boundary_right" if side == 0 else "boundary_left"
        midpoint = self.observe(interface, channel, ports)
        child_ports = (ports[0], midpoint) if side == 0 else (midpoint, ports[1])
        return ChildContext(child_ports, wiring)

    def join_semantics(
        self,
        action: FieldCellActionID,
        parent: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        left: CompletedResult,
        right: CompletedResult,
    ) -> ResultSemantics:
        interface = self.compile_interface(action, parent, wiring)
        outgoing = (
            self.observe(interface, "boundary_left", ports),
            self.observe(interface, "boundary_right", ports),
        )
        kernel = self.kernels.kernel(self._action(action).kernel)
        if left.physical_ticks != right.physical_ticks:
            raise ValueError("spatial children represent different temporal actions")
        if self.spatial_events_add(kernel.effect):
            event_weight = left.event_weight + right.event_weight
            if event_weight not in (0, 1) or left.frame_shift or right.frame_shift:
                raise ValueError("additive-event children have invalid observations")
            frame_shift = 0
        else:
            if (
                left.event_weight != right.event_weight
                or left.frame_shift != right.frame_shift
            ):
                raise ValueError(
                    "spatial children represent different temporal actions"
                )
            event_weight, frame_shift = left.event_weight, left.frame_shift
        half = self.tiles.resolve(parent).width // 2
        extent = (
            half + right.relative_extent
            if right.relative_extent
            else left.relative_extent
        )
        from number_compiler.hashlife.execution.tile_physical_support import (
            spatial_physical_support,
        )

        return ResultSemantics(
            interface,
            outgoing,
            left.physical_ticks,
            event_weight,
            frame_shift,
            0,
            extent,
            observed_input_ports=ports,
            physical_support=spatial_physical_support(
                left.physical_support, right.physical_support
            ),
        )

    def temporal_before_context(
        self,
        action: FieldCellActionID,
        before: FieldCellActionID,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext:
        # Shape validation authenticates this exact action/wiring call chain.
        self.require_results().validate_shape(action, original_ports, wiring)
        record = self._actions[action.local_id]
        children = record.children
        if children is None or children[0] != before:
            raise ValueError("temporal prefix is not a child of this action")
        if wiring.signature != record.signature:
            raise ValueError("temporal prefix has another wiring signature")
        before_record = self._action(before)
        before_ports = self._kernel_ports(before_record.kernel)
        if (
            before_record.signature == record.signature
            and original_ports != before_ports
        ):
            raise ValueError(
                "completed-midpoint powers require canonical exterior ports"
            )
        return ChildContext(
            before_ports,
            ResultWiring(
                before_record.signature,
                wiring.orientation,
                wiring.phase,
            ),
        )

    def temporal_after_context(
        self,
        action: FieldCellActionID,
        after: FieldCellActionID,
        before_result: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ChildContext:
        record = self._action(action)
        children = record.children
        if children is None or children[1] != after:
            raise ValueError("temporal suffix is not the canonical second child")
        # A complete midpoint is a new exact field.  The second bimachine scan
        # starts at its own certified exterior state; it does not inherit the
        # first scan's outgoing carry.
        after_record = self._action(after)
        ports = self._kernel_ports(after_record.kernel)
        return ChildContext(
            ports,
            ResultWiring(after_record.signature, wiring.orientation, wiring.phase),
        )

    def temporal_semantics(
        self,
        action: FieldCellActionID,
        before: CompletedResult,
        after: CompletedResult,
        original_ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> ResultSemantics:
        record = self._action(action)
        if record.children is None:
            raise ValueError("temporal semantics require a composed action")
        return _compose_temporal_semantics(record.cocycle.physical_ticks, before, after)

    def output_active(
        self,
        action: FieldCellActionID,
        source: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
    ) -> bool:
        interface = self.compile_interface(action, source, wiring)
        return bool(self.observe(interface, "activity", ports))

    current_growth = observe_current_growth


__all__ = ["PrimitiveTileKernelAdapter"]
