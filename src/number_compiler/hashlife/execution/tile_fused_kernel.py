"""Primitive-pair fused interface compilation for the canonical tile adapter."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Protocol, cast

from number_compiler.arithmetic.carry.reverse_port_functions import (
    MAX_CLOSED_REVERSE_BASE,
    MIN_CLOSED_REVERSE_BASE,
)
from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID
from number_compiler.arithmetic.radix_division import (
    SymbolicBinaryDivisionEffect,
    certified_binary_division_radix,
)
from number_compiler.hashlife.actions.diamond_actions import PortSignatureID
from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.interfaces.diamond_kernel import (
    DiamondKernelArena,
    PrimitiveKernel,
)
from number_compiler.hashlife.interfaces.diamond_quotient import (
    DiamondQuotientArena,
    LocalInterfaceID,
    MacroComponents,
)
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.hashlife.interfaces.semantic_structures import StructureArena
from number_compiler.hashlife.tiles.tile_context import (
    ChildContext,
    PrimitiveTileResult,
    ResultSemantics,
)
from number_compiler.hashlife.tiles.tile_ports import ResultWiring
from number_compiler.hashlife.tiles.tile_result_records import (
    FusedInterfaceKey,
)
from number_compiler.hashlife.tiles.tile_results import CompletedResultArena
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect
from number_compiler.resources.fused_traversal_workspace import FusedTraversalWorkspace
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)
from number_compiler.resources.stores import LedgerDict


class _ActionView(Protocol):
    @property
    def kernel(self) -> ActionProgramID: ...
    @property
    def children(self) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...
    @property
    def signature(self) -> PortSignatureID: ...


@dataclass(frozen=True, slots=True)
class LeafProductKey:
    """One kernel-symbol function, independent of its producing occurrence."""

    kernel: ActionProgramID
    signature: PortSignatureID
    symbol: int


_FusedTraversalFrame = tuple[TileID, tuple[int, ...], bool]


class _Host(Protocol):
    tiles: TileArena
    kernels: DiamondKernelArena
    quotients: DiamondQuotientArena
    structures: StructureArena
    ledger: ResourceLedger
    _fused_workspace: FusedTraversalWorkspace
    _leaf_owner: int
    _leaf_records: LedgerDict[LocalInterfaceID | LeafProductKey, int | LocalInterfaceID]

    def action_children(
        self,
        action: FieldCellActionID,
    ) -> tuple[FieldCellActionID, FieldCellActionID] | None: ...
    def _action(self, action: FieldCellActionID) -> _ActionView: ...
    def validate_fused_wiring(
        self,
        action: FieldCellActionID,
        producer: ResultWiring,
        result: ResultWiring,
    ) -> None: ...
    def _require_results(self) -> CompletedResultArena: ...
    def _compile_interface(
        self,
        action: FieldCellActionID,
        source: TileID,
        wiring: ResultWiring,
    ) -> LocalInterfaceID: ...
    def _observe(
        self,
        interface: LocalInterfaceID,
        channel: str,
        ports: tuple[int, ...],
    ) -> int: ...
    def _leaf_components(
        self,
        kernel: PrimitiveKernel,
        symbol: int,
    ) -> tuple[FactoredFunctionID, ...]: ...
    def _parent_components(
        self,
        kernel: PrimitiveKernel,
        left: LocalInterfaceID,
        right: LocalInterfaceID,
    ) -> tuple[FactoredFunctionID, ...]: ...
    def child_context(
        self,
        action: FieldCellActionID,
        parent: TileID,
        left: TileID,
        right: TileID,
        ports: tuple[int, ...],
        wiring: ResultWiring,
        side: int,
    ) -> ChildContext: ...


def leaf_product(
    self: _Host,
    action: FieldCellActionID,
    symbol: int,
    wiring: ResultWiring,
) -> LocalInterfaceID:
    """Probe the semantic leaf before compiling any boundary/output functions.

    The adapter's existing leaf store owns both the semantic binding and the
    reverse apply-leaf admission. No source tile or producer context enters the
    key. Symbols are bounded kernel literals, not coordinate observations.
    """
    record = self._action(action)
    if record.children is not None:
        raise ValueError("leaf products require a primitive kernel")
    if type(wiring) is not ResultWiring:
        raise TypeError("leaf products require normalized wiring")
    wiring.__post_init__()
    if wiring.signature != record.signature or wiring.orientation or wiring.phase:
        raise ValueError("leaf product has another kernel interface")
    kernel = self.kernels.kernel(record.kernel)
    if type(symbol) is not int:
        raise TypeError("leaf product requires an exact kernel symbol")
    if not 0 <= symbol <= kernel.blank:
        raise ValueError("leaf product symbol lies outside the kernel alphabet")
    key = LeafProductKey(record.kernel, wiring.signature, symbol)
    found = self._leaf_records.get(key)
    if found is not None:
        if type(found) is not LocalInterfaceID:
            raise TypeError("leaf product contains another result sort")
        if self.quotients.resolve(found).signature != wiring.signature:
            raise ValueError("leaf product has another signature")
        blank = self._leaf_records.get(found)
        if type(blank) is not int or blank != kernel.blank:
            raise ValueError("leaf product lost its reverse admission")
        self.ledger.bump(_execution_keys.TILE_LEAF_PRODUCT_REQUESTS)
        self.ledger.bump(_execution_keys.TILE_LEAF_PRODUCT_EARLY_HITS)
        return found
    self.ledger.bump(_execution_keys.TILE_LEAF_PRODUCT_REQUESTS)
    # Reserve both bindings before semantic construction. A zero/exhausted
    # cache budget must not execute the kernel and reject publication later.
    self.ledger.reserve(self._leaf_owner, entries=2)
    self.ledger.bump(_execution_keys.TILE_LEAF_PRODUCT_EVALUATIONS)
    interface: LocalInterfaceID | None = None
    added_reverse = False
    added_key = False
    try:
        if type(kernel.effect) is BaseBlockEffect and (
            MIN_CLOSED_REVERSE_BASE <= kernel.base <= MAX_CLOSED_REVERSE_BASE
        ):
            from number_compiler.hashlife.interfaces.tile_interface_compilation import (
                _ports,
            )
            from number_compiler.hashlife.interfaces.tile_reverse_functions import (
                reverse_leaf_components,
            )
            from number_compiler.hashlife.interfaces.tile_reverse_sector_functions import (
                attach_leaf_sectors,
            )

            with self.quotients.closed_workspace.scope("leaf"):
                macro = attach_leaf_sectors(
                    reverse_leaf_components(
                        _ports(kernel), kernel.base, symbol, self.ledger
                    ),
                    base=kernel.base,
                    symbol=symbol,
                )
                interface = self.quotients.intern(wiring.signature, macro)
                self.ledger.bump(_execution_keys.REVERSE_PORT_LEAF_INTERFACES)
        elif (
            division_radix := certified_binary_division_radix(kernel.effect)
        ) is not None:
            from number_compiler.hashlife.interfaces.tile_interface_compilation import (
                _ports,
            )
            from number_compiler.hashlife.interfaces.tile_radix_functions import (
                division_leaf_components,
            )

            macro = division_leaf_components(_ports(kernel), division_radix, symbol)
            if type(kernel.effect) is SymbolicBinaryDivisionEffect:
                self.ledger.bump(
                    _execution_keys.SYMBOLIC_TILE_DIVISION_LEAF_COMPILATIONS
                )
        elif type(kernel.effect) is DigitNormalizeBlockEffect and kernel.base == 10:
            from number_compiler.hashlife.interfaces.tile_reverse_sector_functions import (
                attach_leaf_sectors,
            )

            components = self._leaf_components(kernel, symbol)
            with self.quotients.closed_workspace.scope("leaf"):
                macro = attach_leaf_sectors(
                    MacroComponents(
                        *(self.structures.atom(item) for item in components)
                    ),
                    base=kernel.base,
                    symbol=symbol,
                )
                interface = self.quotients.intern(wiring.signature, macro)
        else:
            components = self._leaf_components(kernel, symbol)
            macro = MacroComponents(
                *(self.structures.atom(item) for item in components)
            )
        if interface is None:
            interface = self.quotients.intern(
                wiring.signature,
                macro,
            )
        previous = self._leaf_records.get(interface)
        if previous is None:
            self._leaf_records[interface] = kernel.blank
            added_reverse = True
        elif type(previous) is not int or previous != kernel.blank:
            raise ValueError("leaf quotient alias changed alphabet semantics")
        self._leaf_records[key] = interface
        added_key = True
    except BaseException:
        if added_key:
            self._leaf_records.pop(key, None)
        if added_reverse and interface is not None:
            self._leaf_records.pop(interface, None)
        self.ledger.release(self._leaf_owner, entries=2)
        raise
    if not added_reverse:
        self.ledger.release(self._leaf_owner, entries=1)
        self.ledger.bump(_execution_keys.TILE_LEAF_PRODUCT_LATE_ALIASES)
    self.ledger.bump(_execution_keys.TILE_LEAF_PRODUCT_PUBLICATIONS)
    return interface


def fused_primitive_pair(
    self: _Host,
    action: FieldCellActionID,
) -> tuple[FieldCellActionID, FieldCellActionID] | None:
    """Return only the fixed-port primitive pair implemented by this fuser."""
    pair = self.action_children(action)
    if pair is None or any(self.action_children(child) is not None for child in pair):
        return None
    if any(
        certified_binary_division_radix(
            self.kernels.kernel(self._action(child).kernel).effect
        )
        is not None
        for child in pair
    ):
        # Numeric carry functions use the same causal scheduler; the optional
        # Boolean primitive-pair accelerator cannot expand their port domain.
        return None
    return pair


def fused_interface(
    self: _Host,
    action: FieldCellActionID,
    source: TileID,
    producer_ports: tuple[int, ...],
    wiring: ResultWiring,
    *,
    producer_wiring: ResultWiring | None = None,
) -> LocalInterfaceID:
    """Compile B over A(source) while retaining no exact A output tile."""
    pair = fused_primitive_pair(self, action)
    if pair is None:
        raise ValueError("fused tile demand supports one primitive pair")
    before, after = pair
    producer_wiring = wiring if producer_wiring is None else producer_wiring
    self.validate_fused_wiring(action, producer_wiring, wiring)
    results = self._require_results()
    root_key = FusedInterfaceKey(
        action,
        source,
        producer_ports,
        wiring,
        producer_wiring,
        before=before,
        after=after,
    )
    found = results.lookup_fused_interface(root_key)
    if found is not None:
        return found
    root_level = self.tiles.resolve(source).level
    workspace = self._fused_workspace
    with workspace.scope(root_level, len(producer_ports)):
        workspace.append_frame((source, producer_ports, False))
        root_item = source, producer_ports
        while workspace.frames:
            self.ledger.bump(_execution_keys.TILE_FUSED_FRAMES)
            frame = workspace.pop_frame()
            if type(frame) is not tuple or len(frame) != 3:
                raise TypeError("fused traversal contains another frame sort")
            current, ports, ready = cast(_FusedTraversalFrame, frame)
            if type(current) is not TileID or type(ports) is not tuple:
                raise TypeError("fused traversal contains another frame sort")
            if any(type(port) is not int for port in ports) or type(ready) is not bool:
                raise TypeError("fused traversal contains malformed frame fields")
            item = current, ports
            key = FusedInterfaceKey(
                action,
                current,
                ports,
                wiring,
                producer_wiring,
                before=before,
                after=after,
            )
            cached = (
                None
                if ready or item == root_item
                else results.lookup_fused_interface(key)
            )
            if cached is not None:
                workspace.append_value(cached)
                continue
            node = self.tiles.resolve(current)
            if not node.level:
                if node.symbol is None:
                    raise ValueError("malformed fused source leaf")
                first = self._compile_interface(before, current, producer_wiring)
                symbol = self._observe(first, "output", ports)
                interface = leaf_product(self, after, symbol, wiring)
            elif not ready:
                if node.left is None or node.right is None:
                    raise ValueError("malformed fused source parent")
                left = self.child_context(
                    before,
                    current,
                    node.left,
                    node.right,
                    ports,
                    producer_wiring,
                    0,
                )
                right = self.child_context(
                    before,
                    current,
                    node.left,
                    node.right,
                    ports,
                    producer_wiring,
                    1,
                )
                workspace.append_frame((current, ports, True))
                workspace.append_frame((node.right, right.ports, False))
                workspace.append_frame((node.left, left.ports, False))
                continue
            else:
                if node.left is None or node.right is None or len(workspace.values) < 2:
                    raise ValueError("fused traversal lost completed children")
                from number_compiler.hashlife.execution.tile_causal_interfaces import (
                    combine_local_interfaces,
                )

                right_interface = workspace.pop_value()
                left_interface = workspace.pop_value()
                if (
                    type(left_interface) is not LocalInterfaceID
                    or type(right_interface) is not LocalInterfaceID
                ):
                    raise TypeError("fused traversal contains another result sort")
                interface = combine_local_interfaces(
                    results,
                    after,
                    left_interface,
                    right_interface,
                    wiring,
                )
            workspace.append_value(results.publish_fused_interface(key, interface))
        if len(workspace.values) != 1:
            raise ValueError("fused traversal produced an incomplete result stack")
        result = workspace.pop_value()
        if type(result) is not LocalInterfaceID:
            raise TypeError("fused traversal contains another result sort")
        return result


def fused_child_contexts(
    self: _Host,
    action: FieldCellActionID,
    parent: TileID,
    producer_ports: tuple[int, ...],
    consumer_ports: tuple[int, ...],
    wiring: ResultWiring,
    side: int,
    *,
    producer_wiring: ResultWiring | None = None,
) -> tuple[ChildContext, ChildContext]:
    if type(side) is not int:
        raise TypeError("fused child side requires an exact integer")
    if side not in (0, 1):
        raise ValueError("fused child side must be zero or one")
    self._require_results().validate_shape(action, consumer_ports, wiring)
    producer_wiring = wiring if producer_wiring is None else producer_wiring
    self.validate_fused_wiring(action, producer_wiring, wiring)
    pair = fused_primitive_pair(self, action)
    node = self.tiles.resolve(parent)
    if pair is None or node.left is None or node.right is None:
        raise ValueError("fused child context requires a primitive-pair parent")
    before, _after = pair
    producer = self.child_context(
        before,
        parent,
        node.left,
        node.right,
        producer_ports,
        producer_wiring,
        side,
    )
    sibling = node.right if side == 0 else node.left
    sibling_producer = self.child_context(
        before,
        parent,
        node.left,
        node.right,
        producer_ports,
        producer_wiring,
        1 - side,
    )
    interface = fused_interface(
        self,
        action,
        sibling,
        sibling_producer.ports,
        wiring,
        producer_wiring=sibling_producer.wiring,
    )
    channel = "boundary_right" if side == 0 else "boundary_left"
    midpoint = self._observe(interface, channel, consumer_ports)
    ports = (
        (consumer_ports[0], midpoint) if side == 0 else (midpoint, consumer_ports[1])
    )
    return producer, ChildContext(ports, wiring)


def fused_leaf_result(
    self: _Host,
    action: FieldCellActionID,
    source: TileID,
    producer_ports: tuple[int, ...],
    consumer_ports: tuple[int, ...],
    wiring: ResultWiring,
    *,
    producer_wiring: ResultWiring | None = None,
) -> PrimitiveTileResult:
    node = self.tiles.resolve(source)
    if node.level or node.symbol is None:
        raise ValueError("fused leaf result requires one source symbol")
    self._require_results().validate_shape(action, consumer_ports, wiring)
    interface = fused_interface(
        self,
        action,
        source,
        producer_ports,
        wiring,
        producer_wiring=producer_wiring,
    )
    output = self._observe(interface, "output", consumer_ports)
    outgoing = (
        self._observe(interface, "boundary_left", consumer_ports),
        self._observe(interface, "boundary_right", consumer_ports),
    )
    blank = self.tiles.alphabet(node.alphabet).blank
    return PrimitiveTileResult(
        output,
        ResultSemantics(interface, outgoing, relative_extent=int(output != blank)),
    )


def fused_output_active(
    self: _Host,
    action: FieldCellActionID,
    source: TileID,
    producer_ports: tuple[int, ...],
    consumer_ports: tuple[int, ...],
    wiring: ResultWiring,
    *,
    producer_wiring: ResultWiring | None = None,
) -> bool:
    self._require_results().validate_shape(action, consumer_ports, wiring)
    interface = fused_interface(
        self,
        action,
        source,
        producer_ports,
        wiring,
        producer_wiring=producer_wiring,
    )
    return bool(self._observe(interface, "activity", consumer_ports))


__all__ = [
    "fused_child_contexts",
    "fused_interface",
    "fused_leaf_result",
    "fused_output_active",
    "fused_primitive_pair",
]
