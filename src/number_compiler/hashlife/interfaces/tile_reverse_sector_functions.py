"""Reverse carry-sector components for the existing local-interface quotient."""

from __future__ import annotations

from dataclasses import replace
from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
    ReverseForcingResidues,
)
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.hashlife.actions.field_actions import FieldCellActionID
    from number_compiler.hashlife.execution.tile_causal_interfaces import (
        CausalInterfacePayload,
    )
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.interfaces.diamond_quotient import (
        MacroComponents,
        MacroInterface,
    )
    from number_compiler.hashlife.tiles.tiles import TileID


def validate_reverse_sectors(
    interface: MacroInterface,
    sectors: ReverseCarrySectorTransfer | None,
) -> None:
    """Admit sectors only for the certified decimal pair-kernel contract."""
    if sectors is None:
        return
    if type(sectors) is not ReverseCarrySectorTransfer:
        raise TypeError("reverse sectors require the canonical bounded transfer")
    sectors.__post_init__()
    from number_compiler.hashlife.execution.tile_kernel import _CONTRACT

    permitted = (
        (_CONTRACT, ("base_block", 10)),
        (_CONTRACT, ("digit-normalize-block", 10)),
    )
    if sectors.base != 10 or interface.kernel.behavior not in permitted:
        raise ValueError("reverse sectors require the decimal pair-kernel profile")


def attach_leaf_sectors(
    components: MacroComponents,
    *,
    base: int,
    symbol: int,
) -> MacroComponents:
    """Attach one exact bounded leaf product without changing 13 channels."""
    from number_compiler.hashlife.interfaces.diamond_quotient import MacroComponents

    if type(components) is not MacroComponents:
        raise TypeError("reverse leaf sectors require complete macro components")
    if components.reverse_sectors is not None:
        raise ValueError("reverse leaf sectors are already attached")
    if base != 10:
        return components
    return replace(
        components,
        reverse_sectors=ReverseCarrySectorTransfer.leaf(base, symbol),
    )


def compose_reverse_sectors(
    left: ReverseCarrySectorTransfer | None,
    right: ReverseCarrySectorTransfer | None,
    *,
    ledger: ResourceLedger | None = None,
) -> ReverseCarrySectorTransfer | None:
    """Compose certified children, declining unsupported activity geometry."""
    if ledger is not None:
        ledger.bump("reverse_sector_compose_requests")
    if left is None or right is None:
        if ledger is not None:
            ledger.bump("reverse_sector_compose_failures")
        return None
    if (
        type(left) is not ReverseCarrySectorTransfer
        or type(right) is not ReverseCarrySectorTransfer
    ):
        if ledger is not None:
            ledger.bump("reverse_sector_compose_failures")
        raise TypeError("reverse sector composition requires canonical children")
    try:
        result = left.then(right)
    except BaseException as error:
        if ledger is not None:
            ledger.bump("reverse_sector_compose_failures")
        if type(error) is ValueError and "contiguous prefix" in str(error):
            return None
        raise
    if ledger is not None:
        ledger.bump("reverse_sector_compose_evaluations")
        ledger.bump("reverse_sector_component_outputs", 75)
        ledger.bump("reverse_sector_ring_scalar_operations", 150)
        ledger.bump("reverse_sector_carry_input_evaluations", 2)
    return result


def _aligned_reverse_interval_forcing(
    adapter: PrimitiveTileKernelAdapter,
    primary: CausalInterfacePayload,
    reflected: CausalInterfacePayload,
    *,
    incoming: int,
    reflected_incoming: int,
    growth: int,
    predecessor: CausalInterfacePayload | None = None,
) -> ReverseForcingResidues:
    """Evaluate one scheduler-certified aligned decimal interval.

    This internal compiler primitive validates the bounded semantic operands.
    Its caller remains responsible for proving canonical geometric alignment,
    reflection, and exclusion of a special growth endpoint before invocation.
    Numeric extent alone is deliberately not accepted as that certificate.
    """
    from number_compiler.hashlife.execution.tile_causal_interfaces import (
        CausalInterfacePayload,
    )
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )

    if type(adapter) is not PrimitiveTileKernelAdapter:
        raise TypeError("reverse interval forcing requires the tile authority")
    if type(incoming) is not int or incoming not in (0, 1):
        raise ValueError("reverse interval forcing requires an exact carry bit")
    if type(reflected_incoming) is not int or reflected_incoming not in (0, 1):
        raise ValueError("reflected interval forcing requires an exact carry bit")
    if type(growth) is not int or growth not in (0, 1):
        raise ValueError("reverse interval forcing requires an exact growth bit")
    if (predecessor is None) != (growth == 0):
        raise ValueError("growth interval forcing requires one predecessor interval")

    payloads = (primary, reflected) + (() if predecessor is None else (predecessor,))
    summaries: list[ReverseCarrySectorTransfer] = []
    level: int | None = None
    for payload in payloads:
        if type(payload) is not CausalInterfacePayload:
            raise TypeError("reverse interval forcing requires causal interfaces")
        payload.__post_init__()
        if level is None:
            level = payload.level
        elif payload.level != level:
            raise ValueError("reverse interval forcing changed spatial level")
        record = adapter.quotients.resolve(payload.interface)
        interface = adapter.quotients.interface(record.signature)
        sectors = record.components.reverse_sectors
        validate_reverse_sectors(interface, sectors)
        if type(sectors) is not ReverseCarrySectorTransfer:
            raise ValueError("reverse interval forcing omitted its sector product")
        if sectors.width != 1 << payload.level:
            raise ValueError("reverse interval forcing changed canonical width")
        if sectors.active_width != sectors.width:
            raise ValueError("reverse interval forcing requires full active intervals")
        summaries.append(sectors)
    primary_summary, reflected_summary = summaries[0], summaries[1]
    predecessor_summary = None if predecessor is None else summaries[2]
    adapter.ledger.bump("reverse_interval_forcing_requests")
    try:
        result = primary_summary.interval_forcing(
            reflected_summary,
            incoming=incoming,
            reflected_incoming=reflected_incoming,
            growth=growth,
            predecessor=predecessor_summary,
        )
    except BaseException:
        adapter.ledger.bump("reverse_interval_forcing_failures")
        raise
    adapter.ledger.bump("reverse_interval_forcing_evaluations")
    return result


def supports_reverse_sector_width(
    adapter: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
) -> bool:
    """Recognize the exact decimal action shapes with a sector width law."""
    from number_compiler.arithmetic.contracts.block_kernel import BaseBlockEffect
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.projection.digit_terminal import DigitNormalizeBlockEffect

    if type(adapter) is not PrimitiveTileKernelAdapter:
        raise TypeError("reverse width requires the primitive tile adapter")
    record = adapter._action(action)
    kernel = adapter.kernels.kernel(record.kernel)
    supported = (
        record.homogeneous
        and type(kernel.effect) is BaseBlockEffect
        and kernel.base == 10
    )
    if type(kernel.effect) is DigitNormalizeBlockEffect and kernel.base == 10:
        children = record.children
        if children is None:
            supported = True
        else:
            before, after = children
            producer = adapter._action(before)
            consumer = adapter._action(after)
            producer_kernel = adapter.kernels.kernel(producer.kernel)
            consumer_kernel = adapter.kernels.kernel(consumer.kernel)
            supported = (
                producer.homogeneous
                and type(producer_kernel.effect) is BaseBlockEffect
                and producer_kernel.base == 10
                and consumer.children is None
                and type(consumer_kernel.effect) is DigitNormalizeBlockEffect
                and consumer_kernel.base == 10
            )
    return supported


def reverse_sector_width_from_interface(
    adapter: PrimitiveTileKernelAdapter,
    action: FieldCellActionID,
    tile: TileID,
    payload: CausalInterfacePayload,
    limit: int,
) -> int | None:
    """Return a certified current output extent, or decline another family.

    The payload's sector record summarizes the complete contiguous input of the
    last decimal pair or digit-normalization law.  Its carry exit therefore
    determines the sole possible new most-significant cell.  This does not
    inspect or materialize the exact output tile.
    """
    from number_compiler.arithmetic.carry.carry_monoid import apply_carry_fn
    from number_compiler.hashlife.execution.tile_causal_interfaces import (
        CausalInterfacePayload,
    )
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )
    from number_compiler.hashlife.tiles.tiles import TileID

    if type(adapter) is not PrimitiveTileKernelAdapter:
        raise TypeError("reverse width requires the primitive tile adapter")
    if type(payload) is not CausalInterfacePayload:
        raise TypeError("reverse width requires a causal interface payload")
    if type(tile) is not TileID:
        raise TypeError("reverse width requires a canonical input tile")
    if type(limit) is not int:
        raise TypeError("reverse width limit requires an exact integer")
    node = adapter.tiles.resolve(tile)
    if not 0 <= limit <= node.width:
        raise ValueError("reverse width limit lies outside the source tile")
    if not supports_reverse_sector_width(adapter, action):
        return None
    payload.__post_init__()
    if payload.level != node.level:
        raise ValueError("reverse width interface has another spatial level")
    sectors = adapter.quotients.resolve(payload.interface).components.reverse_sectors
    if sectors is None:
        return None
    if type(sectors) is not ReverseCarrySectorTransfer:
        raise TypeError("reverse width interface has another sector summary sort")
    sectors.__post_init__()
    if sectors.width != node.width:
        raise ValueError("reverse width sector summary changed physical geometry")
    extent = sectors.active_width + apply_carry_fn(sectors.carry, 0)
    if extent > node.width:
        raise ValueError("reverse width requires one terminal padding cell")
    adapter.ledger.bump("reverse_sector_width_observations")
    return min(limit, extent)


__all__ = [
    "attach_leaf_sectors",
    "compose_reverse_sectors",
    "reverse_sector_width_from_interface",
    "supports_reverse_sector_width",
    "validate_reverse_sectors",
]
