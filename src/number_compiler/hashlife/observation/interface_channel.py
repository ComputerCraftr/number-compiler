"""Read one admitted local-interface channel without constructing tile output."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.carry.reverse_port_functions import ReversePortFunction
from number_compiler.arithmetic.radix_port_functions import RadixPortFunction
from number_compiler.hashlife.interfaces.semantic_structures import (
    COMPONENT_ROLES,
    LocalInterfaceID,
    StructureID,
)

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.tile_kernel import (
        PrimitiveTileKernelAdapter,
    )


def observe_channel(
    adapter: PrimitiveTileKernelAdapter,
    interface: LocalInterfaceID,
    channel: str,
    ports: tuple[int, ...],
) -> int:
    if channel not in COMPONENT_ROLES:
        raise ValueError("unknown primitive tile channel")
    record = adapter.quotients.resolve(interface)
    declared = adapter.quotients.interface(record.signature)
    if len(ports) != len(declared.inputs):
        raise ValueError("primitive tile ports have another signature")
    component = record.components.functions()[COMPONENT_ROLES.index(channel)]
    if type(component) is RadixPortFunction or type(component) is ReversePortFunction:
        return component.evaluate(ports, adapter.ledger)
    if type(component) is not StructureID:
        raise ValueError("primitive tile channel is not factored")
    atom = adapter.structures.resolve(component).atom
    if atom is None:
        raise ValueError("primitive tile channel is not scalar")
    values = {
        port.variable: value for port, value in zip(declared.inputs, ports, strict=True)
    }
    result = adapter.bits.evaluate(atom, values)
    if result is None:
        raise ValueError("primitive tile ports are inadmissible")
    return result
