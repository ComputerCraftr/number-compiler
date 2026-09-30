"""Fresh finite Boolean interfaces used by substitution and rebuild contracts."""

from number_compiler.arithmetic.contracts.scoped_handles import TransferSummaryID
from number_compiler.arithmetic.functions.finite_function_types import BOOL, FinitePort
from number_compiler.arithmetic.functions.finite_port_action import (
    FinitePortActionArena,
    PortVariable,
)
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.resources.ledger import ResourceLedger


def binary_carry_ports() -> tuple[
    FinitePortActionArena,
    PortVariable,
    PortVariable,
    TransferSummaryID,
    TransferSummaryID,
]:
    arena = FinitePortActionArena()
    xvar, yvar = PortVariable(0, 0, "carry", 0), PortVariable(1, 0, "carry", 0)
    x, y = arena.variable(xvar), arena.variable(yvar)
    return arena, xvar, yvar, x, y


def three_input_ports() -> tuple[
    FinitePortActionArena,
    tuple[PortVariable, PortVariable, PortVariable],
    tuple[TransferSummaryID, TransferSummaryID, TransferSummaryID],
]:
    arena = FinitePortActionArena()
    px, py, pz = (PortVariable(0, 0, "input", bit) for bit in range(3))
    x, y, z = (arena.variable(port) for port in (px, py, pz))
    return arena, (px, py, pz), (x, y, z)


def semantic_boolean_variable(
    role: str,
) -> tuple[BitFunctionArena, FinitePort, FactoredFunctionID]:
    bits = BitFunctionArena(ResourceLedger())
    port = FinitePort(PortVariable(0, 0, role, 0), 2)
    return bits, port, bits.variable((port,), port, BOOL)
