"""Canonical finite function fixtures for scoped Boolean carry tests."""

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.arithmetic.functions.semantic_functions import (
    SemanticFunctionArena,
)


def carry_atoms(
    functions: SemanticFunctionArena,
) -> tuple[FinitePort, FunctionSignature, SemanticFunctionID, SemanticFunctionID]:
    port = FinitePort(PortVariable(0, 0, "carry", 0), 2)
    signature = FunctionSignature((port,), BOOL)
    zero = functions.atom(signature, 0)
    one = functions.atom(signature, 1)
    return port, signature, zero, one
