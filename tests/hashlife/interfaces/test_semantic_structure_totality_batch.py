"""A quotient normalization shares only transient, exact totality proofs."""

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.semantic_structure_validation import (
    require_total,
    require_total_components,
)
from number_compiler.hashlife.interfaces.semantic_structures import StructureArena
from number_compiler.resources.ledger import ResourceLedger


def test_equal_validity_proof_is_walked_once_within_one_normalization() -> None:
    ledger = ResourceLedger()
    bits = BitFunctionArena(ledger)
    structures = StructureArena(bits)
    port = FinitePort(PortVariable(0, 0, "value", 0), 2)
    variable = structures.atom(bits.variable((port,), port, BOOL))
    constant = structures.atom(bits.constant(FunctionSignature((port,), BOOL), 0))
    assert structures.resolve(variable).valid == structures.resolve(constant).valid
    admissible = bits.functions.atom(FunctionSignature((port,), BOOL), 1)

    before = ledger.counters.get("semantic_structure_totality_pair_visits", 0)
    require_total(structures, variable, admissible)
    single = ledger.counters["semantic_structure_totality_pair_visits"] - before
    require_total_components(structures, (variable, constant), admissible)
    batched = (
        ledger.counters["semantic_structure_totality_pair_visits"] - before - single
    )
    assert batched == single
