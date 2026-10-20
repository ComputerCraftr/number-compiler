"""Canonical finite consumer fixtures shared by probes and adversarial tests."""

from number_compiler.arithmetic.carry.event_memory import carry_field, pair_step
from number_compiler.arithmetic.functions.finite_function_types import FinitePort
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.hashlife.interfaces.semantic_bits import (
    BitFunctionArena,
    FactoredFunctionID,
)
from number_compiler.sequences.collatz.output_morphism import (
    CARRY,
    DIGIT,
    RESIDUAL_SHIFT,
)


def free_collatz_variables(
    bits: BitFunctionArena,
) -> tuple[
    tuple[FinitePort, ...], FactoredFunctionID, FactoredFunctionID, FactoredFunctionID
]:
    ports = (
        FinitePort(PortVariable(0, 0, "digit-occurrence", 0), 64),
        FinitePort(PortVariable(0, 1, "incoming-carry", 0), 3),
        FinitePort(PortVariable(0, 2, "root-shift-query", 0), 6),
    )
    digit = bits.variable(ports, ports[0], DIGIT)
    carry = bits.variable(ports, ports[1], CARRY)
    shift = bits.variable(ports, ports[2], RESIDUAL_SHIFT)
    return ports, digit, carry, shift


def carry_seed_rows(
    pair: tuple[int, ...], count: int, base: int = 10
) -> tuple[tuple[int, ...], list[tuple[int, ...]]]:
    rows: list[tuple[int, ...]] = []
    for _ in range(count):
        rows.append(carry_field(pair, base=base))
        pair, _ = pair_step(pair, base)
    return pair, rows
