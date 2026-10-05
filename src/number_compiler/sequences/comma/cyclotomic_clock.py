"""External occurrence clock for the nine decimal coprime core actions.

The components are residues, not semantic action IDs or elapsed-time weights.
Local selectors use only the characters they need; no 924-entry clock table
or endpoint-specific periodic row is constructed.
"""

from __future__ import annotations

from dataclasses import dataclass

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


@dataclass(frozen=True, slots=True)
class CyclotomicClock:
    mod4: int
    mod3: int
    mod7: int
    mod11: int

    def __post_init__(self) -> None:
        for value, modulus in zip(
            (self.mod4, self.mod3, self.mod7, self.mod11),
            (4, 3, 7, 11),
            strict=True,
        ):
            if type(value) is not int or not 0 <= value < modulus:
                raise ValueError("invalid comma cyclotomic clock character")

    @classmethod
    def from_phase(cls, phase: int) -> CyclotomicClock:
        if type(phase) is not int or phase < 0:
            raise ValueError("comma clock phase must be a nonnegative integer")
        return cls(phase % 4, phase % 3, phase % 7, phase % 11)

    def phase(self, period: int, *, shift: int = 0) -> int:
        """Project a shifted clock onto an admitted core period by exact CRT."""
        if type(period) is not int or type(shift) is not int:
            raise ValueError("invalid comma clock projection")
        if period == 1:
            value = 0
        elif period == 2:
            value = self.mod4 % 2
        elif period == 3:
            value = self.mod3
        elif period == 6:
            value = self.mod3 + 3 * ((self.mod4 - self.mod3) % 2)
        elif period == 22:
            value = self.mod11 + 11 * ((self.mod4 - self.mod11) % 2)
        elif period == 28:
            value = self.mod7 + 7 * ((3 * (self.mod4 - self.mod7)) % 4)
        else:
            raise ValueError("unsupported comma cyclotomic projection")
        return (value + shift) % period


def shifted_component_bit(
    arena: SemanticFunctionArena,
    component: str,
    target_bit: int,
    shift: int,
    modulus: int,
) -> SemanticFunctionID:
    """Compile one bit of a translated finite CRT residue component."""
    width = (modulus - 1).bit_length()
    false = arena.atom(FunctionSignature((), BOOL), 0)
    true = arena.atom(FunctionSignature((), BOOL), 1)
    result = false
    bits: dict[int, SemanticFunctionID] = {}
    for bit in range(width):
        role = f"comma-clock-{component}-b{bit}"
        port = FinitePort(PortVariable(0, 0, role, 0), 2)
        bits[bit] = arena.variable((port,), port, output=BOOL)
    for source_value in range(modulus):
        condition = true
        for bit in range(width):
            signal = bits[bit]
            literal = (
                signal if (source_value >> bit) & 1 else arena.ite(signal, false, true)
            )
            condition = arena.ite(literal, condition, false)
        target_value = (source_value + shift) % modulus
        target = true if (target_value >> target_bit) & 1 else false
        result = arena.ite(condition, target, result)
    return result
