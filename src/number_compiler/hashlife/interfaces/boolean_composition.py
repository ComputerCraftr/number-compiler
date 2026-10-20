"""Boolean composition with one canonical implementation owner."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import dataclass
from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_port_action import PortVariable

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_bits import BooleanCircuit


@dataclass(frozen=True, slots=True)
class CompositionKey:
    root: int
    # Integer roots are aligned exactly with tx.node(root).support. The root
    # identity binds this positional layout within one immutable transaction.
    environment: tuple[int, ...]


def substitute_boolean_fused(
    circuit: BooleanCircuit, root: int, replacements: Mapping[PortVariable, int]
) -> int:
    """Run the owning circuit's simultaneous Boolean substitution."""
    return circuit.substitute_fused(root, replacements)
