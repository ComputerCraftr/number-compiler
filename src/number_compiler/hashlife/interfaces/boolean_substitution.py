"""Iterative simultaneous Boolean substitution within one transaction."""

from __future__ import annotations

from collections.abc import Mapping
from typing import TYPE_CHECKING

from number_compiler.arithmetic.functions.finite_port_action import PortVariable

if TYPE_CHECKING:
    from number_compiler.hashlife.interfaces.semantic_bits import BooleanCircuit


def substitute_boolean(
    circuit: BooleanCircuit, root: int, replacements: Mapping[PortVariable, int]
) -> int:
    """Run the owning circuit's simultaneous Boolean substitution."""
    return circuit.substitute(root, replacements)
