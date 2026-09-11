"""Closed reverse-add interval interfaces in the shared quotient arena."""

from __future__ import annotations

from dataclasses import replace

from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReversePortFunction,
    ReverseRightTransfer,
)
from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.hashlife.interfaces.diamond_quotient import MacroComponents
from number_compiler.hashlife.interfaces.tile_reverse_sector_functions import (
    compose_reverse_sectors,
)
from number_compiler.resources.ledger import ResourceLedger


def _constant(
    ports: tuple[FinitePort, ...], base: int, output: AtomSort, value: int
) -> ReversePortFunction:
    return ReversePortFunction(
        FunctionSignature(ports, output), base, "constant", value=value
    )


def _predicate(
    ports: tuple[FinitePort, ...], base: int, truth_bits: int
) -> ReversePortFunction:
    return ReversePortFunction(
        FunctionSignature(ports, BOOL), base, "predicate", truth_bits=truth_bits
    )


def _finish(
    left: ReversePortFunction,
    right: ReversePortFunction,
    output: ReversePortFunction,
    active: ReversePortFunction,
    halo_left: ReversePortFunction,
    halo_right: ReversePortFunction,
    first: ReversePortFunction,
    last: ReversePortFunction,
) -> MacroComponents:
    if active.kind != "predicate":
        raise ValueError("reverse interval activity requires a closed predicate")
    ports, base = active.signature.inputs, active.base
    zero = _constant(ports, base, BOOL, 0)
    return MacroComponents(
        left,
        right,
        output,
        active,
        first,
        last,
        active,
        halo_left,
        halo_right,
        active,
        active.predicate_not(),
        zero,
        zero,
    )


def reverse_leaf_components(
    ports: tuple[FinitePort, ...],
    base: int,
    symbol: int,
    ledger: ResourceLedger,
) -> MacroComponents:
    """Return all thirteen exact channels for one primitive pair symbol."""
    codec = ReversePortCodec(base)
    blank = 2 * base - 1
    if type(symbol) is not int or not 0 <= symbol <= blank:
        raise ValueError("reverse leaf symbol lies outside its alphabet")
    left_transfer = ReverseLeftTransfer.leaf(base, symbol)
    right_transfer = ReverseRightTransfer.leaf(base, symbol)
    left = ReversePortFunction(
        FunctionSignature(ports, AtomSort("primitive-left-state", codec.left_count)),
        base,
        "left-transfer",
        left=left_transfer,
    )
    right = ReversePortFunction(
        FunctionSignature(ports, AtomSort("primitive-right-state", codec.right_count)),
        base,
        "right-transfer",
        right=right_transfer,
    )
    output = ReversePortFunction(
        FunctionSignature(ports, AtomSort("primitive-symbol", blank + 1)),
        base,
        "output",
        ReverseLeftTransfer.identity(base),
        ReverseRightTransfer.identity(base),
        symbol,
    )
    active = _predicate(ports, base, codec.active_truth_bits(symbol))
    return _finish(
        left,
        right,
        output,
        active,
        output,
        output,
        active,
        active,
    )


def reverse_parent_components(
    left: MacroComponents,
    right: MacroComponents,
    ledger: ResourceLedger,
) -> MacroComponents:
    """Compose adjacent reverse intervals using only bounded closed records."""
    raw_left, raw_right = left.functions(), right.functions()
    if not all(type(value) is ReversePortFunction for value in (*raw_left, *raw_right)):
        raise TypeError("reverse parent requires closed arithmetic child interfaces")
    a = tuple(value for value in raw_left if type(value) is ReversePortFunction)
    b = tuple(value for value in raw_right if type(value) is ReversePortFunction)
    if len(a) != 13 or len(b) != 13 or a[0].base != b[0].base:
        raise ValueError("reverse children have another complete interface")
    if (
        a[0].kind != "left-transfer"
        or a[1].kind != "right-transfer"
        or b[0].kind != "left-transfer"
        or b[1].kind != "right-transfer"
        or a[0].left is None
        or a[1].right is None
        or b[0].left is None
        or b[1].right is None
    ):
        raise ValueError("reverse children omit a directional transfer")
    base = a[0].base
    identity_left = ReverseLeftTransfer.identity(base)
    identity_right = ReverseRightTransfer.identity(base)
    left_transfer = a[0].left.then(b[0].left, ledger)
    right_transfer = b[1].right.then(a[1].right, ledger)
    parent_left = ReversePortFunction(
        a[0].signature, base, "left-transfer", left=left_transfer
    )
    parent_right = ReversePortFunction(
        a[1].signature, base, "right-transfer", right=right_transfer
    )
    a_output = a[2].through(identity_left, b[1].right, ledger)
    a_active = a[3].through(identity_left, b[1].right, ledger)
    b_active = b[3].through(a[0].left, identity_right, ledger)
    active = a_active.predicate_or(b_active, ledger)
    halo_left = a[7].through(identity_left, b[1].right, ledger)
    halo_right = b[8].through(a[0].left, identity_right, ledger)
    ledger.bump("reverse_port_parent_interfaces")
    result = _finish(
        parent_left,
        parent_right,
        a_output,
        active,
        halo_left,
        halo_right,
        a_active,
        b_active,
    )
    if left.reverse_sectors is None and right.reverse_sectors is None:
        return result
    return replace(
        result,
        reverse_sectors=compose_reverse_sectors(
            left.reverse_sectors,
            right.reverse_sectors,
            ledger=ledger,
        ),
    )


__all__ = [
    "reverse_leaf_components",
    "reverse_parent_components",
]
