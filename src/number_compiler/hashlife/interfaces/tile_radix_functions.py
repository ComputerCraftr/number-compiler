"""Closed arithmetic division interfaces in the existing quotient arena."""

from __future__ import annotations

from number_compiler.arithmetic.functions.finite_function_types import (
    BOOL,
    AtomSort,
    FinitePort,
    FunctionSignature,
)
from number_compiler.arithmetic.radix_port_functions import (
    DivisionCarry,
    RadixPortFunction,
)
from number_compiler.hashlife.interfaces.semantic_structures import MacroComponents
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import (
    hashlife_interfaces as _interfaces_keys,
)


def _constant(
    ports: tuple[FinitePort, ...], radix: int, count: int, value: int
) -> RadixPortFunction:
    return RadixPortFunction(
        FunctionSignature(
            ports,
            BOOL
            if count == 2
            else AtomSort(
                "primitive-left-state" if count == 1 else "primitive-symbol", count
            ),
        ),
        radix,
        "constant",
        value=value,
    )


def _finish(
    transfer: RadixPortFunction,
    output: RadixPortFunction,
    active: RadixPortFunction,
    halo_left: RadixPortFunction,
    halo_right: RadixPortFunction,
    first: RadixPortFunction,
    last: RadixPortFunction,
) -> MacroComponents:
    ports, radix = transfer.signature.inputs, transfer.radix
    zero = _constant(ports, radix, 2, 0)
    inactive = (
        _constant(ports, radix, 2, 1 - active.value)
        if active.kind == "constant"
        else RadixPortFunction(
            active.signature, radix, "inactive", threshold=active.threshold
        )
    )
    return MacroComponents(
        _constant(ports, radix, 1, 0),
        transfer,
        output,
        active,
        first,
        last,
        active,
        halo_left,
        halo_right,
        active,
        inactive,
        zero,
        zero,
    )


def division_leaf_components(
    ports: tuple[FinitePort, ...],
    radix: int,
    symbol: int,
) -> MacroComponents:
    carry = DivisionCarry.leaf(radix, symbol)
    transfer = RadixPortFunction(
        FunctionSignature(ports, AtomSort("primitive-right-state", 2 * radix)),
        radix,
        "carry",
        carry,
    )
    output = (
        _constant(ports, radix, 3, 2)
        if symbol == 2
        else RadixPortFunction(
            FunctionSignature(ports, AtomSort("primitive-symbol", 3)),
            radix,
            "output",
            DivisionCarry.identity(radix),
            symbol,
        )
    )
    active = (
        _constant(ports, radix, 2, 0)
        if symbol == 2
        else RadixPortFunction(
            FunctionSignature(ports, BOOL), radix, "active", threshold=carry.threshold
        )
    )
    return _finish(transfer, output, active, output, output, active, active)


def division_parent_components(
    left: MacroComponents,
    right: MacroComponents,
    ledger: ResourceLedger,
) -> MacroComponents:
    aa, bb = left.functions(), right.functions()
    if not all(type(value) is RadixPortFunction for value in (*aa, *bb)):
        raise TypeError("division parent requires closed arithmetic child interfaces")
    a = tuple(value for value in aa if type(value) is RadixPortFunction)
    b = tuple(value for value in bb if type(value) is RadixPortFunction)
    before = b[1].carry
    if before is None or a[1].kind != "carry" or b[1].kind != "carry":
        raise ValueError("division child is missing its outgoing carry function")
    if a[1].signature != b[1].signature or a[1].radix != b[1].radix:
        raise ValueError("division children belong to different finite interfaces")
    transfer = a[1].through(before, ledger)
    output = a[2].through(before, ledger)
    first, last = a[3].through(before, ledger), b[3]
    if first.kind == "constant":
        if first.value != 0:
            raise ValueError("unexpected division activity constant")
        active = last
    elif last.kind == "constant":
        if last.value != 0:
            raise ValueError("unexpected division activity constant")
        active = first
    else:
        # Both nonempty halves observe the same incoming active bit. Their
        # disjunction is a single activation threshold. The full transfer is
        # precisely that threshold, including resets in the higher half.
        active = RadixPortFunction(
            first.signature,
            transfer.radix,
            "active",
            threshold=transfer.carry.threshold if transfer.carry is not None else None,
        )
    ledger.bump(_interfaces_keys.TILE_RADIX_ARITHMETIC_PARENT_INTERFACES)
    return _finish(
        transfer, output, active, a[7].through(before, ledger), b[8], first, last
    )


__all__ = ["division_leaf_components", "division_parent_components"]
