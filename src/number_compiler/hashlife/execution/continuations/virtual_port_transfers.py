"""Bounded virtual-port transfer dispatch without dense domain enumeration."""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID


def validate_virtual_transfer(
    adapter: object,
    action: FieldCellActionID,
    side: int,
    transfer: object,
) -> None:
    if type(transfer) is tuple:
        count = cast(
            Callable[[FieldCellActionID, int], int],
            getattr(
                adapter,
                "primitive_state_count",
            ),
        )(action, side)
        if len(transfer) != count or any(
            type(value) is not int or not 0 <= value < count for value in transfer
        ):
            raise ValueError("virtual interface has another bounded port domain")
        return
    validator = getattr(adapter, "validate_virtual_transfer", None)
    if validator is None:
        raise TypeError("adapter does not admit symbolic virtual transfers")
    cast(
        Callable[[FieldCellActionID, int, object], None],
        validator,
    )(action, side, transfer)


def virtual_transfer_leaf(
    adapter: object,
    action: FieldCellActionID,
    side: int,
    symbol: int,
) -> object:
    hook = getattr(adapter, "virtual_transfer_leaf", None)
    if hook is not None:
        result = cast(
            Callable[[FieldCellActionID, int, int], object | None],
            hook,
        )(action, side, symbol)
        if result is not None:
            validate_virtual_transfer(adapter, action, side, result)
            return result
    count = cast(
        Callable[[FieldCellActionID, int], int],
        getattr(
            adapter,
            "primitive_state_count",
        ),
    )(action, side)
    advance = cast(
        Callable[[FieldCellActionID, int, int, int], int],
        getattr(adapter, "primitive_advance"),
    )
    result = tuple(advance(action, side, state, symbol) for state in range(count))
    validate_virtual_transfer(adapter, action, side, result)
    return result


def compose_virtual_transfers(
    adapter: object,
    action: FieldCellActionID,
    side: int,
    first: object,
    second: object,
) -> object:
    hook = getattr(adapter, "compose_virtual_transfers", None)
    if hook is not None:
        result = cast(
            Callable[[FieldCellActionID, int, object, object], object | None],
            hook,
        )(action, side, first, second)
        if result is not None:
            validate_virtual_transfer(adapter, action, side, result)
            return result
    if type(first) is not tuple or type(second) is not tuple:
        raise TypeError("adapter cannot compose symbolic virtual transfers")
    result = tuple(second[first[state]] for state in range(len(first)))
    validate_virtual_transfer(adapter, action, side, result)
    return result


def apply_virtual_transfer(
    adapter: object,
    action: FieldCellActionID,
    side: int,
    transfer: object,
    state: int,
) -> int:
    hook = getattr(adapter, "apply_virtual_transfer", None)
    if hook is not None:
        result = cast(
            Callable[[FieldCellActionID, int, object, int], int | None],
            hook,
        )(action, side, transfer, state)
        if result is not None:
            if type(result) is not int:
                raise TypeError("symbolic virtual transfer returned a noninteger state")
            return result
    if type(transfer) is not tuple:
        raise TypeError("adapter cannot apply a symbolic virtual transfer")
    return cast(int, transfer[state])


__all__ = [
    "apply_virtual_transfer",
    "compose_virtual_transfers",
    "validate_virtual_transfer",
    "virtual_transfer_leaf",
]
