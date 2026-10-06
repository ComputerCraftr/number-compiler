"""Exact ownership and recurrence audit for reverse carry morphisms."""

from __future__ import annotations

from collections.abc import Callable
from typing import cast

from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReverseRightTransfer,
)
from number_compiler.arithmetic.contracts.block_kernel import (
    _BaseLeftState,
    _BaseRightState,
)
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.tiles.tiles import TileID, TileRecord
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.payload_containers import audit_mapping_items
from number_compiler.resources.payload_contracts import (
    PayloadAuditContribution,
    PayloadAuditEntry,
)
from number_compiler.sequences.reverse_add.reverse_morphism_transfer import (
    ReverseMorphismTransferArena,
)


def _composes(
    first: ReverseBoundOutput, second: ReverseBoundOutput, result: ReverseBoundOutput
) -> bool:
    for value in (first, second, result):
        value.__post_init__()
        if value.left.base != 10:
            return False
    return (
        first.left.then(second.left) == result.left
        and second.right.then(first.right) == result.right
    )


def audit_reverse_morphism_arena(
    ledger_value: object, root_value: object
) -> PayloadAuditContribution:
    """Check every retained binding against its source and child composition.

    The validator is registered on the family-owned arena. Its contribution
    includes only direct keys and values of the five exact ledger stores.
    """
    if (
        type(ledger_value) is not ResourceLedger
        or type(root_value) is not ReverseMorphismTransferArena
    ):
        raise TypeError("reverse morphism contract received a foreign root")
    ledger = ledger_value
    root = root_value
    stores = cast(
        tuple[OwnedMemo[object, object], ...],
        (
            root._sources,
            root._bound,
            root._compositions,
            root._right_bound,
            root._right_compositions,
        ),
    )
    root_valid = (
        root.ledger is ledger
        and root.tiles.ledger is ledger
        and root.bits.ledger is ledger
    )
    approved: list[PayloadAuditEntry] = []
    invalid: list[PayloadAuditEntry] = []

    def add_pair(
        owner: int,
        rows: tuple[tuple[object, object], ...],
        check: Callable[[object, object], None],
    ) -> None:
        for key, value in rows:
            try:
                check(key, value)
            except (
                ArithmeticError,
                AttributeError,
                IndexError,
                KeyError,
                RuntimeError,
                TypeError,
                ValueError,
            ):
                invalid.extend(
                    (PayloadAuditEntry(owner, key), PayloadAuditEntry(owner, value))
                )
            else:
                approved.extend(
                    (PayloadAuditEntry(owner, key), PayloadAuditEntry(owner, value))
                )

    def check_sources(key: object, value: object) -> None:
        if type(key) is not TileID:
            raise ValueError("source control has a non-tile key")
        node = root.tiles.resolve(key)
        if (
            type(value) is not tuple
            or len(value) != 2
            or type(value[0]) is not ReverseLeftTransfer
            or type(value[1]) is not ReverseRightTransfer
        ):
            raise ValueError("source control has an invalid carry pair")
        if node.symbol is not None:
            expected = (
                ReverseLeftTransfer.leaf(10, node.symbol),
                ReverseRightTransfer.leaf(10, node.symbol),
            )
        else:
            if node.left is None or node.right is None:
                raise ValueError("source control has no child tiles")
            left = root._sources[node.left]
            right = root._sources[node.right]
            expected = left[0].then(right[0]), right[1].then(left[1])
        if value != expected:
            raise ValueError("source control differs from the exact tile word")

    def binding_inputs(
        source: object, ports: object
    ) -> tuple[TileRecord, _BaseLeftState, _BaseRightState]:
        if type(source) is not TileID or type(ports) is not tuple or len(ports) != 2:
            raise ValueError("morphism binding has malformed source or ports")
        codec = ReversePortCodec(10)
        if any(type(port) is not int for port in ports):
            raise ValueError("morphism binding ports must be exact integers")
        return (
            root.tiles.resolve(source),
            codec.decode_left(ports[0]),
            codec.decode_right(ports[1]),
        )

    def interior_ports(
        left_tile: TileID,
        right_tile: TileID,
        left: _BaseLeftState,
        right: _BaseRightState,
    ) -> tuple[int, int]:
        codec = ReversePortCodec(10)
        left_control = root._sources[left_tile]
        right_control = root._sources[right_tile]
        return (
            codec.encode_left(left_control[0].apply(left)),
            codec.encode_right(right_control[1].apply(right)),
        )

    def check_bound(key: object, value: object) -> None:
        if type(key) is not tuple or len(key) != 2:
            raise ValueError("bound morphism key is malformed")
        source, ports = key
        node, left, right = binding_inputs(source, ports)
        if type(value) is not ReverseBoundOutput:
            raise ValueError("bound morphism has another output type")
        value.__post_init__()
        if node.symbol is not None:
            kernel = root.output.kernel
            if kernel is None or kernel.ledger is not ledger:
                raise ValueError("bound morphism lost its primitive evaluator")
            symbol = kernel.effect.emit(left, node.symbol, right)
            if value != ReverseBoundOutput.leaf(10, symbol):
                raise ValueError("bound morphism leaf differs from its source")
            return
        if node.left is None or node.right is None:
            raise ValueError("bound morphism parent has no children")
        mid_left, mid_right = interior_ports(node.left, node.right, left, right)
        first = root._bound[node.left, (ports[0], mid_right)]
        second = root._bound[node.right, (mid_left, ports[1])]
        if not _composes(first, second, value):
            raise ValueError("bound morphism differs from child composition")

    def check_right_bound(key: object, value: object) -> None:
        if type(key) is not tuple or len(key) != 2:
            raise ValueError("directional morphism key is malformed")
        source, ports = key
        node, left, right = binding_inputs(source, ports)
        if type(value) is not ReverseRightTransfer:
            raise ValueError("directional morphism has another output type")
        value.__post_init__()
        if node.symbol is not None:
            kernel = root.output.kernel
            if kernel is None or kernel.ledger is not ledger:
                raise ValueError("directional morphism lost its evaluator")
            symbol = kernel.effect.emit(left, node.symbol, right)
            expected = ReverseRightTransfer.leaf(10, symbol)
        else:
            if node.left is None or node.right is None:
                raise ValueError("directional morphism parent has no children")
            mid_left, mid_right = interior_ports(node.left, node.right, left, right)
            first = root._right_bound[node.left, (ports[0], mid_right)]
            second = root._right_bound[node.right, (mid_left, ports[1])]
            expected = second.then(first)
        if value != expected:
            raise ValueError("directional morphism differs from child composition")

    def check_right_composition(key: object, value: object) -> None:
        if type(key) is not tuple or len(key) != 2:
            raise ValueError("directional composition key is malformed")
        first, second = key
        if any(
            type(item) is not ReverseRightTransfer for item in (first, second, value)
        ):
            raise ValueError("directional composition has an invalid carrier")
        first_transfer = cast(ReverseRightTransfer, first)
        second_transfer = cast(ReverseRightTransfer, second)
        result_transfer = cast(ReverseRightTransfer, value)
        for item in (first_transfer, second_transfer, result_transfer):
            item.__post_init__()
            if item.base != 10:
                raise ValueError("directional composition changes radix")
        if second_transfer.then(first_transfer) != result_transfer:
            raise ValueError("directional composition changed its output")

    def check_composition(key: object, value: object) -> None:
        if type(key) is not tuple or len(key) != 2:
            raise ValueError("morphism composition key is malformed")
        first, second = key
        if any(type(item) is not ReverseBoundOutput for item in (first, second, value)):
            raise ValueError("morphism composition has an invalid carrier")
        if not _composes(
            cast(ReverseBoundOutput, first),
            cast(ReverseBoundOutput, second),
            cast(ReverseBoundOutput, value),
        ):
            raise ValueError("morphism composition changed its output")

    if not root_valid:
        invalid.append(PayloadAuditEntry(stores[0].owner, root))
        return PayloadAuditContribution((), tuple(invalid))
    for memo in stores:
        try:
            live_store = ledger.registered_container(memo.owner)
        except RuntimeError:
            live_store = None
        if memo.ledger is not ledger or live_store is not memo._data:
            invalid.append(PayloadAuditEntry(stores[0].owner, root))
            return PayloadAuditContribution((), tuple(invalid))

    checks: tuple[Callable[[object, object], None], ...] = (
        check_sources,
        check_bound,
        check_composition,
        check_right_bound,
        check_right_composition,
    )
    for memo, check in zip(stores, checks, strict=True):
        rows = cast(tuple[tuple[object, object], ...], audit_mapping_items(memo))
        add_pair(memo.owner, rows, check)
    return PayloadAuditContribution(tuple(approved), tuple(invalid))


__all__ = ["audit_reverse_morphism_arena"]
