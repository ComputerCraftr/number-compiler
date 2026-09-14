"""Independently check the connected output-to-carry composition stores."""

from __future__ import annotations

from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReverseRightTransfer,
)
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.execution.reverse_morphism_transfer import (
    ReverseMorphismTransferArena,
)
from number_compiler.hashlife.tiles.tiles import TileID
from number_compiler.resources.ledger import ResourceLedger


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


def audit_reverse_morphisms(
    ledger: object, roots: tuple[object, ...]
) -> tuple[set[int], set[tuple[int, int]]]:
    approved: set[int] = set()
    invalid: set[tuple[int, int]] = set()
    if not isinstance(ledger, ResourceLedger):
        return approved, invalid
    codec = ReversePortCodec(10)
    containers = dict(ledger.iter_containers())
    for arena in roots:
        if type(arena) is not ReverseMorphismTransferArena:
            continue
        valid_owner = (
            arena.ledger is ledger
            and arena.tiles.ledger is ledger
            and arena.bits.ledger is ledger
        )
        for memo in (
            arena._sources,
            arena._bound,
            arena._compositions,
            arena._right_bound,
            arena._right_compositions,
        ):
            if (
                not valid_owner
                or memo.ledger is not ledger
                or containers.get(memo.owner) is not memo._data
            ):
                invalid.add((memo.owner, id(memo)))
        for source, control in arena._sources.items():
            try:
                node = arena.tiles.resolve(source)
                if (
                    type(control) is not tuple
                    or len(control) != 2
                    or type(control[0]) is not ReverseLeftTransfer
                    or type(control[1]) is not ReverseRightTransfer
                ):
                    raise ValueError("invalid source carry control")
                if node.symbol is not None:
                    expected = (
                        ReverseLeftTransfer.leaf(10, node.symbol),
                        ReverseRightTransfer.leaf(10, node.symbol),
                    )
                else:
                    if node.left is None or node.right is None:
                        raise ValueError("source carry control lacks children")
                    a, b = arena._sources[node.left], arena._sources[node.right]
                    expected = a[0].then(b[0]), b[1].then(a[1])
                if control != expected:
                    raise ValueError("source carry control differs from its source")
            except (TypeError, ValueError, AttributeError, KeyError, IndexError):
                invalid.add((arena._sources.owner, id(control)))
        for key, result in arena._bound.items():
            try:
                if (
                    type(key) is not tuple
                    or len(key) != 2
                    or type(key[0]) is not TileID
                    or type(key[1]) is not tuple
                    or len(key[1]) != 2
                ):
                    raise ValueError("invalid carry morphism binding")
                source, ports = key
                left, right = codec.decode_left(ports[0]), codec.decode_right(ports[1])
                node = arena.tiles.resolve(source)
                if type(result) is not ReverseBoundOutput:
                    raise ValueError("invalid carry morphism output")
                result.__post_init__()
                if node.symbol is not None:
                    kernel = arena.output.kernel
                    if kernel is None or kernel.ledger is not ledger:
                        raise ValueError("carry morphism lost its primitive evaluator")
                    symbol = kernel.effect.emit(left, node.symbol, right)
                    if result != ReverseBoundOutput.leaf(10, symbol):
                        raise ValueError("carry morphism leaf differs from its binding")
                else:
                    if node.left is None or node.right is None:
                        raise ValueError("carry morphism binding lacks children")
                    a, b = arena._sources[node.left], arena._sources[node.right]
                    mid_left = codec.encode_left(a[0].apply(left))
                    mid_right = codec.encode_right(b[1].apply(right))
                    first = arena._bound[node.left, (ports[0], mid_right)]
                    second = arena._bound[node.right, (mid_left, ports[1])]
                    if not _composes(first, second, result):
                        raise ValueError(
                            "carry morphism parent differs from its children"
                        )
            except (TypeError, ValueError, AttributeError, KeyError, IndexError):
                invalid.add((arena._bound.owner, id(result)))
            else:
                approved.update((id(key), id(result)))
        for key, right_result in arena._right_bound.items():
            try:
                if (
                    type(key) is not tuple
                    or len(key) != 2
                    or type(key[0]) is not TileID
                    or type(key[1]) is not tuple
                    or len(key[1]) != 2
                ):
                    raise ValueError("invalid directional binding")
                source, ports = key
                left, right = codec.decode_left(ports[0]), codec.decode_right(ports[1])
                node = arena.tiles.resolve(source)
                if type(right_result) is not ReverseRightTransfer:
                    raise ValueError("invalid directional output")
                right_result.__post_init__()
                if node.symbol is not None:
                    kernel = arena.output.kernel
                    if kernel is None or kernel.ledger is not ledger:
                        raise ValueError("directional binding lost its evaluator")
                    # Independent exact oracle; execution uses only the carry consumer.
                    symbol = kernel.effect.emit(left, node.symbol, right)
                    expected_right = ReverseRightTransfer.leaf(10, symbol)
                else:
                    if node.left is None or node.right is None:
                        raise ValueError("directional binding lacks children")
                    a, b = arena._sources[node.left], arena._sources[node.right]
                    mid_left = codec.encode_left(a[0].apply(left))
                    mid_right = codec.encode_right(b[1].apply(right))
                    first_right = arena._right_bound[node.left, (ports[0], mid_right)]
                    second_right = arena._right_bound[node.right, (mid_left, ports[1])]
                    expected_right = second_right.then(first_right)
                if right_result != expected_right:
                    raise ValueError("directional binding changed its output")
            except (TypeError, ValueError, AttributeError, KeyError, IndexError):
                invalid.add((arena._right_bound.owner, id(right_result)))
            else:
                approved.update((id(key), id(right_result)))
        for right_key, right_value in arena._right_compositions.items():
            try:
                if (
                    type(right_key) is not tuple
                    or len(right_key) != 2
                    or any(
                        type(v) is not ReverseRightTransfer
                        for v in (*right_key, right_value)
                    )
                ):
                    raise ValueError("invalid directional composition")
                for v in (*right_key, right_value):
                    v.__post_init__()
                    if v.base != 10:
                        raise ValueError("directional composition changes radix")
                if right_key[1].then(right_key[0]) != right_value:
                    raise ValueError("directional composition changed its output")
            except (TypeError, ValueError, AttributeError, KeyError, IndexError):
                invalid.add((arena._right_compositions.owner, id(right_value)))
            else:
                approved.update(id(v) for v in (*right_key, right_value))
        for composition, result in arena._compositions.items():
            try:
                if (
                    type(composition) is not tuple
                    or len(composition) != 2
                    or any(
                        type(v) is not ReverseBoundOutput
                        for v in (*composition, result)
                    )
                ):
                    raise ValueError("invalid carry morphism composition")
                if not _composes(*composition, result):
                    raise ValueError("carry morphism composition changed its output")
            except (TypeError, ValueError, AttributeError, KeyError, IndexError):
                invalid.add((arena._compositions.owner, id(result)))
            else:
                approved.update(id(v) for v in (*composition, result))
    return approved, invalid
