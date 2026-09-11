"""Compose next carry responses from output morphisms at known producer ports.

Producer bindings specialize the coordinate output before spatial composition.
The result remains a function of every primitive consumer carry state; it is
never an exact output row or a whole-state future-behavior certificate.
"""

from __future__ import annotations

from number_compiler.arithmetic.carry.reverse_port_functions import (
    ReverseLeftTransfer,
    ReversePortCodec,
    ReverseRightTransfer,
)
from number_compiler.arithmetic.contracts.block_kernel import _reverse_output_carry
from number_compiler.hashlife.behavior.reverse_bound_output import ReverseBoundOutput
from number_compiler.hashlife.interfaces.semantic_bits import BitFunctionArena
from number_compiler.hashlife.interfaces.diamond_kernel import PrimitiveKernel
from number_compiler.hashlife.tiles.tiles import TileArena, TileID
from number_compiler.resources.fused_traversal_workspace import FusedTraversalWorkspace
from number_compiler.resources.ledger import OwnedMemo
from number_compiler.sequences.reverse_add.primitive_output_morphism import (
    ReversePrimitiveOutputMorphism,
)

_SourceControl = tuple[ReverseLeftTransfer, ReverseRightTransfer]
_Binding = tuple[TileID, tuple[int, int]]


class ReverseMorphismTransferArena:
    """Known producer ports feed the next consumer's entire finite carry law."""

    def __init__(
        self, tiles: TileArena, bits: BitFunctionArena, kernel: PrimitiveKernel
    ) -> None:
        if tiles.ledger is not bits.ledger:
            raise ValueError("reverse carry morphisms require one resource owner")
        self.tiles, self.bits, self.ledger = tiles, bits, bits.ledger
        self.output = ReversePrimitiveOutputMorphism(bits, kernel)
        self.ledger.register_execution_root(self)
        prefix = f"reverse-morphism-transfer-{len(self.ledger.inventory())}"
        source_owner = self.ledger.register(prefix + "-sources", "query_memo")
        self._sources: OwnedMemo[TileID, _SourceControl] = OwnedMemo(
            self.ledger,
            source_owner,
            nodes_per_entry=9,
            evictable=True,
        )
        bound_owner = self.ledger.register(prefix + "-bindings", "query_memo")
        self._bound: OwnedMemo[_Binding, ReverseBoundOutput] = OwnedMemo(
            self.ledger,
            bound_owner,
            nodes_per_entry=9,
            evictable=True,
        )
        composition_owner = self.ledger.register(prefix + "-composition", "query_memo")
        self._compositions: OwnedMemo[
            tuple[ReverseBoundOutput, ReverseBoundOutput], ReverseBoundOutput
        ] = OwnedMemo(self.ledger, composition_owner, nodes_per_entry=9, evictable=True)
        right_owner = self.ledger.register(prefix + "-right-bindings", "query_memo")
        self._right_bound: OwnedMemo[_Binding, ReverseRightTransfer] = OwnedMemo(
            self.ledger, right_owner, nodes_per_entry=2, evictable=True
        )
        right_composition_owner = self.ledger.register(
            prefix + "-right-composition", "query_memo"
        )
        self._right_compositions: OwnedMemo[
            tuple[ReverseRightTransfer, ReverseRightTransfer], ReverseRightTransfer
        ] = OwnedMemo(
            self.ledger, right_composition_owner, nodes_per_entry=2, evictable=True
        )
        self._workspace = FusedTraversalWorkspace(self.ledger, prefix)

    def clear_bindings(self) -> None:
        """Release source occurrences before the query's tile leases retire."""
        self._bound.clear()
        self._right_bound.clear()
        self._sources.clear()

    def _source_control(self, source: TileID) -> _SourceControl:
        node = self.tiles.resolve(source)
        cached = self._sources.get(source)
        if cached is not None:
            return cached
        workspace = self._workspace
        with workspace.scope(node.level, 9):
            workspace.append_frame((source, False))
            while workspace.frames:
                frame = workspace.pop_frame()
                if type(frame) is not tuple or len(frame) != 2:
                    raise TypeError("source control lost its traversal frame")
                tile, ready = frame
                record = self.tiles.resolve(tile)
                cached = self._sources.get(tile)
                if cached is not None:
                    workspace.append_value(cached)
                    continue
                if not record.level:
                    if record.symbol is None:
                        raise ValueError("source control leaf has no symbol")
                    result = (
                        ReverseLeftTransfer.leaf(10, record.symbol),
                        ReverseRightTransfer.leaf(10, record.symbol),
                    )
                elif ready:
                    second, first = workspace.pop_value(), workspace.pop_value()
                    if type(first) is not tuple or type(second) is not tuple:
                        raise TypeError("source control lost its children")
                    result = (
                        first[0].then(second[0], self.ledger),
                        second[1].then(first[1], self.ledger),
                    )
                else:
                    if record.left is None or record.right is None:
                        raise ValueError("source control parent has no children")
                    workspace.append_frame((tile, True))
                    workspace.append_frame((record.right, False))
                    workspace.append_frame((record.left, False))
                    continue
                self._sources[tile] = result
                workspace.append_value(result)
            root = workspace.pop_value()
            if (
                type(root) is not tuple
                or len(root) != 2
                or workspace.values
                or type(root[0]) is not ReverseLeftTransfer
                or type(root[1]) is not ReverseRightTransfer
            ):
                raise TypeError("source control produced an invalid root")
            return root[0], root[1]

    def compile_bound(
        self, source: TileID, ports: tuple[int, int]
    ) -> ReverseBoundOutput:
        result = self._compile(source, ports, right_only=False)
        if type(result) is not ReverseBoundOutput:
            raise TypeError("complete output requires both directional summaries")
        return result

    def compile_right(
        self, source: TileID, ports: tuple[int, int]
    ) -> ReverseRightTransfer:
        """Reduce the demanded domain stream before spatial composition.

        No exact output symbol, normalized digit ID, or left edge payload is
        interned. Equality is the resulting pair of carry-monoid actions.
        """
        result = self._compile(source, ports, right_only=True)
        if type(result) is not ReverseRightTransfer:
            raise TypeError("right output requires a directional summary")
        return result

    def _compile(
        self, source: TileID, ports: tuple[int, int], *, right_only: bool
    ) -> ReverseBoundOutput | ReverseRightTransfer:
        node = self.tiles.resolve(source)
        alphabet = self.tiles.alphabet(node.alphabet)
        if (
            (alphabet.radix, alphabet.blank, alphabet.symbol_count, alphabet.cell_bits)
            != (10, 19, 20, 5)
            or alphabet.interpretation != "unsigned-radix-cell-with-explicit-blank"
            or alphabet.version != "canonical-tile-alphabet-v1"
        ):
            raise ValueError(
                "reverse carry morphism requires the decimal pair alphabet"
            )
        codec = ReversePortCodec(10)
        if type(ports) is not tuple or len(ports) != 2:
            raise TypeError("producer morphism requires two finite ports")
        codec.decode_left(ports[0])
        codec.decode_right(ports[1])
        memo = self._right_bound if right_only else self._bound
        cached = memo.get((source, ports))
        if cached is not None:
            self.ledger.bump("reverse_morphism_bound_hits")
            return cached
        self._source_control(source)
        workspace = self._workspace
        with workspace.scope(node.level, 2 if right_only else 9):
            workspace.append_frame((source, ports, False))
            while workspace.frames:
                frame = workspace.pop_frame()
                if type(frame) is not tuple or len(frame) != 3:
                    raise TypeError("output morphism lost its traversal frame")
                tile, incoming, ready = frame
                record = self.tiles.resolve(tile)
                cached = memo.get((tile, incoming))
                if cached is not None:
                    workspace.append_value(cached)
                    continue
                if not record.level:
                    if record.symbol is None:
                        raise ValueError("output morphism leaf has no symbol")
                    if right_only:
                        action = _reverse_output_carry(
                            10,
                            codec.decode_left(incoming[0]),
                            record.symbol,
                            codec.decode_right(incoming[1]),
                        )
                        result: ReverseBoundOutput | ReverseRightTransfer = (
                            ReverseRightTransfer(10, action, action)
                        )
                        self.ledger.bump("reverse_morphism_directional_leaf_consumers")
                    else:
                        function = self.output.bind(record.symbol, incoming)
                        symbol = self.bits.evaluate(function, {})
                        if type(symbol) is not int:
                            raise ValueError(
                                "output morphism is undefined on producer ports"
                            )
                        result = ReverseBoundOutput.leaf(10, symbol)
                        self.ledger.bump("reverse_morphism_leaf_bindings")
                elif ready:
                    second, first = workspace.pop_value(), workspace.pop_value()
                    if right_only:
                        if (
                            type(first) is not ReverseRightTransfer
                            or type(second) is not ReverseRightTransfer
                        ):
                            raise TypeError("right morphism lost its carry functions")
                        right_composed = self._right_compositions.get((first, second))
                        if right_composed is None:
                            right_composed = second.then(first, self.ledger)
                            self._right_compositions[first, second] = right_composed
                            self.ledger.bump(
                                "reverse_morphism_directional_compositions"
                            )
                        else:
                            self.ledger.bump("reverse_morphism_composition_hits")
                        result = right_composed
                    else:
                        if (
                            type(first) is not ReverseBoundOutput
                            or type(second) is not ReverseBoundOutput
                        ):
                            raise TypeError("output morphism lost its carry functions")
                        composed = self._compositions.get((first, second))
                        if composed is None:
                            composed = first.then(second, self.ledger)
                            self._compositions[first, second] = composed
                            self.ledger.bump("reverse_morphism_spatial_compositions")
                        else:
                            self.ledger.bump("reverse_morphism_composition_hits")
                        result = composed
                else:
                    if record.left is None or record.right is None:
                        raise ValueError("output morphism parent has no children")
                    a, b = self._sources[record.left], self._sources[record.right]
                    mid_left = codec.encode_left(
                        a[0].apply(codec.decode_left(incoming[0]))
                    )
                    mid_right = codec.encode_right(
                        b[1].apply(codec.decode_right(incoming[1]))
                    )
                    workspace.append_frame((tile, incoming, True))
                    workspace.append_frame(
                        (record.right, (mid_left, incoming[1]), False)
                    )
                    workspace.append_frame(
                        (record.left, (incoming[0], mid_right), False)
                    )
                    continue
                if type(result) is ReverseRightTransfer:
                    self._right_bound[tile, incoming] = result
                elif type(result) is ReverseBoundOutput:
                    self._bound[tile, incoming] = result
                else:
                    raise TypeError("morphism produced another result sort")
                self.ledger.bump("reverse_morphism_output_bindings")
                workspace.append_value(result)
            root = workspace.pop_value()
            expected = ReverseRightTransfer if right_only else ReverseBoundOutput
            if (
                (
                    type(root) is not ReverseBoundOutput
                    and type(root) is not ReverseRightTransfer
                )
                or type(root) is not expected
                or workspace.values
            ):
                raise TypeError("output morphism produced an invalid carry root")
            return root

    def consume(
        self, source: TileID, producer_ports: tuple[int, int], side: int, state: int
    ) -> int:
        if type(side) is not int or side not in (0, 1):
            raise ValueError("reverse morphism requires a directed consumer")
        codec = ReversePortCodec(10)
        if side:
            codec.decode_right(state)
        else:
            codec.decode_left(state)
        if side:
            transfer = self.compile_right(source, producer_ports)
            result = codec.encode_right(transfer.apply(codec.decode_right(state)))
        else:
            result = self.compile_bound(source, producer_ports).apply(side, state)
        self.ledger.bump("reverse_morphism_transfer_observations")
        return result
