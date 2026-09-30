"""Explicit output boundary. Point evaluators never receive this capability."""

from __future__ import annotations

from collections.abc import Callable, Iterator
from sys import getsizeof
from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.exact_tree_context import (
    endpoint_construction,
)
from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
    LoweringCapability,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.output_stream_metrics import closing_output_stream

if TYPE_CHECKING:
    from number_compiler.hashlife.observation.tile_projection import LazyProjection


def iter_canonical_endpoint_digits(
    projection: LazyProjection,
    *,
    owner: ArenaToken,
    capability: LoweringCapability,
) -> Iterator[int]:
    """Emit canonical endpoint leaves once, without repeated point descents."""
    with endpoint_construction(owner, capability):
        if capability.owner is not owner:
            raise ValueError("foreign endpoint lowering capability")
        projection.ledger.bump("endpoint_lowering_requests")
        with closing_output_stream(projection.iter_endpoint_tiles()) as leaves:
            for tile in leaves:
                record = projection.scheduler.tiles.resolve(tile)
                if record.level or record.symbol is None:
                    raise AssertionError("endpoint iterator emitted a non-leaf")
                alphabet = projection.scheduler.tiles.alphabet(record.alphabet)
                if record.symbol == alphabet.blank:
                    raise AssertionError(
                        "blank inside an explicitly requested endpoint"
                    )
                projection.ledger.bump("explicitly_lowered_digits")
                yield record.symbol
        projection.ledger.bump("explicitly_materialized_endpoints")


def iter_endpoint_digits(
    *,
    owner: ArenaToken,
    capability: LoweringCapability,
    width: int,
    blank: int,
    point: Callable[[int], int],
    ledger: ResourceLedger,
    reflect_output: bool = False,
) -> Iterator[int]:
    if type(reflect_output) is not bool:
        raise TypeError("endpoint reflection must be a certified Boolean policy")
    with endpoint_construction(owner, capability):
        if capability.owner is not owner:
            raise ValueError("foreign endpoint lowering capability")
        ledger.bump("endpoint_lowering_requests")
        # This buffer is permitted only inside explicit endpoint lowering. It
        # contains the already emitted part of the requested final output.
        reflected: list[int] = []
        midpoint = (width + 1) // 2
        for position in range(width):
            if reflect_output and position >= midpoint:
                value = reflected[width - 1 - position]
                ledger.bump("endpoint_mirror_reuses")
            else:
                value = point(position)
                if reflect_output:
                    reflected.append(value)
                    ledger.bump(
                        "endpoint_mirror_buffer_peak_bytes",
                        max(
                            0,
                            getsizeof(reflected)
                            - ledger.counters.get(
                                "endpoint_mirror_buffer_peak_bytes", 0
                            ),
                        ),
                    )
            if value == blank:
                raise AssertionError("blank inside an explicitly requested endpoint")
            ledger.bump("explicitly_lowered_digits")
            yield value
        ledger.bump("explicitly_materialized_endpoints")
