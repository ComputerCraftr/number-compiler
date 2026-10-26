"""Resource binding helper for double-reverse SLP projectors."""

from __future__ import annotations

from collections.abc import MutableMapping
from typing import cast

from number_compiler.arithmetic.automata.slp import BimachineSLPProjector
from number_compiler.resources.ledger import OwnedMemo


def attach_projector_memos(
    projector: BimachineSLPProjector,
    memos: tuple[OwnedMemo[object, object], ...],
) -> None:
    if len(memos) != 5:
        raise ValueError("bimachine projector requires five owned memos")
    projector.bind_cache_stores(
        forward=cast(MutableMapping[tuple[int, int], int | None], memos[0]),
        reverse=cast(MutableMapping[tuple[int, int], int | None], memos[1]),
        block=cast(MutableMapping[tuple[int, int, int], int], memos[2]),
        forward_power=cast(MutableMapping[tuple[int, int, int], int | None], memos[3]),
        reverse_power=cast(MutableMapping[tuple[int, int, int], int | None], memos[4]),
    )
