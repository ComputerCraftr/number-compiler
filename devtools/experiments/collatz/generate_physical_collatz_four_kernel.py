"""Offline proof builder for the immutable physical C^4 primitive artifact."""

from __future__ import annotations

import hashlib
import zlib

from devtools.paths import repository_root
from devtools.proofs.block_composed import ComposedBlockEffect
from devtools.proofs.block_power import compose_block_effects
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudget,
    BoundarySide,
    _state_key,
)
from number_compiler.sequences.collatz.block_power import CollatzPhysicalBlockEffect


def build() -> bytes:
    budget = BlockContextBudget()
    c1 = CollatzPhysicalBlockEffect()
    c2 = compose_block_effects(c1, c1, budget=budget)
    effect = ComposedBlockEffect(c2, c2, budget=budget, _force_functional=True)
    left = effect.boundary_universe(BoundarySide.LEFT)
    right = effect.boundary_universe(BoundarySide.RIGHT)
    assert (
        left is not None and right is not None and (len(left), len(right)) == (50, 90)
    )
    domains = (left, right)
    indices = tuple(
        {_state_key(state): index for index, state in enumerate(domain)}
        for domain in domains
    )
    transitions = tuple(
        bytes(
            indices[int(side)][_state_key(effect.advance(side, state, symbol))]
            for state in domains[int(side)]
            for symbol in range(3)
        )
        for side in BoundarySide
    )
    outputs = bytes(
        effect.emit(lstate, symbol, rstate)
        for lstate in left
        for symbol in range(3)
        for rstate in right
    )
    header = b"PC4KERN1" + bytes((2, 2, 4, 50, 90, 0, 0, 8, 7))
    assert all(
        indices[int(side)][_state_key(effect.initial(side))] == 0
        for side in BoundarySide
    )
    return header + transitions[0] + transitions[1] + outputs


if __name__ == "__main__":
    raw = build()
    packed = zlib.compress(raw, level=9)
    path = repository_root() / "src/number_compiler/kernels/physical_collatz_four.zlib"
    path.write_bytes(packed)
    print("raw_sha256", hashlib.sha256(raw).hexdigest())
    print("packed_sha256", hashlib.sha256(packed).hexdigest())
    print("raw_bytes", len(raw), "packed_bytes", len(packed))
