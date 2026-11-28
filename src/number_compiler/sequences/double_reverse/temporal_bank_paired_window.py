"""Exact adjacent physical pair windows sharing source-bound causal cones."""

from __future__ import annotations

from typing import TYPE_CHECKING

from .temporal_bank_output_morphism import frame_from_digits

if TYPE_CHECKING:
    from .protected_temporal_bank import PeriodicBankFrame
    from .source_bound_bank import PointedBankSource


def batch_admitted(source: PointedBankSource, count: int) -> bool:
    """Decline the optional wider scratch path before opening any cone."""
    ledger = source.ledger
    return count > 1 and ledger.max_nodes is None and ledger.max_cache_entries is None


def paired_window_frames(
    source: PointedBankSource,
    coordinates: tuple[int, int, int, int, int],
) -> list[PeriodicBankFrame]:
    """Read both reflected banks and their next physical F-row in order."""
    start, count, birth_left, birth_right, next_width = coordinates
    frames: list[PeriodicBankFrame] = []
    engine = source.engine
    for offset in range(0, count, 18):
        size = min(18, count - offset)
        position = start + offset
        following = position + birth_left
        with source.ledger.reservation(
            source.scratch_owner, entries=4 * size, nodes=4 * size
        ):
            left = engine.pointed_window(
                source.root, source.f_steps, source.phase, position, size
            )
            right = engine.pointed_window(
                source.root,
                source.f_steps,
                source.phase,
                source.width_out - position - size,
                size,
            )
            next_left = engine.pointed_window(
                source.root, source.f_steps + 1, source.phase, following, size
            )
            next_right = engine.pointed_window(
                source.root,
                source.f_steps + 1,
                source.phase,
                next_width - following - size,
                size,
            )
            for a, b, c, d in zip(
                left, reversed(right), next_left, reversed(next_right), strict=True
            ):
                frames.append(
                    frame_from_digits((a, b), (c, d), birth_left, birth_right)
                )
    return frames
