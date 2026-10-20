"""Typed test access to the iterative causal frame runner."""

from __future__ import annotations

from collections.abc import Callable
from typing import Protocol, cast

from number_compiler.hashlife.actions.field_actions import FieldCellActionID
from number_compiler.hashlife.execution.causal_frames import CausalTaskFrame
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.resources.causal_types import CausalState


class _CausalFrameRunner(Protocol):
    def __call__(
        self,
        root: CausalTaskFrame,
        *,
        tile_result: bool,
        return_result: bool = False,
    ) -> object: ...


def run_causal_frame(
    engine: CausalTileEngine,
    frame: CausalTaskFrame,
    *,
    tile_result: bool,
    return_result: bool = False,
) -> object:
    """Run a selected internal frame in a focused regression test."""
    runner = cast(_CausalFrameRunner, object.__getattribute__(engine, "_run"))
    return runner(frame, tile_result=tile_result, return_result=return_result)


def initial_causal_state(
    engine: CausalTileEngine,
    action: FieldCellActionID,
    side: int,
    seed: int | None = None,
) -> CausalState:
    """Build the same internal prefix used by the selected causal frame."""
    initial = cast(
        Callable[[FieldCellActionID, int, int | None], CausalState],
        object.__getattribute__(engine, "_initial"),
    )
    return initial(action, side, seed)


def hold_causal_workspace(engine: CausalTileEngine, hold: bool) -> None:
    """Retain a workspace across explicitly staged internal regression frames."""
    object.__setattr__(engine, "_hold_workspace", hold)


def release_causal_workspace(engine: CausalTileEngine) -> None:
    release = cast(
        Callable[[], None], object.__getattribute__(engine, "_release_workspace")
    )
    release()


__all__ = [
    "run_causal_frame",
    "initial_causal_state",
    "hold_causal_workspace",
    "release_causal_workspace",
]
