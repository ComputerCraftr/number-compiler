"""Public generic observations through the shared runtime K/U carrier."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.arithmetic.contracts.exact_tree_context import source_reads_only
from number_compiler.arithmetic.contracts.scoped_handles import ActionProgramID

if TYPE_CHECKING:
    from number_compiler.hashlife.execution.continuations.diamond_runtime import (
        DiamondRuntime,
    )


@source_reads_only
def parametric_point(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    position: int,
) -> int:
    """Observe one output through the canonical runtime K/U carrier."""
    runtime.actions.resolve(action)
    source = runtime.cells.source_geometry._read_root
    if type(position) is not int or position < 0:
        raise ValueError("point coordinate must be nonnegative")
    if source is None or position >= source.length:
        raise IndexError(position)
    from number_compiler.hashlife.execution.continuations.generic_higher import (
        generic_higher_runtime,
    )

    return generic_higher_runtime(runtime).point(action, position)


@source_reads_only
def parametric_width(
    runtime: DiamondRuntime,
    action: ActionProgramID,
    observer: ActionProgramID,
    maxwidth: int,
) -> int:
    """Find the rightmost active output through runtime U summaries."""
    runtime.actions.resolve(action)
    runtime.actions.resolve(observer)
    source = runtime.cells.source_geometry._read_root
    if (
        source is None
        or type(maxwidth) is not int
        or not 0 <= maxwidth <= source.length
    ):
        raise ValueError("width bound must fit the original source extent")
    if not maxwidth:
        return 0
    from number_compiler.hashlife.execution.continuations.generic_higher import (
        generic_higher_runtime,
    )

    return generic_higher_runtime(runtime).width(action, observer, maxwidth)


__all__ = ["parametric_point", "parametric_width"]
