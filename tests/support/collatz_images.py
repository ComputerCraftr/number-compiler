"""Exact chronological branch observations for independently computed orbits."""

from number_compiler.sequences.collatz.physical_images import (
    CollatzPhysicalImageWorkspace,
)


def assert_branch_segments(
    workspace: CollatzPhysicalImageWorkspace, branches: tuple[int, ...]
) -> None:
    actual: list[int] = []
    for start, width, word in workspace.segments():
        assert start == len(actual)
        actual.extend((word >> offset) & 1 for offset in range(width))
    assert tuple(actual) == branches
