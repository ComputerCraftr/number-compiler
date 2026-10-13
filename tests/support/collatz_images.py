"""Exact chronological branch observations for independently computed orbits."""

from number_compiler.api.number_api import NumberCompiler, PoweredCollatzTermPayload
from number_compiler.api.query_types import CollatzTermQuery
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
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


def projected_collatz_runtime_term(
    *, seed: int, index: int, radix: int, checked_position: int
) -> PoweredCollatzTerm:
    """Return a typed Collatz projection after checking one requested digit."""
    projected = NumberCompiler().project(
        CollatzTermQuery(index, seed=seed, radix=radix)
    )
    assert 0 <= projected.digit(checked_position) < radix
    assert isinstance(projected.payload, PoweredCollatzTermPayload)
    return projected.payload.term
