"""Keep the iterative validation traversals exact and quotient-keyed."""

import pytest

from devtools.benchmarks.comma_mdd_bind import BindKey, BindTraversal
from devtools.benchmarks.comma_mdd_shift import (
    MODES,
    Request,
    ShiftTraversal,
    phase_value,
)
from number_compiler.sequences.comma.boundary_chart import PERIOD
from number_compiler.sequences.comma.future_source_mdd import (
    FutureSourceMDD,
    SourceBranch,
    SourceLeaf,
)


def _diagram() -> FutureSourceMDD:
    nodes = (
        SourceLeaf(0),
        SourceLeaf(1),
        SourceBranch(1, (0, 0, 1, 1)),
        SourceBranch(0, (2, 1, 2)),
        SourceBranch(0, (0, 1, 1)),
    )
    return FutureSourceMDD(nodes, (3,) * 8 + (4,) * 8)


def test_iterative_shift_modes_match_every_phase() -> None:
    diagram = _diagram()
    for mode in MODES:
        traversal = ShiftTraversal(diagram)
        for shift in (0, 1, 19, PERIOD + 7):
            root = traversal.run(Request(3, shift), mode)
            assert all(
                phase_value(traversal.nodes, root, phase)
                == phase_value(diagram.nodes, 3, phase + shift) + 1
                for phase in range(PERIOD)
            )


@pytest.mark.parametrize(
    "mapping", [((0, 4), (1, 2)), ((0, 4),), (), ((0, 4), (1, 2), (99, 3))]
)
def test_iterative_bind_modes_match_pointwise_and_reuse_root(
    mapping: tuple[tuple[int, int], ...],
) -> None:
    diagram = _diagram()
    key = BindKey(3, 0, mapping)
    route = dict(key.mapping)
    for selected in (False, True):
        traversal = BindTraversal(diagram.nodes, selected=selected)
        root = traversal.bind(key)
        assert all(
            phase_value(traversal.nodes, root, phase)
            == phase_value(
                diagram.nodes,
                route.get(phase_value(diagram.nodes, 3, phase), key.fallback),
                phase,
            )
            for phase in range(PERIOD)
        )
        work = traversal.cofactors
        assert traversal.bind(key) == root and traversal.cofactors == work
