"""The chamber quotient must expose its unknown future at EXIT."""

from __future__ import annotations

import pytest

from devtools.verification import ExactOracleAccessForbidden, exact_oracle
from devtools.verification.oracles.sequence_arithmetic import reference_successor
from devtools.verification.reverse_exit_moore import (
    ChamberReturnGraph,
    audit_exit_refinement,
    audit_width_phases,
    build_d5_return_graph,
    carry_observation,
)
from number_compiler.arithmetic.functions.finite_observer import partition_equivalent


@pytest.fixture(scope="module")
def graph() -> ChamberReturnGraph:
    with exact_oracle():
        return build_d5_return_graph()


def test_exit_partition_preserves_exact_returns_separately(
    graph: ChamberReturnGraph,
) -> None:
    size = len(graph.sources)
    assert size == 3610
    assert len(graph.exit_payloads) == 1040
    for source, target_id in zip(graph.sources, graph.successors, strict=True):
        expected = reference_successor(source)
        returned = (
            graph.sources[target_id]
            if target_id < size
            else graph.exit_payloads[target_id - size]
        )
        assert returned == expected
        if target_id >= size:
            assert len(returned) == 6
            assert 19 not in returned
    assert (9, 18, 18, 18, 18, 9) in graph.exit_payloads
    # This seam is neutral, not an invalid punctured carry action.
    assert (9,) * 6 in graph.exit_payloads
    with exact_oracle():
        assert carry_observation((9,) * 6) == ((0, 1, 4), ((0, 0, 0), (1, 0, 0)))


def test_refinement_exposes_returned_port_conflict(graph: ChamberReturnGraph) -> None:
    with exact_oracle():
        report = audit_exit_refinement()
        assert (report.no_growth_rows, report.growth_rows) == (1805, 1805)
        assert (report.no_growth_classes, report.growth_classes) == (900, 30)
        assert report.width_refined_classes == 1053
        assert report.absorbing_exit_classes == 930
        assert report.returned_ports_classes == 1053
        assert report.merged_exit_conflicts == 673
        assert report.first_conflict is not None
        left, right = report.first_conflict
        before = graph.refine(("EXIT",) * len(graph.exit_payloads))
        ids = {source: index for index, source in enumerate(graph.sources)}
        assert before.class_ids[ids[left]] == before.class_ids[ids[right]]
        assert carry_observation(reference_successor(left)) != carry_observation(
            reference_successor(right)
        )
        assert report.production_admission is False


def test_uninterpreted_exit_renaming_preserves_partition(
    graph: ChamberReturnGraph,
) -> None:
    with exact_oracle():
        count = len(graph.exit_payloads)
        original = graph.refine(tuple(range(count)))
        renamed = graph.refine(tuple(("variable", count - i) for i in range(count)))
        assert partition_equivalent(original.class_ids, renamed.class_ids)
        # Conservative open variables distinguish occurrences, not minimal
        # complete semantic actions. This is not a lower bound on that quotient.
        assert len(set(original.class_ids[: len(graph.sources)])) == 3610
        with pytest.raises(ValueError, match="every EXIT"):
            graph.refine((0,))


def test_same_current_output_does_not_erase_different_continuations() -> None:
    # States 0/1 reach different exit variables after a shared current label.
    graph = ChamberReturnGraph(((0,), (1,)), ("same", "same"), (2, 3), ((2,), (3,)))
    with exact_oracle():
        open_result = graph.refine(("alpha", "beta"))
        assert open_result.class_ids[0] != open_result.class_ids[1]
        specialized = graph.refine(("equal-by-caller", "equal-by-caller"))
        assert specialized.class_ids[0] == specialized.class_ids[1]
    with pytest.raises(ExactOracleAccessForbidden):
        graph.refine(("alpha", "beta"))


@pytest.mark.parametrize(
    ("seed", "widths"),
    [
        (196, (9, 16, 31, 58)),
        (1, (7, 14, 28, 56)),
        (89, (10, 17, 28, 50)),
        (10911, (11, 18, 32, 62)),
        (111589511, (15, 22, 37, 64)),
        (4994, (12, 20, 35, 60)),
        (879, (11, 18, 32, 59)),
    ],
)
def test_independent_width_phase_census(seed: int, widths: tuple[int, ...]) -> None:
    with exact_oracle():
        report = audit_width_phases(seed)
    observed = dict(report.widths)
    assert tuple(observed[n] for n in (16, 32, 64, 128)) == widths
    assert report.phases == tuple(range(10))
    assert report.growth_count == observed[256] - observed[0]
