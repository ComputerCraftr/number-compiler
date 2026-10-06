"""Source authority and demand accounting for the shared Antihydra image."""

import pytest

from number_compiler.arithmetic.fields.skew_transfer import integer_dyadic_fiber_action
from number_compiler.hashlife.execution.dyadic_return_records import (
    DyadicReturnImageID,
    _SourceNode,
)
from number_compiler.sequences.antihydra.arithmetic_images import (
    AntihydraArithmeticImageWorkspace,
)
from number_compiler.sequences.antihydra.mahler_action import associated_action
from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm


def test_mahler_serialization_demands_one_aggregate_and_no_segments() -> None:
    term = AntihydraArithmeticTerm(128)
    result = term.result()
    before = result.ledger.counters["antihydra_arithmetic_aggregate_demands"]

    packet = associated_action(result)

    assert packet["extent"] == 128
    # Two reads authenticate the public result. The Mahler action consumes the
    # already-published transfer without requesting another aggregate wrapper.
    assert (
        result.ledger.counters["antihydra_arithmetic_aggregate_demands"] - before == 2
    )
    assert result.ledger.counters["mahler_source_composed_image_reads"] == 1
    assert not term._segments_ready
    assert not term.physical_publications


@pytest.mark.parametrize("corruption", ("action", "source"))
def test_mahler_rejects_foreign_image_binding(
    corruption: str, monkeypatch: pytest.MonkeyPatch
) -> None:
    term = AntihydraArithmeticTerm(8)
    result = term.result()
    workspace = term.arithmetic_workspace
    assert workspace is not None
    if corruption == "action":
        monkeypatch.setattr(workspace, "root_action", workspace.identity)
    else:
        foreign = AntihydraArithmeticTerm(8)
        foreign.result()
        foreign_workspace = foreign.arithmetic_workspace
        assert foreign_workspace is not None
        monkeypatch.setattr(workspace, "root_source", foreign_workspace.root_source)

    with pytest.raises(ValueError, match="arithmetic source image was changed"):
        associated_action(result)


def test_balanced_arithmetic_and_mahler_do_not_assemble_an_intermediate_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> int:
        raise AssertionError("balanced source constructor assembled an exact value")

    monkeypatch.setattr(AntihydraArithmeticImageWorkspace, "_source_value", forbidden)
    term = AntihydraArithmeticTerm(128)
    result = term.result()
    expected = 8
    for _ in range(128):
        expected += expected // 2
    assert result.h == expected
    assert associated_action(result)["extent"] == 128
    assert term.ledger.counters["antihydra_arithmetic_temporal_balanced_routes"] == 1
    assert not term._segments_ready
    assert not term.physical_publications


@pytest.mark.parametrize(
    ("residue", "lift"),
    ((0, 0), (1, 0), (0, 1), (1, 1), (2, 1), (255, 1), (0, 2), (1, 2)),
)
def test_homogeneous_run_admission_matches_independent_centered_recurrence(
    residue: int, lift: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    width = 8
    term = AntihydraArithmeticTerm(width)
    term.result()
    workspace = term.arithmetic_workspace
    assert workspace is not None
    source = workspace._append_source(
        _SourceNode(residue, width, lift, None, None, None, 0, True)
    )
    image = workspace.scheduler.source_image(workspace, source, workspace.identity)
    view = workspace.scheduler._source_image_core().view(image)

    def forbidden(*_args: object, **_kwargs: object) -> int:
        raise AssertionError("run admission assembled the cylinder value")

    monkeypatch.setattr(workspace, "_source_value", forbidden)
    admitted = workspace._whole_initial_run(view, width)

    d = residue + (lift << width) - 1
    expected = d > 0
    initial = d & 1
    for _ in range(width):
        expected = expected and d & 1 == initial
        d = (3 * d + (d & 1)) // 2
    assert admitted == expected


def test_even_cylinder_reuses_transport_across_authenticated_high_fibers() -> None:
    width = 8
    term = AntihydraArithmeticTerm(width)
    term.result()
    workspace = term.arithmetic_workspace
    assert workspace is not None
    ledger = term.ledger
    before = ledger.counters.get("source_image_relative_transfer_hits", 0)
    images = []
    for lift in (1, 2, 3, 7):
        source = workspace._append_source(
            _SourceNode(0, width, lift, None, None, None, 0, True)
        )
        image = workspace.scheduler.source_image(
            workspace, source, workspace.root_action
        )
        view = workspace.scheduler._source_image_core().view(image)
        assert view.binding.source == source
        assert type(view.payload) is DyadicReturnImageID
        summary = workspace.image_node(view.payload).summary
        chart = integer_dyadic_fiber_action(summary.transfer, 0, width)
        expected = lift << width
        for _ in range(width):
            expected += expected // 2
        assert chart.addend + chart.multiplier * lift == expected
        assert (summary.delta, summary.minimum, summary.odd_steps) == (16, 0, 0)
        images.append(image)

    assert len(set(images)) == 4
    assert ledger.counters["source_image_relative_transfer_hits"] - before == 3
