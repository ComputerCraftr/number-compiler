"""Adversarial consumers of source-bound spatial carry actions."""

from __future__ import annotations

import importlib.util

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.source_images import (
    ReverseSourceImageAdapter,
    ReverseSourceImageWorkspace,
)


def _step(digits: tuple[int, ...]) -> tuple[int, ...]:
    carry = 0
    result = []
    for left, right in zip(digits, reversed(digits), strict=True):
        carry, digit = divmod(left + right + carry, 10)
        result.append(digit)
    if carry:
        result.append(carry)
    return tuple(result)


def _seed(digits: tuple[int, ...]) -> int:
    seed = 0
    for digit in reversed(digits):
        seed = seed * 10 + digit
    return seed


@pytest.mark.parametrize("steps", [1, 2])
@pytest.mark.parametrize("width", [16, 64, 256, 1024])
def test_all_point_demands_normalize_each_output_once(steps: int, width: int) -> None:
    original = tuple((7 * i + 3) % 10 for i in range(width - 1)) + (1,)
    expected = original
    for _ in range(steps):
        expected = _step(expected)
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, _seed(original), steps)
    assert workspace.width() == len(expected)
    # Descending independent demands used to restart each prefix and normalize
    # O(width**2) digits. The scheduler memo cannot hide the first-query cost.
    before = ledger.counters.get("reverse_source_mod9_digit_reconstructions", 0)
    result = tuple(workspace.digit(i) for i in reversed(range(len(expected))))
    assert result == tuple(reversed(expected))
    normalized = ledger.counters.get("reverse_source_mod9_digit_reconstructions", 0)
    assert normalized - before <= len(expected)
    assert ledger.counters.get("reverse_source_pullback_predecessor_search", 0) == 0
    assert ledger.counters.get("reverse_source_ports_source_reads", 0) <= 20 * width
    assert (
        ledger.counters.get("reverse_source_ports_interval_publications", 0)
        <= 5 * width
    )
    assert ledger.counters.get("reverse_source_ports_postorder_frames", 0) <= 20 * width
    workspace.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_width_and_random_access_do_not_enter_retired_streams(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    assert (
        importlib.util.find_spec("number_compiler.sequences.reverse_add.source_length")
        is None
    )

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("point/width demand used a positional replay")

    for method in ("iter_second_digits", "iter_primitive_digits", "_carry_and_digit"):
        monkeypatch.setattr(ReverseSourceImageAdapter, method, forbidden, raising=False)
    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 2)
    assert workspace.width() == 4
    assert tuple(workspace.digit(i) for i in (3, 0, 2, 1)) == (1, 5, 6, 7)


def test_q19_occurrence_is_reused_for_width_and_digit_demands() -> None:
    ledger = ResourceLedger()
    workspace = ReverseSourceImageWorkspace(ledger, 1001, 3)
    assert workspace.width() == 4
    assert tuple(workspace.iter_digits()) == (8, 0, 0, 8)
    before = (
        ledger.counters.get("reverse_q19_punctured_t2_applications", 0),
        ledger.counters.get("reverse_q19_punctured_t4_applications", 0),
        ledger.counters.get("reverse_q19_primitive_pair_applications", 0),
    )
    assert before[0] > 0
    assert ledger.counters["reverse_q19_root_bootstrap_publications"] == 1
    assert tuple(workspace.digit(i) for i in range(4)) == (8, 0, 0, 8)
    assert tuple(workspace.iter_digits()) == (8, 0, 0, 8)
    after = (
        ledger.counters.get("reverse_q19_punctured_t2_applications", 0),
        ledger.counters.get("reverse_q19_punctured_t4_applications", 0),
        ledger.counters.get("reverse_q19_primitive_pair_applications", 0),
    )
    assert after == before


def test_no_production_predecessor_cursor_remains() -> None:
    import number_compiler.sequences.reverse_add.source_chamber as chamber

    assert not hasattr(chamber, "OriginalSourceCarryCursor")
    assert not hasattr(ReverseSourceImageAdapter, "_carry_and_digit")


def test_projection_rejects_payload_from_different_action() -> None:
    from dataclasses import replace

    from number_compiler.hashlife.execution.source_image_inventory import (
        SourceImageDemand,
    )

    workspace = ReverseSourceImageWorkspace(ResourceLedger(), 196, 2)
    workspace.width()
    assert workspace._image is not None
    view = workspace.scheduler._source_image_core().view(workspace._image)
    forged = replace(
        view,
        binding=replace(view.binding, action=workspace.actions.primitive),
    )
    with pytest.raises(ValueError, match="binding disagree"):
        workspace.adapter.project(forged, SourceImageDemand("width"))
