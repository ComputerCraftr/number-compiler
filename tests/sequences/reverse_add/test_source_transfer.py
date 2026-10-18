"""Finite reverse/add transfer stays attached to completed source children."""

import pytest

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.source_transfer import (
    PAIR_COORDINATE_ORDER,
    source_transfer_packet,
)
from tests.sequences.source_transfer_support import assert_exact_source_transfer_path


def _reverse_add(value: int) -> int:
    return value + int(str(value)[::-1])


def _pair(value: int, depth: int) -> tuple[int, int]:
    digits = str(value)
    # Q19 matrix coordinates follow the established lower/LSD-inward first
    # ordering used by the source-border rows.
    return int(digits[-1 - depth]), int(digits[depth])


def test_reverse_add_transfer_joins_forward_children_from_query_endpoint() -> None:
    generation = 79
    source = 196
    for _ in range(generation):
        source = _reverse_add(source)
    expected = [source]
    for _ in range(2):
        expected.append(_reverse_add(expected[-1]))

    term = ReverseAddPoweredTerm(196, generation)
    packet = source_transfer_packet(term, steps=2, pair_depth=1)

    assert_exact_source_transfer_path(
        packet,
        tuple(_pair(value, 1) for value in expected),
        physical_interval=(generation, generation + 2),
        border_span=1,
        pair_coordinate_order=PAIR_COORDINATE_ORDER,
    )


def test_reverse_add_transfer_reuses_a_warm_query_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    generation = 79
    term = ReverseAddPoweredTerm(196, generation)
    workspace = term._source_workspace()
    owner, endpoint, _reused, _applications = workspace.completed_q19_occurrence()

    def forbid_cold_source_image(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("warm reverse/add endpoint requested a cold image")

    monkeypatch.setattr(
        type(workspace.scheduler), "source_image_demanded", forbid_cold_source_image
    )
    packet = source_transfer_packet(term, steps=1, pair_depth=1)

    assert packet["status"] == "available"
    assert packet["source_root"] == endpoint.root
    assert packet["source_generation"] == endpoint.temporal_steps
    assert owner is workspace.adapter._q19_owner
