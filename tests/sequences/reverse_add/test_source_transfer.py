"""Finite reverse/add transfer stays attached to completed source children."""

from typing import cast

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
    packet = source_transfer_packet(term, steps=2, pair_depth=1, trace=True)
    trace = packet["trace"]
    assert isinstance(trace, dict)
    trace_packet = cast(dict[str, object], trace)
    detailed_packet = dict(packet)
    detailed_packet.update(trace_packet)

    assert_exact_source_transfer_path(
        detailed_packet,
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
    workspace = term.source_workspace()
    owner, endpoint, _reused, _applications = workspace.completed_q19_occurrence()

    def forbid_cold_source_image(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("warm reverse/add endpoint requested a cold image")

    monkeypatch.setattr(
        type(workspace.scheduler), "source_image_demanded", forbid_cold_source_image
    )
    packet = source_transfer_packet(term, steps=1, pair_depth=1)

    assert packet["status"] == "available"
    assert packet["source_root_local_diagnostic"] == endpoint.root
    assert packet["source_generation"] == endpoint.temporal_steps
    assert packet["future_q19_roots_constructed"] is False
    assert packet["matrix_semantics"] == "projected_source_word_overapproximation"
    assert owner is workspace.adapter.audit_snapshot().q19_owner


def test_reverse_add_generation_257_uses_reflected_incoming_carry() -> None:
    term = ReverseAddPoweredTerm(196, 257)
    packet = source_transfer_packet(term, steps=1, pair_depth=1, trace=True)

    assert packet["status"] == "available"
    trace = packet["trace"]
    assert isinstance(trace, dict)
    assert trace["source_pair_path"] == ((2, 3), (5, 6))


def test_reverse_add_summary_does_not_build_future_q19_children(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = ReverseAddPoweredTerm(196, 79)
    workspace = term.source_workspace()
    workspace.completed_q19_occurrence()

    def forbid_future_child(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("summary matrix constructed a future Q19 child")

    monkeypatch.setattr(
        type(workspace.adapter.audit_snapshot().q19_owner),
        "apply_pair_step",
        forbid_future_child,
    )
    packet = source_transfer_packet(term, steps=2, pair_depth=1)

    assert packet["status"] == "available"
    assert packet["future_q19_roots_constructed"] is False
    assert packet["source_root_assignment_joined"] is False
    assert "trace" not in packet
