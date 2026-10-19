"""Matrix summaries and bounded traces share one admitted query demand."""

from dataclasses import replace

import pytest

from number_compiler.api.cli_context import QueryContext
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.family_registry import CAPABILITIES
from number_compiler.api.matrix_contracts import SourceTransferRequest
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.observation_types import ObservationId
from number_compiler.arithmetic.contracts.family_identity import FamilyId


def test_powered_and_trace_horizons_are_separate() -> None:
    args = ["2rev10", "--seed", "196", "--nth", "32", "--no-value"]
    request = parse_request(
        [*args, "--info", "temporal.matrix", "--temporal-matrix-steps", "4096"]
    )
    assert request is not None
    assert isinstance(request.matrix, SourceTransferRequest)
    assert request.matrix.steps == 4096 and not request.matrix.trace
    with pytest.raises(ValueError, match="trace requires at most 128"):
        parse_request(
            [*args, "--info", "temporal.matrix.trace", "--temporal-matrix-steps", "130"]
        )
    for steps in ("4098", "3"):
        with pytest.raises(ValueError, match="multiples of 2"):
            parse_request(
                [*args, "--info", "temporal.matrix", "--temporal-matrix-steps", steps]
            )


@pytest.mark.parametrize("trace_first", [False, True])
def test_summary_and_trace_share_preparation(
    monkeypatch: pytest.MonkeyPatch, trace_first: bool
) -> None:
    from number_compiler.api import matrix_observation

    names = ["temporal.matrix", "temporal.matrix.trace"]
    if trace_first:
        names.reverse()
    request = parse_request(
        [
            "antihydra",
            "--nth",
            "0",
            "--no-value",
            "--info",
            names[0],
            "--info",
            names[1],
            "--temporal-matrix-steps",
            "4",
        ]
    )
    assert request is not None
    calls: list[SourceTransferRequest] = []

    def observe(context: QueryContext, demand: object) -> dict[str, object]:
        assert context.request is request
        assert isinstance(demand, SourceTransferRequest) and demand.trace
        calls.append(demand)
        return {"pointed_last_center": 3, "trace": {"path": (0, 1, 1, 2, 3)}}

    monkeypatch.setattr(matrix_observation, "antihydra_transfer", observe)
    context = QueryContext(request, NumberCompiler())
    info = context.information()
    assert len(calls) == 1
    assert "trace" not in info["temporal.matrix"]
    assert info["temporal.matrix.trace"]["trace"] == {"path": [0, 1, 1, 2, 3]}
    assert info["temporal.matrix"]["pointed_last_center"] == 3


def test_trace_cannot_bypass_query_admission() -> None:
    request = parse_request(
        [
            "antihydra",
            "--nth",
            "0",
            "--info",
            "temporal.matrix",
            "--temporal-matrix-steps",
            "4",
        ]
    )
    assert request is not None and isinstance(request.matrix, SourceTransferRequest)
    with pytest.raises(ValueError, match="trace demand differs"):
        replace(request, matrix=replace(request.matrix, trace=True))
    forged = replace(request.matrix)
    object.__setattr__(forged, "trace", 1)
    capability = CAPABILITIES[FamilyId.ANTIHYDRA].matrix
    assert capability is not None
    with pytest.raises(TypeError, match="Boolean"):
        capability.validate(forged)


def test_trace_keeps_reverse_decimal_source_guard() -> None:
    with pytest.raises(ValueError, match="decimal"):
        parse_request(
            [
                "reverse-add",
                "--seed",
                "196",
                "--base",
                "8",
                "--nth",
                "0",
                "--info",
                "temporal.matrix.trace",
                "--temporal-matrix-steps",
                "2",
            ]
        )


def test_innovation_has_no_chronological_trace() -> None:
    with pytest.raises(ValueError, match="source-transfer"):
        parse_request(
            [
                "reverse-add",
                "--seed",
                "196",
                "--nth",
                "0",
                "--info",
                "temporal.matrix.trace",
                "--temporal-matrix-kind",
                "innovation",
            ]
        )


def test_mersenne_declares_its_distinct_matrix_clock() -> None:
    request = parse_request(
        [
            "mersenne",
            "--nth",
            "31",
            "--no-value",
            "--info",
            "temporal.matrix",
            "--temporal-matrix-steps",
            "4096",
        ]
    )
    assert request is not None
    capability = CAPABILITIES[FamilyId.MERSENNE].matrix
    assert capability is not None
    assert capability.clock.value == "trace-squaring-steps"
    assert (
        ObservationId.TEMPORAL_MATRIX_TRACE in CAPABILITIES[FamilyId.MERSENNE].nth_info
    )
