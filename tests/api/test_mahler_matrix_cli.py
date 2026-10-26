"""An explicit finite center demand must not change ordinary CLI execution."""

import json

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_context import QueryContext
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.observation_types import ObservationId


def test_mahler_cli_center_matrix_is_optional_and_source_bound(
    capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.sequences.antihydra import mahler_center_depth_matrix as matrix

    arguments = [
        "antihydra",
        "--nth",
        "16",
        "--info",
        "arithmetic.mahler",
        "--format",
        "json",
    ]
    assert (
        main(
            arguments
            + ["--info", "temporal.matrix.trace", "--temporal-matrix-steps", "4"]
        )
        == 0
    )
    demanded = json.loads(capsys.readouterr().out)
    packet = demanded["info"]["temporal.matrix.trace"]
    assert packet["source_certified_physical_ticks"] == 4
    assert packet["temporal_repeat_certified"] is False
    assert len(packet["trace"]["pointed_center_path"]) == 5

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("ordinary Mahler observer constructed a center matrix")

    monkeypatch.setattr(
        matrix.MahlerCertifiedCenterDepthTransfer, "from_source", forbidden
    )
    from number_compiler.sequences.antihydra.mahler_two_sided_cylinder import (
        MahlerTwoSidedCylinder,
    )

    monkeypatch.setattr(MahlerTwoSidedCylinder, "from_pointed_source", forbidden)
    assert main(arguments) == 0
    ordinary = json.loads(capsys.readouterr().out)
    assert ordinary["value"] == demanded["value"]
    assert (
        "source_bound_center_depth_matrix"
        not in ordinary["info"]["arithmetic.mahler"]["value"]["associated_action"]
    )


def test_mahler_matrix_and_trace_share_one_source_transfer(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api.matrix_observation import observe_matrix
    from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
        MahlerCertifiedCenterDepthTransfer,
    )
    from number_compiler.sequences.antihydra.mahler_center_relation_work import (
        MahlerCenterWorkSink,
    )

    request = parse_request(
        [
            "antihydra",
            "--nth",
            "0",
            "--no-value",
            "--info",
            "temporal.matrix",
            "--info",
            "temporal.matrix.trace",
            "--temporal-matrix-steps",
            "4",
        ]
    )
    assert request is not None
    context = QueryContext(request, NumberCompiler())
    original = MahlerCertifiedCenterDepthTransfer.from_source
    issued_sources: list[tuple[int, int]] = []

    def counted(
        cls: type[MahlerCertifiedCenterDepthTransfer],
        source: int,
        steps: int,
        *,
        initial_ledger: int | None = None,
        work_sink: MahlerCenterWorkSink | None = None,
    ) -> MahlerCertifiedCenterDepthTransfer:
        issued_sources.append((source, steps))
        return original(
            source,
            steps,
            initial_ledger=initial_ledger,
            work_sink=work_sink,
        )

    monkeypatch.setattr(
        MahlerCertifiedCenterDepthTransfer, "from_source", classmethod(counted)
    )
    information = context.information()
    summary = information[ObservationId.TEMPORAL_MATRIX.value]
    trace = information[ObservationId.TEMPORAL_MATRIX_TRACE.value]
    assert len(issued_sources) == 1
    assert issued_sources[0][1] == 4
    assert summary["pointed_last_center"] == trace["pointed_last_center"]
    assert "trace" not in summary
    trace_payload = trace["trace"]
    assert isinstance(trace_payload, dict)
    assert trace_payload["pointed_center_path"] == [0, 1, 1, 2, 3]

    def forbidden(
        cls: type[MahlerCertifiedCenterDepthTransfer],
        source: int,
        steps: int,
        *,
        initial_ledger: int | None = None,
        work_sink: MahlerCenterWorkSink | None = None,
    ) -> MahlerCertifiedCenterDepthTransfer:
        raise AssertionError("query-local matrix memo rebuilt its source transfer")

    monkeypatch.setattr(
        MahlerCertifiedCenterDepthTransfer, "from_source", classmethod(forbidden)
    )
    observe_matrix(context, ObservationId.TEMPORAL_MATRIX)
    observe_matrix(context, ObservationId.TEMPORAL_MATRIX_TRACE)
    assert len(issued_sources) == 1


@pytest.mark.parametrize("steps", ["-1", "33", "1.5"])
def test_mahler_cli_matrix_bounds_rejected(steps: str) -> None:
    with pytest.raises((SystemExit, ValueError)):
        parse_request(
            [
                "antihydra",
                "--nth",
                "1",
                "--info",
                "temporal.matrix.trace",
                "--temporal-matrix-steps",
                steps,
            ]
        )


def test_mahler_cli_matrix_requires_its_observer() -> None:
    with pytest.raises((SystemExit, ValueError)):
        parse_request(
            [
                "antihydra",
                "--nth",
                "1",
                "--info",
                "metrics",
                "--temporal-matrix-steps",
                "4",
            ]
        )


def test_mahler_cli_small_source_matrix_uses_padded_pointed_center(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "antihydra",
                "--nth",
                "0",
                "--info",
                "temporal.matrix.trace",
                "--temporal-matrix-steps",
                "4",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    assert packet["value"] == "8"
    matrix = packet["info"]["temporal.matrix.trace"]
    assert matrix["trace"]["pointed_center_path"] == [0, 1, 1, 2, 3]
    assert matrix["temporal_repeat_certified"] is False


def test_mahler_matrix_failed_publication_releases_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api.mahler_matrix_observation import center_matrix_packet
    from number_compiler.sequences.antihydra.mahler_center_depth_matrix import (
        MahlerCertifiedCenterDepthTransfer,
    )
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

    term = AntihydraArithmeticTerm(16, shared_cache=False)
    result = term.result()
    before = (result.ledger.nodes, result.ledger.entries)

    def fail(*args: object, **kwargs: object) -> None:
        raise RuntimeError("injected matrix publication failure")

    original_packet = MahlerCertifiedCenterDepthTransfer.packet
    monkeypatch.setattr(MahlerCertifiedCenterDepthTransfer, "packet", fail)
    with pytest.raises(RuntimeError, match="publication failure"):
        center_matrix_packet(result, 4)
    accounts_after_failure = result.ledger.owner_count
    assert (result.ledger.nodes, result.ledger.entries) == before
    with pytest.raises(RuntimeError, match="publication failure"):
        center_matrix_packet(result, 4)
    assert result.ledger.owner_count == accounts_after_failure
    assert (result.ledger.nodes, result.ledger.entries) == before
    monkeypatch.setattr(MahlerCertifiedCenterDepthTransfer, "packet", original_packet)
    packet = center_matrix_packet(result, 4)
    assert result.ledger.owner_count == accounts_after_failure
    assert (result.ledger.nodes, result.ledger.entries) == before
    assert packet["source_prefix_ledger_safe"] is (result.first_failure_index is None)
    assert packet["source_first_failure_index"] == result.first_failure_index
    assert packet["physical_continuation_authorized"] is False


def test_mahler_matrix_failed_transfer_keeps_partial_work_and_releases_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api.mahler_matrix_observation import center_matrix_packet
    from number_compiler.resources.metric_keys import antihydra as keys
    from number_compiler.sequences.antihydra import (
        mahler_center_sparse_relation as sparse_relation,
    )
    from number_compiler.sequences.antihydra.mahler_center_algebra import center_next
    from number_compiler.sequences.antihydra.runtime import AntihydraArithmeticTerm

    result = AntihydraArithmeticTerm(16, shared_cache=False).result()
    before = (result.ledger.nodes, result.ledger.entries)
    owners_before = result.ledger.owner_count
    center_calls = 0

    def fail_during_third_candidate(state: int, carry: int, parity: int) -> int:
        nonlocal center_calls
        center_calls += 1
        if center_calls == 3:
            raise RuntimeError("injected center transition failure")
        return center_next(state, carry, parity)

    monkeypatch.setattr(sparse_relation, "center_next", fail_during_third_candidate)
    with pytest.raises(RuntimeError, match="center transition failure"):
        center_matrix_packet(result, 4)

    counters = result.ledger.counters
    assert center_calls == 3
    assert counters[keys.MAHLER_CENTER_MATRIX_PHYSICAL_STEPS] == 4
    assert counters[keys.MAHLER_CENTER_MATRIX_CANDIDATE_TRANSITIONS] == 3
    assert result.ledger.owner_count == owners_before + 1
    assert (result.ledger.nodes, result.ledger.entries) == before
