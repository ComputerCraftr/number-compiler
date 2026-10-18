"""The common matrix interface preserves authority and coordinate distinctions."""

from dataclasses import replace

import pytest

from number_compiler.api.cli_requests import parse_request, parser
from number_compiler.api.family_registry import CAPABILITIES
from number_compiler.api.family_types import FamilySpec
from number_compiler.api.matrix_contracts import (
    InnovationMatrixRequest,
    MatrixCoordinate,
    SourceTransferRequest,
)
from number_compiler.api.observation_types import FamilyId


@pytest.mark.parametrize(
    "family", ["reverse-add", "2rev10", "collatz", "antihydra", "fermat"]
)
def test_matrix_requires_physical_horizon(family: str) -> None:
    args = [family, "--nth", "0", "--info", "temporal.matrix"]
    if family in {"reverse-add", "2rev10", "collatz"}:
        args += ["--seed", "196"]
    with pytest.raises(ValueError, match="--temporal-matrix-steps"):
        parse_request(args)
    request = parse_request([*args, "--temporal-matrix-steps", "4"])
    assert request is not None
    assert isinstance(request.matrix, SourceTransferRequest)
    assert request.matrix.steps == 4


def test_innovation_is_explicit_and_has_no_future_horizon() -> None:
    args = [
        "reverse-add",
        "--seed",
        "196",
        "--nth",
        "20",
        "--info",
        "temporal.matrix",
        "--temporal-matrix-kind",
        "innovation",
    ]
    request = parse_request(args)
    assert request is not None
    assert request.matrix == InnovationMatrixRequest()
    with pytest.raises(ValueError, match="future horizon"):
        parse_request([*args, "--temporal-matrix-steps", "4"])
    with pytest.raises(ValueError, match="no source-transfer coordinate"):
        parse_request([*args, "--temporal-matrix-pair-depth", "4"])


@pytest.mark.parametrize("attribute", ["steps", "coordinate"])
def test_mutated_matrix_request_is_rejected_at_query_admission(attribute: str) -> None:
    capability = CAPABILITIES[FamilyId.REVERSE_ADD].matrix
    assert capability is not None
    request = SourceTransferRequest(4, MatrixCoordinate.PAIR_DEPTH, 1)
    object.__setattr__(request, attribute, True)
    with pytest.raises(TypeError):
        capability.validate(request)


@pytest.mark.parametrize("value", [True, -1, 1.5])
def test_matrix_rejects_coercible_physical_steps(value: object) -> None:
    capability = CAPABILITIES[FamilyId.REVERSE_ADD].matrix
    assert capability is not None
    with pytest.raises((ValueError, TypeError)):
        capability.build(
            {
                "temporal_matrix_kind": "source-transfer",
                "temporal_matrix_steps": value,
                "temporal_matrix_pair_depth": 1,
            }
        )


def test_matrix_request_cannot_cross_coordinate_domains() -> None:
    request = parse_request(
        [
            "reverse-add",
            "--seed",
            "196",
            "--nth",
            "0",
            "--info",
            "temporal.matrix",
            "--temporal-matrix-steps",
            "4",
        ]
    )
    assert request is not None
    with pytest.raises(ValueError, match="different transfer law"):
        replace(
            request, matrix=SourceTransferRequest(4, MatrixCoordinate.DIGIT_POSITION, 1)
        )


def test_new_matrix_binding_supplies_parser_options_without_dispatch_edits(
    capsys: pytest.CaptureFixture[str],
) -> None:
    capabilities: dict[FamilyId | str, FamilySpec] = {
        family: spec for family, spec in CAPABILITIES.items()
    }
    spec = capabilities[FamilyId.REVERSE_ADD]
    assert spec.matrix is not None
    capabilities[FamilyId.REVERSE_ADD] = replace(
        spec, matrix=replace(spec.matrix, max_steps=8)
    )
    args = [
        "reverse-add",
        "--seed",
        "196",
        "--nth",
        "0",
        "--info",
        "temporal.matrix",
        "--temporal-matrix-steps",
        "9",
    ]
    with pytest.raises(ValueError, match="at most 8"):
        parse_request(args, registry=capabilities)
    with pytest.raises(SystemExit) as result:
        parser(demanded_family="reverse-add", registry=capabilities).parse_args(
            ["reverse-add", "--help"]
        )
    assert result.value.code == 0
    assert "--temporal-matrix-kind" in capsys.readouterr().out


@pytest.mark.parametrize(
    "flag", ["--temporal-depth-matrix", "--mahler-center-matrix-steps"]
)
def test_retired_matrix_options_are_not_parser_aliases(flag: str) -> None:
    with pytest.raises(SystemExit):
        parse_request(["antihydra", "--nth", "0", "--info", "metrics", flag])
