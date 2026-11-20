"""Semantic matrix kinds use shared declarations without seed-named flags."""

from dataclasses import replace

import pytest

from number_compiler.api.cli_context import QueryContext
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.family_registry import family_spec
from number_compiler.api.matrix_contracts import MatrixKind, OrderedMatrixRequest
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.observation_types import ObservationId
from number_compiler.api.query_types import FiveReverseTermQuery
from number_compiler.arithmetic.contracts.family_identity import FamilyId


def test_carry_contract_retains_bits_and_its_independent_precision_bound() -> None:
    base = family_spec(FamilyId.DOUBLE_REVERSE).matrix
    assert base is not None
    capability = replace(base, ordered_kinds=(MatrixKind.CARRY_CONTINUANT,))
    request = capability.build(
        {
            "temporal_matrix_kind": "carry-continuant",
            "temporal_matrix_steps": 4,
            "temporal_matrix_precision": 133,
            "temporal_matrix_coefficients": (1, -2, 3),
        }
    )
    assert isinstance(request, OrderedMatrixRequest)
    assert request.kind is MatrixKind.CARRY_CONTINUANT
    assert request.precision == 133
    assert request.coefficients == (1, -2, 3)
    with pytest.raises(ValueError, match="precision"):
        OrderedMatrixRequest(MatrixKind.CARRY_CONTINUANT, 4, precision=134)


@pytest.mark.parametrize("family", ["reverse-add", "2rev10"])
def test_ordered_kinds_share_declared_units_and_coefficients(family: str) -> None:
    request = parse_request(
        [
            family,
            "--seed",
            "196",
            "--nth",
            "180",
            "--no-value",
            "--info",
            "temporal.matrix",
            "--temporal-matrix-kind",
            "digit-band",
            "--temporal-matrix-steps",
            "4",
            "--temporal-matrix-band-width",
            "12",
            "--temporal-matrix-coefficients=1,-2,0,3",
        ]
    )
    assert request is not None
    assert isinstance(request.matrix, OrderedMatrixRequest)
    assert request.matrix.kind is MatrixKind.DIGIT_BAND
    assert request.matrix.band_width == 12
    assert request.matrix.steps == 4
    assert request.matrix.coefficients == (1, -2, 0, 3)
    assert request.matrix.modulus == 1_000_000_007


@pytest.mark.parametrize(
    "extra",
    [
        ["--temporal-matrix-precision", "3"],
        ["--temporal-matrix-pair-depth", "2"],
        ["--temporal-matrix-modulus", "0"],
        ["--temporal-matrix-steps", "4097"],
        ["--temporal-matrix-steps", "2"],
    ],
)
def test_ordered_kind_rejects_wrong_coordinate_or_bound(extra: list[str]) -> None:
    args = [
        "2rev10",
        "--seed",
        "196",
        "--nth",
        "4400",
        "--info",
        "temporal.matrix",
        "--temporal-matrix-kind",
        "digit-band",
    ]
    if "--temporal-matrix-steps" not in extra:
        args.extend(["--temporal-matrix-steps", "4"])
    with pytest.raises((ValueError, SystemExit)):
        parse_request(args + extra)


def test_five_reverse_snapshot_has_no_owner_or_detailed_preparation(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("snapshot must not create an execution owner")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    request = parse_request(
        ["5rev10", "--seed", "196", "--nth", "180", "--no-value", "--info", "temporal"]
    )
    assert request is not None
    assert isinstance(request.execution, FiveReverseTermQuery)
    context = QueryContext(request, NumberCompiler())
    packet = context.information()
    assert packet[ObservationId.TEMPORAL.value]["status"] == "snapshot"


def test_ordered_trace_above_bound_is_rejected() -> None:
    with pytest.raises(ValueError):
        parse_request(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "4400",
                "--info",
                "temporal.matrix.trace",
                "--temporal-matrix-kind",
                "digit-band",
                "--temporal-matrix-steps",
                "132",
            ]
        )


def test_ordered_output_preserves_family_specific_horizon() -> None:
    capability = family_spec(FamilyId.REVERSE_ADD).matrix
    assert capability is not None
    capability.validate(OrderedMatrixRequest(MatrixKind.DIGIT_BAND, 128))
    with pytest.raises(ValueError, match="at most 128"):
        capability.validate(OrderedMatrixRequest(MatrixKind.DIGIT_BAND, 129))


def test_five_reverse_exposes_decimal_band_not_an_unproved_bit_fibre() -> None:
    base = [
        "5rev10",
        "--seed",
        "196",
        "--nth",
        "180",
        "--no-value",
        "--info",
        "temporal.matrix",
        "--temporal-matrix-steps",
        "4",
    ]
    request = parse_request(base + ["--temporal-matrix-kind", "digit-band"])
    assert request is not None
    assert isinstance(request.matrix, OrderedMatrixRequest)
    assert request.matrix.band_width == 2
    with pytest.raises(SystemExit):
        parse_request(base + ["--temporal-matrix-kind", "carry-continuant"])


def test_seed_named_observation_is_rejected() -> None:
    with pytest.raises(SystemExit):
        parse_request(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "4400",
                "--info",
                "temporal.seed196-boolean-border",
            ]
        )
