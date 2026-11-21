"""A Fermat CLI matrix can demand the bounded source-owned negacyclic halo."""

import json
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.matrix_contracts import NegacyclicMatrixRequest
from number_compiler.sequences.power_numbers import fermat_negacyclic_halo
from number_compiler.sequences.power_numbers.numbers import FermatNumberSpec

_HALO = (
    "--info",
    "temporal.matrix",
    "--temporal-matrix-kind",
    "negacyclic",
    "--temporal-matrix-steps",
    "3",
    "--format",
    "json",
)


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("CLI constructed an unrequested matrix kind")


@pytest.mark.parametrize(
    ("index", "modulus", "source", "endpoint", "wrap", "high"),
    ((0, 3, 0, 0, 0, 0), (2, 17, 16, 7, 25, -3)),
)
def test_fermat_halo_uses_the_selected_root(
    index: int,
    modulus: int,
    source: int,
    endpoint: int,
    wrap: int,
    high: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(
        FermatNumberSpec, "demand_fermat_powered_port_matrix", _forbidden
    )
    args = ["fermat", "--nth", str(index), "--no-value", *_HALO]
    request = parse_request(args)
    assert request is not None and request.matrix == NegacyclicMatrixRequest(3)
    assert main(args) == 0
    packet = json.loads(capsys.readouterr().out)
    matrix = packet["info"]["temporal.matrix"]
    assert packet["value"] is None
    assert matrix["law"] == "negacyclic-affine"
    assert matrix["horizon"] == {"ticks": 3, "unit": "ordinary-tripling-ticks"}
    assert matrix["source_index"] == index
    assert matrix["source_level"] == (1 << index) - 1
    assert matrix["width_bits"] == 1 << index
    assert matrix["modulus"] == modulus
    assert (matrix["source_residue"], matrix["endpoint_residue"]) == (source, endpoint)
    assert matrix["canonical_source_wrap_bits"] == 32
    assert matrix["canonical_source_wrap"] == wrap
    assert matrix["canonical_inlet_low"] == 0
    assert matrix["canonical_inlet_high_correction"] == high
    assert matrix["raw_source_carry"] is None
    assert (
        matrix["execution_authority"] is False
        and matrix["primality_authority"] is False
    )


@pytest.mark.parametrize(
    "extra",
    (
        ("--info", "temporal.matrix.trace"),
        ("--temporal-matrix-digit-position", "2"),
    ),
)
def test_negacyclic_cli_rejects_other_matrix_coordinates(
    extra: tuple[str, str],
) -> None:
    with pytest.raises(ValueError):
        parse_request(["fermat", "--nth", "2", *_HALO, *extra])


def test_negacyclic_cli_rejects_an_admitted_matrix_index_outside_the_halo(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert main(["fermat", "--nth", "9", "--no-value", *_HALO]) == 2
    assert "negacyclic halo" in capsys.readouterr().err


def test_ordinary_fermat_matrix_does_not_open_the_halo(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(
        fermat_negacyclic_halo, "demand_fixed_multiplier_halo", _forbidden
    )
    assert (
        main(
            [
                "fermat",
                "--nth",
                "2",
                "--no-value",
                "--info",
                "temporal.matrix",
                "--temporal-matrix-steps",
                "3",
                "--format",
                "json",
            ]
        )
        == 0
    )
    matrix = json.loads(capsys.readouterr().out)["info"]["temporal.matrix"]
    assert matrix["matrix_kind"] == "source-transfer"


def test_fermat_help_and_metrics_do_not_open_the_halo(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(
        fermat_negacyclic_halo, "demand_fixed_multiplier_halo", _forbidden
    )
    with pytest.raises(SystemExit) as completion:
        main(["fermat", "--help"])
    assert completion.value.code == 0
    assert "negacyclic" in capsys.readouterr().out
    assert main(["fermat", "--nth", "2", "--no-value", "--info", "metrics"]) == 0


def test_negacyclic_cli_supports_the_full_bounded_horizon(
    capsys: pytest.CaptureFixture[str],
) -> None:
    args = ["fermat", "--nth", "8", "--no-value", *_HALO]
    args[args.index("--temporal-matrix-steps") + 1] = "4096"
    assert main(args) == 0
    matrix = json.loads(capsys.readouterr().out)["info"]["temporal.matrix"]
    modulus = (1 << 256) + 1
    exponent = 1 << 255
    assert matrix["endpoint_residue"] == pow(3, exponent + 4096, modulus)
    canonical_source = pow(3, exponent, modulus)
    assert matrix["canonical_source_wrap"] == (
        (canonical_source * 3**4096 // modulus) % (1 << 32)
    )
    assert matrix["horizon"]["ticks"] == 4096
