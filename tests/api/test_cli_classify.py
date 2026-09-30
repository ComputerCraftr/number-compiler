"""The special-prime command cannot enter research recurrence oracles."""

from __future__ import annotations

import json
from typing import Never

import pytest

from devtools.verification.oracles import classical_ceiling
from number_compiler.api.cli import main
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.arithmetic.polynomials import two_primary_filtration


def _forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("slow path entered default CLI classification")


@pytest.mark.parametrize(("family", "parameter"), [("fermat", 3), ("mersenne", 7)])
def test_classify_admitted_clock_avoids_recurrence_and_full_filtration(
    family: str,
    parameter: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(classical_ceiling, "fermat_classical_ceiling", _forbidden)
    monkeypatch.setattr(classical_ceiling, "mersenne_classical_ceiling", _forbidden)
    monkeypatch.setattr(
        two_primary_filtration, "pure_two_primary_image_filtration", _forbidden
    )
    assert (
        main(
            [
                family,
                "--nth",
                str(parameter),
                "--no-value",
                "--info",
                "primality",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)["info"]["primality"]
    assert row["status"] == "prime" and row["decided"]
    assert "classical_ceiling_allowed" not in row
    assert row["certificate"]["specialization_raw_squarings"] == 0
    assert row["certificate"]["carrier_states_enumerated"] == 0


@pytest.mark.parametrize(("family", "parameter"), [("fermat", 4), ("mersenne", 13)])
def test_classify_unadmitted_clock_returns_unknown_without_fallback(
    family: str,
    parameter: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(classical_ceiling, "fermat_classical_ceiling", _forbidden)
    monkeypatch.setattr(classical_ceiling, "mersenne_classical_ceiling", _forbidden)
    assert (
        main(
            [
                family,
                "--nth",
                str(parameter),
                "--no-value",
                "--info",
                "primality",
                "--format",
                "json",
            ]
        )
        == 3
    )
    row = json.loads(capsys.readouterr().out)["info"]["primality"]
    assert row["status"] == "unknown" and not row["decided"]
    assert row["certificate"]["specialization_raw_squarings"] == 0


@pytest.mark.parametrize(
    "option", ["--allow-classical-ceiling", "--max-classical-squarings"]
)
def test_removed_classical_cli_options_are_rejected(
    option: str,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(
        CanonicalSequenceCompiler, "resolve_special_theorem", _forbidden
    )
    args = ["fermat", "--nth", "4", "--no-value", "--info", "primality", option]
    if option == "--max-classical-squarings":
        args.append("100")
    with pytest.raises(SystemExit) as exc:
        main(args)
    assert exc.value.code == 2


def test_composite_exponent_and_small_forms_remain_decidable(
    capsys: pytest.CaptureFixture[str],
) -> None:
    for family, parameter, status in [
        ("mersenne", "12", "composite"),
        ("mersenne", "2", "prime"),
        ("fermat", "0", "prime"),
    ]:
        assert (
            main(
                [
                    family,
                    "--nth",
                    parameter,
                    "--no-value",
                    "--info",
                    "primality",
                    "--format",
                    "json",
                ]
            )
            == 0
        )
        row = json.loads(capsys.readouterr().out)["info"]["primality"]
        assert row["status"] == status


def test_candidate_budget_and_domain_rejected_before_theorem_work(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(
        CanonicalSequenceCompiler, "resolve_special_theorem", _forbidden
    )
    for args in [
        ["fermat", "20", "--max-candidate-bits", "1024"],
        ["mersenne", "1"],
        ["fermat", "-1"],
    ]:
        assert (
            main(
                [
                    args[0],
                    "--nth",
                    args[1],
                    "--no-value",
                    "--info",
                    "primality",
                    *args[2:],
                ]
            )
            == 2
        )
        assert capsys.readouterr().err.startswith("number-compiler:")


def test_factor_output_and_extra_work_are_explicit(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "mersenne",
                "--nth",
                "131",
                "--no-value",
                "--info",
                "primality",
                "--info",
                "factor",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)["info"]["primality"]
    assert row["factor_witness"] == 263
    assert row["etale_ring_multiplications"] == 261
    assert row["certificate"]["specialization_raw_squarings"] == 0
    assert (
        main(
            [
                "mersenne",
                "--nth",
                "11",
                "--no-value",
                "--info",
                "primality",
                "--info",
                "factor",
                "--format",
                "json",
            ]
        )
        == 0
    )
    info = json.loads(capsys.readouterr().out)["info"]
    assert info["primality"]["status"] == "composite"
    assert info["factor"]["factor_witness"] == 23
    assert (
        main(
            [
                "mersenne",
                "--nth",
                "12",
                "--no-value",
                "--info",
                "primality",
                "--info",
                "factor",
                "--format",
                "json",
            ]
        )
        == 0
    )
    info = json.loads(capsys.readouterr().out)["info"]
    assert info["primality"]["status"] == "composite"
    assert info["factor"]["factor_expression"] == "2^2-1"


def test_no_factor_request_leaves_missing_prime_bit_unresolved(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.sequences.power_numbers import etale_factor

    monkeypatch.setattr(etale_factor, "_quadratic_power_pair", _forbidden)
    assert (
        main(
            [
                "mersenne",
                "--nth",
                "131",
                "--no-value",
                "--info",
                "primality",
                "--format",
                "json",
            ]
        )
        == 3
    )
    row = json.loads(capsys.readouterr().out)["info"]["primality"]
    assert row["status"] == "unknown"
    assert row["factor_witness"] is None
    assert row["etale_ring_multiplications"] == 0


def test_factor_prime_control_does_not_become_a_prime_certificate(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "mersenne",
                "--nth",
                "13",
                "--no-value",
                "--info",
                "primality",
                "--info",
                "factor",
                "--format",
                "json",
            ]
        )
        == 3
    )
    row = json.loads(capsys.readouterr().out)["info"]["primality"]
    assert row["status"] == "unknown" and row["factor_witness"] is None
    assert row["etale_ring_multiplications"] > 0
