"""The public special-prime command exposes admission and charges fallback."""

from __future__ import annotations

import json
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler
from number_compiler.sequences.power_numbers import classical_ceiling
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
    assert main(["classify", family, str(parameter), "--format", "json"]) == 0
    row = json.loads(capsys.readouterr().out)
    assert row["status"] == "prime" and row["decided"]
    assert not row["classical_ceiling_allowed"]
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
    assert main(["classify", family, str(parameter), "--format", "json"]) == 3
    row = json.loads(capsys.readouterr().out)
    assert row["status"] == "unknown" and not row["decided"]
    assert row["certificate"]["specialization_raw_squarings"] == 0


@pytest.mark.parametrize(
    ("family", "parameter", "status", "steps"),
    [
        ("fermat", 4, "prime", 15),
        ("fermat", 5, "composite", 31),
        ("mersenne", 13, "prime", 11),
        ("mersenne", 11, "composite", 9),
    ],
)
def test_explicit_classical_option_preserves_exact_result_and_work(
    family: str,
    parameter: int,
    status: str,
    steps: int,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                "classify",
                family,
                str(parameter),
                "--allow-classical-ceiling",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    assert row["status"] == status and row["classical_ceiling_allowed"]
    assert row["certificate"]["specialization_raw_squarings"] == steps


def test_composite_exponent_and_small_forms_remain_decidable(
    capsys: pytest.CaptureFixture[str],
) -> None:
    for family, parameter, status in [
        ("mersenne", "12", "composite"),
        ("mersenne", "2", "prime"),
        ("fermat", "0", "prime"),
    ]:
        assert main(["classify", family, parameter]) == 0
        assert capsys.readouterr().out.strip() == status


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
        assert main(["classify", *args]) == 2
        assert capsys.readouterr().err.startswith("number-compiler:")
