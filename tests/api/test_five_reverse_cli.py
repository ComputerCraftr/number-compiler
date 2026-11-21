"""Independent public-output fixtures for the five-reversal family."""

from __future__ import annotations

import json

import pytest

from number_compiler.api.cli import main
from number_compiler.api.cli_context import QueryContext
from number_compiler.api.cli_requests import parse_request
from number_compiler.api.number_api import NumberCompiler
from number_compiler.api.query_types import FiveReverseTermQuery
from tests.support.observation_views import view_value


@pytest.mark.parametrize(
    "seed,index,expected",
    (
        (0, 0, 0),
        (0, 4, 0),
        (196, 0, 196),
        (196, 1, 3455),
        (196, 2, 27715),
        (120, 1, 105),
        (1, 3, 260),
    ),
)
def test_five_reverse_exact_public_output(
    seed: int, index: int, expected: int, capsys: pytest.CaptureFixture[str]
) -> None:
    assert main(["5rev10", "--seed", str(seed), "--nth", str(index)]) == 0
    assert capsys.readouterr().out.strip() == str(expected)


def test_five_reverse_modular_only_has_no_execution_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("all-source residue should not construct the exact term")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    request = parse_request(
        [
            "5rev10",
            "--seed",
            "196",
            "--nth",
            "4096",
            "--no-value",
            "--info",
            "arithmetic.modular",
        ]
    )
    assert request is not None
    context = QueryContext(request, NumberCompiler())
    packet = view_value(context.information()["arithmetic.modular"], "endpoint")
    assert packet["modulus"] == 45
    # Decimal reversal preserves residue modulo 9; every positive-index
    # result is divisible by 5. 5**4096 == 4 (mod 9), and 196 == 7 (mod 9).
    assert packet["residue"] == 10
    assert packet["execution_authority"] is False


@pytest.mark.parametrize("seed", (-1, True))
def test_five_reverse_query_rejects_negative_or_boolean_seed(seed: int) -> None:
    with pytest.raises((TypeError, ValueError)):
        FiveReverseTermQuery(0, seed=seed)


def test_five_reverse_explicit_budget_refusal(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert main(["5rev10", "--seed", "196", "--nth", "2", "--max-steps", "1"]) != 0
    assert capsys.readouterr().err


def test_five_reverse_reflected_projection_uses_the_moving_cut(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("moving-cut observations should bypass the physical term")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    request = parse_request(
        [
            "5rev10",
            "--seed",
            "196",
            "--nth",
            "209",
            "--no-value",
            "--info",
            "temporal.closed-form",
            "--temporal-closed-form-digits",
            "4",
            "--info",
            "arithmetic.modular",
            "--arithmetic-modular-kind",
            "digit-field",
            "--arithmetic-modular-places",
            "3",
        ]
    )
    assert request is not None
    with QueryContext(request, NumberCompiler()) as context:
        info = context.information()
    form = view_value(info["temporal.closed-form"], "endpoint")
    assert form["h_source"] == 691
    assert form["h_exponent"] == 104
    assert form["unnormalized_residue"] == 0
    assert form["physical_low_residue"] == 3215
    assert form["binary_half_digit_mask_lsd"] == "1011"
    assert (form["low_first_prefix_base5"], form["high_first_residue_base5"]) == (
        256,
        152,
    )
    field = view_value(info["arithmetic.modular"], "digit-field")
    x = 196
    for _ in range(209):
        x = 5 * int(str(x)[::-1])
    literal_field = int("".join(str(5 * int(digit)) for digit in str(x)))
    assert field["field_residue"] == literal_field % 1125
    assert field["successor_closed"] is False


def test_five_reverse_combined_matrix_demands_share_admission(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.five_reverse.term import FiveReverseTerm

    original = FiveReverseTerm.source_transfer
    calls: list[tuple[int, bool]] = []

    def counted(self: FiveReverseTerm, steps: int, *, trace: bool = False) -> object:
        calls.append((steps, trace))
        return original(self, steps, trace=trace)

    monkeypatch.setattr(FiveReverseTerm, "source_transfer", counted)
    request = parse_request(
        [
            "5rev10",
            "--seed",
            "1",
            "--nth",
            "0",
            "--no-value",
            "--info",
            "temporal.matrix",
            "--info",
            "temporal.matrix.trace",
            "--temporal-matrix-steps",
            "2",
        ]
    )
    assert request is not None
    context = QueryContext(request, NumberCompiler())
    info = context.information()
    assert calls == [(2, True)]
    assert "trace" not in info["temporal.matrix"]
    trace = info["temporal.matrix.trace"]["trace"]
    assert isinstance(trace, list)
    assert len(trace) == 2
    assert info["temporal.matrix"]["execution_authority"] is False


def test_five_reverse_ordered_output_is_explicitly_a_decimal_observation(
    capsys: pytest.CaptureFixture[str],
) -> None:
    status = main(
        [
            "5rev10",
            "--seed",
            "1",
            "--nth",
            "0",
            "--no-value",
            "--format",
            "json",
            "--info",
            "temporal.matrix",
            "--temporal-matrix-kind",
            "digit-band",
            "--temporal-matrix-steps",
            "2",
            "--temporal-matrix-band-width",
            "1",
            "--temporal-matrix-modulus",
            "97",
        ]
    )
    assert status == 0
    packet = json.loads(capsys.readouterr().out)["info"]["temporal.matrix"]
    assert packet["coordinate"] == {"kind": "decimal-band-digits", "value": 1}
    assert packet["coefficient_ring"] == {"kind": "integers-modulo", "modulus": 97}
    assert packet["execution_authority"] is False
    assert packet["horizon"] == {"ticks": 2, "unit": "physical-recurrence-ticks"}
