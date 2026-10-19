"""Explicit output lowering should not round-trip through an endpoint integer."""

from __future__ import annotations

import sys
from decimal import localcontext
from typing import Never

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.api.number_api import FermatTermPayload, MersenneTermPayload
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def _forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("text rendering used an avoidable scalar/width path")


def _reference(value: int, base: int) -> str:
    digits = "0123456789abcdefghijklmnopqrstuvwxyz"
    result: list[str] = []
    while value:
        value, digit = divmod(value, base)
        result.append(digits[digit])
    return "".join(reversed(result)) or "0"


@pytest.mark.parametrize("base", (2, 4, 8, 16, 32))
@pytest.mark.parametrize(
    "family,index",
    (
        ("fermat", 0),
        ("fermat", 3),
        ("fermat", 5),
        ("mersenne", 1),
        ("mersenne", 7),
        ("mersenne", 17),
    ),
)
def test_power_family_text_uses_sparse_or_uniform_source(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    family: str,
    index: int,
    base: int,
) -> None:
    monkeypatch.setattr(FermatTermPayload, "materialize", _forbidden)
    monkeypatch.setattr(MersenneTermPayload, "materialize", _forbidden)
    assert cli.main([family, "--nth", str(index), "--output-base", str(base)]) == 0
    expected = (1 << (1 << index)) + 1 if family == "fermat" else (1 << index) - 1
    assert capsys.readouterr().out.strip() == _reference(expected, base)


@pytest.mark.parametrize("base", (2, 4, 8, 16, 32))
@pytest.mark.parametrize("view_radix", (2, 3, 6))
def test_collatz_power_radix_text_streams_native_binary_image(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    base: int,
    view_radix: int,
) -> None:
    monkeypatch.setattr(PoweredCollatzTerm, "materialize", _forbidden)
    monkeypatch.setattr(PoweredCollatzTerm, "width", _forbidden)
    assert (
        cli.main(
            [
                "collatz",
                "--nth",
                "4",
                "--seed",
                "27",
                "--radix",
                str(view_radix),
                "--output-base",
                str(base),
            ]
        )
        == 0
    )
    assert capsys.readouterr().out.strip() == _reference(62, base)


@pytest.mark.parametrize("source_base,expected", ((2, 54), (4, 84), (8, 54), (16, 204)))
@pytest.mark.parametrize("target_base", (2, 4, 8, 16, 32))
def test_reverse_power_radix_conversion_does_not_rebuild_an_integer(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    source_base: int,
    expected: int,
    target_base: int,
) -> None:
    monkeypatch.setattr(ReverseAddPoweredTerm, "materialize", _forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "width", _forbidden)
    assert (
        cli.main(
            [
                "reverse-add",
                "--nth",
                "1",
                "--seed",
                "27",
                "--base",
                str(source_base),
                "--output-base",
                str(target_base),
            ]
        )
        == 0
    )
    assert capsys.readouterr().out.strip() == _reference(expected, target_base)


def test_196_symbolic_upper_bound_avoids_width_preflight(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(ReverseAddPoweredTerm, "width", _forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "materialize", _forbidden)
    assert cli.main(["reverse-add", "--seed", "196", "--nth", "4"]) == 0
    assert capsys.readouterr().out.strip() == "13783"


def test_tight_output_cap_still_rejects_before_endpoint_emission(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(ReverseAddPoweredTerm, "iter_digits", _forbidden)
    assert (
        cli.main(
            ["reverse-add", "--seed", "196", "--nth", "1", "--max-output-bits", "8"]
        )
        == 2
    )
    output = capsys.readouterr()
    assert not output.out
    assert "output exceeds --max-output-bits" in output.err


def test_decimal_scalar_format_never_changes_process_digit_limit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    previous = sys.get_int_max_str_digits()
    monkeypatch.setattr(sys, "set_int_max_str_digits", _forbidden)
    with localcontext() as context:
        context.prec = 2
        context.Emax = 2
        context.Emin = -2
        assert cli_render.radix_string(10**5000 + 987, 10) == "1" + "0" * 4997 + "987"
        assert cli_render.radix_string(12345, 10) == "12345"
    assert sys.get_int_max_str_digits() == previous


def test_regrouping_consumes_one_pass_and_drops_only_leading_zeroes() -> None:
    assert cli_render.power_of_two_radix_string(iter((3, 2, 1, 0)), 4, 8) == "33"
    assert cli_render.power_of_two_radix_string(iter((0, 0)), 2, 32) == "0"
    assert cli_render.radix_string_from_lsd(iter((3, 2, 1)), 10) == "123"
