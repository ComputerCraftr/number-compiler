"""Arbitrary-seed CLI integration and source-specific finite center returns."""

from __future__ import annotations

import json
from typing import cast

import pytest

from number_compiler.api import cli
from number_compiler.api.cli_requests import parse_request
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_seed_cli import (
    seed_morphism_cli_packet,
)
from tests.support.reverse_add_source_data import iterate_double_reverse as literal


def _mapping(value: object) -> dict[str, object]:
    if not isinstance(value, dict):
        raise AssertionError("expected a string-keyed JSON object")
    mapping = cast(dict[object, object], value)
    if any(type(key) is not str for key in mapping):
        raise AssertionError("expected a string-keyed JSON object")
    return cast(dict[str, object], value)


def _sequence(value: object) -> list[object]:
    if not isinstance(value, list):
        raise TypeError("expected a JSON array")
    return cast(list[object], value)


def _integer(value: object) -> int:
    if type(value) is not int:
        raise AssertionError("expected an exact integer field")
    return value


def _string(value: object) -> str:
    if type(value) is not str:
        raise AssertionError("expected a string field")
    return value


def cli_packet(
    capsys: pytest.CaptureFixture[str], seed: int, n: int, *args: str
) -> dict[str, object]:
    argv = [
        "2rev10",
        "--seed",
        str(seed),
        "--nth",
        str(n),
        "--no-value",
        "--format",
        "json",
        "--info",
        "temporal.seed-morphism",
        *args,
    ]
    assert cli.main(argv) == 0
    wire = _mapping(json.loads(capsys.readouterr().out))
    assert wire["index"] == n
    return _mapping(_mapping(wire["info"])["temporal.seed-morphism"])


@pytest.mark.parametrize(
    "seed,n",
    [
        (0, 0),
        (0, 128),
        (1, 2),
        (1, 32),
        (1, 128),
        (1, 256),
        (2, 64),
        (3, 64),
        (12, 64),
        (101, 128),
        (139, 128),
        (196, 128),
        (196, 256),
        (517, 128),
        (170688, 64),
    ],
)
def test_cli_exact_any_seed_center_and_exterior(
    seed: int, n: int, capsys: pytest.CaptureFixture[str]
) -> None:
    got = cli_packet(capsys, seed, n)
    word = str(literal(seed, n))
    width = len(word)
    size = 1 if width % 2 else 2
    start = (width - size) // 2
    outer = int(word[:start] or "0") * 10 ** (start + size) + int(
        word[start + size :] or "0"
    )
    end = _mapping(got["endpoint"])
    assert end["width"] == width
    assert end["center"] == word[start : start + size]
    assert end["mod99"] == int(word) % 99
    assert end["mod198"] == int(word) % 198
    assert end["punctured_exterior_mod99"] == outer % 99
    assert end["punctured_exterior_mod198"] == outer % 198
    assert end["full_digit_slp"] is True
    assert got["all_depth_period_claim"] is False
    if seed and n >= 64:
        power = _mapping(got["power"])
        assert power["mode"] == "source_certified_hashlife_dyadic"
        assert _integer(power["physical_powered_generations"]) > 0
        assert sum(
            _integer(value) for value in _sequence(power["dyadic_t_squared_chunks"])
        ) * 2 == _integer(power["physical_powered_generations"])


def test_seed_139_extended_bound_certifies_beyond_historical_32(
    capsys: pytest.CaptureFixture[str],
) -> None:
    got = cli_packet(capsys, 139, 128)
    power = _mapping(got["power"])
    assert power["source_prefix_generation"] == 34
    assert power["mode"] == "source_certified_hashlife_dyadic"
    got = cli_packet(capsys, 139, 128, "--temporal-prefix-horizon", "32")
    assert _mapping(got["power"])["mode"] == "exact_scheduler_fallback"
    assert _mapping(got["endpoint"])["mod99"] == literal(139, 128) % 99


def test_power10_seed_coordinates_keep_the_compact_index_encoding(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "0",
                "--nth-power10",
                "3",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.seed-morphism",
            ]
        )
        == 0
    )
    wire = _mapping(json.loads(capsys.readouterr().out))
    encoded = {"encoding": "power10", "exponent": 3}
    assert wire["index"] == encoded
    assert wire["value"] is None
    packet = _mapping(_mapping(wire["info"])["temporal.seed-morphism"])
    assert packet["target_generation"] == encoded
    power = _mapping(packet["power"])
    assert power["source_prefix_generation"] == encoded
    assert power["mode"] == "exact_fixed_zero"


def test_huge_power10_seed_query_refuses_without_expanding_index(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "0",
                "--nth-power10",
                "5000",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.seed-morphism",
            ]
        )
        == 2
    )
    captured = capsys.readouterr()
    assert "generation exceeds its step budget" in captured.err
    assert captured.out == ""
    assert len(captured.err) < 200
    assert "1" + "0" * 100 not in captured.err


@pytest.mark.parametrize("seed", [1, 196])
def test_center_period_scan_matches_exact_time_samples_and_real_drivers(
    seed: int, capsys: pytest.CaptureFixture[str]
) -> None:
    packet = cli_packet(
        capsys,
        seed,
        256,
        "--temporal-period-samples",
        "12",
        "--temporal-period-depth",
        "2",
        "--temporal-period-drivers",
    )
    scan = _mapping(packet["period_observations"])
    assert scan["actual_samples"] == 12
    drivers = _mapping(scan["drivers"])
    letters = _sequence(drivers["letters"])
    assert drivers["status"] == "available"
    assert len(letters) == 11
    for i, row_value in enumerate(_sequence(scan["trace"])):
        row = _mapping(row_value)
        word = str(literal(seed, _integer(row["generation"])))
        assert row["width"] == len(word)
        assert row["residue99"] == int(word) % 99
        assert row["residue198"] == int(word) % 198
        for layer_value in _sequence(scan["layers"]):
            layer = _mapping(layer_value)
            d = _integer(layer["depth"])
            size = 1 if len(word) % 2 else 2
            begin = (len(word) - size) // 2 - d
            end = begin + size + 2 * d
            observed = _sequence(layer["observed_digits"])
            assert _string(observed[i]) == word[begin:end]
    for letter_value in letters:
        letter = _mapping(letter_value)
        assert letter["from_center"] != ""
        assert len(_sequence(letter["incoming_carries"])) == 3
        assert 0 <= _integer(letter["right_f5"]) < 5
    assert _string(scan["scope"]).startswith("exact finite")
    assert packet["all_depth_period_claim"] is False


@pytest.mark.validation
def test_different_center_return_gaps_across_seeds(
    capsys: pytest.CaptureFixture[str],
) -> None:
    _assert_different_center_return_gaps(
        capsys, index=512, samples=64, require_long_gap=True
    )


@pytest.mark.parametrize(
    "index",
    [
        pytest.param(128, id="unit"),
        pytest.param(512, marks=pytest.mark.validation, id="full"),
    ],
)
def test_representative_center_return_gaps_are_seed_specific(
    capsys: pytest.CaptureFixture[str],
    index: int,
) -> None:
    _assert_different_center_return_gaps(
        capsys,
        index=index,
        samples=32,
        require_long_gap=False,
        require_short_gap=index == 512,
    )


def _assert_different_center_return_gaps(
    capsys: pytest.CaptureFixture[str],
    *,
    index: int,
    samples: int,
    require_long_gap: bool,
    require_short_gap: bool = False,
) -> None:
    first = cli_packet(
        capsys,
        1,
        index,
        "--temporal-period-samples",
        str(samples),
        "--temporal-period-depth",
        "0",
    )
    second = cli_packet(
        capsys,
        196,
        index,
        "--temporal-period-samples",
        str(samples),
        "--temporal-period-depth",
        "0",
    )
    layers_a = _sequence(_mapping(first["period_observations"])["layers"])
    layers_b = _sequence(_mapping(second["period_observations"])["layers"])
    a = _mapping(layers_a[0])
    b = _mapping(layers_b[0])
    gaps_a = {
        _integer(_mapping(row)["physical_gap"])
        for row in _sequence(a["consecutive_observed_return_gaps"])
    }
    gaps_b = {
        _integer(_mapping(row)["physical_gap"])
        for row in _sequence(b["consecutive_observed_return_gaps"])
    }
    assert gaps_a != gaps_b
    if require_short_gap:
        assert 4 in gaps_a
    if require_long_gap:
        assert 4 in gaps_a
        assert 40 in gaps_b
    assert a["finite_window_period_lags"] == []
    assert b["finite_window_period_lags"] == []


def test_exact_morphism_after_prefix_does_not_replay_scalar(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(196, 144, max_state_bits=16384) as term:
        term.prepare_bank_source(max_prefix=32)

        def forbidden(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("powered suffix replayed scalar transition")

        monkeypatch.setattr(type(term.source_adapter), "_general_two_step", forbidden)
        monkeypatch.setattr(type(term.source_adapter), "_apply_word", forbidden)
        answer = seed_morphism_cli_packet(term, period_samples=4, period_depth=2)
        assert _mapping(answer["endpoint"])["center"] == "50"
        assert _mapping(answer["power"])["physical_powered_generations"] == 128


@pytest.mark.parametrize(
    "bad",
    [
        ["--temporal-period-samples", "129"],
        ["--temporal-period-stride", "0"],
        ["--temporal-period-depth", "9"],
        ["--temporal-prefix-horizon", "513"],
    ],
)
def test_cli_rejects_oversized_observer_demand(bad: list[str]) -> None:
    with pytest.raises((ValueError, TypeError)):
        parse_request(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "256",
                "--info",
                "temporal.seed-morphism",
                *bad,
            ]
        )


def test_residue_and_seed_morphism_observers_are_order_independent(
    capsys: pytest.CaptureFixture[str],
) -> None:
    root = ["2rev10", "--seed", "139", "--nth", "128", "--no-value", "--format", "json"]
    for flags in (
        ["--info", "temporal.residue99", "--info", "temporal.seed-morphism"],
        ["--info", "temporal.seed-morphism", "--info", "temporal.residue99"],
    ):
        assert cli.main([*root, *flags]) == 0
        packet = _mapping(json.loads(capsys.readouterr().out))["info"]
        packet = _mapping(packet)
        assert (
            _mapping(packet["temporal.residue99"])["target_mod99"]
            == _mapping(_mapping(packet["temporal.seed-morphism"])["endpoint"])["mod99"]
        )
        assert _mapping(packet["temporal.residue99"])["prefix_steps"] == 34
