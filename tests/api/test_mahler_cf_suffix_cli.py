"""Check complete CF packets with literal row products at the public entry point."""

import json
from itertools import product

import pytest

from number_compiler.api.cli import main
from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.sequences.antihydra import mahler_cf_reciprocal_tile as tiles
from number_compiler.sequences.antihydra.mahler_cf_low_period import settled_low_action
from tests.sequences.antihydra.test_mahler_cf_cylinder import literal_cylinder


def _literal_segment(tile: tiles.ReciprocalTile, begin: int, length: int) -> Matrix2:
    digits = "".join(str(tile.quotient * 5**row) for row in range(len(tile.widths)))
    start = tile.start + begin
    result = Matrix2.identity()
    for digit in digits[start : start + length]:
        result = result.multiply(Matrix2.digit(int(digit) + 1))
    return result


def test_public_cylinder_reuses_settled_suffix_before_decode(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    phases: set[int] = set()
    suffix = settled_low_action(3, 2)
    select = tiles.reciprocal_row_interval

    def checked_interval(q: int, t: int, width: int, start: int, count: int) -> int:
        if q * 5**t % 100 == 25:
            assert start + count <= width - 2
        return select(q, t, width, start, count)

    def checked_action(exponent: int, columns: int) -> tuple[int, int, int, int]:
        if columns == 3 and exponent in (3, 4):
            phases.add(exponent)
            assert settled_low_action(exponent, 2) is suffix
        return settled_low_action(exponent, columns)

    for horizon, cap in product(
        (1, 3, 4, 5, 8, 20, 63), (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 17, 40, 500)
    ):
        args = [
            "antihydra",
            "--nth",
            "0",
            "--no-value",
            "--format",
            "json",
            "--info",
            "arithmetic.continued-fraction",
            "--safety-horizon",
            str(horizon),
            "--continued-fraction-max-coefficients",
            str(cap),
        ]
        with monkeypatch.context() as literal:
            literal.setattr(tiles.ReciprocalTile, "segment", _literal_segment)
            expected_status = main(args)
            expected = json.loads(capsys.readouterr().out)
        with monkeypatch.context() as observed:
            observed.setattr(tiles, "reciprocal_row_interval", checked_interval)
            observed.setattr(tiles, "settled_low_action", checked_action)
            assert main(args) == expected_status
            result = json.loads(capsys.readouterr().out)
        assert result == expected
        view = result["info"]["arithmetic.continued-fraction"]
        if expected_status == 0:
            consumed, matrix = literal_cylinder(horizon, cap)
            assert view["coefficient_count"] == consumed
            assert view["matrix"] == [list(row) for row in matrix]
        else:
            assert expected_status == 3
            assert view["status"] == "unknown" and view["coefficient_count"] == cap
    assert phases == {3, 4}


def test_public_spatial_cylinder_uses_settled_action_before_trace(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.arithmetic.automata.carry_spacetime_trace import (
        Pow5SpatialTrace,
    )

    observed: list[tuple[int, int]] = []
    phases: set[int] = set()
    suffix = settled_low_action(3, 2)
    select_action = settled_low_action
    select_interval = tiles.reciprocal_row_interval
    issue = tiles.ReciprocalTile.segment

    def watch_action(exponent: int, columns: int) -> tuple[int, int, int, int]:
        action = select_action(exponent, columns)
        if exponent in (3, 4) and columns in (2, 3):
            phases.add(exponent)
            assert select_action(exponent, 2) is suffix
        return action

    def watch_interval(q: int, t: int, width: int, start: int, count: int) -> int:
        if q * 5**t in (125, 625):
            assert start + count <= width - 2
        return select_interval(q, t, width, start, count)

    def watched(tile: tiles.ReciprocalTile, start: int, length: int) -> Matrix2:
        if tile.first_exponent is not None:
            observed.append(
                (tile.first_exponent, tile.first_exponent + len(tile.widths) - 1)
            )
        return issue(tile, start, length)

    def no_trace(*_args: object, **_kwargs: object) -> None:
        pytest.fail("the settled prefix cannot open the spatial trace")

    monkeypatch.setattr(tiles.ReciprocalTile, "segment", watched)
    monkeypatch.setattr(Pow5SpatialTrace, "issue", no_trace)
    monkeypatch.setattr(tiles, "settled_low_action", watch_action)
    monkeypatch.setattr(tiles, "reciprocal_row_interval", watch_interval)
    assert (
        main(
            [
                "antihydra",
                "--nth",
                "0",
                "--no-value",
                "--format",
                "json",
                "--info",
                "arithmetic.continued-fraction",
                "--safety-horizon",
                "64",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)
    view = packet["info"]["arithmetic.continued-fraction"]
    count, matrix = literal_cylinder(64, 500)
    assert view["coefficient_count"] == count
    assert view["matrix"] == [list(row) for row in matrix]
    assert observed and min(first for first, _ in observed) == 1
    assert max(last for _, last in observed) >= 4
    assert phases == {3, 4}


def test_opt_in_cylinder_uses_reciprocal_actions_at_full_horizon(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.arithmetic.automata.carry_spacetime_trace import (
        Pow5SpatialTrace,
    )

    args = [
        "antihydra",
        "--nth",
        "0",
        "--no-value",
        "--format",
        "json",
        "--info",
        "arithmetic.continued-fraction",
        "--safety-horizon",
        "4096",
    ]
    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_CF_RECIPROCAL", raising=False)
    assert main(args) == 0
    expected = json.loads(capsys.readouterr().out)
    calls = 0
    issue = tiles.ReciprocalTile.segment

    def watched(tile: tiles.ReciprocalTile, start: int, length: int) -> Matrix2:
        nonlocal calls
        calls += 1
        return issue(tile, start, length)

    def no_trace(*_args: object, **_kwargs: object) -> None:
        pytest.fail("reciprocal source cannot construct a spatial trace")

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_CF_RECIPROCAL", "1")
    monkeypatch.setattr(tiles.ReciprocalTile, "segment", watched)
    monkeypatch.setattr(Pow5SpatialTrace, "__init__", no_trace)
    assert main(args) == 0
    actual = json.loads(capsys.readouterr().out)
    assert actual == expected
    assert calls > 0
    assert actual["info"]["arithmetic.continued-fraction"]["coefficient_count"] == 540


def test_opt_in_cylinder_preserves_bounded_unknown_packet(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    args = [
        "antihydra",
        "--nth",
        "0",
        "--no-value",
        "--format",
        "json",
        "--info",
        "arithmetic.continued-fraction",
        "--safety-horizon",
        "4096",
        "--continued-fraction-max-coefficients",
        "1",
    ]
    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_CF_RECIPROCAL", raising=False)
    expected_status = main(args)
    expected = json.loads(capsys.readouterr().out)
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_CF_RECIPROCAL", "1")
    assert main(args) == expected_status == 3
    actual = json.loads(capsys.readouterr().out)
    assert actual == expected
    assert actual["info"]["arithmetic.continued-fraction"]["status"] == "unknown"
