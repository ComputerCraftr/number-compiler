"""Source-bound Mahler CLI views and independent decimal observations."""

from __future__ import annotations

import json

import pytest

from number_compiler.api.cli import main
from number_compiler.api.number_api import NumberCompiler
from number_compiler.resources.process_cache import (
    ProcessCache,
    temporary_process_cache,
)
from number_compiler.sequences.antihydra.runtime import ArithmeticResult
from tests.support.mahler_harmonic_reference import mapping

_BASE = ["antihydra", "--no-value", "--format", "json"]
_SAFETY = ["--info", "safety.ledger", "--safety-ledger-detail", "finite-safety"]
_GRAPH = ["--info", "temporal.macro", "--temporal-macro-kind", "graph-action"]
_CF = ["--info", "arithmetic.continued-fraction"]


@pytest.mark.parametrize("reverse", [False, True])
def test_combined_pointed_views_share_one_term(
    reverse: bool,
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    sources: list[ArithmeticResult] = []
    original = ArithmeticResult.require_source

    def checked(result: ArithmeticResult) -> None:
        sources.append(result)
        original(result)

    monkeypatch.setattr(ArithmeticResult, "require_source", checked)
    views = [*_GRAPH, *_SAFETY] if reverse else [*_SAFETY, *_GRAPH]
    assert (
        main(
            [
                *_BASE,
                "--nth",
                "254",
                *views,
                "--fractional-tail",
                "1/57",
                "--safety-horizon",
                "4",
                "--temporal-macro-copies",
                "2",
            ]
        )
        == 0
    )
    packet: object = json.loads(capsys.readouterr().out)
    info = mapping(mapping(packet)["info"])
    graph_view = mapping(mapping(info["temporal.macro"])["views"])
    graph = mapping(mapping(graph_view["graph-action"])["value"])
    safety_view = mapping(mapping(info["safety.ledger"])["views"])
    safety = mapping(mapping(safety_view["finite-safety"])["value"])
    assert graph["physical_ticks"] == safety["completed_ticks"] == 4
    assert graph["final_fraction"] == safety["fractional_endpoint"] == "27/304"
    assert graph["endpoint"] == safety["integer_endpoint"]
    assert graph["endpoint"] == 21242133332610029783425146870149471736241053456
    assert len(sources) >= 2
    assert all(result is sources[0] for result in sources)


@pytest.mark.parametrize(
    ("fraction", "horizon", "first"),
    [
        ("1/3", "8", 2),
        ("1/2", "0", 0),
        ("1/3", "0", None),
    ],
)
def test_finite_guard_and_ledger_stay_distinct(
    fraction: str,
    horizon: str,
    first: int | None,
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        main(
            [
                *_BASE,
                "--nth",
                "0",
                *_SAFETY,
                "--safety-ledger-detail",
                "finite-guard",
                "--safety-horizon",
                horizon,
                "--fractional-tail",
                fraction,
            ]
        )
        == 0
    )
    packet: object = json.loads(capsys.readouterr().out)
    ledger = mapping(mapping(mapping(packet)["info"])["safety.ledger"])
    assert mapping(ledger["value"])["first_failure_index"] is None
    views = mapping(ledger["views"])
    assert "finite-guard" in views
    safety = mapping(mapping(views["finite-safety"])["value"])
    assert safety["first_unsafe_tick"] == first
    assert safety["disposition"] == ("safe-prefix" if first is None else "unsafe")


def test_independent_band_never_projects_the_antihydra_term(
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("an independent CF source projected the Antihydra term")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    assert (
        main(
            [
                *_BASE,
                "--nth",
                "4000",
                *_CF,
                "--continued-fraction-band",
                "1530,33,1,6",
            ]
        )
        == 0
    )
    response: object = json.loads(capsys.readouterr().out)
    packet = mapping(
        mapping(mapping(response)["info"])["arithmetic.continued-fraction"]
    )
    assert packet["lifted_source"] == 106
    assert packet["matrix"] == [[26041, 6293], [3596, 869]]
    assert packet["clock_unit"] == "power-of-five-exponent"


@pytest.mark.parametrize(
    ("horizon", "status", "exit_code"),
    [("0", "available", 0), ("100", "unknown", 3)],
)
def test_independent_cylinder_skips_term_projection(
    horizon: str,
    status: str,
    exit_code: int,
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("a CF cylinder projected the Antihydra term")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    assert (
        main(
            [
                *_BASE,
                "--nth",
                "4000",
                *_CF,
                "--safety-horizon",
                horizon,
                "--continued-fraction-max-coefficients",
                "1",
            ]
        )
        == exit_code
    )
    response: object = json.loads(capsys.readouterr().out)
    packet = mapping(
        mapping(mapping(response)["info"])["arithmetic.continued-fraction"]
    )
    assert packet["status"] == status
    assert packet["coefficient_count"] == 1
    assert packet["source_law"] == "decimal-powers-of-five"
    if status == "available":
        assert packet["matrix"] == [[6, 1], [1, 0]]
        assert packet["fraction_lower"] == {"numerator": 1, "denominator": 7}
        assert packet["fraction_upper"] == {"numerator": 1, "denominator": 6}
        assert packet["clock_unit"] == "physical-recurrence-ticks"


@pytest.mark.parametrize(
    "flags",
    [
        [*_SAFETY, "--fractional-tail", "1/3"],
        [*_SAFETY, "--fractional-tail", "1/0", "--safety-horizon", "4"],
        [*_GRAPH, "--fractional-tail", "1/57", "--temporal-macro-copies", "0"],
        _CF,
        [*_CF, "--safety-horizon", "4097"],
        [*_CF, "--safety-horizon", "0", "--continued-fraction-max-coefficients", "0"],
        [*_CF, "--continued-fraction-band", "1530,33,1"],
        [*_CF, "--continued-fraction-band", "1530,33,1,6", "--safety-horizon", "5"],
        [
            *_CF,
            "--continued-fraction-band",
            "1530,33,1,6",
            "--continued-fraction-max-coefficients",
            "2",
        ],
        ["--info", "safety.ledger", "--fractional-tail", "1/3"],
    ],
)
def test_bad_observation_inputs_are_checked_before_projection(
    flags: list[str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("malformed Mahler request reached term projection")

    monkeypatch.setattr(NumberCompiler, "project", forbidden)
    outcome: object
    try:
        outcome = main([*_BASE, "--nth", "254", *flags])
    except SystemExit as error:
        outcome = error.code
    assert outcome == 2


def test_combined_band_charges_receiving_ledger_and_releases_on_exit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.cli_requests import parse_request
    from number_compiler.api.number_api import AntihydraTermPayload
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.antihydra import mahler_continued_fraction

    request = parse_request(
        [
            *_BASE,
            "--nth",
            "254",
            *_CF,
            *_SAFETY,
            "--continued-fraction-band",
            "1530,33,1,6",
            "--safety-horizon",
            "4",
            "--fractional-tail",
            "1/57",
        ]
    )
    assert request is not None
    ctx = QueryContext(request, NumberCompiler())
    selected = ctx.term.payload
    assert isinstance(selected, AntihydraTermPayload)
    result = selected.term.result()
    original_nodes = result.ledger.nodes
    with pytest.raises(KeyboardInterrupt), ctx:
        band = mahler_continued_fraction.continued_fraction_band

        def checked(
            exponent: int,
            cut: int,
            width: int,
            rows: int,
            *,
            ledger: ResourceLedger,
            shared_cache: bool = True,
        ) -> dict[str, object]:
            assert ledger is result.ledger
            return band(
                exponent,
                cut,
                width,
                rows,
                ledger=ledger,
                shared_cache=shared_cache,
            )

        monkeypatch.setattr(
            mahler_continued_fraction, "continued_fraction_band", checked
        )
        packets = ctx.information()
        assert packets["arithmetic.continued-fraction"]["status"] == "available"
        assert result.ledger.nodes > original_nodes
        raise KeyboardInterrupt
    assert result.ledger.nodes == original_nodes


def test_cli_reuses_an_issued_diagonal_band_before_lifting(
    capsys: pytest.CaptureFixture[str], monkeypatch: pytest.MonkeyPatch
) -> None:
    import number_compiler.sequences.antihydra.mahler_continued_fraction as cf

    argv = [*_BASE, "--nth", "0", *_CF, "--continued-fraction-band", "1530,32,16,65"]
    shifted = [*argv[:-1], "1531,33,16,64"]
    assert main(shifted, shared_cache=False) == 0
    expected_shift = json.loads(capsys.readouterr().out)
    cache = ProcessCache()

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("published CLI band reconstructed its physical source")

    with temporary_process_cache(cache):
        assert main(argv) == 0
        original = json.loads(capsys.readouterr().out)
        monkeypatch.setattr(cf, "pow", forbidden, raising=False)
        monkeypatch.setattr(cf, "compile_dyadic_ordered_band", forbidden)
        assert main(argv) == 0
        assert json.loads(capsys.readouterr().out) == original
        assert main(shifted) == 0
        assert json.loads(capsys.readouterr().out) == expected_shift
    cache.reset()


@pytest.mark.parametrize(("exponent", "cut", "lift"), [(16, 4, 370), (3000, 64, 1099)])
def test_eight_row_terminal_uses_admitted_physical_lift(
    exponent: int,
    cut: int,
    lift: int,
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields import dyadic_eight_rows, ordered_matrix

    original = dyadic_eight_rows.eight_row_interval
    calls: list[int] = []

    def terminal(q: int) -> ordered_matrix.Matrix2:
        calls.append(q)
        return original(q)

    def forbidden(*_args: object) -> None:
        raise AssertionError("generic leaf fold on admitted eight-row terminal")

    monkeypatch.setattr(dyadic_eight_rows, "eight_row_interval", terminal)
    monkeypatch.setattr(ordered_matrix, "fold_dyadic_leaf", forbidden)
    band = f"{exponent},{cut},1,8"
    assert main([*_BASE, "--nth", "0", *_CF, "--continued-fraction-band", band]) == 0
    packet = mapping(mapping(json.loads(capsys.readouterr().out))["info"])
    action = mapping(packet["arithmetic.continued-fraction"])
    assert calls == [lift]
    a, b, c, d = 1, 0, 0, 1
    for offset in range(8):
        coefficient = (5 ** (exponent + offset) // 10 ** (cut + offset - 1)) % 10 + 1
        a, b, c, d = a * coefficient + b, a, c * coefficient + d, c
    assert action["matrix"] == [[a, b], [c, d]]
