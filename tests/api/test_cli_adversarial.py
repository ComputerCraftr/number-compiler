"""CLI admission must finish before sequence construction or output observation."""

from __future__ import annotations

import json
import os
import subprocess
import sys
from collections.abc import Callable
from dataclasses import asdict
from typing import TYPE_CHECKING, Never, TypedDict, cast

import pytest

import number_compiler.api.cli as cli
from devtools.paths import repository_root
from number_compiler.api.number_api import (
    FormulaTermPayload,
    NumberCompiler,
    PoweredCollatzTermPayload,
    PoweredReverseAddTermPayload,
    ScalarTermPayload,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.formula.formula import FormulaArena, root_from_values
from number_compiler.arithmetic.formula.types import RadixSpec

if TYPE_CHECKING:
    from number_compiler.api.number_api import ProjectedNumberTerm
    from number_compiler.sequences.collatz.block_power import (
        CollatzPhysicalBlockMetrics,
    )
    from number_compiler.sequences.reverse_add.power import ReverseAddPowerMetrics


def forbid_compiler(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("invalid CLI request constructed a compiler")

    monkeypatch.setattr(cli, "NumberCompiler", forbidden)


@pytest.mark.parametrize(
    "arguments, message",
    [
        (["prime", "-1"], "index"),
        (["mersenne", "0"], "index"),
        (["reverse-add", "3"], "requires seed"),
        (["collatz", "3"], "requires seed"),
        (["reverse-add", "3", "--seed", "-1"], "--seed"),
        (["collatz", "3", "--seed", "0"], "--seed"),
        (["collatz", "3", "--seed", "-1"], "--seed"),
        (["196", "3", "--base", "1"], "--base"),
        (["196", "3", "--base", "0"], "--base"),
        (["collatz", "3", "--seed", "27", "--radix", "4"], "--radix"),
        (["collatz", "3", "--seed", "27", "--radix", "-6"], "--radix"),
        (["prime", "1000000000000000", "--output-base", "37"], "--output-base"),
        (["prime", "1000000000000000", "--output-base", "1"], "--output-base"),
        (["prime", "1000000000000000", "--max-output-bits", "0"], "--max-output-bits"),
        (
            ["fermat", "20", "--format", "symbolic", "--max-output-bits", "-1"],
            "--max-output-bits",
        ),
        (["prime", "1", "--start", "-1"], "--start"),
        (["prime", "1000000000000000", "--seed", "1"], "does not apply"),
        (["collatz", "1", "--seed", "1", "--base", "10"], "does not apply"),
        (["196", "1", "--radix", "2"], "does not apply"),
        (["mersenne", "1", "--start", "2"], "does not apply"),
    ],
)
def test_invalid_domains_reject_before_compilation(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    arguments: list[str],
    message: str,
) -> None:
    forbid_compiler(monkeypatch)
    assert cli.main(["nth", *arguments]) == 2
    output = capsys.readouterr()
    assert not output.out
    assert message in output.err
    assert "Traceback" not in output.err


@pytest.mark.parametrize(
    "arguments",
    [
        ["fermat", "100000000000000000000000000", "--max-output-bits", "16"],
        ["mersenne", "100000000000000000000000000", "--max-output-bits", "16"],
        ["prime", "100000000000000000000000000", "--max-output-bits", "16"],
        ["prime", "0", "--start", "65536", "--max-output-bits", "16"],
        ["196", "100000000000000000000000000", "--max-output-bits", "7"],
        [
            "collatz",
            "100000000000000000000000000",
            "--seed",
            "27",
            "--max-output-bits",
            "16",
        ],
    ],
)
def test_provably_over_limit_output_rejects_before_compilation(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    arguments: list[str],
) -> None:
    forbid_compiler(monkeypatch)
    assert cli.main(["nth", *arguments]) == 2
    assert "output exceeds --max-output-bits" in capsys.readouterr().err


@pytest.mark.parametrize(
    "arguments",
    [
        ["nth", "unknown", "0"],
        ["unknown"],
        ["nth", "prime", "1.5"],
        ["nth", "prime", "True"],
        ["nth", "prime", "1_0"],
        ["nth", "prime", "１"],
        ["nth", "prime", " 1"],
        ["nth", "196", "0", "--seed", "1_96"],
        ["nth", "prime", "0", "--max-cache-entries", "-1"],
        ["nth", "prime", "0", "--max-output-bits", "2.5"],
        ["nth", "196", "0", "--seed", "5", "--seed=6"],
        ["nth", "196", "0", "--format", "json", "--format", "value"],
        ["nth", "196", "0", "--base", "10", "--base", "2"],
    ],
)
def test_malformed_unknown_or_conflicting_arguments_are_parser_errors(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    arguments: list[str],
) -> None:
    forbid_compiler(monkeypatch)
    with pytest.raises(SystemExit) as error:
        cli.main(arguments)
    assert error.value.code == 2
    assert "error:" in capsys.readouterr().err


@pytest.mark.parametrize(
    "arguments",
    [True, 1.5, "nth prime 0", ["nth", "prime", True], ["nth", "prime", 1.5]],
)
def test_callable_main_rejects_non_string_arguments(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    arguments: bool | float | list[bool | str] | list[float | str] | str,
) -> None:
    forbid_compiler(monkeypatch)
    assert cli.main(cast("list[str]", arguments)) == 2
    assert "list of strings" in capsys.readouterr().err


@pytest.mark.parametrize("alias", [True, 1.0, "1"])
def test_public_payload_limits_reject_integer_aliases(
    alias: bool | float | str,
) -> None:
    with pytest.raises(TypeError, match="output bit cap"):
        ScalarTermPayload(1).materialize(max_bits=cast("int", alias))

    arena = FormulaArena()
    payload = FormulaTermPayload(root_from_values((1,), arena, RadixSpec(2)), 2)
    with pytest.raises(TypeError, match="output bit cap"):
        payload.materialize(max_bits=cast("int", alias))


@pytest.mark.parametrize("alias", [True, 1.0, "1"])
def test_public_payload_constructors_reject_integer_aliases(
    alias: bool | float | str,
) -> None:
    arena = FormulaArena()
    root = root_from_values((1,), arena, RadixSpec(2))
    with pytest.raises((TypeError, ValueError)):
        FormulaTermPayload(root, cast("int", alias))
    with pytest.raises(TypeError, match="scalar term"):
        ScalarTermPayload(cast("int", alias))


@pytest.mark.parametrize("alias", [True, 2.0, "2"])
def test_powered_collatz_payload_rejects_radix_aliases(
    alias: bool | float | str,
) -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm

    with pytest.raises(TypeError, match="payload radix"):
        PoweredCollatzTermPayload(PoweredCollatzTerm(1, 0), cast("int", alias))


@pytest.mark.parametrize("alias", [0, 1, 0.0, 1.0, "true"])
def test_public_digit_iterators_require_actual_boolean_orientation(
    alias: float | int | str,
) -> None:
    arena = FormulaArena()
    with pytest.raises(TypeError, match="reverse must be a Boolean"):
        FormulaTermPayload(
            root_from_values((1,), arena, RadixSpec(2)),
            2,
        ).iter_digits(reverse=cast("bool", alias))


@pytest.mark.parametrize(
    "kwargs",
    [
        {"output_base": 1, "max_bits": 16},
        {"output_base": 37, "max_bits": 16},
        {"output_base": True, "max_bits": 16},
        {"output_base": 10.0, "max_bits": 16},
        {"output_base": 10, "max_bits": 0},
        {"output_base": 10, "max_bits": -1},
        {"output_base": 10, "max_bits": True},
        {"output_base": 10, "max_bits": 16.5},
    ],
)
def test_renderer_rejects_invalid_limits_before_touching_term(
    kwargs: dict[str, object],
) -> None:
    class PoisonTerm:
        def __getattribute__(self, name: object) -> Never:
            raise AssertionError("renderer observed a term before validating arguments")

    with pytest.raises((TypeError, ValueError)):
        cli._render_value(
            cast("ProjectedNumberTerm", PoisonTerm()), **cast("RenderOptions", kwargs)
        )


@pytest.mark.parametrize(
    "value, base", [(-1, 2), (-1, 10), (True, 2), (1.5, 2), (1, True), (1, 2.5)]
)
def test_scalar_renderer_rejects_negative_or_coerced_values(
    value: bool | float | int, base: bool | float | int
) -> None:
    with pytest.raises((TypeError, ValueError)):
        cli._radix_string(cast("int", value), cast("int", base))


@pytest.mark.parametrize(
    "digits, base", [((-1,), 10), ((10,), 10), ((True,), 2), ((1.5,), 2), ((0,), 2.5)]
)
def test_digit_renderer_checks_the_actual_digit_alphabet(
    digits: tuple[bool] | tuple[float] | tuple[int], base: float | int
) -> None:
    with pytest.raises((TypeError, ValueError)):
        cli._radix_string_from_lsd(cast("tuple[int, ...]", digits), cast("int", base))


@pytest.mark.parametrize(
    "error",
    [
        BlockContextBudgetExceeded("cache budget exceeded"),
        OverflowError("output is too large"),
    ],
)
def test_expected_resource_failures_have_usable_cli_errors(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    error: Exception,
) -> None:
    class LimitedCompiler:
        def project_nth(self, *args: object, **kwargs: object) -> Never:
            raise error

    monkeypatch.setattr(cli, "NumberCompiler", LimitedCompiler)
    assert cli.main(["nth", "prime", "0"]) == 2
    output = capsys.readouterr()
    assert not output.out
    assert str(error) in output.err
    assert "Traceback" not in output.err


def test_valid_zero_indices_alias_overrides_and_small_caps_are_preserved(
    capsys: pytest.CaptureFixture[str],
) -> None:
    for arguments, expected in [
        (["reverse-add", "0", "--seed", "0", "--max-output-bits", "4"], "0"),
        (["196", "0", "--seed", "5", "--base", "2"], "5"),
        (["prime", "0", "--start", "0", "--max-output-bits", "2"], "2"),
        (["fermat", "0", "--max-output-bits", "2"], "3"),
        (["mersenne", "1", "--max-output-bits", "1"], "1"),
        (["196", "0", "--seed", "5", "--seed", "5"], "5"),
    ]:
        assert cli.main(["nth", *arguments]) == 0
        assert capsys.readouterr().out.strip() == expected
    assert (
        cli.main(
            [
                "nth",
                "fermat",
                "1000000000000",
                "--format",
                "symbolic",
                "--max-output-bits",
                "1",
            ]
        )
        == 0
    )
    assert capsys.readouterr().out.strip() == "2^(2^1000000000000)+1"
    assert cli.main(["nth", "prime", "0", "--format", "json"]) == 0
    assert json.loads(capsys.readouterr().out)["value"] == "2"


def test_real_cli_invalid_option_exits_without_traceback() -> None:
    root = repository_root()
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "number_compiler",
            "nth",
            "prime",
            "999999999",
            "--output-base",
            "37",
        ],
        cwd=root,
        env=dict(os.environ),
        capture_output=True,
        text=True,
        timeout=10,
    )
    assert result.returncode == 2
    assert not result.stdout
    assert "--output-base" in result.stderr
    assert "Traceback" not in result.stderr


@pytest.mark.parametrize("family, extra", [("196", []), ("collatz", ["--seed", "27"])])
@pytest.mark.parametrize("output_format", ["value", "json"])
def test_emitted_execution_metrics_match_actual_rendered_term_ledger(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    family: str,
    extra: list[str],
    output_format: str,
) -> None:
    terms: list[ProjectedNumberTerm] = []
    snapshots = []
    payload_type = (
        PoweredReverseAddTermPayload if family == "196" else PoweredCollatzTermPayload
    )
    original_metrics = cast(
        "Callable[[PoweredReverseAddTermPayload | PoweredCollatzTermPayload], ReverseAddPowerMetrics | CollatzPhysicalBlockMetrics]",
        payload_type.power_metrics,
    )

    def capture_metrics(
        payload: PoweredReverseAddTermPayload | PoweredCollatzTermPayload,
    ) -> ReverseAddPowerMetrics | CollatzPhysicalBlockMetrics:
        report = original_metrics(payload)
        snapshots.append(json.loads(json.dumps(asdict(report))))
        return report

    class CapturingCompiler(NumberCompiler):
        def project_nth(
            self,
            family: str,
            index: int,
            *,
            seed: int | None = None,
            base: int = 10,
            radix: int = 2,
            start: int = 2,
        ) -> ProjectedNumberTerm:
            term = super().project_nth(
                family, index, seed=seed, base=base, radix=radix, start=start
            )
            terms.append(term)
            return term

    monkeypatch.setattr(cli, "NumberCompiler", CapturingCompiler)
    monkeypatch.setattr(payload_type, "power_metrics", capture_metrics)
    assert (
        cli.main(["nth", family, "2", *extra, "--format", output_format, "--metrics"])
        == 0
    )
    captured = capsys.readouterr()
    metrics = json.loads(captured.out if output_format == "json" else captured.err)
    descriptors = metrics["projection_metrics"] if output_format == "json" else metrics
    assert descriptors["metrics_scope"] == "construction_and_projection_descriptors"
    assert descriptors["projection_work"] == 0
    assert metrics["execution_metrics_scope"] == "current_powered_term_ledger_snapshot"
    execution = metrics["execution_metrics"]
    term = terms[0]
    assert len(snapshots) == 1
    assert execution == snapshots[0]
    assert isinstance(
        term.payload, (PoweredReverseAddTermPayload, PoweredCollatzTermPayload)
    )
    later = json.loads(json.dumps(asdict(original_metrics(term.payload))))
    # Weak shared source tiles can disappear when unrelated owners are
    # collected between reports. The emitted population must match its actual
    # captured snapshot; all remaining index-owned metrics remain unchanged.
    shared_population = "canonical_tile_arena_nodes_global"
    assert {
        key: value for key, value in execution.items() if key != shared_population
    } == {key: value for key, value in later.items() if key != shared_population}
    assert execution["metrics_schema_version"] == 6
    assert execution["resource_ledger_entries"] == term.payload.term._ledger.entries > 0
    assert execution["resource_observed_nodes"] == term.payload.term._ledger.nodes > 0
    assert (
        sum(row["observed_entries"] for row in execution["resource_inventory"])
        == execution["resource_ledger_entries"]
    )
    assert execution["resource_work_counters"]


@pytest.mark.parametrize("family, extra", [("196", []), ("collatz", ["--seed", "27"])])
def test_symbolic_metrics_do_not_execute_points_or_width(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
    family: str,
    extra: list[str],
) -> None:
    from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    terms: list[ProjectedNumberTerm] = []

    class CapturingCompiler(NumberCompiler):
        def project_nth(
            self,
            family: str,
            index: int,
            *,
            seed: int | None = None,
            base: int = 10,
            radix: int = 2,
            start: int = 2,
        ) -> ProjectedNumberTerm:
            term = super().project_nth(
                family, index, seed=seed, base=base, radix=radix, start=start
            )
            terms.append(term)
            return term

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("metrics forced powered endpoint execution")

    monkeypatch.setattr(cli, "NumberCompiler", CapturingCompiler)
    for cls in (PoweredCollatzTerm, ReverseAddPoweredTerm):
        monkeypatch.setattr(cls, "_point_index", forbidden)
        monkeypatch.setattr(cls, "digit", forbidden)
    assert (
        cli.main(["nth", family, "256", *extra, "--format", "symbolic", "--metrics"])
        == 0
    )
    output = capsys.readouterr()
    execution = json.loads(output.err)["execution_metrics"]
    assert isinstance(
        terms[0].payload, (PoweredReverseAddTermPayload, PoweredCollatzTermPayload)
    )
    assert terms[0].payload.term._index is None
    assert (
        execution["resource_ledger_entries"]
        == terms[0].payload.term._ledger.entries
        > 0
    )
    assert execution["point_queries"] == 0


@pytest.mark.parametrize(
    "family,index", [("prime", "0"), ("fermat", "0"), ("mersenne", "1")]
)
def test_families_without_runtime_ledger_report_unavailable_not_zero(
    capsys: pytest.CaptureFixture[str], family: str, index: str
) -> None:
    assert cli.main(["nth", family, index, "--format", "json"]) == 0
    metrics = json.loads(capsys.readouterr().out)
    assert metrics["execution_metrics"] is None
    assert metrics["execution_metrics_scope"] == "unavailable_for_this_family"
    assert (
        metrics["projection_metrics"]["metrics_scope"]
        == "construction_and_projection_descriptors"
    )


class RenderOptions(TypedDict):
    output_base: int
    max_bits: int
