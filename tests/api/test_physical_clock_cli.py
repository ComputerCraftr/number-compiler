"""The physical clock is a view of the CLI's bound execution, not an itinerary."""

from __future__ import annotations

import json
from fractions import Fraction
from typing import Never, Protocol, runtime_checkable

import pytest

from number_compiler.api.cli import main
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
)
from number_compiler.hashlife.execution.tile_application import TileApplication
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.interfaces.semantic_bits import FactoredFunctionID
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm
from number_compiler.sequences.collatz.power import CollatzEventArena


def _forbidden(*args: object, **kwargs: object) -> Never:
    raise AssertionError("a physical clock must not rediscover an event itinerary")


def _reference(seed: int, ticks: int) -> tuple[int, int]:
    value, odd = seed, 0
    for _ in range(ticks):
        if value & 1:
            odd += 1
            value = 3 * value + 1
        else:
            value //= 2
    return value, odd


@runtime_checkable
class _TabulatedMethod(Protocol):
    def __call__(
        self,
        adapter: PrimitiveTileKernelAdapter,
        ports: tuple[FinitePort, ...],
        output: AtomSort,
        active: tuple[FinitePort, ...],
        table: tuple[int, ...],
    ) -> FactoredFunctionID: ...


@pytest.mark.parametrize(
    "seed,ticks", ((1, 0), (1, 103), (16, 3), (85, 9), (11, 4), (27, 8))
)
def test_physical_clock_cli_uses_bound_interface(
    seed: int,
    ticks: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.sequences.collatz import raw_field

    monkeypatch.setattr(CollatzEventArena, "__init__", _forbidden)
    monkeypatch.setattr(
        raw_field, "accelerated_collatz_sentinel_step_digits", _forbidden
    )
    # The query uses the admitted interface or an already completed root. It
    # must not unconditionally request a full endpoint just to read its clock.
    monkeypatch.setattr(TileApplication, "complete", _forbidden)
    assert (
        main(
            [
                "collatz",
                "--nth",
                str(ticks),
                "--seed",
                str(seed),
                "--info",
                "temporal.clock",
                "--info",
                "metrics",
                "--no-value",
                "--format",
                "json",
            ]
        )
        == 0
    )
    info = json.loads(capsys.readouterr().out)["info"]
    result = info["temporal.clock"]
    _, odd = _reference(seed, ticks)
    growth = result["value"]["homogeneous_growth"]
    assert (growth["growths"], growth["halvings"], growth["radix"]) == (
        odd,
        ticks - odd,
        10,
    )
    order = growth["homogeneous_radix_order"]
    gain = Fraction(3**odd, 2 ** (ticks - odd))
    assert Fraction(10) ** order <= gain < Fraction(10) ** (order + 1)
    radial = result["value"]["radial_sturmian"]
    assert (radial["growths"], radial["halvings"]) == (odd, ticks - odd)
    assert radial["prefix_value"] == int(bin(3**odd)[2:][:8].ljust(8, "0"), 2)
    assert {
        k: v
        for k, v in result["value"].items()
        if k not in {"homogeneous_growth", "radial_sturmian"}
    } == {
        "events": odd,
        "divisions": ticks - odd,
        "physical_ticks": ticks,
        "real_prime_exponents": [odd - ticks, odd],
        "two_adic_exponent": ticks - odd,
        "three_adic_exponent": -odd,
    }
    assert result["requested_ticks"] == ticks
    assert "discovered_events" not in result
    if ticks:
        execution = info["metrics"]["execution_metrics"]
        assert execution["construction"]["source_image_publications"] > 0
        family_work = next(
            row
            for row in execution["family_work"]
            if row["counter_prefix"] == "collatz_physical"
        )
        assert family_work["action_publications"] > 0


def test_clock_composition_rebases_the_source() -> None:
    first = PoweredCollatzTerm(11, 1).s_arithmetic_clock()
    # The second physical action is bound to 34, not to the original 11.
    second = PoweredCollatzTerm(34, 1).s_arithmetic_clock()
    together = PoweredCollatzTerm(11, 2).s_arithmetic_clock()
    assert (first.events, second.events, together.events) == (1, 0, 1)
    assert together.divisions == first.divisions + second.divisions == 1


def test_clock_budget_is_checked_before_execution(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(PoweredCollatzTerm, "s_arithmetic_clock", _forbidden)
    assert (
        main(
            [
                "collatz",
                "--nth",
                "5",
                "--seed",
                "11",
                "--info",
                "temporal.clock",
                "--temporal-clock-max-events",
                "4",
            ]
        )
        == 2
    )
    assert "budget exceeded" in capsys.readouterr().err


def test_cli_physical_output_cannot_rebuild_joint_table(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    original_value: object = PrimitiveTileKernelAdapter.tabulated
    assert isinstance(original_value, _TabulatedMethod)
    original = original_value

    def reject_joint(
        self: PrimitiveTileKernelAdapter,
        ports: tuple[FinitePort, ...],
        output: AtomSort,
        active: tuple[FinitePort, ...],
        table: tuple[int, ...],
    ) -> FactoredFunctionID:
        if len(active) == 2:
            raise AssertionError("CLI rebuilt the joint physical output table")
        return original(self, ports, output, active, table)

    monkeypatch.setattr(PrimitiveTileKernelAdapter, "tabulated", reject_joint)
    assert (
        main(
            [
                "collatz",
                "--nth",
                "16",
                "--seed",
                "27",
                "--format",
                "json",
                "--info",
                "metrics",
            ]
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)
    assert int(result["value"]) == _reference(27, 16)[0]
    metrics = result["info"]["metrics"]["execution_metrics"]
    assert metrics["schema_version"] == 8
    assert metrics["action"]["publications"] > 0
    assert metrics["construction"]["source_image_publications"] > 0


def test_digits_and_metrics_do_not_request_homogeneous_readout(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.api import cylinder_observation

    monkeypatch.setattr(cylinder_observation, "homogeneous_growth_packet", _forbidden)
    assert (
        main(
            [
                "collatz",
                "--nth",
                "16",
                "--seed",
                "27",
                "--info",
                "metrics",
                "--format",
                "json",
            ]
        )
        == 0
    )
    row = json.loads(capsys.readouterr().out)
    assert int(row["value"]) == _reference(27, 16)[0]
    assert all(
        value is None
        for value in row["info"]["metrics"]["execution_metrics"][
            "growth_readout"
        ].values()
    )


@pytest.mark.parametrize("seed,ticks", ((11, 1), (27, 8), (1, 103), (16, 3)))
def test_width_tape_clock_reuses_the_admitted_run(
    seed: int, ticks: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from number_compiler.api.cylinder_observation import observe_physical_clock
    from number_compiler.sequences.collatz import temporal_run_quotient

    term = PoweredCollatzTerm(seed, ticks)
    term.s_arithmetic_clock()
    monkeypatch.setattr(
        temporal_run_quotient, "compile_collatz_temporal_run_quotient", _forbidden
    )
    monkeypatch.setattr(PoweredCollatzTerm, "digits", _forbidden)
    widths = [seed.bit_length()]
    current = seed
    for _ in range(ticks):
        current = 3 * current + 1 if current & 1 else current // 2
        widths.append(current.bit_length())
    before = term.resource_ledger.counters.get(
        "collatz_physical_tape_width_compositions", 0
    )
    packet = observe_physical_clock(
        seed,
        ticks,
        max_ticks=1000,
        max_digits=1000,
        _term=term,
        _include_metrics=False,
    )
    summary = packet["width_tape"]
    assert summary is not None
    assert summary["radix"] == 2
    assert summary["source_width"] == widths[0]
    assert summary["target_width"] == widths[-1]
    assert summary["blank"] == {
        "delta": widths[-1] - widths[0],
        "minimum": min(widths) - widths[0],
        "maximum": max(widths) - widths[0],
    }
    assert (
        term.resource_ledger.counters.get("collatz_physical_tape_width_compositions", 0)
        == before
    )
    assert "work_counters" not in packet


@pytest.mark.parametrize("render_value", (False, True))
def test_cli_prepares_demanded_d8_width_before_value_rendering(
    render_value: bool, capsys: pytest.CaptureFixture[str]
) -> None:
    arguments = [
        "collatz",
        "--seed",
        "27",
        "--nth",
        "64",
        "--info",
        "temporal.clock",
        "--format",
        "json",
    ]
    if not render_value:
        arguments.append("--no-value")
    assert main(arguments) == 0
    packet = json.loads(capsys.readouterr().out)
    width = packet["info"]["temporal.clock"]["width_tape"]
    assert width is not None
    endpoint, _ = _reference(27, 64)
    assert width["target_width"] == endpoint.bit_length()
    assert width["physical_ticks"] == 64


def test_clock_width_payload_is_independent_of_work_counters(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.api.cylinder_observation import observe_physical_clock

    term = PoweredCollatzTerm(27, 64)
    term.s_arithmetic_clock()
    before = observe_physical_clock(27, 64, max_ticks=1000, max_digits=1000, _term=term)
    assert before["width_tape"] is not None
    for counter in tuple(term.resource_ledger.counters):
        if "width" in counter or "tape" in counter or "growth" in counter:
            term.resource_ledger.counters[counter] = 10**12
    monkeypatch.setattr(PoweredCollatzTerm, "_source_numerator", _forbidden)
    monkeypatch.setattr(PoweredCollatzTerm, "digits", _forbidden)
    after = observe_physical_clock(27, 64, max_ticks=1000, max_digits=1000, _term=term)
    assert after["width_tape"] == before["width_tape"]
    assert after["value"] == before["value"]
