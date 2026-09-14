"""The physical clock is a view of the CLI's bound execution, not an itinerary."""

from __future__ import annotations

import json
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.arithmetic.functions.finite_function_types import (
    AtomSort,
    FinitePort,
)
from number_compiler.hashlife.execution.tile_kernel import PrimitiveTileKernelAdapter
from number_compiler.hashlife.execution.tile_scheduler import TileApplication
from number_compiler.hashlife.observation.tile_projection import LazyProjection
from number_compiler.sequences.collatz.physical_support import PhysicalSupport
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
                "clock",
                "--no-value",
                "--format",
                "json",
            ]
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)["info"]["clock"]
    _, odd = _reference(seed, ticks)
    assert result["value"] == {
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
        assert (
            result["work_counters"]["tile_projection_physical_support_observations"]
            == 1
        )
        assert "tile_projection_cocycle_observations" not in result["work_counters"]


def test_clock_reuses_same_completed_source_binding(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    term = PoweredCollatzTerm(11, 4)
    projection = term._point_index()._lazy_application
    assert type(projection) is LazyProjection
    application = projection._open()
    result = application.complete()
    assert (result.physical_ticks, result.event_weight) == (4, 2)
    support = result.physical_support
    assert support is not None
    assert tuple(support.tick(index) for index in range(4)) == (
        True,
        False,
        True,
        False,
    )
    original_root = application._root
    monkeypatch.setattr(application.scheduler, "complete", _forbidden)
    clock = term.s_arithmetic_clock()
    assert (clock.events, clock.divisions) == (2, 2)
    assert application._root is original_root
    application.close()
    with pytest.raises(ValueError):
        term.s_arithmetic_clock()


def test_physical_support_rejects_forgery_and_another_scheduler() -> None:
    first = PoweredCollatzTerm(11, 4)
    second = PoweredCollatzTerm(11, 4)
    support = first._point_index().direct_physical_support()
    other = second._point_index().direct_physical_support()
    projection = first._point_index()._lazy_application
    assert type(projection) is LazyProjection
    first_scheduler = projection._open().scheduler
    with pytest.raises(ValueError, match="another scheduler"):
        first_scheduler.results.validate_physical_support(other)
    forged = PhysicalSupport(
        support.owner,
        support.node_id,
        support.ticks,
        support.odd_ticks,
        support.parity,
        support.left,
        support.right,
    )
    with pytest.raises(ValueError, match="another arena"):
        support.owner.validate(forged)
    object.__setattr__(support, "parity", True)
    with pytest.raises(ValueError, match="semantic fields"):
        support.owner.validate(support)


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
                "clock",
                "--max-events",
                "4",
            ]
        )
        == 2
    )
    assert "budget exceeded" in capsys.readouterr().err


def test_cli_physical_output_cannot_rebuild_joint_table(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    original = PrimitiveTileKernelAdapter._tabulated

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

    monkeypatch.setattr(PrimitiveTileKernelAdapter, "_tabulated", reject_joint)
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
    assert metrics["collatz_physical_factored_output_compilations"] > 0
    assert metrics["collatz_physical_joint_output_tables_elided"] > 0
