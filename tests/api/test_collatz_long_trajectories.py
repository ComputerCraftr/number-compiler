"""Long distinct prefixes exercise source construction before cycle compression.

The oracle uses only ordinary exact-integer Collatz steps. Expanded trajectories
are test references, never inputs to production or evidence of cheap discovery.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Never

import pytest

from number_compiler.api.cli import main
from number_compiler.hashlife.execution.tile_causal import CausalTileEngine
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


@dataclass(frozen=True)
class _Trajectory:
    seed: int
    first_one: int
    values: tuple[int, ...]
    odd_counts: tuple[int, ...]

    @property
    def cycle_entry(self) -> int:
        return self.first_one - 2  # First 4, followed by 2, then 1.


@pytest.fixture(
    scope="module",
    params=((931386509544713451, 2283), (63728127, 949)),
    ids=("user-seed-2283-steps", "second-seed-949-steps"),
)
def trajectory(request: pytest.FixtureRequest) -> _Trajectory:
    seed, first_one = request.param
    values = [seed]
    odd_counts = [0]
    for _ in range(10000):
        value = values[-1]
        odd_counts.append(odd_counts[-1] + value % 2)
        values.append(3 * value + 1 if value % 2 else value // 2)
    return _Trajectory(seed, first_one, tuple(values), tuple(odd_counts))


def _forbidden(*_args: object, **_kwargs: object) -> Never:
    raise AssertionError("long Collatz query entered the retired causal executor")


def test_reference_has_a_long_distinct_prefix(trajectory: _Trajectory) -> None:
    entry = trajectory.cycle_entry
    assert entry >= 900
    assert len(set(trajectory.values[:entry])) == entry
    assert not set(trajectory.values[:entry]).intersection((1, 4, 2))
    assert trajectory.values.index(1) == trajectory.first_one
    assert trajectory.values[entry : entry + 6] == (4, 2, 1, 4, 2, 1)


def test_noncycle_block_boundaries_and_clock_share_the_source_image(
    trajectory: _Trajectory,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(CausalTileEngine, "__init__", _forbidden)
    boundaries = (64, 128, 256, 512, 768, 1024, 1536, 2048)
    steps_to_check = {0, 1, trajectory.cycle_entry - 1}
    steps_to_check.update(
        boundary + offset
        for boundary in boundaries
        for offset in (-1, 0, 1)
        if boundary + offset < trajectory.cycle_entry
    )
    for steps in sorted(steps_to_check):
        expected = trajectory.values[steps]
        term = PoweredCollatzTerm(trajectory.seed, steps)
        assert term.materialize(max_bits=expected.bit_length()) == expected, steps
        leaf_work = term._ledger.counters.get("collatz_physical_leaf_steps", 0)
        compositions = term._ledger.counters.get(
            "source_image_chronological_compositions", 0
        )
        clock = term.s_arithmetic_clock()
        odd = trajectory.odd_counts[steps]
        assert (clock.events, clock.divisions) == (odd, steps - odd), steps
        assert term._ledger.counters.get("collatz_physical_leaf_steps", 0) == leaf_work
        assert (
            term._ledger.counters.get("source_image_chronological_compositions", 0)
            == compositions
        )
        assert term._ledger.counters.get("collatz_physical_cycle_compressions", 0) == 0


@pytest.mark.parametrize("offset", (-1, 0, 1, 2, 3, 4, 63, 64, 65))
def test_exact_cycle_entry_and_phase(
    trajectory: _Trajectory,
    offset: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(CausalTileEngine, "__init__", _forbidden)
    steps = trajectory.cycle_entry + offset
    term = PoweredCollatzTerm(trajectory.seed, steps)
    expected = trajectory.values[steps]
    assert term.materialize(max_bits=expected.bit_length()) == expected
    clock = term.s_arithmetic_clock()
    assert (clock.events, clock.divisions) == (
        trajectory.odd_counts[steps],
        steps - trajectory.odd_counts[steps],
    )


@pytest.mark.parametrize("steps", (0, 1, 1000, 2000, 5000, 10000))
def test_long_trajectory_cli_values(
    trajectory: _Trajectory,
    steps: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    monkeypatch.setattr(CausalTileEngine, "__init__", _forbidden)
    assert (
        main(
            [
                "collatz",
                "--seed",
                str(trajectory.seed),
                "--nth",
                str(steps),
                "--max-output-bits",
                str(trajectory.values[steps].bit_length()),
            ]
        )
        == 0
    )
    captured = capsys.readouterr()
    assert captured.out == f"{trajectory.values[steps]}\n"
    assert captured.err == ""
