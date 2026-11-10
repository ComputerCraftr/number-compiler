"""Source-guarded XOR and harmonic projections for the 6305 odd run."""

from __future__ import annotations

from typing import TYPE_CHECKING

import pytest

from devtools.verification.oracles.sequence_arithmetic import collatz_literal
from number_compiler.api import cli
from number_compiler.hashlife.execution.dyadic_return_runs import (
    RunArithmeticWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz import temporal_run_pumping
from number_compiler.sequences.collatz.border_harmonic_ring import (
    ZeroTailFreeBorderRing,
)
from number_compiler.sequences.collatz.joint_harmonic_band import (
    TWO_ODD_HARMONIC_BAND,
    TwoOddHarmonicPoint,
)
from number_compiler.sequences.collatz.joint_temporal_action import (
    CollatzJointTemporalBuilder,
)
from number_compiler.sequences.collatz.tape_width import (
    CollatzWidthSpineAccumulator,
)
from number_compiler.sequences.collatz.temporal_run_quotient import (
    compile_collatz_temporal_run_quotient,
)
from number_compiler.sequences.collatz.temporal_run_state import CollatzRunControl

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.innovation_input_tape import (
        ParityProgramBuilder,
    )
    from number_compiler.sequences.collatz.source_cylinder_cache import (
        CollatzDyadicMacros,
    )


def _track_homogeneous_runs(monkeypatch: pytest.MonkeyPatch) -> list[int]:
    original = temporal_run_pumping.consume_homogeneous_run
    joined_lengths: list[int] = []

    def record_joined_run(
        control: CollatzRunControl,
        *,
        seed: int,
        available: int,
        control_bits: int,
        include_joint_cocycle: bool,
        ledger: ResourceLedger,
        scratch: RunArithmeticWorkspace,
        width_spine: CollatzWidthSpineAccumulator,
        joint_builder: CollatzJointTemporalBuilder,
        parity_builder: ParityProgramBuilder | None,
        macros: CollatzDyadicMacros | None,
    ) -> None:
        joined_lengths.append(available)
        original(
            control,
            seed=seed,
            available=available,
            control_bits=control_bits,
            include_joint_cocycle=include_joint_cocycle,
            ledger=ledger,
            scratch=scratch,
            width_spine=width_spine,
            joint_builder=joint_builder,
            parity_builder=parity_builder,
            macros=macros,
        )

    monkeypatch.setattr(
        temporal_run_pumping, "consume_homogeneous_run", record_joined_run
    )
    return joined_lengths


def test_seed_63_joint_ports_follow_source_guarded_11_blocks() -> None:
    point = TWO_ODD_HARMONIC_BAND.point(63)
    ring = ZeroTailFreeBorderRing.from_source(63)

    assert point.full_block_capacity == 3
    assert point.return_to_three_capacity == 2
    assert point.cyclotomic_period == 3
    assert point.advance(3).phase7 == point.phase7
    assert point.advance(3).v2_center == 0
    assert point.advance(3).border_digit == 8
    assert point.odd_prefix_ports(6)[:4] == (0, 8, 1, 4)
    assert point.base6_five_band_after_odd_steps(2) == 2
    assert ring.pointed_harmonic_band() == point

    with pytest.raises(TypeError, match="source issuer"):
        TwoOddHarmonicPoint(6, 0, 1, 3, 0, 14)


def test_public_run_quotient_consumes_joined_odd_exit_and_forced_even_run(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source = (1 << 70) - 1
    ticks = 143  # 70 normalized odd steps, then the forced 3-step even run.
    joined_lengths = _track_homogeneous_runs(monkeypatch)
    result = compile_collatz_temporal_run_quotient(
        source, ticks, ledger=ResourceLedger()
    )

    assert joined_lengths == [70, 3]
    assert result.endpoint == collatz_literal(source, ticks)


@pytest.mark.usefixtures("isolated_process_cache")
def test_default_cli_reaches_harmonic_join_for_admitted_short_root(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    source = 262143
    ticks = 37
    joined_lengths = _track_homogeneous_runs(monkeypatch)

    assert cli.main(["collatz", "--seed", str(source), "--nth", str(ticks)]) == 0

    output = capsys.readouterr()
    assert not output.err
    assert output.out.strip() == str(collatz_literal(source, ticks))
    assert joined_lengths == [18, 3]
