"""NC19 shared border quotient and source-authenticated segmented halo tests."""

from __future__ import annotations

import json
from collections.abc import Callable
from random import Random
from typing import Never

import pytest

from number_compiler.api import cli
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.temporal_defect_period import (
    source_bound_defect_period_packet,
)
from number_compiler.sequences.double_reverse.temporal_defect_quotient import (
    FourSymbolDefect,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    PHYSICAL_GROWTH_CYCLES,
    DoubleReverseTemporalHashlife,
    edge_phase_of_integer,
    growth_ports,
)
from number_compiler.sequences.double_reverse.temporal_hashlife_pointed import (
    CertifiedDefectTape,
)
from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
    certified_width_moments,
)


def _step(value: int) -> int:
    return 2 * int(str(value)[::-1])


def test_single_border_growth_quotient_is_closed_on_random_admitted_words() -> None:
    assert len(set(PHYSICAL_GROWTH_CYCLES)) == 4
    assert all(sum(word) == 2 for word in PHYSICAL_GROWTH_CYCLES)
    rng = Random(0x19A7)
    prefixes = (("17",), ("17",), ("48", "49"), ("48", "49"))
    suffixes = (("68", "88"), ("42",), ("42",), ("68", "88"))
    for phase in range(4):
        word = PHYSICAL_GROWTH_CYCLES[phase]
        for j in range(1, 120):
            inner = "".join(str(rng.randrange(10)) for _ in range(j % 13))
            value = int(
                rng.choice(prefixes[phase]) + inner + rng.choice(suffixes[phase])
            )
            assert edge_phase_of_integer(value) == phase
            for expected_growth in word:
                successor = _step(value)
                assert len(str(successor)) - len(str(value)) == expected_growth
                value = successor
            assert len(str(value)) == (j % 13 + 4) + 2
            assert certified_width_moments(phase, 4).U == 2
            assert edge_phase_of_integer(value) == phase
        left_growth, right_growth = growth_ports(phase, 2)
        assert left_growth + right_growth == 2


def test_both_cli_observers_reuse_one_authenticated_defect_cone(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    import number_compiler.sequences.double_reverse.temporal_defect_period as period_module

    def prohibited_second_scan(*_args: object, **_kwargs: object) -> Never:
        raise AssertionError("second source-cone defect compilation was performed")

    monkeypatch.setattr(
        period_module, "defect_clock_cli_packet", prohibited_second_scan
    )
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "168",
                "--nth",
                "256",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.defect-clock",
                "--info",
                "temporal.seed-morphism",
                "--temporal-period-samples",
                "24",
                "--temporal-defect-digits",
                "18",
            ]
        )
        == 0
    )
    payload = json.loads(capsys.readouterr().out)["info"]
    direct = payload["temporal.defect-clock"]
    seed = payload["temporal.seed-morphism"]
    assert direct["status"] == "available"
    assert seed["period_observations"]["full_endpoint_suffix_verified"] is True
    assert direct["rows"] == seed["period_observations"]["rows"]
    assert (
        direct["composed_signed_action"]
        == seed["period_observations"]["composed_signed_action"]
    )
    assert direct["source_halo_segments"] == 1


def test_streamed_defect_tape_matches_materialized_actions_without_history() -> None:
    with DoubleReverseTerm(168, 128, max_state_bits=16384) as term:
        _, source = term.prepare_bank_source(max_prefix=16)
        digits = 11
        samples = 7
        stride = 1
        start_f = source.f_steps - 2 - 2 * stride * (samples - 1)
        materialized = source.engine.pointed_combined_defect_tape(
            source.root, start_f, source.phase, digits, samples, stride
        )
        streamed_actions: list[FourSymbolDefect] = []
        streamed = source.engine.pointed_combined_defect_tape(
            source.root,
            start_f,
            source.phase,
            digits,
            samples,
            stride,
            on_emission=streamed_actions.append,
        )
        assert materialized.emissions == tuple(streamed_actions)
        assert streamed.emissions == ()
        assert (materialized.halo_segments, materialized.locally_advanced_f_steps) == (
            streamed.halo_segments,
            streamed.locally_advanced_f_steps,
        )


def test_cli_defect_observer_consumes_streamed_tape(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    original = DoubleReverseTemporalHashlife.pointed_combined_defect_tape
    issued: list[CertifiedDefectTape] = []

    def capture_tape(
        engine: DoubleReverseTemporalHashlife,
        root: int,
        start_steps: int,
        phase: int,
        digits: int,
        samples: int,
        stride: int = 1,
        *,
        on_emission: Callable[[FourSymbolDefect], None] | None = None,
    ) -> CertifiedDefectTape:
        tape = original(
            engine,
            root,
            start_steps,
            phase,
            digits,
            samples,
            stride,
            on_emission=on_emission,
        )
        issued.append(tape)
        return tape

    monkeypatch.setattr(
        DoubleReverseTemporalHashlife,
        "pointed_combined_defect_tape",
        capture_tape,
    )
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "168",
                "--nth",
                "128",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.defect-clock",
                "--temporal-defect-digits",
                "12",
                "--temporal-period-samples",
                "12",
            ]
        )
        == 0
    )
    assert capsys.readouterr().out
    assert issued
    assert all(not tape.emissions for tape in issued)


def test_defect_observer_reserves_before_reading_source(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(168, 128, max_state_bits=16384) as term:
        _, source = term.prepare_bank_source(max_prefix=16)

        def refuse_reservation(
            ledger: ResourceLedger,
            owner: int,
            *,
            entries: int = 0,
            nodes: int = 0,
        ) -> Never:
            assert ledger is source.ledger
            assert owner == source.scratch_owner
            assert entries > 0 and nodes > 0
            raise BlockContextBudgetExceeded("injected observer scratch refusal")

        def prohibit_source_read(*_args: object, **_kwargs: object) -> Never:
            raise AssertionError("source was read before scratch admission")

        with monkeypatch.context() as patcher:
            patcher.setattr(ResourceLedger, "reservation", refuse_reservation)
            patcher.setattr(
                DoubleReverseTemporalHashlife,
                "pointed_combined_defect_tape",
                prohibit_source_read,
            )
            patcher.setattr(
                DoubleReverseTemporalHashlife,
                "pointed_window",
                prohibit_source_read,
            )
            with pytest.raises(BlockContextBudgetExceeded, match="scratch refusal"):
                source_bound_defect_period_packet(
                    source, digits=12, samples=8, stride=1, max_lag=4
                )


def test_streamed_defect_cancellation_releases_source_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(168, 128, max_state_bits=16384) as term:
        _, source = term.prepare_bank_source(max_prefix=16)
        expected = source_bound_defect_period_packet(
            source, digits=12, samples=4, stride=1, max_lag=2
        )
        assert expected["status"] == "available"
        scratch_before = source.ledger.account_usage(source.scratch_owner)
        original = DoubleReverseTemporalHashlife.pointed_combined_defect_tape
        emitted = 0
        published: list[dict[str, object]] = []

        def cancel_after_first(
            engine: DoubleReverseTemporalHashlife,
            root: int,
            start_steps: int,
            phase: int,
            digits: int,
            samples: int,
            stride: int = 1,
            *,
            on_emission: Callable[[FourSymbolDefect], None] | None = None,
        ) -> CertifiedDefectTape:
            def emit(defect: FourSymbolDefect) -> None:
                nonlocal emitted
                if on_emission is None:
                    raise AssertionError("observer did not request streamed emissions")
                on_emission(defect)
                emitted += 1
                if emitted == 1:
                    raise RuntimeError("injected streamed observer cancellation")

            return original(
                engine,
                root,
                start_steps,
                phase,
                digits,
                samples,
                stride,
                on_emission=emit,
            )

        with monkeypatch.context() as patcher:
            patcher.setattr(
                DoubleReverseTemporalHashlife,
                "pointed_combined_defect_tape",
                cancel_after_first,
            )
            with pytest.raises(
                RuntimeError, match="injected streamed observer cancellation"
            ):
                packet = source_bound_defect_period_packet(
                    source, digits=12, samples=4, stride=1, max_lag=2
                )
                published.append(packet)

        assert emitted == 1
        assert published == []
        assert source.ledger.account_usage(source.scratch_owner) == scratch_before
        assert (
            source_bound_defect_period_packet(
                source, digits=12, samples=4, stride=1, max_lag=2
            )
            == expected
        )


def test_segmented_source_halo_not_single_sample_cones(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "168",
                "--nth",
                "3000",
                "--max-state-bits",
                "8192",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.defect-clock",
                "--temporal-defect-digits",
                "24",
                "--temporal-period-samples",
                "20",
                "--temporal-period-stride",
                "32",
                "--temporal-period-max-lag",
                "12",
            ]
        )
        == 0
    )
    result = json.loads(capsys.readouterr().out)["info"]["temporal.defect-clock"]
    assert result["status"] == "available"
    assert result["source_halo_segments"] == 2
    assert result["segmented_source_halo"] is True
    assert result["shared_source_halo"] is False
    assert result["local_t_squared_steps"] == 2 * 32 * (20 - 2)
    assert result["samples"] == 20
    assert result["infinite_period_certified"] is False
    # The exact temporal seam still comes from authenticated scalar probes.
    assert len(result["rows"]) == 20
    assert all(len(row["carry_first"]) == 24 for row in result["rows"])


def test_canonical_cli_repeated_request_shares_one_certificate(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.api import bank_observation

    original = bank_observation.double_reverse_residue_packet
    calls: list[DoubleReverseTerm] = []

    def once(term: DoubleReverseTerm) -> dict[str, object]:
        calls.append(term)
        if len(calls) != 1:
            raise AssertionError("duplicate residue / growth-quotient source fold")
        return original(term)

    monkeypatch.setattr(bank_observation, "double_reverse_residue_packet", once)
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "512",
                "--no-value",
                "--format",
                "json",
                "--info",
                "temporal.residue99",
                "--info",
                "temporal.residue99",
            ]
        )
        == 0
    )
    packets = json.loads(capsys.readouterr().out)["info"]
    assert tuple(packets) == ("temporal.residue99",)
    assert packets["temporal.residue99"]["target_generation"] == 512
    assert len(calls) == 1
