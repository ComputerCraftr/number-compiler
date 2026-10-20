"""Exact source-derived, skewed open-ring action and Moore production checks."""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace
from random import Random
from typing import cast

import pytest

from number_compiler.sequences.double_reverse import open_temporal_ring
from number_compiler.sequences.double_reverse._temporal_bank_authority import (
    SourceAuthorizedRecord,
    SourceRecordAuthority,
)
from number_compiler.sequences.double_reverse._temporal_bank_authority import (
    validate_source_record as validate_source_record_owner,
)
from number_compiler.sequences.double_reverse.conditional_open_moore import (
    ConditionalOpenMoore,
    ConditionalOpenMooreBudgetExceeded,
)
from number_compiler.sequences.double_reverse.open_temporal_ring import (
    OpenRingPorts,
    OpenRingState,
    certified_open_temporal_bank,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.protected_temporal_bank import (
    BANK_CHANNELS,
    PeriodicBankFrame,
    bank_channel_name,
)
from number_compiler.sequences.double_reverse.source_bound_bank import PointedBankSource
from number_compiler.sequences.double_reverse.temporal_hashlife import growth_ports


def _literal(seed: int, physical_steps: int) -> int:
    for _ in range(physical_steps):
        seed = 2 * int(str(seed)[::-1])
    return seed


def _two_phase_ingress_fixture() -> tuple[OpenRingState, OpenRingPorts, OpenRingPorts]:
    return (
        OpenRingState((2,), (8,), 0),
        OpenRingPorts(7, 9, (8, 8), (0, 1)),
        OpenRingPorts(9, 3, (1, 2), (4, 5)),
    )


@pytest.mark.parametrize(
    "upper,lower",
    [("17", "88"), ("17", "42"), ("48", "42"), ("48", "88"), ("49", "88")],
)
@pytest.mark.parametrize("steps", [1, 2, 4, 7])
def test_open_ring_matches_both_boundaries_and_conditional_borrows(
    upper: str, lower: str, steps: int
) -> None:
    random = Random(749 + 17 * steps)
    # This deliberately has a nonperiodic interior, not a cyclic spatial ring.
    middle = "".join(str(random.randrange(10)) for _ in range(100))
    seed = int(upper + middle + lower)
    with DoubleReverseTerm(seed, 2 * (steps + 1)) as term:
        phase = term.temporal_engine.certify(term.source_root)
        assert phase is not None
        births_left, births_right = growth_ports(phase, steps)
        coordinate = births_left + 20
        engine = term.temporal_engine
        cursor = engine.advance_source_prefix()
        source = cast(
            Callable[..., PointedBankSource],
            object.__getattribute__(term, "_pointed_bank_source"),
        )(
            cursor,
            term.source_root,
            phase,
            steps,
            len(str(seed)) + births_left + births_right,
        )
        packet = certified_open_temporal_bank(source, coordinate, 5)
        assert packet.f_steps == steps
        assert packet.width_out == len(str(seed)) + births_left + births_right
        assert packet.input_period is None  # no invented harmonic period
        actual = str(_literal(seed, 2 * steps))
        following = str(_literal(seed, 2 * steps + 2))
        increment_left = growth_ports(phase, steps + 1)[0] - births_left
        for i in range(packet.pair_count):
            position = coordinate + i
            source_pair = (int(actual[position]), int(actual[-1 - position]))
            next_position = position + increment_left
            next_pair = (
                int(following[next_position]),
                int(following[-1 - next_position]),
            )
            frame = packet.at(i)
            assert frame.digits == source_pair
            assert frame.next_digits == next_pair
            assert frame.carry_xor == ((source_pair[0] >= 5) ^ (source_pair[1] >= 5))
            assert frame.borrow_left == (
                int(next_pair[0] < source_pair[0]),
                int(next_pair[0] < source_pair[0] + 1),
            )
            assert frame.borrow_right == (
                int(next_pair[1] < source_pair[1]),
                int(next_pair[1] < source_pair[1] + 1),
            )


def test_open_ring_period_one_has_source_bound_minimized_future() -> None:
    seed = int("17" + "9" * 90 + "88")
    with DoubleReverseTerm(seed, 24) as term:
        packet = term.open_temporal_bank_window(18, 5)
        assert packet.input_period == 1
        assert packet.moore_classes == 2
        assert packet.moore_cycle == 2
        for frame in packet.frames:
            assert frame.digits == (9, 9)
        old = packet.input_period
        object.__setattr__(packet, "input_period", 7)
        with pytest.raises(ValueError, match="authority"):
            packet.at(0)
        object.__setattr__(packet, "input_period", old)
        assert packet.at(0).digits == (9, 9)
    with pytest.raises(ValueError, match="authority"):
        packet.at(0)


def test_open_ring_validated_projection_checks_source_once_and_rejects_tampering(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = int("17" + "9" * 90 + "88")
    with DoubleReverseTerm(seed, 24) as term:
        packet = term.open_temporal_bank_window(18, 5)
        original_validate = validate_source_record_owner
        validations = 0

        def counted_validate(
            record: SourceAuthorizedRecord,
        ) -> SourceRecordAuthority:
            nonlocal validations
            validations += 1
            return original_validate(record)

        monkeypatch.setattr(
            open_temporal_ring, "validate_source_record", counted_validate
        )
        counts, words = packet.validated_projection(("carry_xor", "f5"))
        assert validations == 1
        assert counts["carry_xor"] == sum(frame.carry_xor for frame in packet.frames)
        assert words["carry_xor"] == (
            tuple(frame.carry_xor for frame in packet.frames),
            1,
            (),
        )

        original_period = packet.input_period
        object.__setattr__(packet, "input_period", 19)
        with pytest.raises(ValueError, match="authority"):
            packet.validated_projection(("carry_xor",))
        assert validations == 2
        object.__setattr__(packet, "input_period", original_period)
        assert (
            packet.validated_projection(("carry_xor",))[0]["carry_xor"]
            == counts["carry_xor"]
        )


def test_direct_open_ring_guard_refusal_is_accounted_once() -> None:
    from number_compiler.resources.metric_keys import double_reverse as metric_keys
    from number_compiler.sequences.double_reverse.open_temporal_ring import (
        MAX_OPEN_PAIRS,
        OpenTemporalRingRefused,
        certified_open_temporal_bank,
    )

    with DoubleReverseTerm(196, 18) as term:
        _entry, source = term.prepare_bank_source(max_prefix=16)
        before = (
            term.metrics().get(metric_keys.DOUBLE_REVERSE_OPEN_RING_GUARD_REFUSALS) or 0
        )
        with pytest.raises(OpenTemporalRingRefused, match="finite-horizon"):
            certified_open_temporal_bank(source, 0, MAX_OPEN_PAIRS + 1)
        after = (
            term.metrics().get(metric_keys.DOUBLE_REVERSE_OPEN_RING_GUARD_REFUSALS) or 0
        )
        assert after == before + 1


def test_mismatched_moore_output_is_not_counted_as_publication(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.resources.metric_keys import double_reverse as metric_keys
    from number_compiler.sequences.double_reverse import open_temporal_ring

    seed = int("17" + "9" * 90 + "88")
    called = False

    def mismatched_output(
        _initial: OpenRingState,
        _motif: tuple[OpenRingPorts, ...],
        _target_time: int,
    ) -> tuple[tuple[PeriodicBankFrame, ...], int, int, int]:
        nonlocal called
        called = True
        return (), 1, 0, 1

    monkeypatch.setattr(open_temporal_ring, "closed_driven_moore", mismatched_output)
    with DoubleReverseTerm(seed, 24) as term:
        before = (
            term.metrics().get(metric_keys.DOUBLE_REVERSE_OPEN_RING_MOORE_PUBLICATIONS)
            or 0
        )
        with pytest.raises(AssertionError, match="changed the verified source"):
            term.open_temporal_bank_window(18, 5)
        after = (
            term.metrics().get(metric_keys.DOUBLE_REVERSE_OPEN_RING_MOORE_PUBLICATIONS)
            or 0
        )
        assert called
        assert after == before


def test_open_temporal_window_is_actual_production_output() -> None:
    seed = int("17" + "9" * 90 + "88")
    with DoubleReverseTerm(seed, 14) as term:
        window = term.exact_temporal_bank_window(12, 6)
        assert window.open_used
        assert window.open_input_period == 1
        assert window.open_moore_classes == 2
        literal = str(_literal(seed, 14))
        for index in range(window.pair_count):
            position = 12 + index
            assert window.at(index).digits == (
                int(literal[position]),
                int(literal[-1 - position]),
            )
        assert term.metrics()["double_reverse_open_ring_window_publications"] > 0


def test_random_nonperiodic_window_uses_exact_open_inputs() -> None:
    seed = int("17" + "1934075881690945570139411" + "88")
    with DoubleReverseTerm(seed, 12) as term:
        window = term.exact_temporal_bank_window(7, 4)
        # Production avoids an eager O(D) inlet scan for a nonperiodic bank.
        assert not window.open_used
        assert window.open_input_period is None
        assert window.open_moore_classes is None
        actual = str(_literal(seed, 12))
        assert [frame.pair for frame in window.frames] == [
            int(actual[7 + i]) + int(actual[-1 - 7 - i]) for i in range(4)
        ]


def test_conditional_open_ring_never_wraps_unknown_inward_digit() -> None:
    source = OpenRingState((1, 3), (4, 8), 0)
    port = OpenRingPorts(0, 2, (0, 5), (7, 6))
    future, frames = source.advance(port)
    # The right ray shifts +1 on phase zero and needs TWO exterior digits.
    from number_compiler.sequences.double_reverse.stencil_moore import stencil_cell

    assert future.right[1] == stencil_cell(8, 7, 6)
    altered = replace(port, right_after=(9, 6))
    changed, _ = source.advance(altered)
    assert future != changed
    assert len(frames) == 2


def test_unclosed_or_oversized_source_refuses_pumping() -> None:
    seed = int("17" + "1934075881690945570139411" + "88")
    with (
        DoubleReverseTerm(seed, 120) as term,
        pytest.raises(ValueError, match="lookback cannot exceed 32"),
    ):
        term.open_temporal_bank_window(12, 2, lookback_f_steps=33)


def test_conditional_future_moore_checks_all_admitted_input_letters() -> None:
    from number_compiler.sequences.double_reverse.conditional_open_moore import (
        minimize_conditional_open_ring,
    )

    state = OpenRingState((4,), (5,), 0)
    a = OpenRingPorts(4, 6, (1, 2), (5, 3))
    b = OpenRingPorts(4, 8, (1, 2), (5, 3))
    quotient = minimize_conditional_open_ring(state, ((a, b),), max_states=500)
    assert 1 <= quotient.class_count <= len(quotient.class_ids)
    assert len(quotient.alphabet) == 2
    expected = state
    total = {name: 0 for name in quotient.repeat_program((a,), 0)[1]}
    for t in range(25):
        if t:
            target, counts = quotient.repeat_program((a,), t)
            assert 0 <= target < quotient.class_count
            assert counts == total
        expected, frames = expected.advance(a)
        for channel in BANK_CHANNELS:
            total[bank_channel_name(channel)] += frames[0].scalar(channel)
    target, counts = quotient.repeat_program((a,), 10**12)
    assert 0 <= target < quotient.class_count
    assert all(value >= 0 for value in counts.values())
    with pytest.raises(ValueError, match="unadmitted"):
        quotient.letter(OpenRingPorts(8, 8, (0, 0), (0, 0)))


def test_nonconstant_inlet_cycle_retains_input_phase() -> None:
    from number_compiler.sequences.double_reverse.open_temporal_ring import (
        closed_driven_moore,
    )

    state, a, b = _two_phase_ingress_fixture()
    for t in (0, 1, 2, 8):
        exact = state
        for step in range(t):
            exact, _frames = exact.advance((a, b)[step % 2])
        expected, _next = exact.advance((a, b)[t % 2])
        result = closed_driven_moore(state, (a, b), t)
        assert result is not None
        frames, _classes, _preperiod, cycle = result
        assert cycle % 2 == 0
        assert frames[0].digits == (exact.left[0], exact.right[0])
        assert frames[0].next_digits == (expected.left[0], expected.right[0])


def test_phase_conditional_moore_refuses_uncertified_letter_order() -> None:
    from number_compiler.sequences.double_reverse.conditional_open_moore import (
        minimize_conditional_open_ring,
    )

    source, a, b = _two_phase_ingress_fixture()
    quotient = minimize_conditional_open_ring(source, ((a,), (b,)), max_states=500)
    # Correct two-phase input can be squared as a complete input-driven action.
    target, masks = quotient.repeat_program((a, b), 10**9)
    assert 0 <= target < quotient.class_count
    assert all(x >= 0 for x in masks.values())
    with pytest.raises(ValueError, match="guarded Moore transition"):
        quotient.repeat_program((a,), 2)


def test_open_moore_only_turns_typed_budget_exhaustion_into_no_quotient(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.double_reverse import (
        conditional_open_moore,
        open_temporal_ring,
    )

    state, a, b = _two_phase_ingress_fixture()

    def budget_refusal(
        _initial: OpenRingState,
        _allowed_by_phase: tuple[tuple[OpenRingPorts, ...], ...],
        *,
        max_states: int = 4096,
    ) -> ConditionalOpenMoore:
        del max_states
        raise ConditionalOpenMooreBudgetExceeded(
            "state universe did not close within budget"
        )

    monkeypatch.setattr(
        conditional_open_moore, "minimize_conditional_open_ring", budget_refusal
    )
    assert open_temporal_ring.closed_driven_moore(state, (a, b), 7) is None

    def malformed_value_error(
        _initial: OpenRingState,
        _allowed_by_phase: tuple[tuple[OpenRingPorts, ...], ...],
        *,
        max_states: int = 4096,
    ) -> ConditionalOpenMoore:
        del max_states
        raise ValueError("state universe did not close within budget")

    monkeypatch.setattr(
        conditional_open_moore,
        "minimize_conditional_open_ring",
        malformed_value_error,
    )
    with pytest.raises(ValueError, match="state universe did not close"):
        open_temporal_ring.closed_driven_moore(state, (a, b), 7)


@pytest.mark.parametrize(
    "generation,count", [(18, 3), (32, 5), (64, 14), (128, 12), (200, 8)]
)
def test_seed196_late_cursor_outputs_without_target_endpoint(
    generation: int, count: int
) -> None:
    from unittest.mock import patch

    # The source adapter may publish an authenticated *earlier* SLP action,
    # but neither the public final endpoint nor its final integer is needed.
    with (
        patch.object(
            DoubleReverseTerm,
            "prepare_endpoint",
            side_effect=AssertionError("unexpected final endpoint"),
        ),
        DoubleReverseTerm(196, generation) as term,
    ):
        pair_start = 7 if generation == 200 else 0
        result = term.open_temporal_bank_window(pair_start, count)
        value = str(_literal(196, generation))
        assert result.width_out == len(value)
        for i, frame in enumerate(result.frames):
            k = pair_start + i
            assert frame.digits == (int(value[k]), int(value[-1 - k]))
        assert result.physical_prefix < generation
        # The recorded 120/576 harmonics are NOT source-certified inlets.
        assert result.input_period is None


def test_open_ring_cli_publishes_actual_seed196_gt_eq_lt_banks(capsys: object) -> None:
    # This test is executed by the repository's guarded pytest runner when
    # available. The source-only API is also checked independently above.
    import json

    from number_compiler.api import cli

    code = cli.main(
        [
            "2rev10",
            "--seed",
            "196",
            "--nth",
            "64",
            "--no-value",
            "--info",
            "temporal.open-ring",
            "--spatial-pair-bank-position",
            "0",
            "--spatial-bank-morphism-count",
            "14",
            "--format",
            "json",
        ]
    )
    assert code == 0
    output = json.loads(capsys.readouterr().out)  # type: ignore[attr-defined]
    row = output["info"]["temporal.open-ring"]
    assert (row["physical_prefix"], row["f_steps"], row["width_out"]) == (48, 8, 30)
    assert row["moore_classes"] is None
    assert {
        k: sum(row["output_words"][k])
        for k in ("lt_low", "lt_high", "eq", "gt_low", "gt_high")
    } == {"lt_low": 4, "lt_high": 4, "eq": 1, "gt_low": 2, "gt_high": 3}
