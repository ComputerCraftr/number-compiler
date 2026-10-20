"""Independent checks for source radix-2/5 and guarded temporal Walsh ports."""

from __future__ import annotations

import json
from dataclasses import fields

import pytest

from number_compiler.api import cli
from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.resources.metric_collection import collect_ledger_metrics
from number_compiler.sequences.double_reverse import (
    source_bound_bank as source_bound_bank_module,
)
from number_compiler.sequences.double_reverse._temporal_bank_authority import (
    validate_source_record,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.protected_temporal_bank import (
    PeriodicBankFrame,
    ProtectedPeriodicBank,
    ProtectedPeriodicBankRefused,
    bank_channel_name,
)
from number_compiler.sequences.double_reverse.radix25_temporal_bank import (
    BOOL_CHANNELS,
    JointRadix25TemporalBank,
    radix25_shift_port,
    temporal_bank_walsh64,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    DoubleReverseTemporalHashlife,
    growth_ports,
)


def _step(value: int) -> int:
    return int(str(value)[::-1]) << 1


def _inverse_walsh(coefficients: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        4
        * sum(
            (-1 if (row & column).bit_count() & 1 else 1) * coefficients[column]
            for column in range(64)
        )
        % 5
        for row in range(64)
    )


def _assert_joint_walsh_matches_frames(
    joint: JointRadix25TemporalBank,
) -> tuple[PeriodicBankFrame, ...]:
    """Check each published Walsh channel against its independent frame word."""
    frames, _authority = joint.protected.authorized_frames(0, 64)
    assert joint.walsh64.lane_count == 64
    assert set(joint.walsh64.masks) == {
        bank_channel_name(channel) for channel in BOOL_CHANNELS
    }
    for channel in BOOL_CHANNELS:
        name = bank_channel_name(channel)
        expected = tuple(
            (joint.walsh64.masks[name] >> index) & 1 for index in range(64)
        )
        assert _inverse_walsh(joint.walsh64.transform_mod5[name]) == expected
        assert expected == tuple(frame.scalar(channel) for frame in frames)
    f5 = tuple(frame.f5 for frame in frames)
    assert _inverse_walsh(joint.walsh64.f5_transform) == f5
    return frames


def test_radix25_crt_and_guarded_two_step_match_integer_arithmetic() -> None:
    arena = SLPArena()
    for source in range(512):
        root = arena.word(tuple(map(int, str(source))))
        port = radix25_shift_port(arena, root, places=7)
        first = _step(source)
        assert port.source_mod10 == source % 10**7
        assert port.next_mod10 == first % 10**7
        assert port.shifted_mod2 == first % 2**7
        assert port.doubled_mod5 == first % 5**7
        if source % 10:
            assert port.two_step_mod10 == _step(first) % 10**7
        else:
            assert port.two_step_mod10 is None


def test_radix25_fold_keeps_a_trillion_repeat_compressed() -> None:
    arena = SLPArena()
    tile = arena.word((4, 8))
    root = arena.repeat(tile, 10**12)
    port = radix25_shift_port(arena, root, places=9)
    assert port.width == 2 * 10**12
    assert port.next_mod10 == (2 * int("84" * 5)) % 10**9
    assert len(arena.nodes) < 15


def test_joint_bank_walsh_is_invertible_and_tracks_both_rays() -> None:
    seed = int("17" + "48" * 170 + "88")
    with DoubleReverseTerm(seed, 128, max_state_bits=4096) as term:
        joint = term.joint_radix25_temporal_bank(150, places=8, period=2)
        assert joint.physical_prefix == 0
        assert joint.protected.represented_steps == 64
        assert joint.protected.moore_classes is not None
        frames = _assert_joint_walsh_matches_frames(joint)
        assert term.published_image is None
        assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1
        assert joint.source.next_mod10 == _step(seed) % 10**8

        value = seed
        for tick in range(64):
            digits = str(value)
            left_birth, right_birth = growth_ports(0, tick)
            left = int(digits[150 + left_birth])
            right = int(digits[len(str(seed)) - 1 - 150 + right_birth])
            frame = frames[tick]
            assert frame.digits == (left, right)
            assert frame.carry_xor == (int(left >= 5) ^ int(right >= 5))
            value = _step(_step(value))


def test_phase_three_walsh_tracks_independent_birth_bits() -> None:
    seed = int("48" + "48" * 170 + "88")
    with DoubleReverseTerm(seed, 128, max_state_bits=4096) as term:
        joint = term.joint_radix25_temporal_bank(150, places=8, period=2)
        assert joint.protected.phase_in == 3
        frames = _assert_joint_walsh_matches_frames(joint)
        assert (frames[0].growth_left, frames[0].growth_right) == (1, 1)
        assert frames[0].growth == 2


def test_temporal_bank_authority_rejects_forgery_and_cross_root_join() -> None:
    seed_text = "17" + "48" * 170 + "88"
    other_text = (
        seed_text[:30] + ("5" if seed_text[30] != "5" else "6") + seed_text[31:]
    )
    with (
        DoubleReverseTerm(int(seed_text), 128, max_state_bits=4096) as first,
        DoubleReverseTerm(int(other_text), 128, max_state_bits=4096) as second,
    ):
        joint = first.joint_radix25_temporal_bank(150, places=8, period=2)
        forged = ProtectedPeriodicBank(
            **{
                field.name: getattr(joint.protected, field.name)
                for field in fields(ProtectedPeriodicBank)
            }
        )
        with pytest.raises(ValueError, match="authority"):
            temporal_bank_walsh64(forged)
        with pytest.raises(ValueError, match="authority"):
            forged.authorized_frames(0, 1)

        unrelated_source = second.source_radix25_shift(places=8)
        with pytest.raises(ValueError, match="different source roots"):
            JointRadix25TemporalBank(
                joint.physical_prefix,
                unrelated_source,
                joint.protected,
                joint.walsh64,
            )

        source_authority = validate_source_record(joint.source)
        source_arena = source_authority.arena
        assert source_arena is not None
        wrong_generation_source = radix25_shift_port(
            source_arena,
            source_authority.root,
            places=8,
            physical_prefix=joint.physical_prefix + 1,
        )
        with pytest.raises(ValueError, match="owner generations"):
            JointRadix25TemporalBank(
                joint.physical_prefix,
                wrong_generation_source,
                joint.protected,
                joint.walsh64,
            )


def test_walsh_rejects_closed_source_and_tampered_nested_mask() -> None:
    seed = int("17" + "48" * 170 + "88")
    with DoubleReverseTerm(seed, 128, max_state_bits=4096) as term:
        joint = term.joint_radix25_temporal_bank(150, places=8, period=2)
        closed_bank = joint.protected
    with pytest.raises(ValueError, match="authority"):
        temporal_bank_walsh64(closed_bank)
    with pytest.raises(ValueError, match="authority"):
        closed_bank.authorized_frames(0, 1)

    with DoubleReverseTerm(seed, 128, max_state_bits=4096) as term:
        joint = term.joint_radix25_temporal_bank(150, places=8, period=2)
        masks = dict(joint.walsh64.masks)
        masks["eq"] ^= 1
        object.__setattr__(joint.walsh64, "masks", masks)
        with pytest.raises(ValueError, match="authority"):
            JointRadix25TemporalBank(
                joint.physical_prefix,
                joint.source,
                joint.protected,
                joint.walsh64,
            )


def test_exact_pair_consumes_certified_bank_and_refuses_to_reopen_cones(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = int("17" + "48" * 170 + "88")
    value = seed
    for _ in range(128):
        value = _step(value)

    def forbid_cone(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("certified periodic bank replayed pointed cones")

    with DoubleReverseTerm(seed, 128, max_state_bits=4096) as term:
        monkeypatch.setattr(
            DoubleReverseTemporalHashlife, "pointed_stencil", forbid_cone
        )
        pair = term.exact_temporal_pair(150)
        digits = str(value)
        assert pair.digits == (int(digits[150]), int(digits[-151]))
        assert term.metrics()["double_reverse_periodic_bank_pointed_reuse"] == 1
        assert term.published_image is None


def test_exact_pair_falls_back_when_periodic_bank_refuses(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    source_digits = list("17" + "48" * 20 + "88")
    # The cheap period-2 selector sees equal endpoints at source positions
    # 19/21, while the selected source period fails inside the halo at 20.
    source_digits[20] = "5"
    seed = int("".join(source_digits))
    value = seed
    for _ in range(4):
        value = _step(value)
    with DoubleReverseTerm(seed, 4) as term:
        with pytest.raises(ProtectedPeriodicBankRefused, match="periodic halo"):
            term.protected_temporal_bank(19, period=2)
        pair = term.exact_temporal_pair(20)
        digits = str(value)
        assert pair.digits == (int(digits[20]), int(digits[-21]))
        assert term.metrics().get("double_reverse_periodic_bank_pointed_reuse", 0) == 0


def test_exact_pair_does_not_hide_malformed_periodic_bank_errors(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = int("17" + "48" * 20 + "88")

    def malformed(*_args: object, **_kwargs: object) -> object:
        raise ValueError("source root is invalid")

    monkeypatch.setattr(source_bound_bank_module, "protected_periodic_bank", malformed)
    with (
        DoubleReverseTerm(seed, 4) as term,
        pytest.raises(ValueError, match="source root is invalid"),
    ):
        term.exact_temporal_pair(20)


def test_short_primitive_uses_binary_shift_and_long_source_stays_an_slp() -> None:
    with DoubleReverseTerm(196, 1, max_state_bits=128) as term:
        assert term.materialize(max_bits=128) == 1382
        assert term.metrics()["double_reverse_binary_shift_primitives"] == 1
        assert (
            term.metrics().get("double_reverse_spatial_transducer_applications", 0) == 0
        )
        assert collect_ledger_metrics(term.resource_ledger).resource_audit_complete == 1

    long_seed = int("1234567890" * 8)
    with DoubleReverseTerm(long_seed, 1, max_state_bits=1024) as term:
        assert term.materialize(max_bits=1024) == _step(long_seed)
        assert term.metrics().get("double_reverse_binary_shift_primitives", 0) == 0
        assert term.metrics()["double_reverse_spatial_transducer_applications"] == 1


def test_typed_cli_observers_use_qualified_radix_and_walsh_flags(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                "196",
                "--nth",
                "0",
                "--no-value",
                "--info",
                "arithmetic.radix25-shift",
                "--arithmetic-radix-places",
                "8",
                "--format",
                "json",
            ]
        )
        == 0
    )
    payload = json.loads(capsys.readouterr().out)["info"]["arithmetic.radix25-shift"]
    assert payload["next_mod10"] == 1382
    assert payload["two_step_mod10"] == 5662

    seed = "17" + "48" * 170 + "88"
    assert (
        cli.main(
            [
                "2rev10",
                "--seed",
                seed,
                "--nth",
                "128",
                "--no-value",
                "--info",
                "temporal.radix-walsh",
                "--arithmetic-radix-places",
                "8",
                "--temporal-grammar-position",
                "150",
                "--temporal-grammar-period",
                "2",
                "--temporal-walsh-start",
                "0",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)["info"]["temporal.radix-walsh"]
    assert packet["walsh64"]["lane_count"] == 64
    assert packet["source"]["next_mod10"] == _step(int(seed)) % 10**8
