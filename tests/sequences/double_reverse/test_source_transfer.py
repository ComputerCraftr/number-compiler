"""Finite 2rev10 transfer joins exact T-squared source roots."""

from typing import cast

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import double_reverse as _double_reverse_keys
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.source_transfer import (
    MAX_PHYSICAL_STEPS,
    PAIR_COORDINATE_ORDER,
    _same_word,
    source_transfer_packet,
)
from number_compiler.sequences.double_reverse.temporal_depth_transfer_matrix import (
    BooleanPairMatrix,
)
from tests.sequences.source_transfer_support import assert_exact_source_transfer_path


def _double_reverse(value: int) -> int:
    return 2 * int(str(value)[::-1])


def _pair(value: int, depth: int) -> tuple[int, int]:
    digits = str(value)
    return int(digits[depth]), int(digits[-1 - depth])


def _fourth_digit_carry(value: int) -> int:
    return int(str(value)[-4] >= "5")


@pytest.mark.parametrize("steps", (8, 10, 16))
def test_double_reverse_transfer_joins_forward_two_tick_children(steps: int) -> None:
    generation = 32
    source = 196
    for _ in range(generation):
        source = _double_reverse(source)
    expected = [source]
    for _ in range(steps):
        expected.append(_double_reverse(expected[-1]))

    with DoubleReverseTerm(196, generation, max_state_bits=16384) as term:
        packet = source_transfer_packet(term, steps=steps, pair_depth=1)

    expected_pairs = tuple(_pair(value, 1) for value in expected[::2])
    assert_exact_source_transfer_path(
        packet,
        expected_pairs,
        physical_interval=(generation, generation + steps),
        border_span=2,
        pair_coordinate_order=PAIR_COORDINATE_ORDER,
    )
    depth_windows = cast(tuple[dict[str, object], ...], packet["depth_windows"])
    expected_window_count = (steps // 2 + 3) // 4
    assert len(depth_windows) == expected_window_count
    joined_action = BooleanPairMatrix.identity()
    f_step_offset = 0
    for window in depth_windows:
        f_steps = len(cast(tuple[tuple[int, int], ...], window["source_pair_path"])) - 1
        assert 1 <= f_steps <= 4
        assert window["physical_interval"] == (
            generation + 2 * f_step_offset,
            generation + 2 * (f_step_offset + f_steps),
        )
        assert (
            window["source_pair_path"]
            == expected_pairs[f_step_offset : f_step_offset + f_steps + 1]
        )
        window_action = BooleanPairMatrix(
            cast(tuple[int, ...], window["transition_rows"])
        )
        joined_action = joined_action.then(window_action)
        f_step_offset += f_steps
    assert f_step_offset == steps // 2
    assert joined_action.rows == packet["depth_window_joined_transition_rows"]
    assert joined_action.endpoints(expected_pairs[0]) == (expected_pairs[-1],)

    border_phases = cast(tuple[dict[str, object], ...], packet["border_phases"])
    assert tuple(phase["fourth_digit_carries"] for phase in border_phases) == tuple(
        (
            _fourth_digit_carry(expected[index]),
            _fourth_digit_carry(expected[index + 1]),
        )
        for index in range(0, steps, 2)
    )


def test_double_reverse_transfer_reuses_a_warm_query_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    generation = 32
    with DoubleReverseTerm(196, generation, max_state_bits=16384) as term:
        endpoint_root = term._root()

        def forbid_cold_source_image(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("warm 2rev10 endpoint requested a cold image")

        monkeypatch.setattr(
            type(term._scheduler), "source_image", forbid_cold_source_image
        )
        packet = source_transfer_packet(term, steps=2, pair_depth=1)

        assert packet["status"] == "available"
        assert packet["source_root"] == endpoint_root


def test_endpoint_rebase_streams_exact_words_and_cleans_up_early_exits(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(196, 2, max_state_bits=16384) as term:
        left = term._arena.word((1, 2, 3, 4))
        early_mismatch = term._arena.word((9, 2, 3, 4))
        late_mismatch = term._arena.word((1, 2, 3, 5))

        assert _same_word(term, left, left)
        assert not _same_word(term, left, early_mismatch)
        comparison_digits = term.metrics()[
            _double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_DIGITS
        ]
        assert not _same_word(term, left, late_mismatch)
        assert (
            term.metrics()[_double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_DIGITS]
            - comparison_digits
            == 4
        )

        def scratch_usage() -> tuple[int, int]:
            scratch = next(
                account
                for account in term._ledger.inventory()
                if account.owner == term._scratch_owner
            )
            return scratch.entries, scratch.nodes

        assert scratch_usage() == (0, 0)

        original_bump = ResourceLedger.bump
        node_visits = 0

        def fail_during_stream(
            ledger: ResourceLedger, counter: str, amount: int = 1
        ) -> None:
            nonlocal node_visits
            if (
                counter
                == _double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_NODE_VISITS
            ):
                node_visits += 1
                if node_visits == 2:
                    raise RuntimeError("injected endpoint comparison failure")
            original_bump(ledger, counter, amount)

        monkeypatch.setattr(ResourceLedger, "bump", fail_during_stream)
        with pytest.raises(RuntimeError, match="injected endpoint comparison failure"):
            _same_word(term, left, late_mismatch)
        assert scratch_usage() == (0, 0)


def test_double_reverse_transfer_rejects_oversized_horizon_before_source_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbid_source_preparation(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("invalid horizon reached pointed-source preparation")

    monkeypatch.setattr(
        DoubleReverseTerm, "_prepare_bank_source", forbid_source_preparation
    )
    with (
        DoubleReverseTerm(196, 2, max_state_bits=16384) as term,
        pytest.raises(ValueError, match="physical ticks"),
    ):
        source_transfer_packet(term, steps=MAX_PHYSICAL_STEPS + 2, pair_depth=1)


@pytest.mark.parametrize("pair_depth", (14, 15, 16))
def test_double_reverse_transfer_admits_deep_windows_with_bounded_halos(
    pair_depth: int,
) -> None:
    generation = 79
    source = 196
    for _ in range(generation):
        source = _double_reverse(source)
    expected = [
        source,
        _double_reverse(source),
        _double_reverse(_double_reverse(source)),
    ]

    with DoubleReverseTerm(196, generation, max_state_bits=16384) as term:
        packet = source_transfer_packet(term, steps=2, pair_depth=pair_depth)

    assert packet["status"] == "available"
    assert packet["source_pair_path"] == tuple(
        _pair(value, pair_depth) for value in expected[::2]
    )
    depth_windows = cast(tuple[dict[str, object], ...], packet["depth_windows"])
    assert len(depth_windows) == 1
    assert cast(int, depth_windows[0]["causal_halo_pairs"]) == pair_depth + 2
    assert cast(int, depth_windows[0]["causal_halo_pairs"]) <= 18


def test_double_reverse_transfer_rejects_unsupported_depth_before_source_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbid_source_preparation(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("invalid depth reached pointed-source preparation")

    monkeypatch.setattr(
        DoubleReverseTerm, "_prepare_bank_source", forbid_source_preparation
    )
    with (
        DoubleReverseTerm(196, 2, max_state_bits=16384) as term,
        pytest.raises(ValueError, match="pair depth"),
    ):
        source_transfer_packet(term, steps=2, pair_depth=17)
