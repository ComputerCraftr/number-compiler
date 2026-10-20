"""Finite 2rev10 transfer joins exact T-squared source roots."""

from typing import cast

import pytest

from number_compiler.hashlife.execution.tile_scheduler import TileScheduler
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import double_reverse as _double_reverse_keys
from number_compiler.sequences.double_reverse.boundary_cycles import Edge
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.source_transfer import (
    MAX_PHYSICAL_STEPS,
    MAX_POWERED_PHYSICAL_STEPS,
    PAIR_COORDINATE_ORDER,
    same_word,
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
        packet = source_transfer_packet(term, steps=steps, pair_depth=1, trace=True)

    details = packet["trace"]
    assert isinstance(details, dict)
    detailed_packet = {**packet, **cast(dict[str, object], details)}
    expected_pairs = tuple(_pair(value, 1) for value in expected[::2])
    assert_exact_source_transfer_path(
        detailed_packet,
        expected_pairs,
        physical_interval=(generation, generation + steps),
        border_span=2,
        pair_coordinate_order=PAIR_COORDINATE_ORDER,
    )
    depth_windows = cast(tuple[dict[str, object], ...], details["depth_windows"])
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
    assert joined_action.rows == details["depth_window_joined_transition_rows"]
    assert joined_action.endpoints(expected_pairs[0]) == (expected_pairs[-1],)

    border_phases = cast(tuple[dict[str, object], ...], details["border_phases"])
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
        endpoint_root = term.endpoint_root()

        def forbid_cold_source_image(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("warm 2rev10 endpoint requested a cold image")

        monkeypatch.setattr(TileScheduler, "source_image", forbid_cold_source_image)
        packet = source_transfer_packet(term, steps=2, pair_depth=1)

        assert packet["status"] == "available"
        assert packet["source_root_local_diagnostic"] == endpoint_root
        assert packet["chronological_future_roots_constructed"] is False
        assert packet["inner_pair_matrix_computed"] is False


def test_bounded_fallback_summary_keeps_chronology_only_in_explicit_trace(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.double_reverse import source_transfer as owner
    from number_compiler.sequences.double_reverse import temporal_predictive_border

    generation = 32
    steps = 8
    source = 196
    for _ in range(generation):
        source = _double_reverse(source)
    target = source
    for _ in range(steps):
        target = _double_reverse(target)

    def unavailable(*_args: object, **_kwargs: object) -> dict[str, object]:
        return {"status": "unavailable", "reason": "injected powered-cylinder refusal"}

    monkeypatch.setattr(
        temporal_predictive_border, "predictive_source_transfer", unavailable
    )
    chronological = owner.chronological_source_transfer_packet
    requested_trace_flags: list[bool] = []

    def record_trace_demand(
        term: DoubleReverseTerm,
        *,
        steps: int,
        pair_depth: int,
        include_trace: bool,
    ) -> dict[str, object]:
        requested_trace_flags.append(include_trace)
        return chronological(
            term,
            steps=steps,
            pair_depth=pair_depth,
            include_trace=include_trace,
        )

    monkeypatch.setattr(
        owner, "chronological_source_transfer_packet", record_trace_demand
    )
    with DoubleReverseTerm(196, generation, max_state_bits=16384) as term:
        packet = source_transfer_packet(term, steps=steps, pair_depth=1)

    assert packet["status"] == "available"
    assert packet["construction"] == "bounded_exact_source_fallback"
    assert packet["powered_projection_unavailable"] == (
        "injected powered-cylinder refusal"
    )
    assert packet["source_pair"] == _pair(source, 1)
    assert packet["pointed_target_pair"] == _pair(target, 1)
    assert "trace" not in packet
    assert not {
        "source_pair_path",
        "transition_rows",
        "phase_matrices",
        "border_phases",
        "four_tick_observed_words",
        "depth_windows",
        "depth_window_joined_transition_rows",
        "source_horizon_physical_ticks",
    }.intersection(packet)
    assert requested_trace_flags == [False]


def test_endpoint_rebase_streams_exact_words_and_cleans_up_early_exits(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    with DoubleReverseTerm(196, 2, max_state_bits=16384) as term:
        left = term.source_arena.word((1, 2, 3, 4))
        early_mismatch = term.source_arena.word((9, 2, 3, 4))
        late_mismatch = term.source_arena.word((1, 2, 3, 5))

        assert same_word(term, left, left)
        assert not same_word(term, left, early_mismatch)
        comparison_digits = term.metrics()[
            _double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_DIGITS
        ]
        assert not same_word(term, left, late_mismatch)
        assert (
            term.metrics()[_double_reverse_keys.DOUBLE_REVERSE_STATE_COMPARISON_DIGITS]
            - comparison_digits
            == 4
        )

        def scratch_usage() -> tuple[int, int]:
            scratch = next(
                account
                for account in term.resource_ledger.inventory()
                if account.owner == term.scratch_owner
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
            same_word(term, left, late_mismatch)
        assert scratch_usage() == (0, 0)


def test_double_reverse_transfer_rejects_oversized_horizon_before_source_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbid_source_preparation(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("invalid horizon reached pointed-source preparation")

    monkeypatch.setattr(
        DoubleReverseTerm, "prepare_bank_source", forbid_source_preparation
    )
    with (
        DoubleReverseTerm(196, 2, max_state_bits=16384) as term,
        pytest.raises(ValueError, match="physical ticks"),
    ):
        source_transfer_packet(
            term,
            steps=MAX_PHYSICAL_STEPS + 2,
            pair_depth=1,
            trace=True,
        )


def test_border_relation_cache_rejects_bool_aliases_after_warmup() -> None:
    from number_compiler.sequences.double_reverse.temporal_border_bank import (
        EDGE_STATES,
    )
    from number_compiler.sequences.double_reverse.temporal_predictive_border import (
        forced_outer_pair_word,
        powered_border_relation,
        reachable_edges,
    )

    edge = next(state for state in EDGE_STATES if 1 in state)
    assert forced_outer_pair_word(edge, 0) == ((edge[0], edge[-1]),)
    powered_border_relation(1)

    boolean_edge = cast(Edge, tuple(True if digit == 1 else digit for digit in edge))
    with pytest.raises(ValueError, match="exact carry-closed"):
        forced_outer_pair_word(boolean_edge, 0)
    with pytest.raises(ValueError, match="exact carry-closed"):
        reachable_edges(boolean_edge, 0)
    with pytest.raises(ValueError, match="0..4096"):
        powered_border_relation(True)
    with pytest.raises(ValueError, match="0..4096"):
        reachable_edges(edge, True)


def _assert_powered_projection_does_not_advance_future_roots(
    generation: int, steps: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    with DoubleReverseTerm(
        196, generation, max_steps=8192, max_state_bits=16384
    ) as term:
        root = term.endpoint_root()

        def forbid_chronological_action(*_args: object, **_kwargs: object) -> None:
            raise AssertionError("powered projection replayed future F actions")

        monkeypatch.setattr(
            type(term.temporal_engine),
            "advance_action",
            forbid_chronological_action,
        )
        packet = source_transfer_packet(term, steps=steps, pair_depth=1)

        assert packet["source_root_local_diagnostic"] == root
        assert packet["physical_ticks"] == steps
        assert packet["chronological_future_roots_constructed"] is False
        assert packet["execution_authority"] is False


def test_double_reverse_powered_relation_from_short_source_skips_future_roots(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _assert_powered_projection_does_not_advance_future_roots(32, 128, monkeypatch)


@pytest.mark.validation
def test_double_reverse_powered_relation_admits_4096_ticks_without_trace_roots(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Keep the long, production-shaped source setup as explicit end-to-end
    # validation. The unit test above checks the same future-root poison on a
    # short authenticated source; the unit suite need not also pay the roughly
    # 21-second generation-1024 endpoint-construction cost.
    _assert_powered_projection_does_not_advance_future_roots(
        1024, MAX_POWERED_PHYSICAL_STEPS, monkeypatch
    )


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
        packet = source_transfer_packet(
            term, steps=2, pair_depth=pair_depth, trace=True
        )

    assert packet["status"] == "available"
    details = packet["trace"]
    assert isinstance(details, dict)
    assert details["source_pair_path"] == tuple(
        _pair(value, pair_depth) for value in expected[::2]
    )
    depth_windows = cast(tuple[dict[str, object], ...], details["depth_windows"])
    assert len(depth_windows) == 1
    assert cast(int, depth_windows[0]["causal_halo_pairs"]) == pair_depth + 2
    assert cast(int, depth_windows[0]["causal_halo_pairs"]) <= 18


def test_double_reverse_transfer_rejects_unsupported_depth_before_source_work(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbid_source_preparation(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("invalid depth reached pointed-source preparation")

    monkeypatch.setattr(
        DoubleReverseTerm, "prepare_bank_source", forbid_source_preparation
    )
    with (
        DoubleReverseTerm(196, 2, max_state_bits=16384) as term,
        pytest.raises(ValueError, match="pair depth"),
    ):
        source_transfer_packet(term, steps=2, pair_depth=17)
