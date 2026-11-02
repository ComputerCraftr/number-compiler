"""Source-certified Moore quotient, not an eager Q19 endpoint observer."""

from __future__ import annotations

import json

import pytest

from number_compiler.api import cli, cli_render
from number_compiler.api.cli_requests import parse_request
from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.resources.metric_keys import reverse_add as reverse_add_metrics
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.temporal_accumulator99 import (
    AccumulatorMooreState99,
    AccumulatorStateKey99,
    RankOneAccumulatorAction99,
    from_seed,
)
from number_compiler.sequences.reverse_add.temporal_residue99 import (
    from_seed as scalar99,
)
from tests.support.reverse_add_accumulator import (
    assert_accumulator99_cache_lifecycle,
)


def _oracle(seed: int, steps: int) -> tuple[int, int, int, int]:
    x = u = a = seed
    b = 0
    for n in range(steps):
        y = x + int(str(x)[::-1])
        nxt = y if (n + 1) % 2 == 0 else int(str(y)[::-1])
        if n & 1:
            a += nxt - u
        else:
            b += nxt - u
        x, u = y, nxt
    return x, int(str(x)[::-1]), a, b


@pytest.mark.parametrize("seed", [0, 1, 11, 168, 196, 99, 250, 999, 123456])
def test_all_bootstrap_phases_and_physical_parity(seed: int) -> None:
    for n in range(35):
        q = from_seed(seed, n)
        x, reverse, a, b = _oracle(seed, n)
        assert (q.state.a, q.state.b) == (a % 99, b % 99)
        assert (q.integer_mod99, q.reverse_mod99) == (x % 99, reverse % 99)
        assert q.integer_mod99 == scalar99(seed, n).target_mod99
        if q.absorbed_mod11:
            assert q.state.sum_mod99 == x % 99
            assert q.state.successor() == from_seed(seed, n + 1).state


def test_source_196_uses_exact_rank_one_matrix_and_pointed_18_cycle() -> None:
    assert from_seed(196, 4).state.semantic_id == AccumulatorStateKey99(0, 5, 17)
    assert from_seed(196, 6).state.semantic_id == AccumulatorStateKey99(0, 49, 39)
    for n in range(4, 4 + 54):
        q = from_seed(196, n)
        assert q.state == from_seed(196, n + 18).state
    assert len({from_seed(196, n).state.future_class_id for n in range(4, 22)}) == 18
    assert from_seed(196, 4).sum_mod99 == from_seed(196, 10).sum_mod99
    assert from_seed(196, 4).difference_mod99 != from_seed(196, 10).difference_mod99


def test_matrix_right_congruence_and_minimal_phase_merger() -> None:
    N = RankOneAccumulatorAction99.two_steps()
    for a in range(99):
        for b in range(99):
            zero = (a + b) % 99 == 0
            even = AccumulatorMooreState99(0, a, b)
            odd = AccumulatorMooreState99(1, a, b)
            assert (even.future_class_id == odd.future_class_id) is zero
            if zero:
                assert (
                    even.successor().future_class_id == odd.successor().future_class_id
                )
            else:
                assert (even.successor().a, even.successor().b) != (
                    odd.successor().a,
                    odd.successor().b,
                )
            assert N.apply(even) == even.successor().successor()
    for n in [0, 1, 2, 3, 9, 128, 10**6]:
        powered = N.power(n)
        # 4**n mod 297, then exact division by 3, stays bounded.
        h = ((pow(4, n, 297) - 1) // 3) % 99
        assert powered.coupling == h
        assert powered.multiplier == (1 + 3 * h) % 99
        assert N.power(2 * n) == powered.square()


def test_modular_matrix_and_accumulator_cli_do_not_construct_q19(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("the modular right congruence must bypass Q19")

    monkeypatch.setattr(ReverseAddPoweredTerm, "source_workspace", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "completed_q19_occurrence", forbidden)
    monkeypatch.setattr(cli_render, "render_value", forbidden)
    n = 10**12
    for info, extra in [
        ("temporal.accumulator99", []),
        (
            "temporal.matrix",
            ["--temporal-matrix-kind", "innovation", "--temporal-matrix-modulus", "99"],
        ),
    ]:
        assert (
            cli.main(
                [
                    "reverse-add",
                    "--seed",
                    "196",
                    "--nth",
                    str(n),
                    "--no-value",
                    "--info",
                    info,
                    *extra,
                    "--format",
                    "json",
                ]
            )
            == 0
        )
        packet = json.loads(capsys.readouterr().out)
        assert packet["value"] is None
        if info == "temporal.accumulator99":
            row = packet["info"][info]
            assert row["bootstrap_generation"] == 4
            assert row["even_blocks_powered"] == (n - 4) // 2
            assert row["complete_integer_certified"] is False
            assert row["integer_mod99"] == 22
            assert row["difference_mod99"] == 54
        else:
            row = packet["info"][info]
            assert row["modulus"] == 99
            assert row["execution_authority"] is False


def test_nondecimal_rejected_for_accumulator_projection() -> None:
    with pytest.raises(ValueError, match="decimal"):
        parse_request(
            [
                "reverse-add",
                "--seed",
                "196",
                "--base",
                "19",
                "--nth",
                "17",
                "--info",
                "temporal.accumulator99",
            ]
        )


def test_production_accumulator_bounds_source_before_decimal_scan(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.reverse_add.temporal_accumulator99 as accumulator

    def forbidden(*args: object, **kwargs: object) -> tuple[int, int]:
        raise AssertionError("source admission must precede decimal reversal")

    monkeypatch.setattr(accumulator, "reverse_decimal_and_width", forbidden)
    import number_compiler.sequences.reverse_add.temporal_matrix as temporal_matrix

    monkeypatch.setattr(temporal_matrix, "reverse_decimal_and_width", forbidden)
    term = ReverseAddPoweredTerm(10**4096, 10**12)
    with pytest.raises(ValueError, match="exceeds 4096 digits"):
        term.temporal_moments(modulus=99)
    ledger = term.resource_ledger
    assert (ledger.entries, ledger.nodes) == (0, 0)
    assert (
        ledger.counters[reverse_add_metrics.REVERSE_ACCUMULATOR99_BOOTSTRAP_FAILED_WORK]
        == 1
    )


def test_production_accumulator_reservation_rolls_back_on_budget_and_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.reverse_add.temporal_accumulator99 as accumulator

    limited = ReverseAddPoweredTerm(196, 10**12, max_context_nodes=0)
    with pytest.raises(BlockContextBudgetExceeded):
        limited.temporal_accumulator99()
    assert (limited.resource_ledger.entries, limited.resource_ledger.nodes) == (0, 0)
    assert (
        limited.resource_ledger.counters[
            reverse_add_metrics.REVERSE_ACCUMULATOR99_BOOTSTRAP_FAILED_WORK
        ]
        == 1
    )

    failing = ReverseAddPoweredTerm(196, 10**12)

    def fail_during_scan(*args: object, **kwargs: object) -> tuple[int, int]:
        raise RuntimeError("injected reversal failure")

    monkeypatch.setattr(accumulator, "reverse_decimal_and_width", fail_during_scan)
    with pytest.raises(RuntimeError, match="injected reversal failure"):
        failing.temporal_accumulator99()
    assert (failing.resource_ledger.entries, failing.resource_ledger.nodes) == (0, 0)
    assert (
        failing.resource_ledger.counters[
            reverse_add_metrics.REVERSE_ACCUMULATOR99_BOOTSTRAP_FAILED_WORK
        ]
        == 1
    )


def test_guarded_accumulator_preserves_trillion_generation_and_releases_scratch() -> (
    None
):
    term = ReverseAddPoweredTerm(196, 10**12)
    result = term.temporal_accumulator99(include_source_reverse=True)
    assert result.integer_mod99 == 22
    assert result.source_reverse_mod99 == 691 % 99
    # Bootstrap scratch is gone; only the bounded, evictable source-bound
    # result memo remains for another observer on this same term.
    assert term.resource_ledger.entries == 1
    assert term.resource_ledger.nodes == 40
    assert (
        term.resource_ledger.counters[
            reverse_add_metrics.REVERSE_ACCUMULATOR99_BOOTSTRAP_DIGIT_STEPS
        ]
        > 0
    )
    assert term.resource_ledger.evict_query_memos()
    assert (term.resource_ledger.entries, term.resource_ledger.nodes) == (0, 0)


def test_huge_index_mod99_matrix_uses_charged_residue_factors() -> None:
    from number_compiler.sequences.reverse_add.temporal_matrix import (
        source_bound_modular_moments,
    )

    generation = 10**250 + 18
    term = ReverseAddPoweredTerm(196, generation)
    result = source_bound_modular_moments(term, modulus=99)
    target = 22 * pow(2, generation - 4, 99) % 99
    source = 196 % 99
    source_reverse = 691 % 99

    assert (result.U, result.V, result.modulus) == (
        (target - source_reverse) % 99,
        (target - source - (generation % 99) * source_reverse) % 99,
        99,
    )
    assert (
        term.resource_ledger.counters[
            reverse_add_metrics.REVERSE_ACCUMULATOR99_BOOTSTRAP_OPERAND_BITS
        ]
        >= generation.bit_length()
    )
    assert_accumulator99_cache_lifecycle(term)
