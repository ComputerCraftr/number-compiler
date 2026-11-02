"""Bounded source-bound Laurent projection and half-tape production checks."""

from __future__ import annotations

from collections.abc import MutableMapping
from dataclasses import replace
from itertools import groupby
from typing import Never, cast

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import reverse_add as metric_keys
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.punctured_temporal import (
    PuncturedTemporalWork,
    one_two_step_pair,
    punctured_pair_runs,
)
from number_compiler.sequences.reverse_add.temporal_matrix import SkewMoment
from number_compiler.sequences.reverse_add.temporal_port_quotient import (
    NativeTransportWidthExceeded,
    SymmetricCoefficientPort,
    native_decimal_string_transport,
)
from tests.support.reference_arithmetic import (
    literal_pair_sum_successor,
    literal_reverse_add,
)


def _runs(symbols: tuple[int, ...]) -> tuple[tuple[int, int], ...]:
    return tuple((symbol, sum(1 for _ in group)) for symbol, group in groupby(symbols))


def _pair_word(digits: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(
        digits[index] + digits[len(digits) - index - 1] for index in range(len(digits))
    )


def _laurent_store(term: ReverseAddPoweredTerm) -> MutableMapping[object, object]:
    cache_owner = next(
        owner.owner
        for owner in term.resource_ledger.inventory()
        if owner.name.startswith("reverse-laurent-result-cache-")
    )
    container = dict(term.resource_ledger.iter_containers())[cache_owner]
    assert isinstance(container, MutableMapping)
    return cast(MutableMapping[object, object], container)


def _refuse_next_ledger_reservation(
    monkeypatch: pytest.MonkeyPatch,
) -> list[bool]:
    original_reserve = ResourceLedger.reserve
    refused = [False]

    def reserve(
        ledger: ResourceLedger,
        owner: int,
        entries: int = 0,
        nodes: int = 0,
    ) -> None:
        owner_name = ledger.inventory_owner(owner).name
        if not refused[0] and owner_name.startswith("reverse-laurent-source-work-"):
            refused[0] = True
            raise BlockContextBudgetExceeded("injected scratch capacity miss")
        original_reserve(ledger, owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(ResourceLedger, "reserve", reserve)
    return refused


def _port_for_seed(seed: int) -> SymmetricCoefficientPort:
    pair = _pair_word(digits_lsd(seed, 10))
    return SymmetricCoefficientPort.from_half_runs(
        _runs(pair[: (len(pair) + 1) // 2]), odd=bool(len(pair) & 1)
    )


def _check_pair_block(seed: int, steps: int) -> PuncturedTemporalWork:
    state = _port_for_seed(seed)
    work = PuncturedTemporalWork()
    result_runs, result_width = punctured_pair_runs(
        state.half_runs, odd=bool(state.width & 1), steps=steps, work=work
    )
    pair = _pair_word(digits_lsd(seed, 10))
    for _ in range(steps):
        pair, _growth = literal_pair_sum_successor(pair)
    assert result_runs == _runs(pair[: (len(pair) + 1) // 2])
    assert result_width == len(pair)
    return work


@pytest.mark.parametrize("seed", (1, 79, 196, 139, 10089, 999999))
@pytest.mark.parametrize("steps", (2, 4, 16))
def test_half_tape_successors_match_independent_pair_reference(
    seed: int, steps: int
) -> None:
    work = _check_pair_block(seed, steps)
    assert work.half_tape_tick_transitions + work.native_decimal_ticks == steps
    assert work.native_decimal_ticks == (steps - 1 if steps >= 16 else 0)
    assert work.two_step_actions == steps // 2
    assert work.event_regions == 0
    assert work.prefix_queries == 0


def test_half_tape_production_does_not_call_event_grid_oracle(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.reverse_add.punctured_temporal as temporal

    state = _port_for_seed(196)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("production half-tape path called the event-grid oracle")

    monkeypatch.setattr(temporal, "one_two_step_pair", forbidden)
    work = temporal.PuncturedTemporalWork()
    punctured_pair_runs(
        state.half_runs,
        odd=bool(state.width & 1),
        steps=2,
        work=work,
    )
    assert work.event_regions == work.prefix_queries == 0
    assert work.half_tape_tick_transitions == 2


def test_t2_half_tape_matches_retained_event_grid_oracle() -> None:
    for seed in (1, 79, 196, 139, 10089):
        source_digits = digits_lsd(seed, 10)
        pair = _pair_word(source_digits)
        half_runs = _runs(pair[: (len(pair) + 1) // 2])
        work = PuncturedTemporalWork()
        actual_half, actual_width = punctured_pair_runs(
            half_runs,
            odd=bool(len(pair) & 1),
            steps=2,
            work=work,
        )
        oracle_half, oracle_width = one_two_step_pair(_runs(pair), work)
        assert actual_half == oracle_half
        assert actual_width == oracle_width


@pytest.mark.parametrize("steps", (17, 33, 65, 129, 258, 513, 516, 1023))
def test_non_dyadic_finite_q19_blocks_match_literal_pair_successors(steps: int) -> None:
    work = _check_pair_block(196, steps)
    assert work.half_tape_tick_transitions == 1
    assert work.native_decimal_ticks == steps - 1
    assert work.two_step_actions == steps // 2


def test_bounded_decimal_string_transport_preserves_global_int_limit() -> None:
    import sys

    before = sys.get_int_max_str_digits()
    result, visits = native_decimal_string_transport("196", 33)
    assert result == str(literal_reverse_add(196, 33))
    assert visits > 0
    assert sys.get_int_max_str_digits() == before
    with pytest.raises(NativeTransportWidthExceeded):
        native_decimal_string_transport("196", 4, max_width=6)


def test_native_width_guard_falls_back_to_exact_half_tape_path(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.reverse_add.punctured_temporal as temporal

    monkeypatch.setattr(temporal, "MAX_EXACT_DECIMAL_BLOCK_WIDTH", 1)
    work = _check_pair_block(196, 16)
    assert work.half_tape_tick_transitions == 16
    assert work.native_decimal_ticks == 0


@pytest.mark.parametrize("seed", (0, 1, 79, 196, 139, 10089))
@pytest.mark.parametrize("generation", (0, 1, 2, 7, 16, 32))
def test_laurent_modular_matrices_match_literal_source(
    seed: int, generation: int
) -> None:
    term = ReverseAddPoweredTerm(seed, generation)
    endpoint = literal_reverse_add(seed, generation)
    source_reverse = int(str(seed)[::-1])
    endpoint_reverse = int(str(endpoint)[::-1])
    first, second = seed, 0
    previous_u = seed
    current = seed
    for tick in range(generation):
        current = literal_reverse_add(current, 1)
        following_u = current if (tick + 1) % 2 == 0 else int(str(current)[::-1])
        if tick % 2 == 0:
            second += following_u - previous_u
        else:
            first += following_u - previous_u
        previous_u = following_u
    try:
        for modulus in (7, 198):
            expected = SkewMoment(
                generation,
                (endpoint_reverse - source_reverse) % modulus,
                (endpoint - seed - generation * source_reverse) % modulus,
                modulus,
            )
            assert term.temporal_moments(modulus=modulus) == expected
        result = term.temporal_laurent_accumulator()
        assert result.target_mod7 == endpoint % 7
        assert result.target_reverse_mod7 == endpoint_reverse % 7
        assert result.target_mod198 == endpoint % 198
        assert result.target_reverse_mod198 == endpoint_reverse % 198
        assert result.first_accumulator_mod7 == first % 7
        assert result.second_accumulator_mod7 == second % 7
        assert result.first_accumulator_mod198 == first % 198
        assert result.second_accumulator_mod198 == second % 198
        assert term.published_workspace is None
        if generation:
            assert (
                term.resource_ledger.counters[metric_keys.REVERSE_LAURENT_CACHE_MISSES]
                == 1
            )
            assert (
                term.resource_ledger.counters[metric_keys.REVERSE_LAURENT_CACHE_HITS]
                == 2
            )
            assert term.resource_ledger.counters.get(
                metric_keys.REVERSE_LAURENT_SOURCE_TICKS, 0
            ) == (0 if seed == 0 else generation)
    finally:
        workspace = term.published_workspace
        if workspace is not None:
            workspace.dispose()


def test_laurent_horizon_uses_exact_q19_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add import pair_numeric_ports
    from number_compiler.sequences.reverse_add.pair_numeric_ports import (
        ReversePairNumericProjection,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )

    term = ReverseAddPoweredTerm(196, 4098)
    bounded_term = ReverseAddPoweredTerm(196, 1)
    owner, occurrence, used_cache, reused_work = bounded_term.completed_q19_occurrence()
    projected_occurrence = replace(occurrence, temporal_steps=4098)

    def forbidden_laurent(_term: ReverseAddPoweredTerm) -> Never:
        raise AssertionError("finite Laurent path exceeded its admitted horizon")

    def completed_q19(
        _term: ReverseAddPoweredTerm,
    ) -> tuple[ReversePairQ19OutputOwner, ReversePairOutputOccurrence, bool, int]:
        return owner, projected_occurrence, used_cache, reused_work

    def exact_projection(
        _owner: ReversePairQ19OutputOwner,
        _occurrence: ReversePairOutputOccurrence,
        *,
        modulus: int,
    ) -> ReversePairNumericProjection:
        return ReversePairNumericProjection(
            modulus=modulus,
            output_width=5,
            target_mod=123 % modulus,
            reverse_target_mod=456 % modulus,
            pair_carry_out=0,
            q19_root=0,
            temporal_steps=4098,
        )

    monkeypatch.setattr(
        ReverseAddPoweredTerm, "temporal_laurent_accumulator", forbidden_laurent
    )
    monkeypatch.setattr(
        ReverseAddPoweredTerm, "completed_q19_occurrence", completed_q19
    )
    monkeypatch.setattr(pair_numeric_ports, "project_q19_numeric", exact_projection)

    try:
        assert term.temporal_moments(modulus=7) == SkewMoment(
            4098,
            (456 - 691) % 7,
            (123 - 196 - 4098 * 691) % 7,
            7,
        )
        assert term.published_workspace is None
        assert (
            term.resource_ledger.counters.get(
                metric_keys.REVERSE_LAURENT_SOURCE_TICKS, 0
            )
            == 0
        )
    finally:
        workspace = bounded_term.published_workspace
        if workspace is not None:
            workspace.dispose()


@pytest.mark.parametrize("modulus", (7, 198))
def test_optional_laurent_capacity_miss_uses_exact_q19_fallback(
    monkeypatch: pytest.MonkeyPatch, modulus: int
) -> None:
    term = ReverseAddPoweredTerm(196, 4)
    refused = _refuse_next_ledger_reservation(monkeypatch)
    endpoint = literal_reverse_add(term.seed, term.generation)
    source_reverse = int(str(term.seed)[::-1])
    endpoint_reverse = int(str(endpoint)[::-1])
    expected = SkewMoment(
        term.generation,
        (endpoint_reverse - source_reverse) % modulus,
        (endpoint - term.seed - term.generation * source_reverse) % modulus,
        modulus,
    )

    try:
        assert term.temporal_moments(modulus=modulus) == expected
        assert refused[0]
        assert term.published_workspace is not None
        assert (
            term.resource_ledger.counters.get(
                metric_keys.REVERSE_LAURENT_SOURCE_TICKS, 0
            )
            == 0
        )
    finally:
        workspace = term.published_workspace
        if workspace is not None:
            workspace.dispose()


def test_optional_laurent_capacity_miss_does_not_accept_forged_q19_duration(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )

    term = ReverseAddPoweredTerm(196, 1)
    owner, occurrence, used_cache, reused_work = term.completed_q19_occurrence()
    forged_occurrence = replace(occurrence, temporal_steps=2)
    refused = _refuse_next_ledger_reservation(monkeypatch)

    def forged_q19(
        _term: ReverseAddPoweredTerm,
    ) -> tuple[ReversePairQ19OutputOwner, ReversePairOutputOccurrence, bool, int]:
        return owner, forged_occurrence, used_cache, reused_work

    monkeypatch.setattr(ReverseAddPoweredTerm, "completed_q19_occurrence", forged_q19)
    try:
        with pytest.raises(ValueError, match="temporal duration"):
            term.temporal_moments(modulus=7)
        assert refused[0]
    finally:
        workspace = term.published_workspace
        if workspace is not None:
            workspace.dispose()


def test_scratch_budget_is_reserved_before_seed_digit_decode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import number_compiler.sequences.reverse_add.temporal_laurent_accumulator as laurent

    term = ReverseAddPoweredTerm(196, 4, max_context_nodes=64)

    def forbidden(*_args: object, **_kwargs: object) -> tuple[int, ...]:
        raise AssertionError("seed digits were decoded before scratch admission")

    monkeypatch.setattr(laurent, "digits_lsd", forbidden)
    with pytest.raises(BlockContextBudgetExceeded):
        term.temporal_laurent_accumulator()
    assert (
        term.resource_ledger.counters.get(metric_keys.REVERSE_LAURENT_SOURCE_TICKS, 0)
        == 0
    )
    assert term.published_workspace is None


def test_laurent_query_memo_recomputes_after_ledger_eviction() -> None:
    term = ReverseAddPoweredTerm(196, 4)
    first = term.temporal_laurent_accumulator()
    evicted = term.resource_ledger.evict_query_memos()
    assert evicted

    second = term.temporal_laurent_accumulator()
    counters = term.resource_ledger.counters
    assert second == first
    assert counters[metric_keys.REVERSE_LAURENT_CACHE_MISSES] == 2
    assert counters.get(metric_keys.REVERSE_LAURENT_CACHE_HITS, 0) == 0
    assert counters[metric_keys.REVERSE_LAURENT_SOURCE_TICKS] == 8
    assert term.published_workspace is None


def test_laurent_query_memo_reissues_after_owner_disposal() -> None:
    from number_compiler.resources.owned_memo import OwnedMemo

    term = ReverseAddPoweredTerm(196, 4)
    first = term.temporal_laurent_accumulator()
    for candidate in term.resource_ledger.iter_execution_roots():
        if isinstance(candidate, OwnedMemo):
            cast(OwnedMemo[object, object], candidate).dispose()
            break
    else:
        pytest.fail("Laurent result did not publish a ledger-owned memo")

    second = term.temporal_laurent_accumulator()
    counters = term.resource_ledger.counters
    assert second == first
    assert counters[metric_keys.REVERSE_LAURENT_CACHE_MISSES] == 2
    assert counters.get(metric_keys.REVERSE_LAURENT_CACHE_HITS, 0) == 0
    assert counters[metric_keys.REVERSE_LAURENT_SOURCE_TICKS] == 8


def test_laurent_memo_rejects_foreign_same_type_observation() -> None:
    first_term = ReverseAddPoweredTerm(79, 4)
    second_term = ReverseAddPoweredTerm(196, 4)
    first_result = first_term.temporal_laurent_accumulator()
    foreign_result = second_term.temporal_laurent_accumulator()
    first_store = _laurent_store(first_term)
    second_store = _laurent_store(second_term)
    original_entry = first_store[None]

    first_store[None] = foreign_result
    try:
        with pytest.raises(TypeError, match="foreign entry"):
            first_term.temporal_laurent_accumulator()

        first_store[None] = second_store[None]
        with pytest.raises(ValueError, match="foreign source binding"):
            first_term.temporal_laurent_accumulator()
    finally:
        first_store[None] = original_entry

    assert first_term.temporal_laurent_accumulator() is first_result


def test_laurent_memo_rejects_mutated_same_generation_result() -> None:
    term = ReverseAddPoweredTerm(196, 4)
    result = term.temporal_laurent_accumulator()
    original = result.target_mod7
    object.__setattr__(result, "target_mod7", (original + 1) % 7)
    with pytest.raises(ValueError, match="changed after publication"):
        term.temporal_laurent_accumulator()
    object.__setattr__(result, "target_mod7", original)
    assert term.temporal_laurent_accumulator() is result


def test_zero_seed_fixed_point_does_not_expand_a_temporal_tape() -> None:
    term = ReverseAddPoweredTerm(0, 100_000)
    assert term.temporal_moments(modulus=198) == SkewMoment(100_000, 0, 0, 198)
    assert (
        term.resource_ledger.counters.get(metric_keys.REVERSE_LAURENT_SOURCE_TICKS, 0)
        == 0
    )
    assert term.published_workspace is None
