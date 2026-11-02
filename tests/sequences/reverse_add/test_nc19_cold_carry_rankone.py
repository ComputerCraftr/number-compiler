"""Independent cold-path checks for issued carry folds and rank-one powers."""

from __future__ import annotations

from collections.abc import Callable
from random import Random

import pytest

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.run_pairing import pair_mirror_digit_runs
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add import temporal_accumulator99
from number_compiler.sequences.reverse_add import (
    temporal_laurent_accumulator as laurent,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.temporal_accumulator99 import (
    PoweredAccumulator99,
    RankOneAccumulatorAction99,
)
from number_compiler.sequences.reverse_add.temporal_port_quotient import (
    AlignedCarryPort,
    DecimalRunProjection,
    SymmetricCoefficientPort,
    decimal_run_residues,
)
from number_compiler.sequences.reverse_add.temporal_residue99 import (
    reverse_decimal_and_width,
)
from tests.support.reverse_add_accumulator import (
    assert_accumulator99_cache_lifecycle,
)


def _digits(value: int) -> tuple[int, ...]:
    return tuple(int(character) for character in str(value)[::-1])


def _reverse(value: int) -> int:
    return int(str(value)[::-1])


@pytest.mark.parametrize("width", (1, 2, 3, 5, 8, 16, 33, 65))
def test_internal_carry_mask_matches_expanded_binary_word(width: int) -> None:
    random = Random(1777 * width)
    for _ in range(60):
        switches = tuple(
            position for position in range(1, width + 1) if random.randrange(2)
        )
        port = AlignedCarryPort(width, switches)
        carry = 0
        outgoing: list[int] = []
        switch_set = set(switches)
        for position in range(1, width + 1):
            if position in switch_set:
                carry ^= 1
            outgoing.append(carry)
        expected = int("".join(str(bit) for bit in outgoing[:-1]) or "0")
        assert port.growth == outgoing[-1]
        for modulus in (7, 9, 11, 99, 198, 1386):
            residue, visits, operand_bits = port.internal_carry_mask_mod(modulus)
            assert residue == expected % modulus
            assert visits == len(switches)
            assert operand_bits >= 0


def test_successor_rle_matches_literal_and_shared_general_pairer() -> None:
    random = Random(196)
    seeds = [0, 1, 95, 168, 196, 100067, 100760, 60744805]
    seeds.extend(random.randrange(1, 10**10) for _ in range(40))
    for seed in seeds:
        value = seed
        port = SymmetricCoefficientPort.from_source_digits(_digits(seed))
        for _ in range(10):
            step = port.successor_with_carry()
            value += _reverse(value)
            expected = SymmetricCoefficientPort.from_source_digits(_digits(value))
            publicly_paired, odd, _visits = pair_mirror_digit_runs(
                step.normalized_digits_lsd, half_only=True
            )
            assert step.target == expected
            assert step.target.half_runs == publicly_paired
            assert odd == bool(step.carry.target_width & 1)
            port = step.target


@pytest.mark.parametrize("seed", (1, 79, 168, 196, 100067))
@pytest.mark.parametrize("generation", (0, 1, 2, 9, 33, 64))
def test_laurent_reuses_issued_carry_without_successor_tape_rescans(
    seed: int,
    generation: int,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = decimal_run_residues
    calls = 0

    def checked(
        runs: tuple[tuple[int, int], ...], modulus: int
    ) -> DecimalRunProjection:
        nonlocal calls
        calls += 1
        if calls > 1:
            raise AssertionError("Laurent carry fold rescanned a successor digit tape")
        return original(runs, modulus)

    monkeypatch.setattr(laurent, "decimal_run_residues", checked)
    result = ReverseAddPoweredTerm(seed, generation).temporal_laurent_accumulator()
    value = seed
    for _ in range(generation):
        value += _reverse(value)
    assert calls == 1
    assert (result.target_mod7, result.target_reverse_mod7) == (
        value % 7,
        _reverse(value) % 7,
    )
    assert (result.target_mod198, result.target_reverse_mod198) == (
        value % 198,
        _reverse(value) % 198,
    )


def test_rank_one_power_matches_chronological_composition_for_every_class() -> None:
    for coupling in range(99):
        action = RankOneAccumulatorAction99((1 + 3 * coupling) % 99, coupling)
        expected = RankOneAccumulatorAction99.identity()
        for exponent in range(17):
            assert action.power(exponent) == expected
            assert action.power(exponent).power(2) == expected.square()
            expected = expected.then(action)
        assert action.square().power(1234567) == action.power(2469134)


def test_mod99_consumers_share_one_term_owned_bootstrap(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = temporal_accumulator99.from_seed_guarded
    issued: list[tuple[int, int, bool]] = []

    def checked(
        seed: int,
        generation: int,
        *,
        ledger: ResourceLedger,
        include_source_reverse: bool = False,
    ) -> PoweredAccumulator99:
        issued.append((seed, generation, include_source_reverse))
        return original(
            seed,
            generation,
            ledger=ledger,
            include_source_reverse=include_source_reverse,
        )

    monkeypatch.setattr(temporal_accumulator99, "from_seed_guarded", checked)
    term = ReverseAddPoweredTerm(196, 2048)
    base = term.temporal_accumulator99()
    assert base.source_reverse_mod99 is None
    moment = term.temporal_moments(modulus=99)
    enriched = term.temporal_accumulator99(include_source_reverse=True)
    assert term.temporal_accumulator99() is base
    source_reverse = enriched.source_reverse_mod99
    assert source_reverse is not None
    assert moment.U == (enriched.reverse_mod99 - source_reverse) % 99
    assert issued == [(196, 2048, False)]
    assert_accumulator99_cache_lifecycle(term)
    term.generation = 2049
    with pytest.raises(ValueError, match="binding"):
        term.temporal_accumulator99()


def test_mod99_cache_never_crosses_term_owners() -> None:
    first = ReverseAddPoweredTerm(196, 2048).temporal_accumulator99()
    second = ReverseAddPoweredTerm(168, 2048).temporal_accumulator99()
    assert first is not second
    assert (first.source_mod99, first.state) != (second.source_mod99, second.state)


def test_mod99_cache_rejects_mutated_frozen_result() -> None:
    term = ReverseAddPoweredTerm(196, 2048)
    result = term.temporal_accumulator99()
    object.__setattr__(result, "integer_mod99", result.integer_mod99 + 1)
    with pytest.raises(ValueError, match="source-bound result"):
        term.temporal_accumulator99()
    term.resource_ledger.evict_query_memos()
    assert (term.resource_ledger.entries, term.resource_ledger.nodes) == (0, 0)


def test_generation_zero_base_demand_does_not_add_a_source_reversal(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original = reverse_decimal_and_width
    calls = 0

    def one_required_endpoint_reversal(
        value: int,
        *,
        before_digit: Callable[[int, int], None] | None = None,
    ) -> tuple[int, int]:
        nonlocal calls
        calls += 1
        if calls > 1:
            raise AssertionError("base demand evaluated an optional source reversal")
        return original(value, before_digit=before_digit)

    monkeypatch.setattr(
        temporal_accumulator99,
        "reverse_decimal_and_width",
        one_required_endpoint_reversal,
    )
    term = ReverseAddPoweredTerm(196, 0)
    base = term.temporal_accumulator99()
    assert base.source_reverse_mod99 is None
    assert calls == 1
    enriched = term.temporal_accumulator99(include_source_reverse=True)
    assert enriched.source_reverse_mod99 == base.reverse_mod99
    assert calls == 1
    assert term.temporal_accumulator99() is base
    term.resource_ledger.evict_query_memos()


def test_mod99_result_does_not_require_optional_retention_budget(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    original_reserve = ResourceLedger.reserve

    def refuse_result_memo(
        ledger: ResourceLedger,
        owner: int,
        entries: int = 0,
        nodes: int = 0,
    ) -> None:
        if ledger.inventory_owner(owner).name.startswith(
            "reverse-accumulator99-cache-"
        ):
            raise BlockContextBudgetExceeded("injected optional memo refusal")
        original_reserve(ledger, owner, entries=entries, nodes=nodes)

    monkeypatch.setattr(ResourceLedger, "reserve", refuse_result_memo)
    term = ReverseAddPoweredTerm(196, 10**12)
    result = term.temporal_accumulator99()
    assert result.integer_mod99 == 22
    assert (term.resource_ledger.entries, term.resource_ledger.nodes) == (0, 0)
