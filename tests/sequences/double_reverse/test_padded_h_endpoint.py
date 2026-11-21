"""Compare padded H cones with literal reflected multiplication."""

import pytest

from number_compiler.arithmetic.automata.ledgered_slp import LedgerSLPArena
from number_compiler.arithmetic.carry.reflected_h_power import (
    padded_h_endpoint,
    padded_h_publish,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.hashlife.execution.source_image_inventory import (
    SourceImageCandidate,
    SourceImageView,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.metric_keys import arithmetic_carry as carry_keys
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.source_adapter import (
    DoubleReverseAction,
    DoubleReverseSourceAdapter,
)


@pytest.mark.parametrize("multiplier", (2, 5))
@pytest.mark.parametrize("seed", (0, 1, 7, 10, 30, 50, 73, 196, 903939))
def test_padded_h_matches_literal_endpoints(multiplier: int, seed: int) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("padded-h", "scratch")
    value = seed
    for generation in range(21):
        assert (
            padded_h_endpoint(
                seed,
                generation,
                multiplier,
                ledger=ledger,
                scratch_owner=owner,
                max_state_bits=512,
            )
            == value
        )
        assert ledger.account_usage(owner) == (0, 0)
        value = multiplier * int(str(value)[::-1])
    ledger.mark_disposed(owner)


def test_padded_h_rejects_state_budget() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("padded-h", "scratch")
    with pytest.raises(BlockContextBudgetExceeded):
        padded_h_endpoint(
            73, 20, 2, ledger=ledger, scratch_owner=owner, max_state_bits=8
        )
    assert ledger.account_usage(owner) == (0, 0)


@pytest.mark.parametrize("multiplier", (2, 5))
@pytest.mark.parametrize("generation", (0, 1, 2, 10, 127, 128))
@pytest.mark.parametrize("seed", (7, 196))
def test_padded_h_publishes_exact_owned_slp(
    multiplier: int, generation: int, seed: int
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("padded-h", "scratch")
    arena = LedgerSLPArena(ledger, "padded-h-output", "double_reverse_test")
    expected = seed
    for _ in range(generation):
        expected = multiplier * int(str(expected)[::-1])
    root = padded_h_publish(
        seed,
        generation,
        multiplier,
        arena=arena,
        scratch_owner=owner,
        max_state_bits=2048,
    )
    assert arena.materialize(root) == tuple(int(digit) for digit in str(expected))
    assert ledger.account_usage(owner) == (0, 0)
    arena.dispose()
    ledger.mark_disposed(owner)


@pytest.mark.parametrize("after_publication", (False, True))
def test_padded_h_failed_publication_rolls_back_arena(
    after_publication: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("padded-h", "scratch")
    arena = LedgerSLPArena(ledger, "padded-h-output", "double_reverse_test")
    before_nodes = len(arena.nodes)
    before_usage = (ledger.nodes, ledger.entries)
    original = LedgerSLPArena.word

    def fail_word(self: LedgerSLPArena, word: tuple[int, ...] | list[int]) -> int:
        if after_publication:
            original(self, word)
        raise RuntimeError("injected padded publication failure")

    with monkeypatch.context() as patch:
        patch.setattr(LedgerSLPArena, "word", fail_word)
        with pytest.raises(RuntimeError, match="injected padded publication failure"):
            padded_h_publish(
                196, 2, 2, arena=arena, scratch_owner=owner, max_state_bits=512
            )
    assert len(arena.nodes) == before_nodes
    assert (ledger.nodes, ledger.entries) == before_usage
    assert ledger.account_usage(owner) == (0, 0)
    arena.dispose()
    ledger.mark_disposed(owner)


def test_padded_h_resource_refusal_releases_only_its_own_scratch() -> None:
    ledger = ResourceLedger(max_nodes=100, max_cache_entries=100)
    owner = ledger.register("padded-h", "scratch")
    ledger.reserve(owner, entries=3, nodes=3)
    with pytest.raises(BlockContextBudgetExceeded):
        padded_h_endpoint(
            196, 20, 2, ledger=ledger, scratch_owner=owner, max_state_bits=512
        )
    assert ledger.account_usage(owner) == (3, 3)
    ledger.release(owner, entries=3, nodes=3)


def test_padded_candidate_uses_receiving_double_reverse_source() -> None:
    with DoubleReverseTerm(196, 0, max_steps=128) as term:
        term.prepare_endpoint()
        scheduler = object.__getattribute__(term, "_scheduler")
        image = object.__getattribute__(term, "_image")
        adapter = object.__getattribute__(term, "_adapter")
        arena = object.__getattribute__(term, "_arena")
        view = scheduler.source_image_core().view(image)
        candidate = adapter.padded_source_candidate(DoubleReverseAction(128), view)
        expected = 196
        for _ in range(128):
            expected = 2 * int(str(expected)[::-1])
        root = object.__getattribute__(candidate.payload, "root")
        assert arena.materialize(root) == tuple(int(digit) for digit in str(expected))
        assert candidate.extent == 128


def test_wide_non_c0_production_uses_padded_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = 2
    for _ in range(600):
        previous = int(str(seed // 2)[::-1])
        seed = previous if previous % 2 == 0 else 10 * previous
    expected = seed
    for _ in range(256):
        expected = 2 * int(str(expected)[::-1])
    original = DoubleReverseSourceAdapter.padded_source_candidate
    calls = 0

    def tracked(
        self: DoubleReverseSourceAdapter, action: object, source: SourceImageView
    ) -> SourceImageCandidate:
        nonlocal calls
        calls += 1
        return original(self, action, source)

    monkeypatch.setattr(DoubleReverseSourceAdapter, "padded_source_candidate", tracked)
    with DoubleReverseTerm(seed, 256, max_steps=256) as term:
        assert term.materialize(max_bits=4096) == expected
    assert calls == 1


def test_wide_certified_c0_production_does_not_use_padded_endpoint(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = int("17" + "0" * 140 + "88")
    expected = seed
    for _ in range(256):
        expected = 2 * int(str(expected)[::-1])

    def poisoned(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("certified C0 must retain its own producer")

    monkeypatch.setattr(DoubleReverseSourceAdapter, "padded_source_candidate", poisoned)
    with DoubleReverseTerm(seed, 256, max_steps=256) as term:
        assert term.materialize(max_bits=4096) == expected


def test_wide_cached_c0_entry_beyond_probe_bound_keeps_authority(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = int("17" + "0" * 140 + "88")
    with DoubleReverseTerm(seed, 0, max_steps=256) as term:
        term.prepare_endpoint()
        adapter = term.source_adapter
        for _ in range(4):
            adapter.advance_temporal_prefix()
        cursor = adapter.advance_temporal_prefix()
        assert cursor.physical_steps > 512 // len(str(seed))
        assert cursor.certified_phase is not None
        scheduler = object.__getattribute__(term, "_scheduler")
        image = object.__getattribute__(term, "_image")
        view = scheduler.source_image_core().view(image)

        def poisoned(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("cached C0 must retain its authority")

        monkeypatch.setattr(
            DoubleReverseSourceAdapter, "padded_source_candidate", poisoned
        )
        assert adapter.apply_composite(DoubleReverseAction(256), view, None) is not None


@pytest.mark.parametrize("multiplier", (2, 5))
@pytest.mark.parametrize("generation", (127, 128, 256))
def test_padded_h_longer_dyadic_windows(multiplier: int, generation: int) -> None:
    ledger = ResourceLedger()
    owner = ledger.register("padded-h", "scratch")
    value = 196
    for _ in range(generation):
        value = multiplier * int(str(value)[::-1])
    assert (
        padded_h_endpoint(
            196,
            generation,
            multiplier,
            ledger=ledger,
            scratch_owner=owner,
            max_state_bits=2048,
        )
        == value
    )
    assert ledger.account_usage(owner) == (0, 0)
    assert ledger.counters[carry_keys.REFLECTED_H_PRIMITIVE_TRANSITIONS] > 0
    assert ledger.counters[carry_keys.REFLECTED_H_COMPUTED_CONES] > 0
    assert ledger.counters[carry_keys.REFLECTED_H_REUSED_CONES] > 0
