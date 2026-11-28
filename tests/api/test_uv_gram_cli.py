"""Source-first U/V admission for the demanded Q19 carry Gram packet."""

from __future__ import annotations

import json
from typing import cast

import pytest

from number_compiler.api import cli
from tests.support.q19_tiles import U as _U
from tests.support.q19_tiles import V as _V
from tests.support.q19_tiles import physical_seed as _seed


def _cli(
    seed: str, capsys: pytest.CaptureFixture[str], generation: int = 3
) -> dict[str, object]:
    status = cli.main(
        [
            "reverse-add",
            "--seed",
            seed,
            "--nth",
            str(generation),
            "--no-value",
            "--info",
            "spatial.carry-gram",
            "--format",
            "json",
        ]
    )
    output = capsys.readouterr()
    assert status == 0, output.err
    packet: dict[str, object] = json.loads(output.out)
    return packet


def _pop_work(packet: dict[str, object]) -> dict[str, int]:
    info = cast(dict[str, object], packet["info"])
    observation = cast(dict[str, object], info["spatial.carry-gram"])
    return cast(dict[str, int], observation.pop("work"))


@pytest.mark.parametrize("generation", (3, 9))
@pytest.mark.parametrize("word", [_U, _V, _U + _U, _U + _V, _V + _U, _V + _V])
def test_prechild_uv_cli_matches_complete_packet(
    word: tuple[int, ...],
    generation: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    seed = _seed(word)
    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_UV_GRAM", raising=False)
    expected = _cli(seed, capsys, generation)
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_UV_GRAM", "1")

    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("admitted source opened its temporal child")

    monkeypatch.setattr(ReverseAddPoweredTerm, "completed_q19_occurrence", forbidden)
    monkeypatch.setattr(ReversePairQ19OutputOwner, "apply_pair_step", forbidden)
    actual = _cli(seed, capsys, generation)
    actual_work = _pop_work(actual)
    _pop_work(expected)
    assert actual_work["source_guard_nodes"] > 0
    assert actual_work["source_guard_transitions"] > actual_work["source_guard_nodes"]
    assert actual_work["source_guard_precheck_reads"] == 7
    assert actual_work["physical_ticks_skipped"] == generation
    assert actual == expected


@pytest.mark.parametrize(("position", "precheck_reads"), [(12, 7), (0, 3)])
def test_unadmitted_source_uses_exact_fallback(
    position: int,
    precheck_reads: int,
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    mutated = _U[:position] + (_U[position] + 9,) + _U[position + 1 :]
    seed = _seed(mutated)
    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_UV_GRAM", raising=False)
    expected = _cli(seed, capsys)
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_UV_GRAM", "1")
    actual = _cli(seed, capsys)
    actual_work = _pop_work(actual)
    fallback_work = _pop_work(expected)
    assert actual_work["source_guard_precheck_reads"] == precheck_reads
    if precheck_reads == 7:
        assert actual_work["source_guard_nodes"] > 0
        assert (
            actual_work["source_guard_transitions"] > actual_work["source_guard_nodes"]
        )
    else:
        assert actual_work["source_guard_nodes"] == 0
        assert actual_work["source_guard_transitions"] == 0
    assert actual_work["source_nodes"] == (
        actual_work["source_guard_nodes"] + fallback_work["source_nodes"]
    )
    assert actual_work["physical_ticks_skipped"] == 0
    assert actual == expected


def test_preflight_capacity_refusal_releases_reservation() -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_uv_gram import source_uv_gram

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(int(_seed(_U)), 10), base=10)
    try:
        before = ledger.nodes, ledger.entries
        ledger.max_nodes = ledger.nodes + 1
        with source_uv_gram(owner, owner.initial) as action:
            assert action is None
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_malformed_source_symbol_refuses_without_index_alias(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add import q19_uv_gram
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(int(_seed(_U)), 10), base=10)
    try:
        before = ledger.nodes, ledger.entries

        def forged(*_args: object, **kwargs: object) -> object:
            terminal = kwargs["terminal_value"]
            assert callable(terminal)
            return terminal(-1)

        monkeypatch.setattr(q19_uv_gram, "fold_slp_dag", forged)
        with pytest.raises(ValueError, match="invalid Q19 source symbol"):
            with q19_uv_gram.source_uv_gram(owner, owner.initial):
                pass
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_foreign_or_mutated_source_is_rejected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add import q19_uv_gram
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(int(_seed(_U)), 10), base=10)
    foreign = ReversePairQ19OutputOwner(ledger, digits_lsd(int(_seed(_U)), 10), base=10)
    try:
        with pytest.raises(ValueError):
            with q19_uv_gram.source_uv_gram(owner, foreign.initial):
                pass

        before = ledger.nodes, ledger.entries
        original = q19_uv_gram._then  # pyright: ignore[reportPrivateUsage]

        def change_generation(
            first: tuple[int, ...], later: tuple[int, ...]
        ) -> tuple[int, ...]:
            result = original(first, later)
            owner.arena._invalidate_node_ids()  # pyright: ignore[reportPrivateUsage]
            return result

        monkeypatch.setattr(q19_uv_gram, "_then", change_generation)
        with pytest.raises(ValueError, match="source grammar changed"):
            with q19_uv_gram.source_uv_gram(owner, owner.initial):
                pass
        assert (ledger.nodes, ledger.entries) == before
    finally:
        foreign.dispose()
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_cancelled_uv_composition_releases_source_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_ordered_gram import (
        Q19OrderedGramAction,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_uv_gram import source_uv_gram

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(int(_seed(_U)), 10), base=10)
    try:
        before = ledger.nodes, ledger.entries

        def cancelled(*_args: object, **_kwargs: object) -> object:
            raise RuntimeError("cancelled ordered action")

        monkeypatch.setattr(Q19OrderedGramAction, "then", cancelled)
        with pytest.raises(RuntimeError, match="cancelled ordered action"):
            with source_uv_gram(owner, owner.initial):
                pass
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_midfold_budget_failure_propagates_and_releases_scratch() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_uv_gram import source_uv_gram

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(int(_seed(_U)), 10), base=10)
    try:
        before = ledger.nodes, ledger.entries
        width_limbs = max(1, (owner.initial.pair_width.bit_length() + 63) // 64)
        ledger.max_nodes = ledger.nodes + 46 * 128 + 2048 + 64 * width_limbs + 1
        with pytest.raises(BlockContextBudgetExceeded):
            with source_uv_gram(owner, owner.initial):
                pass
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_precheck_source_generation_mutation_does_not_fall_back(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )
    from number_compiler.sequences.reverse_add.q19_uv_gram import source_uv_gram

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(int(_seed(_U)), 10), base=10)
    try:
        before = ledger.nodes, ledger.entries
        original = owner.symbol_at

        def changed(root: int, index: int) -> int:
            value = original(root, index)
            owner.arena._invalidate_node_ids()  # pyright: ignore[reportPrivateUsage]
            return value + 1

        monkeypatch.setattr(owner, "symbol_at", changed)
        with pytest.raises(ValueError, match="source grammar changed"):
            with source_uv_gram(owner, owner.initial):
                raise AssertionError("stale admission must not fall back")
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_uv_alphabet_builds_each_state_symbol_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add import q19_uv_gram

    original = q19_uv_gram._transition  # pyright: ignore[reportPrivateUsage]
    calls = 0

    def counted(state: tuple[int, int, int], symbol: int) -> tuple[int, int, int]:
        nonlocal calls
        calls += 1
        return original(state, symbol)

    monkeypatch.setattr(q19_uv_gram, "_transition", counted)
    alphabet = q19_uv_gram._alphabet()  # pyright: ignore[reportPrivateUsage]
    identity, atoms, _accepted = alphabet
    assert calls == 22 * len(identity)
    assert len(atoms) == 22
    assert all(len(column) == len(identity) for column in atoms)
