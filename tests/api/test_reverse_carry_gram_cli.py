"""The demanded carry correlation packet follows the selected physical source."""

from __future__ import annotations

import json
from math import comb

import pytest

from number_compiler.api import cli

_MODULUS = 1_000_000_007


def _literal_rows(value: int) -> list[dict[str, object]]:
    digits = [int(digit) for digit in str(value)[::-1]]
    pairs = [digits[i] + digits[-1 - i] for i in range(len(digits))]
    rows: list[dict[str, object]] = []
    for left in (0, 1):
        for right in (0, 1):
            carry = left
            a: list[int] = []
            for pair in pairs:
                a.append(1 - 2 * carry)
                carry = (pair + carry) // 10
            left_exit = carry
            carry = right
            b: list[int] = []
            for pair in reversed(pairs):
                b.append(1 - 2 * carry)
                carry = (pair + carry) // 10
            b.reverse()
            channels = {
                "A": a,
                "B": b,
                "AB": [x * y for x, y in zip(a, b, strict=True)],
                "A_i B_(i+1)": [a[i] * b[i + 1] for i in range(len(a) - 1)],
                "A_(i+1) B_i": [a[i + 1] * b[i] for i in range(len(a) - 1)],
            }
            rows.append(
                {
                    "inlets": [left, right],
                    "outlets": [left_exit, carry],
                    **{
                        name: [
                            sum(comb(i, k) * bit for i, bit in enumerate(bits))
                            % _MODULUS
                            for k in range(3)
                        ]
                        for name, bits in channels.items()
                    },
                }
            )
    return rows


@pytest.mark.parametrize(
    ("seed", "generation"),
    [(0, 0), (0, 1), (599, 0), (599, 1), (599, 3), (196, 3), (10001, 2)],
)
def test_ordered_carry_gram_packet(
    seed: int, generation: int, capsys: pytest.CaptureFixture[str]
) -> None:
    status = cli.main(
        [
            "reverse-add",
            "--seed",
            str(seed),
            "--nth",
            str(generation),
            "--no-value",
            "--info",
            "spatial.carry-gram",
            "--format",
            "json",
        ]
    )
    packet = json.loads(capsys.readouterr().out)
    assert status == 0
    value = seed
    for _ in range(generation):
        value += int(str(value)[::-1])
    observation = packet["info"]["spatial.carry-gram"]
    assert observation["rows"] == _literal_rows(value)
    assert observation["source_generation"] == generation
    assert observation["source_width"] == len(str(value))
    assert observation["source_positions"] == [0, len(str(value))]


def test_other_demands_do_not_build_carry_gram(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.sequences.reverse_add import q19_gram_observation

    def forbidden(*_args: object, **_kwargs: object) -> object:
        raise AssertionError("unrequested carry correlation was evaluated")

    monkeypatch.setattr(q19_gram_observation, "source_carry_gram", forbidden)
    assert (
        cli.main(["reverse-add", "--seed", "599", "--nth", "3", "--info", "metrics"])
        == 0
    )
    capsys.readouterr()


def test_carry_gram_rejects_non_decimal_source(
    capsys: pytest.CaptureFixture[str],
) -> None:
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "599",
                "--base",
                "3",
                "--nth",
                "1",
                "--info",
                "spatial.carry-gram",
            ]
        )
        == 2
    )
    assert "decimal" in capsys.readouterr().err


def test_carry_gram_refusal_releases_source_scratch() -> None:
    from number_compiler.arithmetic.contracts.block_effect import (
        BlockContextBudgetExceeded,
    )
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_gram_observation import (
        source_carry_gram,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(599, 10), base=10)
    try:
        before = (ledger.nodes, ledger.entries)
        ledger.max_nodes = ledger.nodes + 1
        with (
            pytest.raises(BlockContextBudgetExceeded),
            source_carry_gram(owner, owner.initial),
        ):
            raise AssertionError("a refused source must not be projected")
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_carry_gram_interrupted_fold_releases_scratch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_gram_observation import (
        source_carry_gram,
    )
    from number_compiler.sequences.reverse_add.q19_ordered_gram import (
        Q19OrderedGramAction,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(599, 10), base=10)
    try:
        before = ledger.nodes, ledger.entries

        def interrupted(*_args: object, **_kwargs: object) -> object:
            raise RuntimeError("interrupted Gram composition")

        monkeypatch.setattr(Q19OrderedGramAction, "then", interrupted)
        with pytest.raises(RuntimeError, match="interrupted Gram composition"):
            with source_carry_gram(owner, owner.initial):
                raise AssertionError("interrupted action must not publish")
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_carry_gram_folds_repeated_q19_root_without_expansion(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_gram_observation import (
        source_carry_gram,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(1, 10), base=10)
    try:
        repeated = owner.arena.repeat(owner.arena.terminal(2), 128)
        root = owner.arena.concat_many(
            (owner.arena.terminal(19), repeated, owner.arena.terminal(21))
        )
        occurrence = owner.publish(owner.candidate(root, temporal_steps=256))

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("the repeated source was expanded")

        monkeypatch.setattr(owner, "iter_encoded_symbols", forbidden)
        with source_carry_gram(owner, occurrence) as action:
            # Pair value 2 is the field of a 256-digit word of ones.
            assert action.length == 256
            for actual, expected in zip(
                action.rows, _literal_rows(int("1" * 256)), strict=True
            ):
                assert list(actual.a) == expected["A"]
                assert list(actual.b) == expected["B"]
                assert list(actual.ab) == expected["AB"]
                assert list(actual.a_next_b) == expected["A_i B_(i+1)"]
                assert list(actual.next_a_b) == expected["A_(i+1) B_i"]
        assert ledger.counters["reverse_q19_gram_node_visits"] < 20
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0


def test_carry_gram_rejects_foreign_and_stale_source() -> None:
    from dataclasses import replace

    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add.q19_gram_observation import (
        source_carry_gram,
    )
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(599, 10), base=10)
    foreign_ledger = ResourceLedger()
    foreign = ReversePairQ19OutputOwner(foreign_ledger, digits_lsd(599, 10), base=10)
    try:
        before = ledger.nodes, ledger.entries
        for source in (foreign.initial, replace(owner.initial, temporal_steps=2)):
            with (
                pytest.raises((ValueError, RuntimeError)),
                source_carry_gram(owner, source),
            ):
                raise AssertionError("foreign source must not be projected")
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
        foreign.dispose()
        assert ledger.nodes == ledger.entries == 0
        assert foreign_ledger.nodes == foreign_ledger.entries == 0


def test_source_gram_interns_only_three_ordered_carry_domains(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    from number_compiler.sequences.reverse_add.q19_ordered_gram import (
        Q19OrderedGramAction,
    )

    original = Q19OrderedGramAction.atom
    seen: set[int] = set()

    def checked_atom(
        _cls: type[Q19OrderedGramAction], symbol: int, z: int, modulus: int, degree: int
    ) -> Q19OrderedGramAction:
        assert symbol not in seen, "repeated carry-domain atom construction"
        seen.add(symbol)
        return original(symbol, z, modulus, degree)

    monkeypatch.setattr(Q19OrderedGramAction, "atom", classmethod(checked_atom))
    assert (
        cli.main(
            [
                "reverse-add",
                "--seed",
                "109908",
                "--nth",
                "0",
                "--no-value",
                "--info",
                "spatial.carry-gram",
                "--format",
                "json",
            ]
        )
        == 0
    )
    packet = json.loads(capsys.readouterr().out)["info"]["spatial.carry-gram"]
    assert packet["rows"] == _literal_rows(109908)
    assert packet["work"]["conditional_atoms"] == 3
    assert seen == {0, 9, 10}


@pytest.mark.parametrize("symbol", [-1, 22])
def test_carry_gram_rejects_bad_nonmarker_symbol_before_atom(
    symbol: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    from collections.abc import Callable
    from typing import cast

    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.resources.ledger import ResourceLedger
    from number_compiler.sequences.reverse_add import q19_gram_observation
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairQ19OutputOwner,
    )

    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(599, 10), base=10)
    try:
        before = ledger.nodes, ledger.entries

        def malformed(*_args: object, **kwargs: object) -> object:
            terminal = cast(Callable[[int], object], kwargs["terminal_value"])
            return terminal(symbol)

        monkeypatch.setattr(q19_gram_observation, "fold_slp_dag", malformed)
        with pytest.raises(ValueError, match="invalid Q19 source symbol"):
            with q19_gram_observation.source_carry_gram(owner, owner.initial):
                raise AssertionError("bad source must not be projected")
        assert (ledger.nodes, ledger.entries) == before
    finally:
        owner.dispose()
        assert ledger.nodes == ledger.entries == 0
