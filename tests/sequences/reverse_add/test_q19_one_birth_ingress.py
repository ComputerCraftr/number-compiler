"""The initial one-birth carry is bound to the complete physical source."""

from __future__ import annotations

from random import Random

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add import q19_one_birth_ingress as ingress
from number_compiler.sequences.reverse_add.border_carry_safety import BorderTile
from number_compiler.sequences.reverse_add.q19_occurrence import (
    ReversePairOutputOccurrence,
)
from number_compiler.sequences.reverse_add.q19_one_birth_ingress import (
    first_birth_inner_carry,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner


def _physical_carry(digits: tuple[int, ...]) -> int:
    source = int("".join(map(str, reversed(digits))))
    born = source + int(str(source)[::-1])
    output = tuple(map(int, str(born)[::-1]))
    assert len(output) == len(digits) + 1
    carry = 0
    for i in range(len(output) - 2):
        carry = (output[i] + output[-1 - i] + carry) // 10
    return carry


def _outward_birth_digits(random: Random, width: int) -> tuple[int, ...]:
    interior = tuple(random.randrange(10) for _ in range(width - 2))
    return (8, *interior, 9)


def test_one_birth_singleton_matches_physical_inlet_and_budget() -> None:
    random = Random(20261127)
    hits = 0
    for width in range(8, 80):
        for _ in range(8):
            digits = _outward_birth_digits(random, width)
            inlet, visited = first_birth_inner_carry(digits, 8192)
            assert 0 <= visited <= width // 2 - 1
            if inlet is not None:
                hits += 1
                assert inlet == _physical_carry(digits)
                if visited > 3:
                    assert first_birth_inner_carry(digits, visited - 1)[0] is None
    assert hits > 500
    assert first_birth_inner_carry((8, 1, 2, 3, 4, 5, 6, 8), 20) == (None, 1)
    assert first_birth_inner_carry((8, 1, 2, 3, 4, 5, 6, 9), 2) == (None, 1)


def test_live_border_uses_all_inlet_singleton_before_second_step(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_Q19_ONE_BIRTH_INGRESS", "1")
    digits = tuple(map(int, "900544455998"[::-1]))  # 196 after 23 physical ticks
    results: list[tuple[tuple[int, ...], int]] = []
    original = first_birth_inner_carry

    def no_inlet(
        _owner: object,
        _source: object,
        _digits: object,
        _border: object,
        _horizon: int,
        _remaining: int,
    ) -> tuple[None, int]:
        return None, 0

    for enable in (False, True):
        with monkeypatch.context() as patch:
            if not enable:
                patch.setattr(
                    ingress,
                    "bound_first_birth_inlet",
                    no_inlet,
                )
            ledger = ResourceLedger()
            owner = ReversePairQ19OutputOwner(ledger, digits, base=10)
            try:
                cert = owner.certify_border_growth(
                    owner.initial, steps=8, window_digits=2
                )
                results.append(
                    (
                        cert.growth_word,
                        ledger.counters["reverse_q19_border_control_edge_transitions"],
                    )
                )
            finally:
                owner.dispose()
            assert ledger.nodes == ledger.entries == 0
    assert original(digits, 8192)[0] in (0, 1)
    assert results[0][0] == results[1][0] == (1, 0, 1, 0, 1, 0, 1, 0)
    assert results[1][1] < results[0][1]


def _all_inlet_carries(pair_word: tuple[int, ...]) -> set[int]:
    result: set[int] = set()
    for inlet in (0, 1):
        low: list[int] = []
        high: list[int] = []
        carry = 0
        for pair in pair_word:
            low.append((pair + carry) % 10)
            carry = (pair + carry) // 10
        carry = inlet
        for pair in reversed(pair_word):
            high.append((pair + carry) % 10)
            carry = (pair + carry) // 10
        high.reverse()
        emitted = [low[i] + (1 if i == 0 else high[i - 1]) for i in range(len(low))]
        for inward in (0, 1):
            carry = inward
            for pair in reversed(emitted[2:]):
                carry = (pair + carry) // 10
            result.add(carry)
    return result


def test_singleton_matches_all_four_unconstrained_inlet_choices() -> None:
    random = Random(582311)
    for width in range(8, 60):
        for _ in range(16):
            digits = _outward_birth_digits(random, width)
            actual, _ = first_birth_inner_carry(digits, 8192)
            pairs = tuple(digits[i] + digits[-1 - i] for i in range(width // 2 - 1))
            if actual is not None:
                assert _all_inlet_carries(pairs) == {actual}


def test_equal_outer_pair_prefix_does_not_authorize_the_opposite_inlet() -> None:
    words = (
        (17, 9, 9, 9, 9, 6, 14, 3, 5, 0, 9, 7, 12, 6, 12, 17),
        (17, 9, 9, 9, 9, 14, 1, 5, 4, 3, 7, 0, 7, 18, 8, 1),
    )
    inlets: list[int | None] = []
    for pairs in words:
        low = [min(value, 9) for value in pairs]
        high = [value - digit for value, digit in zip(pairs, low, strict=True)]
        digits = tuple(low + list(reversed(high)))
        inlet, visited = first_birth_inner_carry(digits, 8192)
        assert visited > 5
        assert inlet == _physical_carry(digits)
        inlets.append(inlet)
    assert inlets == [1, 0]


def test_delayed_quiet_controls_do_not_create_future_authority() -> None:
    prefix = (
        17,
        6,
        0,
        2,
        2,
        2,
        2,
        2,
        2,
        11,
        2,
        2,
        2,
        4,
        2,
        14,
        11,
        2,
        8,
        2,
        2,
        2,
        13,
        14,
        2,
        2,
        12,
        2,
        0,
        14,
        6,
        2,
        16,
    )
    for changed, expected in ((False, 279), (True, 261)):
        pairs = list(prefix) + [2] * (220 - len(prefix))
        if changed:
            pairs[44] = 5
        low = [min(value, 9) for value in pairs]
        high = [value - digit for value, digit in zip(pairs, low, strict=True)]
        value = int("".join(map(str, low + high[::-1])))
        source = tuple(map(int, str(value)[::-1]))
        inlet, _ = first_birth_inner_carry(source, 8192)
        assert inlet == _physical_carry(source)
        first = None
        for tick in range(expected + 1):
            successor = value + int(str(value)[::-1])
            if tick % 2 and int(str(value)[0]) + value % 10 == 8:
                if int(str(successor)[0]) + successor % 10 == 16:
                    first = tick
                    break
            value = successor
        assert first == expected


def test_seed196_five_column_failure_precedes_width_divergence() -> None:
    value = 196
    for _ in range(48):
        value += int(str(value)[::-1])
    source = str(value)
    assert tuple(int(source[i]) + int(source[~i]) for i in range(5)) == (
        17,
        4,
        10,
        9,
        4,
    )

    quiet_inlets: list[int] = []
    for _ in range(8):
        quiet_row = str(value + int(str(value)[::-1]))
        assert len(quiet_row) == len(str(value)) + 1
        carry = 0
        for low, high in zip(reversed(quiet_row[1:]), quiet_row[:-1], strict=True):
            carry = (int(low) + int(high) + carry) // 10
        quiet_inlets.append(carry)
        value = int(quiet_row) + int(quiet_row[::-1])
        assert len(str(value)) == len(quiet_row)
    assert quiet_inlets == [1] * 7 + [0]


def test_issued_noninitial_source_authenticates_the_born_inlet(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_Q19_ONE_BIRTH_INGRESS", "1")
    ledger = ResourceLedger()
    digits = tuple(map(int, "130992928913"[::-1]))
    owner = ReversePairQ19OutputOwner(ledger, digits, base=10)
    try:
        source = owner.apply_pair_step(owner.initial)
        emitted = tuple(owner.digit(source, i) for i in range(source.output_width))
        assert "".join(map(str, reversed(emitted))) == "900544455998"
        carry, visits = ingress.bound_first_birth_inlet(
            owner, source, None, BorderTile(2, 90, 98), 2, 8192
        )
        assert visits > 0 and carry == _physical_carry(emitted)
        cert = owner.certify_border_growth(source, steps=5, window_digits=2)
        assert cert.growth_word == (0, 1, 0, 1, 0)
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0


def test_source_transfer_cli_consumes_the_bounded_physical_guard(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    import json

    from number_compiler.api.cli import main

    original = ingress.bound_first_birth_inlet
    accepted: list[int] = []

    def counted(
        owner: ReversePairQ19OutputOwner,
        source: ReversePairOutputOccurrence,
        digits: tuple[int, ...] | None,
        border: BorderTile,
        horizon: int,
        remaining: int,
    ) -> tuple[int | None, int]:
        result = original(owner, source, digits, border, horizon, remaining)
        if result[0] is not None:
            accepted.append(result[0])
        return result

    args = [
        "reverse-add",
        "--seed",
        "82000123499",
        "--nth",
        "1",
        "--no-value",
        "--info",
        "temporal.matrix",
        "--temporal-matrix-kind",
        "source-transfer",
        "--temporal-matrix-steps",
        "2",
        "--temporal-matrix-pair-depth",
        "2",
        "--format",
        "json",
    ]
    monkeypatch.delenv("NUMBER_COMPILER_ENABLE_Q19_ONE_BIRTH_INGRESS", raising=False)
    assert main(args) == 2
    assert "no certified K-digit carry phase" in capsys.readouterr().err
    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_Q19_ONE_BIRTH_INGRESS", "1")
    monkeypatch.setattr(ingress, "bound_first_birth_inlet", counted)
    assert main(args) == 0
    packet = json.loads(capsys.readouterr().out)["info"]["temporal.matrix"]
    assert accepted and packet["status"] == "available"
    value = 82000123499
    source = value + int(str(value)[::-1])
    digits = str(source)
    assert packet["source_pair"] == [int(digits[-3]), int(digits[2])]
    growth: list[int] = []
    for _ in range(2):
        successor = source + int(str(source)[::-1])
        growth.append(int(len(str(successor)) > len(str(source))))
        source = successor
    assert packet["source_width_growth"] == growth
    endpoint = str(source)
    assert [int(endpoint[-3]), int(endpoint[2])] in packet["conditional_endpoint_pairs"]


def test_seed196_bounded_growth_refuses_when_later_boundary_is_ambiguous(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add.q19_border_control import (
        BoundaryControlNotAuthorized,
    )

    monkeypatch.setenv("NUMBER_COMPILER_ENABLE_Q19_ONE_BIRTH_INGRESS", "1")
    ledger = ResourceLedger()
    digits = tuple(map(int, "900544455998"[::-1]))
    owner = ReversePairQ19OutputOwner(ledger, digits, base=10)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=10, window_digits=2
        )
        assert certificate.growth_word == (1, 0, 1, 0, 1, 0, 1, 0, 0, 1)
        assert certificate.final_width == 17
        with pytest.raises(BoundaryControlNotAuthorized, match="alternatives disagree"):
            owner.certify_border_growth(owner.initial, steps=16, window_digits=2)
    finally:
        owner.dispose()
    assert ledger.nodes == ledger.entries == 0
