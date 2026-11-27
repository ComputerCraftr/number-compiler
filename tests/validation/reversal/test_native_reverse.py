"""Exact endpoint and accounting checks for an explicitly built native wheel."""

from __future__ import annotations

import random
from importlib import import_module

import pytest

from number_compiler.arithmetic.carry.native_reverse_actions import (
    DiagonalWork,
    diagonal_endpoint,
    guard_projection,
    native_pair_action,
)
from number_compiler.resources.ledger import ResourceLedger

pytestmark = pytest.mark.validation


def _literal(seed: int, multiplier: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        reverse = int(str(value)[::-1])
        value = value + reverse if multiplier == 1 else multiplier * reverse
    return value


def _pairs(value: int) -> bytes:
    digits = str(value)
    return bytes(int(a) + int(b) for a, b in zip(digits, reversed(digits), strict=True))


def test_diagonal_outputs_match_independent_physical_steps() -> None:
    native = import_module("number_compiler.kernels._reverse_quotients")
    random_source = random.Random(43)
    for multiplier in (2, 5):
        for side in (3, 4):
            for seed in (0, 6, 30, 50, 196, 1960, 10**20, 10**20 - 1):
                for steps in (0, 1, 2, 3, 15, 22, 64):
                    digits, _work = native.multiply(str(seed), multiplier, steps, side)
                    assert int(digits) == _literal(seed, multiplier, steps)
            for _ in range(32):
                seed = random_source.randrange(10**30)
                steps = random_source.randrange(1, 100)
                digits, _work = native.multiply(str(seed), multiplier, steps, side)
                assert int(digits) == _literal(seed, multiplier, steps)


@pytest.mark.parametrize("multiplier", [2, 5])
def test_even_square_composes_the_odd_base_table(multiplier: int) -> None:
    native = import_module("number_compiler.kernels._reverse_quotients")
    seed = 50100
    for steps in (0, 13, 14):
        digits, _work = native.multiply(f"000{seed}", multiplier, steps, 4)
        assert digits == str(_literal(seed, multiplier, steps))


def test_diagonal_charges_receiver_and_rolls_back_on_cancellation() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("native test scratch", "scratch")

    def receive(digits: str, work: DiagonalWork) -> int:
        assert ledger.nodes > len(digits)
        assert work.tiles and work.table_entries and work.fringe_gates
        assert work.rows == work.word_updates == 0
        return int(digits)

    def cancel(digits: str, work: DiagonalWork) -> int:
        receive(digits, work)
        raise KeyboardInterrupt

    assert diagonal_endpoint(ledger, owner, 139, 2, 512, 4096, receive) == _literal(
        139, 2, 512
    )
    with pytest.raises(KeyboardInterrupt):
        diagonal_endpoint(ledger, owner, 139, 2, 512, 4096, cancel)
    assert ledger.entries == ledger.nodes == 0
    assert diagonal_endpoint(ledger, owner, 139, 2, 512, 16, cancel) is None


def test_causal_pair_field_and_conditional_guard_stay_exact() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("native Q19 scratch", "scratch")
    for seed in (0, 10, 98, 196, 988903000008):
        source = _pairs(seed)
        result = native_pair_action(
            ledger, owner, source, 512, lambda pairs, _work: pairs
        )
        assert result == _pairs(_literal(seed, 1, 512))
    assert ledger.nodes == ledger.entries == 0

    interior = _pairs(988903000008)[1:6]
    at16 = guard_projection(ledger, owner, interior, 16, endpoint=True)
    at17 = guard_projection(ledger, owner, interior, 17, endpoint=True)
    assert at16 is not None and at16.admitted and at16.endpoint_sums == (6, 7, 8, 9)
    assert at17 is not None and not at17.admitted and at17.endpoint_sums
    source48 = _pairs(_literal(196, 1, 48))
    projection = guard_projection(ledger, owner, source48[1:5], 7, endpoint=True)
    assert projection is not None and projection.endpoint_sums == (0,)
    assert projection.normalized_factors(7, source48[1]) == (((0, 13), (0, 32)),)
    assert ledger.nodes == ledger.entries == 0


def test_guard_projection_refuses_corrupt_input_and_releases_capacity() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("invalid native reversal scratch", "scratch")
    with pytest.raises(ValueError, match="invalid symmetric pair field"):
        native_pair_action(
            ledger, owner, bytes((9, 7)), 512, lambda pairs, _work: pairs
        )
    with pytest.raises(ValueError, match="invalid guard source"):
        guard_projection(ledger, owner, bytes((19,)), 16)
    with pytest.raises(ValueError, match="budget exceeded"):
        guard_projection(ledger, owner, bytes((17,)), 16, node_cap=1)
    assert ledger.nodes == ledger.entries == 0


def test_iterative_guard_releases_its_frame_budget_on_refusal() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("native guard frame scratch", "scratch")
    interior = bytes((8, 9, 5, 7, 4, 7, 5, 4))

    result = guard_projection(ledger, owner, interior, 5, endpoint=True)
    assert result is not None
    assert result.mask == 1
    assert result.appends > 2
    assert ledger.nodes == ledger.entries == 0

    with pytest.raises(ValueError, match="budget exceeded"):
        guard_projection(
            ledger,
            owner,
            interior,
            5,
            endpoint=True,
            node_cap=result.nodes + result.appends - 1,
        )
    assert ledger.nodes == ledger.entries == 0
    assert guard_projection(ledger, owner, interior, 5, endpoint=True) == result
