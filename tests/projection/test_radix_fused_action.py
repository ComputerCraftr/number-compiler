"""Complete original-source/C1 division actions, not residue response caches."""

from __future__ import annotations

from tests.support.assertions import assert_rejected_atomically

from collections.abc import Mapping
from itertools import product
from typing import Never

import pytest

from number_compiler.arithmetic.functions.finite_function_types import (
    SemanticFunctionID,
)
from number_compiler.arithmetic.functions.finite_port_action import PortVariable
from number_compiler.projection.lazy_radix import collatz_radix_digit
from number_compiler.projection.radix_fused_action import FusedRadixArena
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.collatz.block_power import PoweredCollatzTerm


@pytest.mark.parametrize("physical", (False, True))
def test_complete_carries_coordinate_output_and_activity(physical: bool) -> None:
    arena = FusedRadixArena(ResourceLedger())
    source = (1, 0, 1)
    action = arena.compile(source, radix=3, stages=2, physical=physical)
    width = 1 << action.level
    for incoming, d0, d1 in product(range(3), repeat=3):
        carry = incoming
        word = []
        for position in range(width):
            symbol = source[position] if position < len(source) else 0
            if physical:
                total = 3 * symbol + carry
                word.append(total & 1)
                carry = total >> 1
            else:
                word.append(symbol)
        exits = []
        active = False
        for initial in (d0, d1):
            active = any(word)
            residue = initial
            output = [0] * width
            for position in reversed(range(width)):
                residue, output[position] = (
                    (2 * residue + word[position]) % 3,
                    (2 * residue + word[position]) // 3,
                )
            exits.append(residue)
            word = output
        inputs = {
            port.variable: value
            for port, value in zip(action.ports, (incoming, d0, d1, 0), strict=True)
        }

        def read(
            bits: tuple[SemanticFunctionID, ...],
            values: Mapping[PortVariable, int],
        ) -> int:
            return sum(
                arena.functions.evaluate(bit, values).value << index
                for index, bit in enumerate(bits)
            )

        assert read(action.physical_exit, inputs) == carry
        assert tuple(
            read(component, inputs) for component in action.division_exit
        ) == tuple(exits)
        assert arena.functions.evaluate(action.active, inputs).value == active
        for position in range(width):
            inputs[action.ports[-1].variable] = position
            assert (
                arena.functions.evaluate(action.output, inputs).value == word[position]
            )


def test_full_output_distinguishes_same_remainders_and_aliases_original_padding() -> (
    None
):
    arena = FusedRadixArena(ResourceLedger())
    first = arena.compile((1, 0, 0, 0), radix=3, stages=2, physical=False)
    second = arena.compile((0, 1, 0, 1), radix=3, stages=2, physical=False)
    assert first.division_exit == second.division_exit
    assert first.output != second.output
    assert first != second
    assert arena.compile((1,), radix=3, stages=2, physical=False) == arena.compile(
        (1, 0), radix=3, stages=2, physical=False
    )


@pytest.mark.parametrize("steps", (0, 1))
@pytest.mark.parametrize("seed", (26, 27))
@pytest.mark.parametrize("radix", (3, 6, 12))
def test_supported_queries_without_binary_point_or_endpoint_lowering(
    seed: int, steps: int, radix: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    term = PoweredCollatzTerm(seed, steps)
    expected = seed if not steps else seed // 2 if seed % 2 == 0 else 3 * seed + 1

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("fused action must use only original source")

    for name in ("digit", "digits", "iter_digits", "materialize"):
        monkeypatch.setattr(PoweredCollatzTerm, name, forbidden)
    for index in range(4):
        if expected // radix**index:
            assert (
                collatz_radix_digit(term, radix, index)
                == expected // radix**index % radix
            )
        else:
            with pytest.raises(IndexError):
                collatz_radix_digit(term, radix, index)
    projection = term._radix_projections[radix]
    assert not any(hasattr(projection, item) for item in ("_ranges", "_transfers"))


def test_fixed_digit_three_budget_and_parent_warm_reuse(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    seed = (1 << 95) + 0x123456789ABCDEF12345
    term = PoweredCollatzTerm(seed, 1, max_context_nodes=5000, max_cache_entries=10000)
    expected = (3 * seed + 1) // 27 % 3
    assert collatz_radix_digit(term, 3, 3) == expected
    projection = term._radix_projections[3]
    assert projection._native_source is not None
    before_reads = term._ledger.counters.get("original_radix_source_bit_reads", 0)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError(
            "warm complete parent must avoid child compilation/source queries"
        )

    monkeypatch.setattr(FusedRadixArena, "compile", forbidden)
    monkeypatch.setattr(PoweredCollatzTerm, "digit", forbidden)
    assert collatz_radix_digit(term, 3, 3) == expected
    assert (
        term._ledger.counters.get("original_radix_source_bit_reads", 0) == before_reads
    )
    assert term._ledger.nodes <= 5000
    assert term._ledger.entries <= 10000
    assert not any(hasattr(projection, item) for item in ("_ranges", "_transfers"))
    assert not term._ledger.counters.get("radix_source_point_queries", 0)


def test_foreign_action_rejected_before_work() -> None:
    first, second = FusedRadixArena(ResourceLedger()), FusedRadixArena(ResourceLedger())
    action = first.compile((1, 0, 1), radix=3, stages=1, physical=True)
    assert_rejected_atomically(second.ledger, lambda: second.digit(action), ValueError)


@pytest.mark.parametrize("radix, expected, fused", ((6, 1, False), (10, 8, True)))
def test_fused_non_native_parent_warm_reuse(
    monkeypatch: pytest.MonkeyPatch, radix: int, expected: int, fused: bool
) -> None:
    term = PoweredCollatzTerm(27, 1)
    assert collatz_radix_digit(term, radix, 1) == expected
    projection = term._radix_projections[radix]
    assert (projection._fused is not None) == fused
    assert (projection._native_source is not None) != fused
    before_reads = term._ledger.counters.get("original_radix_source_bit_reads", 0)

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("parent hit must not compile descendants")

    monkeypatch.setattr(FusedRadixArena, "compile", forbidden)
    assert collatz_radix_digit(term, radix, 1) == expected
    assert (
        term._ledger.counters.get("original_radix_source_bit_reads", 0) == before_reads
    )


def test_same_ledger_foreign_original_rejected_before_warm_lookup() -> None:
    from number_compiler.projection.lazy_radix import RadixProjection

    source, foreign = PoweredCollatzTerm(27, 1), PoweredCollatzTerm(31, 1)
    width = source.width()
    projection = RadixProjection(3, width, source._ledger)
    assert projection.digit(source, 1) == 0
    foreign._ledger = source._ledger
    before = source._ledger.snapshot()
    for index in (-1, 1, width):
        with pytest.raises(ValueError, match="another binary source"):
            projection.digit(foreign, index)
    assert source._ledger.snapshot() == before
