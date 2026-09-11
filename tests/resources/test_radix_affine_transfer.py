"""A spatial division port must not allocate a table indexed by its radix."""

from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.radix_transfer import RadixRemainderTransfer
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("radix", (2, 3, 6, 10, 12))
def test_complete_affine_transfer_matches_every_incoming_remainder(radix: int) -> None:
    for word in product((0, 1, 2), repeat=4):
        ledger = ResourceLedger()
        transfer = RadixRemainderTransfer(radix, 1, 0)
        for symbol in word:
            transfer = transfer.then(RadixRemainderTransfer.leaf(radix, symbol), ledger)
        for incoming in range(radix):
            expected = incoming
            for symbol in word:
                if symbol != 2:
                    expected = (2 * expected + symbol) % radix
            assert transfer.apply(incoming, ledger) == expected


def test_large_radix_composition_never_forms_a_wide_product() -> None:
    radix = (1 << 63) - 25
    ledger = ResourceLedger()
    first = RadixRemainderTransfer(radix, radix - 3, radix - 5)
    second = RadixRemainderTransfer(radix, radix - 7, radix - 11)
    composed = first.then(second, ledger)
    for state in (0, 1, radix // 2, radix - 1):
        assert composed.apply(state, ledger) == second.apply(
            first.apply(state, ledger), ledger
        )
    assert ledger.counters["maximum_arithmetic_bits"] <= 64
    assert ledger.counters.get("unbounded_arithmetic_observations", 0) == 0
    assert composed.__slots__ == ("radix", "multiplier", "offset")


def test_affine_equivalence_and_composition_order() -> None:
    ledger = ResourceLedger()
    zero = RadixRemainderTransfer.leaf(3, 0)
    one = RadixRemainderTransfer.leaf(3, 1)
    # 00 and 11 induce the same complete remainder function modulo three.
    assert zero.then(zero, ledger) == one.then(one, ledger)
    assert zero.then(one, ledger) != one.then(zero, ledger)
    assert zero.then(one, ledger).then(zero, ledger) == zero.then(
        one.then(zero, ledger), ledger
    )
    # This is only carry equivalence; no output-morphism equality is asserted.


@pytest.mark.parametrize("value", (True, 1.0, -1, 3))
def test_invalid_state_rejects_before_arithmetic(value: bool | float | int) -> None:
    ledger = ResourceLedger()
    transfer = RadixRemainderTransfer(3, 2, 1)
    before = ledger.counters.copy()
    with pytest.raises((TypeError, ValueError)):
        transfer.apply(cast("int", value), ledger)
    assert ledger.counters == before
