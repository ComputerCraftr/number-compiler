"""Directed growth differs from XOR; universal envelopes retain ambiguity."""

from dataclasses import replace
from itertools import product

import pytest

from number_compiler.arithmetic.carry.carry_monoid import CarryFn
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.payload_audit import audit_registered_payloads
from number_compiler.sequences.reverse_add.border_carry_safety import BorderTile
from number_compiler.sequences.reverse_add.diagonal_growth_bank import (
    DirectedDiagonalAction,
    DirectedGrowthMask,
    UniversalBorderWidthPower,
)
from number_compiler.sequences.reverse_add.q19_output import ReversePairQ19OutputOwner
from number_compiler.sequences.reverse_add.symmetric_carry_filter import (
    filter_symmetric_transfer,
)


def test_symmetric_exact_range_requires_a_complete_domain_assignment() -> None:
    # A decisive outer reset does not make an empty inner domain realizable.
    for domains in (((8,), ()), ((), (10,))):
        with pytest.raises(ValueError, match="nonempty"):
            filter_symmetric_transfer(domains, (CarryFn.CONST0,))
    identity = filter_symmetric_transfer((), (CarryFn.ID,))
    assert identity.possible_transfers == (CarryFn.ID,)


def test_directed_diagonal_preserves_signed_growth_and_chronology() -> None:
    start = DirectedGrowthMask.from_growth_words((0, 1, 0), (1, 0, 0))
    for first in product((0, 1), repeat=4):
        for second in product((0, 1), repeat=4):
            action = DirectedDiagonalAction.from_inlets(first, second, window=3)
            state = start
            for a, b in zip(first, second, strict=True):
                state = state.shift(a, b)
            assert action.apply(start) == state
            assert action.signed_growth == sum(second) - sum(first)
            assert action.width_after(7, 11) == (7 + sum(first), 11 + sum(second))
            low = DirectedDiagonalAction.from_inlets(first[:2], second[:2], window=3)
            high = DirectedDiagonalAction.from_inlets(first[2:], second[2:], window=3)
            assert low.then(high) == action
    plus = DirectedGrowthMask.from_growth_words((0,), (1,))
    minus = DirectedGrowthMask.from_growth_words((1,), (0,))
    assert plus.xor == minus.xor
    assert plus.signed_window_growth == -minus.signed_window_growth == 1
    atom = DirectedDiagonalAction.from_inlets((0, 1), (1, 1), window=3)
    assert atom.formal_power(10**6).signed_growth == 10**6
    with pytest.raises(ValueError):
        DirectedGrowthMask(3, 1, 1)


def test_issued_diagonal_uses_retained_action_without_source_reconstruction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=4, window_digits=1
        )
        comparison = certificate.directed_growth_diagonal(
            0, 1, window=1, continuation=2
        )
        assert audit_registered_payloads(ledger).forbidden_future_payloads == 0
        expected = comparison.action.apply(comparison.initial)
        expected_delta = comparison.action.signed_growth

        def forbidden(*_args: object, **_kwargs: object) -> DirectedDiagonalAction:
            raise AssertionError("a warm diagonal consumer rebuilt its inlet action")

        monkeypatch.setattr(DirectedDiagonalAction, "from_inlets", forbidden)
        assert comparison.terminal() == expected
        assert comparison.signed_width_delta() == expected_delta
        assert comparison.formal_power(3).duration == 3 * comparison.action.duration
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_diagonal_comparison_rejects_copies_and_changed_issued_payload() -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=3, window_digits=1
        )
        comparison = certificate.directed_growth_diagonal(
            0, 1, window=1, continuation=1
        )
        copied = replace(comparison)
        forged = replace(
            comparison,
            action=DirectedDiagonalAction.identity(comparison.initial.window),
        )
        with pytest.raises(ValueError, match="retained"):
            copied.terminal()
        with pytest.raises(ValueError, match="retained"):
            forged.terminal()

        original = comparison.action
        object.__setattr__(
            comparison, "action", DirectedDiagonalAction.identity(original.window)
        )
        with pytest.raises(ValueError, match="altered"):
            comparison.terminal()
        assert audit_registered_payloads(ledger).forbidden_future_payloads > 0
        object.__setattr__(comparison, "action", original)
        assert comparison.terminal() == original.apply(comparison.initial)
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


@pytest.mark.parametrize("steps,minimum,maximum", ((8, 4, 4), (14, 7, 7), (15, 7, 8)))
def test_92_28_width_has_a_sharp_finite_envelope(
    steps: int, minimum: int, maximum: int
) -> None:
    model = UniversalBorderWidthPower(BorderTile(2, 92, 28), entry_width=23)
    bounds = model.bounds(steps)
    assert (bounds.min_growth, bounds.max_growth) == (minimum, maximum)
    assert bounds.constructed_border_states == 458
    assert bounds.exact_width == (23 + minimum if minimum == maximum else None)
    assert bounds.composition_pairs > 0
    assert bounds.peak_relation_cells <= 250_000
