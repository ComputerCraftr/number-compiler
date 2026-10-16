"""Carry-forced inward masks are an exact current-source law, not an oracle."""

from __future__ import annotations

from collections.abc import Callable
from random import Random

import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.inward_bank_harmonics import (
    BANDS,
    InwardBankWindow,
    inward_bank_select,
    pair_band,
)
from number_compiler.sequences.reverse_add.q19_conditional_stencil import (
    GuardedPairStencil,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)


def _reverse(value: int) -> int:
    return int(str(value)[::-1])


def _pair_accessor(symbols: tuple[int, ...]) -> Callable[[int], int]:
    def pair_at(index: int) -> int:
        return symbols[index]

    return pair_at


def _symmetric_pair_accessor(
    symbols: tuple[int, ...], width: int
) -> Callable[[int], int]:
    def pair_at(index: int) -> int:
        return symbols[index if index < width // 2 else width - 1 - index]

    return pair_at


def _source_data(x: int) -> tuple[int, list[int], list[int], int, list[int]]:
    d = digits_lsd(x, 10)
    w = len(d)
    s = [d[i] + d[w - 1 - i] for i in range(w)]
    c = [0]
    for z in s:
        c.append(int(z + c[-1] >= 10))
    nxt = x + _reverse(x)
    to_d = digits_lsd(nxt, 10)
    target = [to_d[i] + to_d[-i - 1] for i in range(len(to_d))]
    assert len(to_d) == w + c[-1]
    return w, s, c, c[-1], target


def test_no_future_integer_is_needed_for_exact_selected_bands() -> None:
    rng = Random(20261015)
    for seed in [
        196,
        17071,
        17971,
        174571,
        12302,
        99999,
        10189,
        10089,
        *[rng.randrange(10 ** (k - 1), 10**k) for k in range(3, 45)],
    ]:
        w, s, c, g, target = _source_data(seed)
        for i in range(w // 2):
            for budget in (0, 1, 2, 4, 8, 100):
                result = inward_bank_select(
                    width=w,
                    coordinate=i,
                    growth=g,
                    pair_at=_pair_accessor(tuple(s)),
                    low_carry=c[i],
                    high_border_carries=(c[w - 1],),
                    inward_lookahead=budget,
                )
                assert target[i] in result.possible_coefficients
                assert pair_band(target[i]) in result.possible_bands
                assert result.possible_f5 and target[i] % 5 in result.possible_f5
                if result.forced_band is not None:
                    assert result.forced_band == pair_band(target[i])
                if result.forced_coefficient is not None:
                    assert result.forced_coefficient == target[i]
                assert all(result.forced_masks[band] in (0, 1, None) for band in BANDS)
                assert sum(bit == 1 for bit in result.forced_masks.values()) <= 1
                if budget == 100:
                    assert result.forced_coefficient == target[i]


def test_gt_reset_and_eq_wire_are_not_interchangeable() -> None:
    for seed in (17071, 17971, 174571, 10089, 10189):
        w, s, c, g, target = _source_data(seed)
        last = w // 2 - 1
        result = inward_bank_select(
            width=w,
            coordinate=last,
            growth=g,
            pair_at=_pair_accessor(tuple(s)),
            low_carry=c[last],
            high_border_carries=(c[w - 1],),
            inward_lookahead=100,
        )
        assert result.forced_coefficient == target[last]
    # False high port is explicitly contradictory to an inward reset.
    w, s, c, g, target = _source_data(17971)
    if s[1] != 9:
        with pytest.raises(ValueError):
            inward_bank_select(
                width=w,
                coordinate=1,
                growth=g,
                pair_at=_pair_accessor(tuple(s)),
                low_carry=c[1],
                high_border_carries=(1 - c[w - 1],),
                inward_lookahead=100,
            )


def test_inward_unknown_requires_a_set_valued_mask() -> None:
    rng = Random(319)
    witnessed = False
    for _ in range(300):
        x = rng.randrange(10**12, 10**13)
        w, s, c, g, _target = _source_data(x)
        for i in range(1, w // 2):
            result = inward_bank_select(
                width=w,
                coordinate=i,
                growth=g,
                pair_at=_pair_accessor(tuple(s)),
                low_carry=c[i],
                high_border_carries=(c[w - 1],),
                inward_lookahead=0,
            )
            if len(result.possible_bands) > 1:
                assert result.forced_band is None
                witnessed = True
                break
        if witnessed:
            break
    assert witnessed, "test must witness a genuinely ambiguous bank selection"


def test_owner_source_bound_port_requires_no_completed_target(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    for x in (196, 17071, 17971, 174571, 12302, 99999, 10089, 10189):
        ledger = ResourceLedger()
        owner = ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)
        try:
            stencil = GuardedPairStencil.from_occurrence(owner, owner.initial)
            w, _s, _c, _g, target = _source_data(x)
            assert stencil.source_width == w

            def forbidden(*_args: object, **_kwargs: object) -> None:
                raise AssertionError("observer executed a future physical Q19 kernel")

            monkeypatch.setattr(owner, "apply_punctured_pair_block", forbidden)
            for i in range(w // 2):
                result = stencil.inward_bank_at(owner, i, inward_lookahead=8)
                assert target[i] in result.possible_coefficients
                assert result.forced_coefficient == target[i]
        finally:
            owner.dispose()
            assert ledger.entries == ledger.nodes == 0


def test_symbolic_walsh_is_issued_only_for_forced_64_lanes() -> None:
    # Pair coefficient 2 is an LT-low reset. Every next cell is 4 under
    # nongrowth, so the LT-low Walsh packet is (64 mod5,0,...,0).
    x = int("1" * 256)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(x, 10), base=10)
    try:
        stencil = GuardedPairStencil.from_occurrence(owner, owner.initial)
        window = stencil.inward_bank_window(
            owner, start=20, count=64, inward_lookahead=1
        )
        assert len(window.selections) == 64
        assert window.mask_domain("lt_low") == (1,) * 64
        assert window.must_may_masks("lt_low") == (2**64 - 1,) * 2
        assert window.walsh64_mod5("lt_low") == (4,) + (0,) * 63
        assert window.walsh64_mod5("gt_high") == (0,) * 64
        with pytest.raises(ValueError):
            window.mask_domain("nonexistent")
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0

    # An unproved inward reset must remain a may/must interval. It must not
    # be represented by a concrete Walsh lane picked from the actual source.
    rng = Random(842)
    for _ in range(100):
        w = 160
        s = [rng.randrange(19) for _ in range(w // 2)]

        # Use exact palindromic source symbols, but only reveal b0 externally.
        p = _symmetric_pair_accessor(tuple(s), w)

        c = [0]
        for i in range(w):
            c.append(int(p(i) + c[-1] >= 10))
        sels = tuple(
            inward_bank_select(
                width=w,
                coordinate=i,
                growth=c[-1],
                pair_at=p,
                low_carry=c[i],
                high_border_carries=(c[w - 1],),
                inward_lookahead=0,
            )
            for i in range(64)
        )
        win = InwardBankWindow(0, sels)
        if any(v is None for band in BANDS for v in win.mask_domain(band)):
            for band in BANDS:
                if None in win.mask_domain(band):
                    with pytest.raises(ValueError):
                        win.walsh64_mod5(band)
                    return
    raise AssertionError("unable to witness conditional Walsh refusal")


def test_center_and_width_invalid_requests_are_not_silent() -> None:
    x = 196
    w, s, _c, g, _target = _source_data(x)
    with pytest.raises(ValueError):
        inward_bank_select(
            width=w,
            coordinate=w // 2,
            growth=g,
            pair_at=_pair_accessor(tuple(s)),
            low_carry=0,
        )
    with pytest.raises(ValueError):
        inward_bank_select(
            width=w,
            coordinate=0,
            growth=g,
            pair_at=_pair_accessor(tuple(s)),
            low_carry=0,
            high_border_carries=(),
        )
