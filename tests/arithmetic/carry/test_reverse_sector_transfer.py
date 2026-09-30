"""Independent laws for bounded reverse carry-sector transfers."""

from __future__ import annotations

from collections.abc import Callable, Sequence
from itertools import product
from typing import cast

import pytest

from number_compiler.arithmetic.carry.carry_monoid import (
    apply_carry_fn,
    value_carry_fn,
)
from number_compiler.arithmetic.carry.event_memory import pair_step
from number_compiler.arithmetic.carry.reverse_sector_transfer import (
    ReverseCarrySectorTransfer,
)
from tests.support.reference_arithmetic import negacyclic_reduce as _reduce


def _summary(values: Sequence[int], base: int) -> ReverseCarrySectorTransfer:
    items = tuple(values)
    if not items:
        raise ValueError("test summary requires a nonempty word")
    result = ReverseCarrySectorTransfer.leaf(base, items[0])
    for value in items[1:]:
        result = result.then(ReverseCarrySectorTransfer.leaf(base, value))
    return result


def _carries(values: Sequence[int], base: int, incoming: int) -> tuple[int, ...]:
    carry = incoming
    out = [carry]
    for value in values:
        carry = apply_carry_fn(value_carry_fn(value, base), carry)
        out.append(carry)
    return tuple(out)


def _forcing(values: Sequence[int], base: int, incoming: int) -> tuple[int, ...]:
    carry = _carries(values, base, incoming)
    width = len(values)
    growth = carry[-1]
    if not growth:
        return tuple(
            carry[index]
            + carry[width - index - 1]
            - base * (carry[index + 1] + carry[width - index])
            for index in range(width)
        )
    out = [0] * (width + 1)
    out[0] = out[width] = 1 - base * carry[1]
    for index in range(1, width):
        out[index] = (
            carry[index]
            + carry[width - index]
            - base * (carry[index + 1] + carry[width - index + 1])
        )
    return tuple(out)


def _local_output(
    source: Sequence[int],
    source_carries: Sequence[int],
    reflected_carries: Sequence[int],
    base: int,
    *,
    predecessor: Sequence[int] | None = None,
) -> tuple[int, ...]:
    width = len(source)
    if len(source_carries) != width + 1 or len(reflected_carries) != width + 1:
        raise ValueError("local forcing oracle requires complete carry boundaries")
    linear = (
        tuple(2 * value for value in source)
        if predecessor is None
        else tuple(a + b for a, b in zip(source, predecessor, strict=True))
    )
    return tuple(
        linear[index]
        + source_carries[index]
        + reflected_carries[width - index - 1]
        - base * (source_carries[index + 1] + reflected_carries[width - index])
        for index in range(width)
    )


@pytest.mark.parametrize("values", ((8, 9, 8), (10, 9, 10)))
@pytest.mark.parametrize("incoming", (0, 1))
def test_sector_forcing_matches_both_normalization_growth_cases(
    values: tuple[int, ...], incoming: int
) -> None:
    summary = _summary(values, 10)
    actual = summary.forcing(incoming)
    expected = _forcing(values, 10, incoming)
    assert actual.growth == _carries(values, 10, incoming)[-1]
    for sector in actual.sectors:
        assert sector.full == _reduce(expected, sector.classes)
        successor = (
            (
                values[0],
                *(values[index - 1] + values[index] for index in range(1, len(values))),
                values[-1],
            )
            if actual.growth
            else tuple(2 * value for value in values)
        )
        assert sector.output == _reduce(
            tuple(
                linear + forcing
                for linear, forcing in zip(successor, expected, strict=True)
            ),
            sector.classes,
        )


def test_eq_domain_propagates_both_incoming_carries() -> None:
    summary = _summary((9, 9, 9, 9), 10)
    assert apply_carry_fn(summary.carry, 0) == 0
    assert apply_carry_fn(summary.carry, 1) == 1
    for incoming in (0, 1):
        carries = _carries((9, 9, 9, 9), 10, incoming)
        for sector in summary.sectors:
            assert sector.before[incoming] == _reduce(carries[:-1], sector.classes)
            assert sector.after[incoming] == _reduce(carries[1:], sector.classes)


def test_spatial_composition_is_associative() -> None:
    leaves = tuple(ReverseCarrySectorTransfer.leaf(10, value) for value in (8, 9, 10))
    assert leaves[0].then(leaves[1]).then(leaves[2]) == leaves[0].then(
        leaves[1].then(leaves[2])
    )


def test_sector_summary_depends_on_domains_not_source_magnitudes() -> None:
    low = _summary((0, 9, 10, 9, 0), 10)
    high = _summary((8, 9, 18, 9, 8), 10)
    assert low.carry == high.carry
    for incoming in (0, 1):
        low_forcing = low.forcing(incoming)
        high_forcing = high.forcing(incoming)
        assert low_forcing.growth == high_forcing.growth
        assert tuple(
            (sector.forward, sector.reflected, sector.full)
            for sector in low_forcing.sectors
        ) == tuple(
            (sector.forward, sector.reflected, sector.full)
            for sector in high_forcing.sectors
        )


def test_equal_sector_summary_does_not_imply_equal_successor_behavior() -> None:
    low = (4,) * 16
    high = (5,) * 16
    # Their coefficient difference is
    # (1 + z)(1 + z**2)(1 + z**4)(1 + z**8), so it vanishes in
    # every retained z**m + 1 sector while the carry domains also agree.
    assert _summary(low, 10) == _summary(high, 10)
    assert pair_step(low, 10) == ((8,) * 16, 0)
    assert pair_step(high, 10) == ((10,) * 16, 0)


@pytest.mark.parametrize(
    "incoming,reflected_incoming", tuple(product((0, 1), repeat=2))
)
def test_local_no_growth_forcing_uses_explicit_reflected_interval(
    incoming: int, reflected_incoming: int
) -> None:
    source_values = (8, 9, 10)
    reflected_values = (10, 8, 9)
    source = _summary(source_values, 10)
    reflected = _summary(reflected_values, 10)
    actual = source.interval_forcing(
        reflected,
        incoming=incoming,
        reflected_incoming=reflected_incoming,
        growth=0,
    )
    expected = _local_output(
        source_values,
        _carries(source_values, 10, incoming),
        _carries(reflected_values, 10, reflected_incoming),
        10,
    )
    for sector in actual.sectors:
        assert sector.output == _reduce(expected, sector.classes)


@pytest.mark.parametrize(
    "incoming,reflected_incoming", tuple(product((0, 1), repeat=2))
)
def test_local_growth_forcing_consumes_aligned_predecessor_and_partner_halo(
    incoming: int, reflected_incoming: int
) -> None:
    # These are already aligned interior regions: predecessor[k] is S[i-1]
    # and reflected[k] is the physical partner carry cell for the growth law.
    source_values = (10, 9, 8)
    predecessor_values = (8, 10, 9)
    reflected_values = (9, 10, 8)
    source = _summary(source_values, 10)
    predecessor = _summary(predecessor_values, 10)
    reflected = _summary(reflected_values, 10)
    actual = source.interval_forcing(
        reflected,
        incoming=incoming,
        reflected_incoming=reflected_incoming,
        growth=1,
        predecessor=predecessor,
    )
    expected = _local_output(
        source_values,
        _carries(source_values, 10, incoming),
        _carries(reflected_values, 10, reflected_incoming),
        10,
        predecessor=predecessor_values,
    )
    for sector in actual.sectors:
        assert sector.output == _reduce(expected, sector.classes)


def test_local_forcing_rejects_unaligned_growth_and_numeric_aliases() -> None:
    source = _summary((8, 9), 10)
    reflected = _summary((9, 8), 10)
    with pytest.raises(ValueError, match="predecessor"):
        source.interval_forcing(
            reflected,
            incoming=0,
            reflected_incoming=0,
            growth=1,
        )
    with pytest.raises(ValueError, match="carry bit"):
        source.interval_forcing(
            reflected,
            incoming=cast(int, False),
            reflected_incoming=0,
            growth=0,
        )


def test_local_forcing_exhausts_each_decimal_leaf_factor() -> None:
    leaves = tuple(ReverseCarrySectorTransfer.leaf(10, symbol) for symbol in range(19))
    for source_symbol, reflected_symbol in product(range(19), repeat=2):
        source = leaves[source_symbol]
        reflected = leaves[reflected_symbol]
        predecessor_symbol = (source_symbol + reflected_symbol) % 19
        predecessor = leaves[predecessor_symbol]
        for incoming, reflected_incoming in product((0, 1), repeat=2):
            no_growth = source.interval_forcing(
                reflected,
                incoming=incoming,
                reflected_incoming=reflected_incoming,
                growth=0,
            )
            no_growth_expected = _local_output(
                (source_symbol,),
                _carries((source_symbol,), 10, incoming),
                _carries((reflected_symbol,), 10, reflected_incoming),
                10,
            )
            for sector in no_growth.sectors:
                assert sector.output == _reduce(no_growth_expected, sector.classes)
            growth = source.interval_forcing(
                reflected,
                incoming=incoming,
                reflected_incoming=reflected_incoming,
                growth=1,
                predecessor=predecessor,
            )
            growth_expected = _local_output(
                (source_symbol,),
                _carries((source_symbol,), 10, incoming),
                _carries((reflected_symbol,), 10, reflected_incoming),
                10,
                predecessor=(predecessor_symbol,),
            )
            for sector in growth.sectors:
                assert sector.output == _reduce(growth_expected, sector.classes)
    # The predecessor enters only through addition of its source residue.
    # Hold the nonlinear carry factors fixed and exhaust that independent axis.
    for predecessor_symbol in range(19):
        actual = leaves[8].interval_forcing(
            leaves[10],
            incoming=1,
            reflected_incoming=1,
            growth=1,
            predecessor=leaves[predecessor_symbol],
        )
        expected = _local_output(
            (8,),
            _carries((8,), 10, 1),
            _carries((10,), 10, 1),
            10,
            predecessor=(predecessor_symbol,),
        )
        for sector in actual.sectors:
            assert sector.output == _reduce(expected, sector.classes)


def test_summary_has_one_fixed_bounded_payload_shape() -> None:
    assert ReverseCarrySectorTransfer.retained_slots() == 76
    assert (
        _summary((8,), 10).retained_slots() == _summary((8,) * 64, 10).retained_slots()
    )


def test_trailing_blank_tiles_are_neutral_but_retain_physical_geometry() -> None:
    active = _summary((8, 9, 10), 10)
    padded = active.then(_summary((19, 19, 19, 19, 19), 10))
    assert padded.width == 8
    assert padded.active_width == active.active_width == 3
    assert padded.carry == active.carry
    assert padded.sectors == active.sectors
    for incoming in (0, 1):
        assert padded.forcing(incoming) == active.forcing(incoming)


def test_blank_prefix_before_activity_is_rejected_without_losing_extent() -> None:
    blank = ReverseCarrySectorTransfer.leaf(10, 19)
    active = ReverseCarrySectorTransfer.leaf(10, 8)
    with pytest.raises(ValueError, match="contiguous prefix"):
        blank.then(active)
    assert blank.width == 1 and blank.active_width == 0
    with pytest.raises(ValueError, match="no reverse forcing field"):
        blank.forcing()


@pytest.mark.parametrize("base,symbol", ((1, 0), (1 << 31 | 1, 0), (10, -1), (10, 20)))
def test_leaf_rejects_unbounded_radices_and_symbols(base: int, symbol: int) -> None:
    with pytest.raises(ValueError):
        ReverseCarrySectorTransfer.leaf(base, symbol)


def test_leaf_rejects_boolean_and_float_numeric_aliases() -> None:
    invalid: tuple[Callable[[], ReverseCarrySectorTransfer], ...] = (
        lambda: ReverseCarrySectorTransfer.leaf(True, 0),
        lambda: ReverseCarrySectorTransfer.leaf(10, True),
        lambda: ReverseCarrySectorTransfer.leaf(cast(int, 10.0), 0),
    )
    for call in invalid:
        with pytest.raises((TypeError, ValueError)):
            call()


def test_unissued_transfer_rejects_composition_and_forcing() -> None:
    issued = _summary((8, 9), 10)
    forged = object.__new__(ReverseCarrySectorTransfer)
    for name in ("base", "width", "active_width", "carry", "sectors"):
        object.__setattr__(forged, name, getattr(issued, name))
    with pytest.raises(TypeError, match="verified leaf or composition"):
        forged.__post_init__()
    with pytest.raises(TypeError, match="verified leaf or composition"):
        issued.then(forged)
    with pytest.raises(TypeError, match="verified leaf or composition"):
        forged.forcing()
