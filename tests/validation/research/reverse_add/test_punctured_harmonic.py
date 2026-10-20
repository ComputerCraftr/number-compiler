"""Independent physical carry controls for the research border reduction."""

from itertools import product
from typing import cast

import pytest

from devtools.verification.carry_harmonic_ports import (
    CarryHarmonicPortAction,
    PortRows,
    PuncturedCarryHarmonic,
)
from number_compiler.arithmetic.carry.carry_monoid import CarryFn


def _direct_border(word: tuple[CarryFn, ...]) -> PortRows:
    rows: list[tuple[int, int, int]] = []
    for incoming in (0, 1):
        carry = incoming
        first = second = 0
        for index, domain in enumerate(word):
            after = carry if domain is CarryFn.ID else int(domain is CarryFn.CONST1)
            difference = after - carry
            first += difference * (2 if index % 2 else 1)
            second += difference * (3 if index % 2 else 1)
            carry = after
        rows.append((carry, first % 5, second % 5))
    return rows[0], rows[1]


def test_identity_puncture_and_twenty_active_classes_are_exact() -> None:
    reached: set[PuncturedCarryHarmonic] = set()
    for width in range(7):
        for word in product(tuple(CarryFn), repeat=width):
            rows = _direct_border(word)
            assert CarryHarmonicPortAction.from_domains(word).border_rows() == rows
            if all(domain is CarryFn.ID for domain in word):
                with pytest.raises(ValueError, match="punctured"):
                    PuncturedCarryHarmonic.from_border_rows(rows)
            else:
                port = PuncturedCarryHarmonic.from_border_rows(rows)
                assert port.border_rows() == rows
                reached.add(port)
    assert reached == {
        PuncturedCarryHarmonic(o, p, f)
        for o, p, f in product(range(2), range(2), range(5))
    }


def test_even_composition_matches_forward_carries_exhaustively() -> None:
    words = [
        (word, PuncturedCarryHarmonic.from_border_rows(_direct_border(word)))
        for word in product(tuple(CarryFn), repeat=4)
        if any(domain is not CarryFn.ID for domain in word)
    ]
    assert len(words) == 80
    for left_word, left in words:
        for right_word, right in words:
            assert left.then_even(right).border_rows() == _direct_border(
                left_word + right_word
            )


def test_power_square_and_vieta_use_only_border_projection() -> None:
    representatives: dict[PuncturedCarryHarmonic, tuple[CarryFn, ...]] = {}
    for word in product(tuple(CarryFn), repeat=6):
        if any(domain is not CarryFn.ID for domain in word):
            port = PuncturedCarryHarmonic.from_border_rows(_direct_border(word))
            representatives.setdefault(port, word)
    assert len(representatives) == 20
    for port, word in representatives.items():
        assert port.square_even().centered == 2 * port.centered % 5
        assert port.square_even().square_even().square_even().square_even() == port
        for exponent in range(1, 16):
            assert port.power_even(exponent).border_rows() == _direct_border(
                word * exponent
            )
        assert port.power_even(10**100 + 3) == port.power_even(3)
        for reflected in representatives:
            e1, e2 = port.vieta_with(reflected)
            assert (e1, e2) == reflected.vieta_with(port)
            for root in (port.centered, reflected.centered):
                assert (root * root - e1 * root + e2) % 5 == 0


@pytest.mark.parametrize("value", (True, 1.0, -1, 2))
def test_boolean_sheets_reject_aliases_and_out_of_domain_values(value: int) -> None:
    with pytest.raises(ValueError):
        PuncturedCarryHarmonic(value, 0, 0)
    with pytest.raises(ValueError):
        PuncturedCarryHarmonic(0, value, 0)


@pytest.mark.parametrize("exponent", (True, 1.0, 0, -1))
def test_punctured_power_has_no_identity_exponent(exponent: int) -> None:
    with pytest.raises(ValueError):
        PuncturedCarryHarmonic(0, 0, 0).power_even(exponent)


def test_border_decoder_rejects_numeric_aliases_in_both_rows() -> None:
    valid = PuncturedCarryHarmonic(1, 0, 0).border_rows()
    for row_index, column in product(range(2), range(3)):
        rows = [list(row) for row in valid]
        rows[row_index][column] = cast(int, float(rows[row_index][column]))
        with pytest.raises(ValueError):
            PuncturedCarryHarmonic.from_border_rows(
                cast(PortRows, (tuple(rows[0]), tuple(rows[1])))
            )


def test_active_zero_coordinate_is_idempotent_and_is_not_identity() -> None:
    port = PuncturedCarryHarmonic(0, 0, 0)
    assert port.square_even() == port
    assert port.border_rows() != ((0, 0, 0), (1, 0, 0))
    assert port.then_even(PuncturedCarryHarmonic(1, 1, 0)) != PuncturedCarryHarmonic(
        1, 1, 0
    )


def test_even_algebra_associates_without_replaying_carries(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    import devtools.verification.carry_harmonic_ports as owner

    ports = tuple(
        PuncturedCarryHarmonic(o, p, f)
        for o, p, f in product(range(2), range(2), range(5))
    )

    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("punctured algebra reconstructed a carry-domain word")

    monkeypatch.setattr(owner, "apply_carry_fn", forbidden)
    monkeypatch.setattr(owner, "harmonic_sum", forbidden)
    monkeypatch.setattr(CarryHarmonicPortAction, "from_domains", forbidden)
    for left, middle, right in product(ports, repeat=3):
        assert left.then_even(middle).then_even(right) == left.then_even(
            middle.then_even(right)
        )
    for port in ports:
        assert port.power_even(10**100 + 3) == port.power_even(3)


def test_punctured_projection_cannot_allocate_inside_point_observer() -> None:
    from number_compiler.arithmetic.contracts.exact_tree_context import (
        ExactTreeConstructionForbidden,
        source_reads_only,
    )

    @source_reads_only
    def allocate() -> PuncturedCarryHarmonic:
        return PuncturedCarryHarmonic(0, 0, 0)

    with pytest.raises(ExactTreeConstructionForbidden):
        allocate()


def test_odd_width_joins_keep_the_full_width_owner() -> None:
    word = (CarryFn.CONST0, CarryFn.CONST1, CarryFn.ID)
    action = CarryHarmonicPortAction.from_domains(word)
    port = action.punctured_border()
    assert port == PuncturedCarryHarmonic(1, 0, 2)
    # The projection has no width phase. Its even law cannot join this odd
    # occurrence; the existing width-bearing owner supplies phase transport.
    assert port.square_even().harmonic == 3
    repeated = action.then(action)
    assert repeated.border_rows() == _direct_border(word + word)
    assert repeated.punctured_border().harmonic == 1
