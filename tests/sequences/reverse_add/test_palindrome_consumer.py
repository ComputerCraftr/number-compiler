import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.formula.formula import FormulaArena
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.sequences.reverse_add.digits import pair_root_from_integer
from number_compiler.sequences.reverse_add.palindrome import (
    mirror_palindrome,
    next_result_is_palindrome,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_exact_carry_and_shifted_mirror_theorem_across_radices() -> None:
    for base in (2, 3, 5, 10, 15):
        spec = RadixSpec(base)
        for seed in range(250):
            digits = digits_lsd(seed, base)
            reverse = 0
            for d in digits:
                reverse = reverse * base + d
            target = digits_lsd(seed + reverse, base)
            arena = FormulaArena()
            pair = pair_root_from_integer(seed, arena, spec)
            assert next_result_is_palindrome(arena, pair, spec) == (
                target == target[::-1]
            )


def test_outer_safety_tube_does_not_read_interior() -> None:
    seen = []

    def digit(i: int) -> int:
        seen.append(i)
        assert i in (0, 999, 1, 998, 2, 997)
        return int(i == 997)

    assert not mirror_palindrome(1000, digit)
    assert seen == [0, 999, 1, 998, 2, 997]


def test_surviving_shell_does_not_certify_palindrome() -> None:
    values = (1, 2, 3, 4, 5, 6, 3, 2, 1)
    assert not mirror_palindrome(len(values), values.__getitem__)


def test_powered_output_never_materializes(monkeypatch: pytest.MonkeyPatch) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("palindrome demand materialized a target")

    monkeypatch.setattr(ReverseAddPoweredTerm, "materialize", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "iter_digits", forbidden)
    assert ReverseAddPoweredTerm(121, 0).is_palindrome()
    assert not ReverseAddPoweredTerm(196, 1).is_palindrome()
    assert ReverseAddPoweredTerm(56, 1).is_palindrome()


def test_powered_mirror_ladder_uses_the_existing_digit_owner(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("mirror sheet reconstructed the target integer")

    monkeypatch.setattr(ReverseAddPoweredTerm, "materialize", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "iter_digits", forbidden)
    assert ReverseAddPoweredTerm(56, 1).mirror_obstruction() is None
    certificate = ReverseAddPoweredTerm(196, 1).mirror_obstruction()
    assert certificate is not None and certificate.nonzero
