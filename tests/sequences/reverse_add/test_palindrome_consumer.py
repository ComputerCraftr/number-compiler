import pytest

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.arithmetic.formula.formula import FormulaArena
from number_compiler.arithmetic.formula.types import RadixSpec
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.resources.stores import LedgerList
from number_compiler.sequences.reverse_add.digits import pair_root_from_integer
from number_compiler.sequences.reverse_add.palindrome import (
    mirror_palindrome,
    mirror_palindrome_from_output,
    next_result_is_palindrome,
)
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from tests.support.reverse_add_source_data import iterate_reverse_add
from tests.support.reverse_cutover import assert_mirror_scratch_released


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
    seen: list[int] = []

    def digit(i: int) -> int:
        seen.append(i)
        assert i in (0, 999, 1, 998, 2, 997)
        return int(i == 997)

    assert not mirror_palindrome(1000, digit)
    assert seen == [0, 999, 1, 998, 2, 997]


def test_surviving_shell_does_not_certify_palindrome() -> None:
    values = (1, 2, 3, 4, 5, 6, 3, 2, 1)
    assert not mirror_palindrome(len(values), values.__getitem__)


def test_powered_palindrome_streams_without_integer_or_point_reconstruction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        pytest.fail("palindrome demand materialized a target")

    monkeypatch.setattr(ReverseAddPoweredTerm, "materialize", forbidden)
    monkeypatch.setattr(ReverseAddPoweredTerm, "digit", forbidden)
    assert ReverseAddPoweredTerm(121, 0).is_palindrome()
    assert not ReverseAddPoweredTerm(196, 1).is_palindrome()
    assert ReverseAddPoweredTerm(56, 1).is_palindrome()


@pytest.mark.parametrize(("seed", "steps"), ((196, 20), (1, 8), (121, 0)))
def test_powered_palindrome_uses_one_charged_output_stream(
    seed: int, steps: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    expected = iterate_reverse_add(seed, steps)
    digits = str(expected)
    term = ReverseAddPoweredTerm(seed, steps)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("palindrome restarted a temporal point query")

    monkeypatch.setattr(ReverseAddPoweredTerm, "digit", forbidden)
    assert term.is_palindrome() == (digits == digits[::-1])
    assert term.resource_ledger.counters["reverse_output_stream_requests"] == 1
    assert term.resource_ledger.counters["reverse_output_stream_emitted_digits"] == len(
        digits
    )
    assert_mirror_scratch_released(term)


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


def test_mirror_output_rejects_incompatible_scratch_accounting() -> None:
    ledger = ResourceLedger()
    owner = ledger.register("incorrect-mirror-scratch", "explicit_lowering")
    scratch: LedgerList[int] = ledger.make_list(
        owner, nodes_per_entry=1, append_only=False
    )
    before = ledger.snapshot()
    with pytest.raises(ValueError, match="another ledger or policy"):
        mirror_palindrome_from_output(3, (1, 2, 1), ledger=ledger, scratch=scratch)
    assert not scratch
    assert ledger.snapshot() == before
