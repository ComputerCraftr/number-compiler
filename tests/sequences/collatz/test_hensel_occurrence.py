"""Focused tests for the live Collatz Hensel occurrence carrier."""

import pytest

from number_compiler.arithmetic.automata.program_word import (
    EMPTY,
    CanonicalWord,
    from_runs,
    from_values,
    iter_runs,
)
from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.sequences.collatz import frame
from number_compiler.sequences.collatz.hensel_occurrence import (
    CollatzHenselAction,
    CollatzHenselOccurrence,
    CollatzHenselOccurrenceCarrier,
    canonicalize_hensel_occurrence,
    hensel_second_image,
)
from number_compiler.sequences.collatz.pair import accelerated_odd_collatz


def test_129_and_385_reimage_to_distinct_successors_with_shared_action() -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    first = carrier.from_value(129)
    second = carrier.from_value(385)
    first_step = carrier.next_step(first)
    second_step = carrier.next_step(second)

    assert first.action is second.action
    assert first_step.target.value == 97
    assert second_step.target.value == 289
    assert first_step.valuation == accelerated_odd_collatz(129).valuation
    assert second_step.valuation == accelerated_odd_collatz(385).valuation
    assert first_step.target.suffix != second_step.target.suffix


def test_action_transition_uses_the_canonical_affine_section() -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    # The raw a=2 source is rebased before the exact root transition.
    source = carrier.reimage(
        CollatzHenselAction(2, 0, 3),
        from_values((2,)),
    )
    assert source.a == 1
    step = carrier.next_step(source)
    assert step.target.action.a == 1
    assert step.target.action.h == 1
    assert step.root is not None


def test_affine_occurrence_normalization_preserves_value_and_is_idempotent() -> None:
    raw = CollatzHenselOccurrence(
        CollatzHenselAction(2, 2, 37),
        from_values((2, 1, 3)),
        7,
    )
    normalized = canonicalize_hensel_occurrence(raw)
    assert normalized.a == 1
    assert normalized.h == 2
    assert normalized.b == 1
    assert normalized.suffix_value == 2 * raw.suffix_value + 2
    assert normalized.value == raw.value
    assert normalized.logical_steps == raw.logical_steps
    assert canonicalize_hensel_occurrence(normalized) is normalized


def test_carrier_interns_equal_raw_affine_representatives_once() -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    raw = carrier.reimage(CollatzHenselAction(2, 2, 1), from_values((2,)))
    canonical = carrier.reimage(CollatzHenselAction(1, 2, 1), from_values((0, 1)))
    assert raw is canonical
    assert raw.value == 73
    assert carrier.hits == 1


def test_affine_normalization_transduces_a_million_quarters_by_runs() -> None:
    raw = CollatzHenselOccurrence(
        CollatzHenselAction(2, 0, 3),
        from_runs(((3, 1_000_000),)),
    )
    normalized = canonicalize_hensel_occurrence(raw)
    assert normalized.action == CollatzHenselAction(1, 0, 1)
    assert tuple(iter_runs(normalized.suffix)) == ((3, 1_000_000), (1, 1))
    assert normalized.suffix.length == 1_000_001
    assert normalized.suffix.run_count == 2


def test_affine_normalization_preserves_explicit_zero_occurrence_geometry() -> None:
    zero = from_values((0,))
    normalized = canonicalize_hensel_occurrence(
        CollatzHenselOccurrence(CollatzHenselAction(2, 0, 1), zero)
    )
    assert normalized.suffix.length == 1
    assert tuple(iter_runs(normalized.suffix)) == ((0, 1),)
    with pytest.raises(ValueError):
        CollatzHenselAction(1, 0, -1)


def test_empty_and_zero_suffixes_remain_distinct_occurrences() -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    action = CollatzHenselAction(1, 0, 1)
    zero_word = from_values((0,))
    empty = carrier.reimage(action, EMPTY)
    zero = carrier.reimage(action, zero_word)
    assert empty.suffix is EMPTY
    assert zero.suffix is zero_word
    assert empty.occurrence_key != zero.occurrence_key
    assert carrier.next_step(zero).target.value == 1


def test_suffix_reimaging_matches_direct_successor_for_small_odd_values() -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    for value in range(1, 512, 2):
        suffix_value = (value - 1) // 2
        suffix = (
            EMPTY if suffix_value == 0 else from_values(digits_lsd(suffix_value, 4))
        )
        occurrence = carrier.reimage(CollatzHenselAction(1, 0, 1), suffix)
        step = carrier.next_step(occurrence)
        expected = accelerated_odd_collatz(value)
        assert step.target.value == expected.target
        assert step.valuation == expected.valuation


def test_nonlinear_root_consumption_rebases_the_mismatch_multiplier() -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    low = carrier.reimage(
        CollatzHenselAction(1, 0, 1),
        from_values((1,)),
    )
    high = carrier.reimage(
        CollatzHenselAction(1, 0, 3),
        from_values((1,)),
    )
    low_step = carrier.next_step(low)
    high_step = carrier.next_step(high)
    assert low_step.root is not None and low_step.mismatch is not None
    assert high_step.root is not None and high_step.mismatch is not None
    assert low_step.target.action.a == high_step.target.action.a == 1
    assert low_step.target.action.h == high_step.target.action.h == 1
    assert (low_step.target.value, high_step.target.value) == (5, 1)


def test_next_step_does_not_materialize_a_successor_word(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    source = carrier.from_value(129)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("next step materialized a successor word")

    monkeypatch.setattr(frame, "collatz_radix4_frame_factorization", forbidden)
    step = carrier.next_step(source)
    assert step.target.value == 97


def test_image_second_uses_normalized_frame_and_matches_exact_two_steps() -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    first = carrier.image_second(129)
    second = carrier.image_second(385)
    assert first.value == 73
    assert second.value == 217
    assert first.action.canonical_key == second.action.canonical_key
    assert first.action.multiplier == 18
    assert first.suffix_value == 4
    assert second.suffix_value == 12
    assert first.logical_steps == second.logical_steps == 2
    assert hensel_second_image(129, carrier=carrier) is first


def test_shared_action_exposes_latent_suffix_difference_at_cylinder_49() -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    left, right = carrier.image_second(129), carrier.image_second(385)
    assert left.action is right.action
    assert (left.suffix_value, right.suffix_value) == (4, 12)
    assert left.multiplier == 18 and left.b == 1
    for expected in ((55, 163), (83, 245)):
        left, right = carrier.next_step(left).target, carrier.next_step(right).target
        assert (left.value, right.value) == expected
        assert left.action is right.action
    assert left.multiplier == 162 and left.b == 83
    assert (left.suffix_value, right.suffix_value) == (0, 1)
    first, second = carrier.next_step(left), carrier.next_step(right)
    assert first.root == second.root
    assert first.root is not None and first.root.root_residue(6) == 49
    assert (first.valuation, second.valuation) == (1, 5)
    assert (first.target.value, second.target.value) == (125, 23)


@pytest.mark.parametrize("seed", (1, 15, 19, 27, 129, 385, 58723))
def test_repeated_second_image_occurrences(seed: int) -> None:
    carrier = CollatzHenselOccurrenceCarrier()
    value = seed
    for _ in range(12):
        first = accelerated_odd_collatz(value)
        second = accelerated_odd_collatz(first.target)
        occurrence = carrier.image_second(value)
        assert occurrence.value == second.target
        value = occurrence.value


def test_second_image_word_does_not_query_boundary_twice(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.collatz.root_germs import (
        RationalPadicRootGerm,
        RationalPadicRootMismatch,
    )

    original = RationalPadicRootGerm.first_mismatch_word
    calls: list[RationalPadicRootGerm] = []

    def forbidden(*_args: object, **_kwargs: object) -> None:
        raise AssertionError("direct second image constructed a first successor")

    def tracked(
        self: RationalPadicRootGerm, word: CanonicalWord
    ) -> tuple[RationalPadicRootMismatch, CanonicalWord]:
        calls.append(self)
        return original(self, word)

    monkeypatch.setattr(RationalPadicRootGerm, "first_mismatch_word", tracked)
    monkeypatch.setattr(frame.CollatzAffineSuffixGerm, "next_step", forbidden)
    monkeypatch.setattr(frame, "collatz_radix4_frame_factorization", forbidden)
    carrier = CollatzHenselOccurrenceCarrier()
    result = carrier.image_second(from_values(digits_lsd(129, 4)))
    assert result.value == 73
    assert len(calls) == 1
    with pytest.raises(ValueError, match="odd"):
        carrier.image_second(from_values((2,)))
