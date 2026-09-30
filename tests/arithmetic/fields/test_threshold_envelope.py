"""Independent rational prefix oracles for the shared safety normal form."""

from fractions import Fraction
from itertools import accumulate, product
from operator import add, mul

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import (
    ExactRational as Q,
)
from number_compiler.arithmetic.fields.consumer_pullback import (
    PrefixSafety,
)
from number_compiler.arithmetic.fields.morphism_core import AffineCocycle
from number_compiler.arithmetic.fields.skew_transfer import SkewTransfer
from number_compiler.arithmetic.fields.threshold_envelope import ThresholdEnvelope


def test_complete_prefix_envelope_and_associative_chronological_pullback() -> None:
    actions = (SkewTransfer(3, 1, 2), SkewTransfer(3, 1, 16), SkewTransfer(3, 1, 4))
    envelopes = tuple(
        ThresholdEnvelope.affine(Q(a.upper, a.lower), Q(a.offset, a.lower))
        for a in actions
    )
    a, b, _unused_c_binding = actions
    ea, eb, ec = envelopes
    ab = a.then(b, multiply=mul, add=add)
    left = ea.then(a, eb).then(ab, ec)
    right = ea.then(a, eb.then(b, ec))
    assert left == right
    assert ThresholdEnvelope.normalize(left.lines) == left
    for source, threshold in product(range(-4, 25), range(-3, 25)):
        value = Fraction(source)
        values = []
        for action in actions:
            value = (action.upper * value + action.offset) / action.lower
            values.append(value)
        boundary = left.evaluate(Q(threshold))
        assert boundary is not None
        exact = Fraction(boundary.numerator, boundary.denominator)
        assert (source < exact) == any(value < threshold for value in values)
        assert (source > exact) == all(value > threshold for value in values)


def test_envelope_forgets_dominated_lines_not_admission_or_domain() -> None:
    line = AffineCocycle(Q(2), Q(-1))
    assert ThresholdEnvelope(
        (line, line, AffineCocycle(Q(2), Q(-4)))
    ) == ThresholdEnvelope((line,))
    empty = ThresholdEnvelope(())
    assert empty.evaluate(Q(0)) is None
    assert empty.then(
        SkewTransfer(1, 0, 1), ThresholdEnvelope((line,))
    ) == ThresholdEnvelope((line,))
    with pytest.raises(BlockContextBudgetExceeded):
        ThresholdEnvelope.normalize((line, line), max_lines=1)
    with pytest.raises(ValueError, match="positive"):
        empty.then(
            SkewTransfer(0, 4, 1), empty
        )  # Singleton shortcut is not a cylinder.
    with pytest.raises(ValueError, match="positive"):
        ThresholdEnvelope((AffineCocycle(Q(0), Q(1)),))
    with pytest.raises(ValueError, match="positive"):
        ThresholdEnvelope.affine(Q(0), Q(1))
    with pytest.raises(ValueError, match="1..4096"):
        empty.then(SkewTransfer(1, 0, 1), empty, max_lines=4097)


def test_upper_hull_preserves_crossings_and_negative_thresholds() -> None:
    for intercepts in product((-3, 0, 4), repeat=4):
        lines = tuple(
            AffineCocycle(Q(i + 1, 3), Q(b)) for i, b in enumerate(intercepts)
        )
        envelope = ThresholdEnvelope(lines)
        assert envelope == ThresholdEnvelope(tuple(reversed(lines)))
        for numerator in range(-40, 41):
            threshold = Fraction(numerator, 3)
            expected = max(
                Fraction(i + 1, 3) * threshold + b for i, b in enumerate(intercepts)
            )
            result = envelope.evaluate(Q(numerator, 3))
            assert result is not None
            assert Fraction(result.numerator, result.denominator) == expected


def test_prefix_safety_repetition_and_first_failure_include_negative_drift() -> None:
    for weights in product((-2, 0, 3), repeat=3):
        prefixes = tuple(accumulate(weights, initial=0))
        safety = PrefixSafety(prefixes[-1], min(prefixes))
        for copies in range(7):
            repeated = tuple(accumulate(weights * copies, initial=0))
            assert safety.repeat(copies) == PrefixSafety(repeated[-1], min(repeated))
            for balance in range(7):
                expected = next(
                    (
                        i
                        for i in range(copies)
                        if balance + i * safety.delta + safety.minimum < 0
                    ),
                    None,
                )
                assert safety.first_failing_copy(balance, copies) == expected
    falling = PrefixSafety(-2, -3)
    assert falling.first_failing_copy(10**18 + 3, 10**30) == 5 * 10**17 + 1
    assert PrefixSafety(3, -1).repeat(10**30) == PrefixSafety(3 * 10**30, -1)
