"""Differential and source-ownership checks for Q19 same-column action reuse."""

from random import Random

import pytest

from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19
from number_compiler.sequences.reverse_add.q19_repeat_port import Q19RepeatPortState
from number_compiler.sequences.reverse_add.temporal_boolean_ring_2_11 import (
    BCDPlanes,
    Powered211CarrySheets,
)


def _oracle(digits: tuple[int, ...]) -> tuple[tuple[int, ...], int, int]:
    width = len(digits)
    carry = 0
    carry_in = 0
    output: list[int] = []
    for j, digit in enumerate(digits):
        carry_in |= carry << j
        total = digit + digits[width - 1 - j] + carry
        output.append(total % 10)
        carry = total // 10
    if carry:
        output.append(carry)
    equal = sum(1 << j for j in range(width) if digits[j] == output[j])
    return tuple(output), equal, carry_in


def _check_step(digits: tuple[int, ...]) -> None:
    state = Q19RepeatPortState.from_digits(digits)
    future, action, emitted = state.advance(emit_digits=True)
    expected, same, cin = _oracle(digits)
    assert emitted == expected
    assert future.frame == PackedQ19.from_digits(expected)
    assert action.same_lsd == same
    assert action.carry_in_lsd == cin
    assert sum(x.bit_count() for x in action.value_masks) == same.bit_count()
    assert future.zero_lsd == sum(1 << j for j, d in enumerate(expected) if d == 0)
    assert future.nine_lsd == sum(1 << j for j, d in enumerate(expected) if d == 9)
    for j, digit in enumerate(digits):
        assert action.symbol_at(j) == (digit if same & (1 << j) else None)
    assert Q19RepeatPortState.from_digits(digits).advance()[2] is None


def test_exact_mask_randomized_width_and_births() -> None:
    rng = Random(1962026)
    for width in range(1, 120):
        for _ in range(10):
            digits = tuple(rng.randrange(10) for _ in range(width - 1)) + (
                rng.randrange(1, 10),
            )
            _check_step(digits)


@pytest.mark.parametrize(
    "digits",
    [
        (1,),
        (9,),
        (0,),
        (9, 9),
        (0, 0, 1),
        (0, 9, 1),
        (9, 0, 9),
        (1, 2, 0, 8),
        (1, 1, 1, 8),
        (6, 9, 1),
        (2, 2, 2, 2, 2),
        (9,) * 257,
        (0,) * 256 + (1,),
    ],
)
def test_exact_mask_guard_and_large_width(digits: tuple[int, ...]) -> None:
    _check_step(digits)


def test_pair_carry_sheets_alone_cannot_derive_repeat_mask() -> None:
    a = (1, 2, 0, 8)  # 8021
    b = (1, 1, 1, 8)  # 8111
    assert PackedQ19.from_digits(a) == PackedQ19.from_digits(b)
    ta, ra, oa = Q19RepeatPortState.from_digits(a).advance(emit_digits=True)
    tb, rb, ob = Q19RepeatPortState.from_digits(b).advance(emit_digits=True)
    assert oa == ob == (9, 2, 2, 9)
    assert ta.frame == tb.frame
    assert ra.carry_in_lsd == rb.carry_in_lsd
    assert ra.same_lsd == 0b10
    assert rb.same_lsd == 0


def test_two_five_boolean_planes_feed_same_q19_repeat_action() -> None:
    rng = Random(20261114)
    for width in range(1, 65):
        for _ in range(3):
            source = tuple(rng.randrange(10) for _ in range(width - 1)) + (
                rng.randrange(1, 10),
            )
            q2, r5 = BCDPlanes.from_digits(source).two_five_complementary_sheets()
            from_carry = Q19RepeatPortState.from_two_five_carry_planes(q2, r5, width)
            from_digits = Q19RepeatPortState.from_digits(source)
            assert from_carry == from_digits
            assert from_carry.advance() == from_digits.advance()


def test_source_196_successor_masks_remain_valid_for_512_steps() -> None:
    state = Q19RepeatPortState.from_digits((6, 9, 1))
    source = (6, 9, 1)
    repeats = 0
    for _ in range(512):
        nxt, action, _unused = state.advance()
        expected, same, carry = _oracle(source)
        assert action.same_lsd == same
        assert action.carry_in_lsd == carry
        assert nxt.frame == PackedQ19.from_digits(expected)
        repeats += action.reusable_single_digit_generators
        source = expected
        state = nxt
    assert repeats > 0


def test_homogeneous_stage_q19_reuse_consumes_two_five_sheets() -> None:
    for exponents in ((0, 0), (3, 5), (19, 47), (100, 400)):
        stage = Powered211CarrySheets.from_seed(196, *exponents, 15)
        digits, reuse = stage.q19_next_with_repeats()
        assert digits == stage.q19_next()
        original = stage.source.trimmed_digits_lsd()
        _expected, same, carry = _oracle(original)
        assert reuse.same_lsd == same
        assert reuse.carry_in_lsd == carry
        assert reuse.width == len(original)


def test_repeat_certificate_is_not_a_future_source_period() -> None:
    state = Q19RepeatPortState.from_digits((1, 2, 0, 8))
    future, action, _digits = state.advance()
    assert action.same_lsd == 0b10
    # Different next-source masks are not evidence of a repeating action.
    assert state.frame != future.frame
