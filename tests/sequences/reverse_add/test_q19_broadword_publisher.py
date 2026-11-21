"""Exact source tests for the width-growing Q19 pair-sum publisher."""

from itertools import product
from random import Random

import pytest

from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_broadword_publisher import PackedQ19
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from tests.support.reference_arithmetic import (
    literal_reverse_add_digits,
    radix_digits_lsd,
)


def test_packed_q19_successor_matches_independent_decimal_oracle() -> None:
    random = Random(7109)
    seeds: tuple[int, ...] = (
        0,
        1,
        9,
        10,
        19,
        99,
        196,
        100001,
        1000000001,
        10999,
        99999,
    )
    seeds += tuple(random.randrange(10**9) for _ in range(12))
    for seed in seeds:
        frame = PackedQ19.from_digits(radix_digits_lsd(seed, 10))
        for steps in range(1, 13):
            frame, emitted = frame.advance(emit_digits=True)
            expected = literal_reverse_add_digits(seed, steps)
            assert emitted == expected
            assert frame == PackedQ19.from_digits(expected)


def test_native_lower_carry_sweep_covers_every_three_pair_chain() -> None:
    from tests.support.reference_arithmetic import literal_pair_sum_successor

    for outer, middle, inner in product(range(1, 19), range(19), range(19)):
        packed = outer | (middle << 6) | (inner << 12)
        frame = PackedQ19(packed, 3, None)
        target, emitted = frame.advance(emit_digits=True)
        pair_field = (outer, middle, inner, inner, middle, outer)
        expected_pairs, _ = literal_pair_sum_successor(pair_field)
        expected_value = sum(pair * 10**index for index, pair in enumerate(pair_field))
        assert emitted is not None
        assert emitted == radix_digits_lsd(expected_value, 10)
        assert target == PackedQ19.from_digits(emitted)
        assert expected_pairs == tuple(
            digit + reflected
            for digit, reflected in zip(emitted, reversed(emitted), strict=True)
        )


def test_q19_palindrome_preimage_matches_literal_successor() -> None:
    for seed in range(10000):
        frame = PackedQ19.from_digits(radix_digits_lsd(seed, 10))
        target = seed + int(str(seed)[::-1])
        assert frame.next_is_palindrome() == (str(target) == str(target)[::-1])


def test_wide_growth_preimage_checks_each_pair_and_odd_center() -> None:
    count = 1024
    pairs = sum((11 if index % 3 else 0) << (6 * index) for index in range(count)) | 11
    assert PackedQ19(pairs, count, 0).next_is_palindrome()
    position = 713
    corrupted = (pairs & ~(63 << (6 * position))) | (10 << (6 * position))
    assert not PackedQ19(corrupted, count, 0).next_is_palindrome()
    assert not PackedQ19(pairs, count, 1).next_is_palindrome()


def test_joint_ordinary_xor_inverse_authenticates_one_reflected_source() -> None:
    from number_compiler.arithmetic.carry.joint_output_inverse import (
        recover_joint_operands,
    )

    for source in range(256):
        for reflected in range(256):
            ordinary = source + reflected
            xor = source + (source ^ reflected)
            assert recover_joint_operands(ordinary, xor) == (source, reflected)
    for source in (0, 10, 92, 98, 196, 216, 480):
        reflected = int(str(source)[::-1])
        frame = PackedQ19.from_joint_outputs(
            source + reflected, source + (source ^ reflected)
        )
        assert frame == PackedQ19.from_digits(radix_digits_lsd(source, 10))
    with pytest.raises(ValueError, match="decimal reflection"):
        PackedQ19.from_joint_outputs(12 + 34, 12 + (12 ^ 34))


def test_bounded_palindrome_search_reports_first_positive_arrival() -> None:
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

    term = ReverseAddPoweredTerm(196, 0)
    assert term.first_palindrome_within(0) is None
    assert term.first_palindrome_within(10) is None
    assert ReverseAddPoweredTerm(92, 0).first_palindrome_within(1) == 1
    assert ReverseAddPoweredTerm(98, 0).first_palindrome_within(1) is None


@pytest.mark.parametrize("seed", (1, 196))
def test_root_decimal_broadword_publisher_issues_exact_terminal_output(
    seed: int,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, radix_digits_lsd(seed, 10), base=10)
    try:
        occurrence = owner.publish_broadword_source(64)
        assert occurrence.temporal_steps == 64
        assert tuple(owner.iter_digits(occurrence)) == literal_reverse_add_digits(
            seed, 64
        )
        counters = ledger.counters
        assert counters["reverse_q19_broadword_semantic_steps"] == 63
        assert counters["reverse_q19_broadword_endpoint_publications"] == 1
        assert counters.get("reverse_q19_primitive_pair_applications", 0) == 0
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_broadword_owner_hit_precedes_source_pair_reconstruction(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    owner = ReversePairQ19OutputOwner(
        ResourceLedger(), radix_digits_lsd(196, 10), base=10
    )
    try:
        first = owner.publish_broadword_source(64)

        def forbidden(*_args: object, **_kwargs: object) -> object:
            raise AssertionError("warm Q19 lookup rebuilt its pair state")

        monkeypatch.setattr(PackedQ19, "from_digits", forbidden)
        monkeypatch.setattr(owner, "_full_summary", forbidden)
        assert owner.publish_broadword_source(64) is first
    finally:
        owner.dispose()


def test_broadword_rejects_noncanonical_packed_sources() -> None:
    with pytest.raises(ValueError, match="canonical decimal digits"):
        PackedQ19.from_digits((1, True, 9))
    with pytest.raises(ValueError, match="leading zero"):
        PackedQ19.from_digits((1, 0))
    with pytest.raises(ValueError, match="packed Q19 pair extent"):
        PackedQ19(1 << 6, 1, None)
    with pytest.raises(ValueError, match="packed Q19 pair extent"):
        PackedQ19(-1, 1, None)
    with pytest.raises(ValueError, match="packed Q19 pair lane"):
        PackedQ19(19, 1, None)
    with pytest.raises(ValueError, match="packed Q19 pair lane"):
        PackedQ19(63, 1, None)
    with pytest.raises(ValueError, match="zero leading pair"):
        PackedQ19(0, 1, None)
    assert PackedQ19.from_digits(radix_digits_lsd(100001, 10)).count == 3
    assert PackedQ19.from_digits(radix_digits_lsd(1000000001, 10)).count == 5


def test_equal_pair_states_preserve_both_directional_carry_seams() -> None:
    first_digits = (1, 2, 7, 8)
    second_digits = (3, 4, 5, 6)
    first = PackedQ19.from_digits(first_digits)
    second = PackedQ19.from_digits(second_digits)
    assert first == second
    first_target, first_output = first.advance(emit_digits=True)
    second_target, second_output = second.advance(emit_digits=True)
    assert first_target == second_target
    assert first_output == second_output
    first_seed = sum(digit * 10**index for index, digit in enumerate(first_digits))
    second_seed = sum(digit * 10**index for index, digit in enumerate(second_digits))
    assert first_output == literal_reverse_add_digits(first_seed, 1)
    assert second_output == literal_reverse_add_digits(second_seed, 1)


def test_broadword_publication_failure_rolls_back_endpoint_and_suffix(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, radix_digits_lsd(196, 10), base=10)
    try:
        issued_before = dict(owner.audit_snapshot().issued.payload_view)
        nodes_before = len(owner.arena.nodes)
        entries_before, ledger_nodes_before = ledger.entries, ledger.nodes

        def fail_candidate(*_args: object, **_kwargs: object) -> object:
            raise RuntimeError("injected terminal certificate failure")

        monkeypatch.setattr(owner, "candidate", fail_candidate)
        with pytest.raises(RuntimeError, match="terminal certificate"):
            owner.publish_broadword_source(64)
        counters = ledger.counters
        assert counters["reverse_q19_broadword_semantic_steps"] == 63
        assert counters.get("reverse_q19_broadword_endpoint_publications", 0) == 0
        assert counters["reverse_q19_broadword_prefix_rounds"] > 0
        assert counters["reverse_q19_broadword_operand_bits"] > 0
        assert dict(owner.audit_snapshot().issued.payload_view) == issued_before
        assert len(owner.arena.nodes) == nodes_before
        assert (ledger.entries, ledger.nodes) == (
            entries_before,
            ledger_nodes_before,
        )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_palindrome_outer_and_center_rejections_skip_lane_masks(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add import q19_broadword_publisher

    def fail(_count: int) -> tuple[int, int]:
        pytest.fail("rejected source constructed the full lane mask")

    frames = (PackedQ19(18, 1, None), PackedQ19(11, 1, 3), PackedQ19(8, 1, 5))
    monkeypatch.setattr(q19_broadword_publisher, "_lane_masks", fail)
    for frame in frames:
        assert not frame.next_is_palindrome()
