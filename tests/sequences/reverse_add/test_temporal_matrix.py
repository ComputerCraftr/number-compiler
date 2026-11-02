"""NC11 exact two-moment composition and non-oracle observer regressions."""

from __future__ import annotations

from random import Random
from typing import cast

import pytest

from number_compiler.resources.ledger import ResourceLedger, ResourceScope
from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
from number_compiler.sequences.reverse_add.temporal_matrix import (
    ReverseInnovationBank,
    SkewMoment,
    SourceBoundMoment,
)
from tests.support.reverse_pair_oracle import literal_decimal_borrow_tape


def reverse10(value: int) -> int:
    return int(str(value)[::-1])


def trajectory(seed: int, steps: int) -> list[int]:
    values = [seed]
    for _ in range(steps):
        value = values[-1]
        values.append(value + reverse10(value))
    return values


def test_skew_moments_are_associative_and_correct_on_actual_intervals() -> None:
    vals = trajectory(196, 125)
    for a, b, c in ((0, 9, 18), (79, 88, 97), (79, 97, 98), (119, 120, 122)):
        first = SourceBoundMoment.from_endpoints(vals[a], vals[b], steps=b - a)
        second = SourceBoundMoment.from_endpoints(vals[b], vals[c], steps=c - b)
        whole = first.then(second)
        expected = SourceBoundMoment.from_endpoints(vals[a], vals[c], steps=c - a)
        assert whole == expected
        assert whole.moment.matrix[0][1] == c - a
        assert whole.moment.apply(vals[a], reverse10(vals[a])) == (
            vals[c],
            reverse10(vals[c]),
        )
        if b - a == c - b:
            assert first.square_if_adjacent(second) == expected
    with pytest.raises(ValueError, match="seam mismatch"):
        first.then(SourceBoundMoment.primitive(196))


def test_conditional_matrix_square_is_not_a_physical_return_certificate() -> None:
    vals = trajectory(196, 98)
    actual = SourceBoundMoment.from_endpoints(vals[79], vals[88], steps=9)
    following = SourceBoundMoment.from_endpoints(vals[88], vals[97], steps=9)
    assert actual.square_if_adjacent(following).target == vals[97]
    assert actual.moment.square_formal() != actual.moment.then(following.moment)
    assert actual.moment.U != following.moment.U
    with pytest.raises(ValueError, match="seam mismatch"):
        actual.square_if_adjacent(actual)


def test_endpoint_join_rejects_same_width_mod7_residue_false_seam() -> None:
    first = SourceBoundMoment.primitive(196)
    second = SourceBoundMoment.from_endpoints(887, 1675, steps=1)
    joined = first.then(second)
    competing = SourceBoundMoment.primitive(1010)

    assert joined.target == 1675 == 887 + 788
    assert competing.source == 1010 == 109 + 901
    assert joined.target_width == competing.source_width == 4
    assert joined.target % 7 == competing.source % 7 == 2
    with pytest.raises(ValueError, match="source/target temporal seam mismatch"):
        joined.then(competing)


def test_formal_skew_quadratic_clock_large_exponent_without_replay() -> None:
    rng = Random(643)
    for _ in range(100):
        d = rng.randrange(1, 20)
        u = rng.randrange(-1000, 1000)
        v = rng.randrange(-1000, 1000)
        moment = SkewMoment(d, u, v)
        for count in (0, 1, 2, 3, 8, 100, 10**50):
            got = moment.power_formal(count)
            assert got.duration == d * count
            assert got.U == u * count
            assert got.V == count * v + d * u * count * (count - 1) // 2
            assert got.apply(37, 93) == (37 + count * d * 93 + got.V, 93 + count * u)
    a = SkewMoment(4, (-100) % 97, 27, 97)
    b = a.power_formal(10**12)
    assert b.U == (-100 * 10**12) % 97
    assert b.V == (27 * 10**12 + 4 * -100 * (10**12) * (10**12 - 1) // 2) % 97
    assert SkewMoment(0, 0, 0).matrix == ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def test_bank_carry_borrow_xor_partition_and_walsh() -> None:
    values = trajectory(196, 300)
    for index in (0, 1, 9, 10, 79, 80, 83, 87, 88, 98, 111, 119, 120, 122, 146, 252):
        x = values[index]
        prev = None if index == 0 else values[index - 1]
        bank = ReverseInnovationBank.observe(x, previous=prev)
        assert bank.masks_partition()
        lt_low, lt_high, _eq, gt_low, gt_high = bank.five_band_masks
        assert bank.lt_mask == lt_low | lt_high
        assert bank.gt_mask == gt_low | gt_high
        assert not (lt_high & gt_high)
        for position in range(bank.width // 2):
            reflected = bank.width - position - 1
            for mask in bank.five_band_masks:
                assert (mask >> position) & 1 == (mask >> reflected) & 1
        digits = [int(d) for d in str(x)[::-1]]
        for position, digit in enumerate(digits):
            pair = digit + digits[-1 - position]
            assert tuple((mask >> position) & 1 for mask in bank.five_band_masks) == (
                int(pair <= 4),
                int(5 <= pair <= 8),
                int(pair == 9),
                int(10 <= pair <= 14),
                int(15 <= pair <= 18),
            )
        assert bank.growth in (0, 1)
        digits = [int(d) for d in str(x)[::-1]]
        carry = 0
        for position, digit in enumerate(digits):
            carry = int(digit + digits[-1 - position] + carry >= 10)
            assert (bank.carry_mask >> position) & 1 == carry
        next_value = x + reverse10(x)
        next_reverse = reverse10(next_value)
        current_reverse = reverse10(x)
        assert bank.future_innovation_sign == (
            (next_reverse > current_reverse) - (next_reverse < current_reverse)
        )
        future_magnitude_borrow, magnitude_terminal = literal_decimal_borrow_tape(
            max(next_reverse, current_reverse),
            min(next_reverse, current_reverse),
            len(str(next_value)),
        )
        assert magnitude_terminal == 0
        assert bank.future_borrow_mask == future_magnitude_borrow
        assert bank.future_xor_mask == bank.carry_mask ^ future_magnitude_borrow
        if prev is None:
            assert bank.borrow_mask is None and bank.xor_mask is None
        else:
            borrow_mask, xor_mask = bank.borrow_mask, bank.xor_mask
            assert borrow_mask is not None and xor_mask is not None
            assert xor_mask == bank.carry_mask ^ borrow_mask
            reverse_value, reverse_previous = reverse10(x), reverse10(prev)
            assert bank.innovation_sign == (
                (reverse_value > reverse_previous) - (reverse_value < reverse_previous)
            )
            and_or = bank.and_or_masks
            assert and_or is not None
            and_mask, or_mask = and_or
            assert (and_mask ^ or_mask) == bank.xor_mask
            assert len(bank.xor_walsh64 or ()) == 64
            assert all(-64 <= h <= 64 for h in bank.xor_walsh64 or ())
        for entry in bank.modular:
            m = entry.modulus
            assert entry.carry == int(x % m + reverse10(x) % m >= m)
            if prev is not None:
                r = reverse10(x)
                rp = reverse10(prev)
                a, b = max(r, rp), min(r, rp)
                assert entry.innovation_borrow == int(a % m < b % m)
                assert entry.innovation_borrow is not None
                assert entry.xor == entry.carry ^ entry.innovation_borrow


def test_authenticated_term_matrix_uses_production_q19_and_budget() -> None:
    values = trajectory(196, 32)
    for index in (0, 1, 3, 16, 32):
        term = ReverseAddPoweredTerm(196, index)
        try:
            result = term.temporal_matrix(max_bits=2048)
            assert result.target == values[index]
            assert result.moment.apply(196, 691) == (
                values[index],
                reverse10(values[index]),
            )
            bank = term.temporal_stencil(max_bits=2048, max_digits=8192)
            assert bank.width == len(str(values[index]))
            assert bank.masks_partition()
        finally:
            if term.published_workspace is not None:
                term.published_workspace.dispose()
    term = ReverseAddPoweredTerm(196, 64)
    with pytest.raises(ValueError):
        term.temporal_matrix(max_bits=16)
    assert term.published_workspace is None


def test_reject_incomplete_bad_clock_and_wrong_banks() -> None:
    with pytest.raises(ValueError):
        SkewMoment(0, 1, 0)
    with pytest.raises(ValueError):
        SkewMoment(2, -1, 0, 19)
    with pytest.raises(ValueError):
        SkewMoment(2, 1, 1).then(SkewMoment(3, 0, 0, 7))
    with pytest.raises(ValueError):
        ReverseInnovationBank.observe(196, moduli=(9, 9))
    with pytest.raises(ValueError):
        ReverseInnovationBank.observe(196, max_digits=2)
    with pytest.raises(ValueError):
        SourceBoundMoment.from_endpoints(196, 999_999, steps=1)


def test_bank_rejects_oversized_operands_before_decimal_decode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.sequences.reverse_add import temporal_matrix

    def forbidden_decode(*_args: object, **_kwargs: object) -> tuple[int, ...]:
        raise AssertionError("oversized stencil operand reached decimal decoding")

    monkeypatch.setattr(temporal_matrix, "digits_lsd", forbidden_decode)
    with pytest.raises(ValueError, match="digit budget"):
        ReverseInnovationBank.observe(10**1000, max_digits=32)
    with pytest.raises(ValueError, match="previous innovation source"):
        ReverseInnovationBank.observe(196, previous=10**1000, max_digits=32)


def test_endpoint_moment_observation_cannot_enter_q19_execution() -> None:
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.sequences.reverse_add.q19_output import (
        ReversePairOutputOccurrence,
        ReversePairQ19OutputOwner,
    )

    observation = SourceBoundMoment.from_endpoints(196, 196, steps=0)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(196, 10), base=10)
    try:
        with pytest.raises(TypeError, match="exact Q19 output occurrence"):
            owner.apply_punctured_pair_block(
                cast(ReversePairOutputOccurrence, observation), steps=2
            )
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


def test_modular_projection_from_q19_compressed_carry_ports() -> None:
    from number_compiler.sequences.reverse_add.pair_numeric_ports import (
        project_q19_numeric,
    )

    vals = trajectory(196, 122)
    for index in (0, 1, 2, 9, 16, 79, 87, 88, 98, 119, 120, 122):
        term = ReverseAddPoweredTerm(196, index)
        try:
            for modulus in (2, 9, 11, 17, 99, 1009, 2**64 - 59):
                moment = term.temporal_moments(modulus=modulus)
                source_mod, reverse_mod = moment.apply(196, 691)
                assert source_mod == vals[index] % modulus
                assert reverse_mod == reverse10(vals[index]) % modulus
            if index > 0:
                workspace = term.published_workspace
                assert workspace is not None
                image = workspace.audit_snapshot().image
                assert image is not None
                view = workspace.scheduler.source_image_core().view(image)
                from number_compiler.sequences.reverse_add.source_images import (
                    ReverseImagePayload,
                )

                payload = cast(ReverseImagePayload, view.payload)
                occurrence = payload.pair_output
                owner = workspace.adapter.audit_snapshot().q19_owner
                assert occurrence is not None and owner is not None
                result = project_q19_numeric(owner, occurrence, modulus=1009)
                assert result.output_width == len(str(vals[index]))
                assert result.target_mod == vals[index] % 1009
                assert result.reverse_target_mod == reverse10(vals[index]) % 1009
                assert (
                    workspace.ledger.counters.get(
                        "recursive_output_stream_emitted_digits", 0
                    )
                    == 0
                )
        finally:
            if term.published_workspace is not None:
                term.published_workspace.dispose()


def test_q19_million_cell_repeat_numeric_ports_no_expansion() -> None:
    from number_compiler.arithmetic.automata.slp import SLPArena
    from number_compiler.sequences.reverse_add.pair_numeric_ports import (
        fold_pair_slp,
    )

    arena = SLPArena()
    root = arena.repeat(arena.terminal(9), 10**12)
    modulus = 1009
    ledger = ResourceLedger()
    workspace_owner = ledger.register(
        "test-q19-numeric-fold", "temporary_work", scope=ResourceScope.INDEX_OWNED
    )
    result = fold_pair_slp(
        arena,
        root,
        modulus=modulus,
        ledger=ledger,
        workspace_owner=workspace_owner,
    )
    n = 10**12
    assert result.length == n
    assert result.forward.outgoing[0] == 0
    assert result.backward.outgoing[0] == 0
    nine_word = pow(10, n, modulus) - 1
    assert result.forward.forward[0] == nine_word % modulus
    assert result.backward.reversed[0] == nine_word % modulus
    assert result.prefix_forward.length == n - 1
    assert result.prefix_backward.length == n - 1
    assert ledger.entries == ledger.nodes == 0
    ledger.mark_disposed(workspace_owner)


def test_numeric_fold_workspace_releases_on_operator_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    from number_compiler.arithmetic.automata.slp import SLPArena
    from number_compiler.sequences.reverse_add.pair_numeric_ports import (
        DecimalPairNumericPort,
        fold_pair_slp,
    )

    def fail_composition(
        _self: DecimalPairNumericPort,
        _high: DecimalPairNumericPort,
        *,
        ledger: ResourceLedger | None = None,
    ) -> DecimalPairNumericPort:
        del ledger
        raise RuntimeError("injected numeric port composition failure")

    monkeypatch.setattr(DecimalPairNumericPort, "then", fail_composition)
    arena = SLPArena()
    root = arena.concat(arena.terminal(8), arena.terminal(7))
    ledger = ResourceLedger()
    workspace_owner = ledger.register(
        "test-q19-numeric-fold-failure",
        "temporary_work",
        scope=ResourceScope.INDEX_OWNED,
    )
    with pytest.raises(RuntimeError, match="injected"):
        fold_pair_slp(
            arena,
            root,
            modulus=1009,
            ledger=ledger,
            workspace_owner=workspace_owner,
        )
    assert ledger.entries == ledger.nodes == 0
    ledger.mark_disposed(workspace_owner)


def test_zero_is_a_source_certified_fixed_point_without_q19() -> None:
    for depth in (0, 1, 4, 31, 1_000_000):
        term = ReverseAddPoweredTerm(0, depth)
        assert term.temporal_moments(modulus=1009).apply(0, 0) == (0, 0)
        assert term.published_workspace is None
