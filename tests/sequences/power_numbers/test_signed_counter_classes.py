"""Exact non-eager signed Fermat class actions and prime guard regressions."""

from __future__ import annotations

from dataclasses import replace
from random import Random

import pytest

from number_compiler.arithmetic.fields.walsh import WalshH5
from number_compiler.sequences.power_numbers.signed_counter_classes import (
    SignedCounterClassAction,
)
from number_compiler.sequences.power_numbers.three_dyadic_boolean_counter import (
    BinaryCounterFoldAction,
    demand_dyadic_boolean_counter,
)


def _independent_class_vector(
    source: int, addend: int, length: int, w: int, incoming: int
) -> tuple[tuple[int, int], ...]:
    mask = (1 << length) - 1
    output = (source + addend + incoming) & mask
    classes = [0] * w
    for i in range(length):
        delta = ((output >> i) & 1) - ((source >> i) & 1)
        classes[i % w] += delta if (i // w) % 2 == 0 else -delta
    return tuple((i, value) for i, value in enumerate(classes) if value)


def _reference_unit(t: int, modulus: int) -> int:
    numerator = pow(3, 1 << t, modulus)
    return ((numerator - 1) * pow(2, -(t + 2), modulus)) % modulus


def test_signed_class_fold_equivalence_and_full_mask_differentials() -> None:
    rng = Random(26015)
    for w in (1, 2, 3, 4, 7, 16, 32):
        modulus = (1 << w) + 1
        for _ in range(70):
            length = rng.randrange(1, 80)
            source = rng.getrandbits(length)
            addend = rng.getrandbits(length)
            action = SignedCounterClassAction.from_words(source, addend, length, w)
            scalar = BinaryCounterFoldAction.from_words(source, addend, length, w)
            assert action.residue_action == scalar
            for incoming in (0, 1):
                carry, signed, delta, harmonic = action.apply(incoming)
                result = (source + addend + incoming) & ((1 << length) - 1)
                assert carry == (source + addend + incoming) >> length
                assert signed == _independent_class_vector(
                    source, addend, length, w, incoming
                )
                assert delta == (result - source) % modulus
                assert sum((1 << p) * v for p, v in signed) % modulus == delta
                assert harmonic == WalshH5.from_mask(source ^ result, length)


def test_repeated_block_is_powered_without_materializing_copies() -> None:
    for w in (3, 8, 16):
        block = SignedCounterClassAction.from_words(0b100101, 0b011011, 6, w)
        for k in range(11):
            assert block.repeat(k) == (
                SignedCounterClassAction.identity(w)
                if k == 0
                else SignedCounterClassAction.from_words(
                    sum(0b100101 << (6 * j) for j in range(k)),
                    sum(0b011011 << (6 * j) for j in range(k)),
                    6 * k,
                    w,
                )
            )
        very_long = block.repeat(10**12)
        assert very_long.length == 6 * 10**12
        assert len(very_long.signed_classes[0]) <= w
        assert len(very_long.signed_classes[1]) <= w
        assert very_long.residue_action == block.residue_action.repeat(10**12)


def test_f4_f5_source_authenticated_windows_share_complete_classes() -> None:
    for w, levels, masks in (
        (16, (11, 12, 13, 14), (0xBB497389, 0x333E1D99, 0xD039D2BF, 0x56DBB589)),
        (32, (27, 28, 29, 30), (0x16A5CE8B, 0xCBEBF297, 0x367CF299, 0x8BA54D79)),
    ):
        for t, mask in zip(levels, masks):
            window = demand_dyadic_boolean_counter(t, 32, fermat_width=w)
            assert window.xor_mask == mask
            signed_action = window.signed_class_action
            assert signed_action.residue_action == window.fold_action
            signed = signed_action.apply(window.carry_in)[1]
            independent: dict[int, int] = {}
            for p, delta in window.signed_position_counts:
                class_r = p % w
                independent[class_r] = independent.get(class_r, 0) + (
                    delta if p < w else -delta
                )  # all p in demanded window lie below 2*w for these tests
            assert signed == _independent_class_vector(
                window.source_bits, window.addend_bits, 32, w, window.carry_in
            )
            assert tuple(
                sorted((r, count) for r, count in independent.items() if count)
            ) == (window.absolute_signed_classes)
            assert (
                signed_action.apply(window.carry_in)[2]
                == (window.fold_action.apply(window.carry_in)[1])
            )
            assert not window.covers_complete_unit_transition


def test_residue_moore_action_is_coarser_than_signed_witness() -> None:
    # Different signed-class transfers can yield identical carry/remainder/H5
    # future behavior for ANY appended authenticated operand block.
    a = SignedCounterClassAction.from_words(0, 450, 12, 3)
    b = SignedCounterClassAction.from_words(0, 1080, 12, 3)
    assert a.witness_id != b.witness_id
    assert a.semantic_id == b.semantic_id
    for higher in (
        SignedCounterClassAction.from_words(5, 9, 5, 3),
        SignedCounterClassAction.from_words(0, 0, 8, 3),
    ):
        assert a.then(higher).semantic_id == b.then(higher).semantic_id


def test_high_source_bits_cannot_be_discarded_by_a_low_counter_halo() -> None:
    # 2^(2*w) == 1 modulo the Fermat candidate, rather than zero.
    w = 16
    f = (1 << w) + 1
    x = 1
    y = x + (1 << (2 * w))
    assert (x & ((1 << w) - 1)) == (y & ((1 << w) - 1))
    assert (y - x) % f == 1
    # The low source observations agree, but a high edit changes the fold.
    # This is a generic obstruction, not a claim about true 3^2^t states.


def test_reject_noncanonical_class_payload_and_incompatible_widths() -> None:
    a = SignedCounterClassAction.from_words(0, 3, 2, 4)
    with pytest.raises(ValueError):
        replace(a, signed_classes=(((0, 1), (0, 2)), ()))
    with pytest.raises(ValueError):
        replace(a, signed_classes=(((8, 1),), ()))
    with pytest.raises(ValueError):
        a.then(SignedCounterClassAction.identity(8))


def test_terminal_demand_consumes_absolute_signed_classes_without_promotion() -> None:
    from number_compiler.sequences.power_numbers.terminal_source_demand import (
        SourceTerminalDemand,
    )

    for index in (4, 5):
        demand = SourceTerminalDemand.for_candidate("fermat", index)
        windows = demand.observe_fermat_boolean_counters(32)
        classes = demand.observe_fermat_signed_class_windows(32)
        modulus = (1 << (1 << index)) + 1
        assert len(classes) == 4
        for window, packet in zip(windows, classes):
            assert packet == window.absolute_signed_classes
            assert sum((1 << p) * count for p, count in packet) % modulus == (
                window.signed_fermat_correction
            )
            assert not window.covers_complete_unit_transition
        assert all(demand.missing_proofs)


def test_terminal_partial_classes_have_nonzero_missing_high_contribution() -> None:
    # Explicit research oracle only: this test evaluates powers modulo F_n.
    # The production quotient does not depend on or invoke it.
    from number_compiler.sequences.power_numbers.terminal_source_demand import (
        SourceTerminalDemand,
    )

    for index in (4, 5):
        width = 1 << index
        f = (1 << width) + 1
        demand = SourceTerminalDemand.for_candidate("fermat", index)
        windows = demand.observe_fermat_boolean_counters(128)
        for win in windows:
            exact = (
                _reference_unit(win.level + 1, f) - _reference_unit(win.level, f)
            ) % f
            assert (exact - win.signed_fermat_correction) % f != 0
            assert not win.covers_complete_unit_transition
