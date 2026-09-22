"""Shared F5 spatial consumers on the actual centered Antihydra cylinders.

The references are bounded numeral arithmetic. Spatial observation does not
replace source admission, the fractional guard, or the ledger minimum.
"""

from devtools.experiments.antihydra.spatial_carry import (
    block_carry_action,
    compress_repeated_block,
)
from number_compiler.arithmetic.carry.collatz_f5_quotient import (
    RADIX64_F5_SPATIAL_LEAVES,
    CollatzF5SpatialAction,
    radix64_f5_class,
    radix64_f5_directional_views,
    radix64_pair_f5_views,
)
from number_compiler.arithmetic.carry.collatz_output_quotient import (
    DOMAIN_ACTIONS,
    radix64_geometry_emit,
)
from number_compiler.arithmetic.fields.morphism_core import binary_power
from number_compiler.sequences.antihydra.blocks import admitted_arithmetic_cylinder


def test_mahler_spatial_multiplier_uses_the_same_complete_carry_ports() -> None:
    for low in range(64):
        for high in range(64):
            shared = RADIX64_F5_SPATIAL_LEAVES[low].then(
                RADIX64_F5_SPATIAL_LEAVES[high]
            )
            reference = block_carry_action(3, 64**2, low + 64 * high)
            for incoming in range(3):
                assert DOMAIN_ACTIONS[shared.carry_action][incoming] == reference.apply(
                    incoming
                )


def test_shared_directional_f5_output_matches_centered_production_all_two_cells() -> (
    None
):
    cores = tuple(admitted_arithmetic_cylinder(bit, 1) for bit in range(2))
    for residue in range(64**2):
        low, high = residue % 64, residue // 64
        carry, raw_low = radix64_geometry_emit(low, 1)
        _, raw_high = radix64_geometry_emit(high, carry)
        left, _ = radix64_f5_directional_views(raw_low, 1)
        _, right = radix64_f5_directional_views(raw_high, 1)
        observed = radix64_pair_f5_views(left, right, 1)
        for high_fiber in (1, 2**80 + 37):
            centered = residue + 64**2 * high_fiber
            h = centered + 1
            after, ledger = cores[h % 2].advance(h, 0)
            # Independent total arithmetic reference; no production point evaluator.
            assert after == h + h // 2
            assert after - 1 == (3 * centered + 1) // 2
            assert ledger == (2 if h % 2 == 0 else -1)
            assert observed == radix64_f5_class((after - 1) % 64)


def test_odd_event_transfer_keeps_antihydras_extra_multiplier_and_ledger() -> None:
    gaps = set()
    for source in range(5, 4096, 2):
        numerator = 3 * source + 1
        gap = (numerator & -numerator).bit_length() - 1
        gaps.add(gap)
        h = source + 1
        core = admitted_arithmetic_cylinder(h % (1 << gap), gap)
        after, ledger = core.advance(h, 0)
        assert after - 1 == 3 ** (gap - 1) * (numerator >> gap)
        assert ledger == core.delta == 3 - gap
        assert core.minimum == min(0, 3 - gap)
        # h is even at the centered odd event, then odd until the next event.
        assert core.parity_word == (1 << gap) - 2
    assert {1, 2, 4, 6, 8, 10, 12} <= gaps


def test_binary_spatial_power_matches_mahler_fixed_carry_without_expanding_word() -> (
    None
):
    def compose(
        first: CollatzF5SpatialAction | None, second: CollatzF5SpatialAction | None
    ) -> CollatzF5SpatialAction | None:
        if first is None:
            return second
        if second is None:
            return first
        return first.then(second)

    for repetitions in (1, 5, 10**12, 5**64):
        for digit, leaf in enumerate(RADIX64_F5_SPATIAL_LEAVES):
            powered = binary_power(leaf, repetitions, identity=None, compose=compose)
            assert powered.value is not None
            assert leaf.repeat(repetitions) == powered.value
            assert (
                powered.compositions
                == repetitions.bit_count() + repetitions.bit_length() - 1
            )
            assert powered.value.phase == repetitions * leaf.phase % 5
            for incoming in range(3):
                reference = compress_repeated_block(3, 64, digit, incoming, repetitions)
                assert reference.checked_steps <= 2
                assert (
                    DOMAIN_ACTIONS[powered.value.carry_action][incoming]
                    == reference.outgoing_carry
                )


def test_spatial_class_collision_still_needs_the_centered_source_boundary() -> None:
    a, b = 67, 75
    assert tuple(RADIX64_F5_SPATIAL_LEAVES[d] for d in (a % 64, a // 64)) == tuple(
        RADIX64_F5_SPATIAL_LEAVES[d] for d in (b % 64, b // 64)
    )
    core = admitted_arithmetic_cylinder(0, 1)
    first, _ = core.advance(a + 1, 0)
    second, _ = core.advance(b + 1, 0)
    assert (first - 1, second - 1) == (101, 113)
    assert radix64_f5_class((first - 1) % 64) != radix64_f5_class((second - 1) % 64)
    # This is an observer collision, not a counterexample to a complete cylinder.


def test_antihydra_centered_macro_uses_same_primary_birth_transport() -> None:
    """Bounded refinement against admitted macros; no all-time guard claim."""
    from number_compiler.arithmetic.carry.collatz_binary_forcing import (
        binary_carry_birth,
    )
    from number_compiler.arithmetic.fields.radix import digits_lsd
    from number_compiler.arithmetic.polynomials.primary_jet import (
        PrimaryJetAffineMorphism,
        primary_jet_from_digits,
    )

    def jet(value: int) -> tuple[int, ...]:
        return primary_jet_from_digits(digits_lsd(value, 2), degree=5, modulus=32).jet

    cores = tuple(admitted_arithmetic_cylinder(bit, 1) for bit in range(2))
    for source in (5, 7, 27, 129, 931386509544713450):
        centered = source
        combined = PrimaryJetAffineMorphism.identity(5, 32)
        suffix = []
        for k in range(1, 17):
            birth = binary_carry_birth(centered, incoming=centered % 2)
            event = PrimaryJetAffineMorphism.binary_event(1, birth)
            suffix.append(event)
            combined = combined.then(event)
            h = centered + 1
            after, _ledger = cores[h % 2].advance(h, 0)
            centered = after - 1
            assert centered == (3 * (h - 1) + (h - 1) % 2) // 2
            assert combined.apply(jet(source)) == jet(centered)
            assert combined.source_annihilated == (k >= 5)
            if k >= 5:
                last = PrimaryJetAffineMorphism.identity(5, 32)
                for item in suffix[-5:]:
                    last = last.then(item)
                assert combined.canonical_key == last.canonical_key
