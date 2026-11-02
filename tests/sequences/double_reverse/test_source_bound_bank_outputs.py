"""Independent checks for source-bound spatial bank and residue outputs."""

from __future__ import annotations

from dataclasses import dataclass, replace

import pytest

from number_compiler.arithmetic.automata.slp import SLPArena
from number_compiler.arithmetic.fields.skew_moments import SkewMoment
from number_compiler.resources.metric_keys.double_reverse import (
    DOUBLE_REVERSE_PERIODIC_BANK_MOORE_CONSTRUCTIONS,
    DOUBLE_REVERSE_PERIODIC_BANK_MOORE_OUTPUT_EVALUATIONS,
    DOUBLE_REVERSE_PERIODIC_BANK_TEMPORAL_STATES,
)
from number_compiler.sequences.double_reverse._temporal_bank_authority import (
    SourceAuthorizedRecord,
    issue_source_record,
    snapshot_value,
    validate_source_record,
)
from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
from number_compiler.sequences.double_reverse.protected_temporal_bank import (
    BANK_CHANNELS,
)
from number_compiler.sequences.double_reverse.source_bound_bank import (
    PointedBankSource,
    exact_temporal_pair_digits,
)
from number_compiler.sequences.double_reverse.temporal_bank_output_morphism import (
    ExactPointedBankWindow,
    frame_from_digits,
)
from number_compiler.sequences.double_reverse.temporal_hashlife import (
    PHYSICAL_GROWTH_CYCLES,
    growth_ports,
)
from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
    CertifiedResidueTemporalAction,
    certified_width_moments,
)


@dataclass(frozen=True, slots=True)
class _SkewMomentLookalike:
    duration: int
    U: int
    V: int
    modulus: int | None = None


@dataclass(frozen=True, slots=True)
class _NestedSnapshotRecord(SourceAuthorizedRecord):
    moments: object


@pytest.mark.parametrize("phase", range(4))
@pytest.mark.parametrize("steps", (0, 1, 3, 4, 9, 513))
def test_certified_width_moments_use_shared_skew_monoid(phase: int, steps: int) -> None:
    cycle = PHYSICAL_GROWTH_CYCLES[phase]
    growth = tuple(cycle[index % len(cycle)] for index in range(steps))
    expected = (
        steps,
        sum(growth),
        sum((steps - index - 1) * bit for index, bit in enumerate(growth)),
    )

    action = certified_width_moments(phase, steps)

    assert type(action) is SkewMoment
    assert (action.duration, action.U, action.V) == expected


@pytest.mark.parametrize(("phase", "steps"), ((True, 1), (0, True)))
def test_certified_width_moments_reject_boolean_coordinates(
    phase: int, steps: int
) -> None:
    with pytest.raises(ValueError):
        certified_width_moments(phase, steps)


def _literal(seed: int, steps: int) -> int:
    value = seed
    for _ in range(steps):
        value = 2 * int(str(value)[::-1])
    return value


def test_source_residue_action_is_sealed_to_its_certified_prefix() -> None:
    seed = int("17" + "48" * 30 + "88")
    with DoubleReverseTerm(seed, 12) as term:
        expected = _literal(seed, 12)
        prefix, action = term.temporal_residue_quotient()
        assert prefix == 0
        action.validate_source_authority()
        assert action.target_mod99 == expected % 99
        assert action.target_mod198 == expected % 198
        forged = replace(action, target_mod99=(action.target_mod99 + 1) % 99)
        with pytest.raises(ValueError, match="authority"):
            forged.validate_source_authority()
        original_phase = action.phase
        object.__setattr__(action, "phase", bool(original_phase))
        with pytest.raises(ValueError, match="authority"):
            action.validate_source_authority()
        object.__setattr__(action, "phase", original_phase)
        action.validate_source_authority()


@pytest.mark.parametrize(
    ("interior", "period", "expected_closed"),
    (("48" * 60, 2, False), ("9" * 120, 1, True)),
)
def test_nonperiodic_finite_window_and_periodic_spatial_morphism_match_digits(
    interior: str, period: int, expected_closed: bool
) -> None:
    # The one changed interior digit prevents any whole-interior period claim.
    nonperiodic = list("17" + "48" * 30 + "88")
    nonperiodic[29] = "7"
    seed = int("".join(nonperiodic))
    with DoubleReverseTerm(seed, 8) as term:
        expected = str(_literal(seed, 8))
        window = term.exact_temporal_bank_window(4, 6)
        window.residue_action.validate_source_authority()
        for offset in range(window.pair_count):
            coordinate = window.final_pair_start + offset
            assert window.at(offset).digits == (
                int(expected[coordinate]),
                int(expected[len(expected) - 1 - coordinate]),
            )
    with pytest.raises(ValueError, match="authority"):
        window.at(0)

    seed = int("17" + interior + "88")
    with DoubleReverseTerm(seed, 12) as term:
        expected = str(_literal(seed, 12))
        bank = term.temporal_bank_output_morphism(13, 8, period=period)
        assert (bank.temporal_period is not None) is expected_closed
        assert (bank.moore_classes is not None) is expected_closed
        bank.residue_action.validate_source_authority()
        assert bank.final_pair_start == 13
        assert (bank.left_births, bank.right_births) == growth_ports(
            bank.phase_in, bank.f_steps
        )
        for offset in range(bank.pair_count):
            coordinate = bank.final_pair_start + offset
            assert bank.at(offset).digits == (
                int(expected[coordinate]),
                int(expected[len(expected) - 1 - coordinate]),
            )
        original_residue = bank.residue_action.target_mod99
        object.__setattr__(
            bank.residue_action,
            "target_mod99",
            (original_residue + 1) % 99,
        )
        with pytest.raises(ValueError, match="authority"):
            bank.at(0)
        object.__setattr__(bank.residue_action, "target_mod99", original_residue)
        assert bank.at(0).digits[0] == int(expected[bank.final_pair_start])
        assert term.metrics()[DOUBLE_REVERSE_PERIODIC_BANK_TEMPORAL_STATES] > 0
        temporal_states = term.metrics()[DOUBLE_REVERSE_PERIODIC_BANK_TEMPORAL_STATES]
        if expected_closed:
            assert term.metrics()[
                DOUBLE_REVERSE_PERIODIC_BANK_MOORE_CONSTRUCTIONS
            ] == 1 + len(BANK_CHANNELS)
            assert term.metrics()[
                DOUBLE_REVERSE_PERIODIC_BANK_MOORE_OUTPUT_EVALUATIONS
            ] == temporal_states * bank.input_period * len(BANK_CHANNELS)
        else:
            assert term.metrics()[DOUBLE_REVERSE_PERIODIC_BANK_MOORE_CONSTRUCTIONS] == 0
            assert (
                term.metrics()[DOUBLE_REVERSE_PERIODIC_BANK_MOORE_OUTPUT_EVALUATIONS]
                == 0
            )
        scratch = next(
            account
            for account in term.resource_ledger.inventory()
            if account.owner == term.scratch_owner
        )
        assert scratch.entries == scratch.nodes == 0


def test_residue_actions_reject_swapped_foreign_source_authorities() -> None:
    seed = int("17" + "48" * 30 + "88")
    with (
        DoubleReverseTerm(seed, 12) as first,
        DoubleReverseTerm(seed, 12) as second,
    ):
        _, first_action = first.temporal_residue_quotient()
        _, second_action = second.temporal_residue_quotient()
        first_authority = getattr(first_action, "_source_authority", None)
        second_authority = getattr(second_action, "_source_authority", None)
        assert first_authority is not None
        assert second_authority is not None
        object.__setattr__(first_action, "_source_authority", second_authority)
        object.__setattr__(second_action, "_source_authority", first_authority)
        with pytest.raises(ValueError, match="authority"):
            first_action.validate_source_authority()
        with pytest.raises(ValueError, match="authority"):
            second_action.validate_source_authority()


def test_source_snapshot_is_iterative_bounded_and_rejects_cycles() -> None:
    nested: object = 7
    for _ in range(2_000):
        nested = [nested]
    assert snapshot_value(nested) is not None
    arena = SLPArena()
    root = arena.word([4, 8])
    packet = issue_source_record(_NestedSnapshotRecord(nested), arena, root)
    validate_source_record(packet)
    cyclic: list[object] = []
    cyclic.append(cyclic)
    with pytest.raises(ValueError, match="cycle"):
        snapshot_value(cyclic)


def test_source_snapshot_preserves_concrete_nested_types() -> None:
    arena = SLPArena()
    root = arena.word([4, 8])
    packet = issue_source_record(
        _NestedSnapshotRecord(SkewMoment(3, 2, 1)), arena, root
    )
    object.__setattr__(
        packet,
        "moments",
        _SkewMomentLookalike(duration=3, U=2, V=1),
    )
    with pytest.raises(ValueError, match="authority"):
        validate_source_record(packet)


def test_zero_step_pair_reads_source_and_excludes_mirrored_center() -> None:
    seed = int("17" + "48" * 15 + "888")
    with DoubleReverseTerm(seed, 0) as term:
        root = term.source_root
        width = term.source_arena.nodes[root].length
        source = PointedBankSource(
            term.source_arena,
            term.temporal_engine,
            term.resource_ledger,
            term.scratch_owner,
            0,
            root,
            0,
            0,
            width,
            term.max_steps,
            term.max_state_bits,
            term.source_adapter.width_bits,
        )
        expected = str(seed)
        digits, used_bank = exact_temporal_pair_digits(source, 4)
        assert digits == (int(expected[4]), int(expected[-5]))
        assert not used_bank
        center = (width - 1) // 2
        with pytest.raises(IndexError):
            exact_temporal_pair_digits(source, center)


def test_directly_forged_finite_window_frame_has_no_source_authority() -> None:
    frame = frame_from_digits((1, 2), (3, 4), 0, 0)
    residue = CertifiedResidueTemporalAction(
        phase=0,
        width_in=10,
        duration=2,
        growth=1,
        skew=0,
        width_out=11,
        multiplier_mod99=2,
        multiplier_mod198=2,
        source_mod99=1,
        source_mod198=1,
        target_mod99=2,
        target_mod198=2,
    )
    forged = ExactPointedBankWindow(0, 1, 0, 10, 11, 0, (frame,), residue)
    with pytest.raises(ValueError, match="source authority"):
        forged.at(0)
