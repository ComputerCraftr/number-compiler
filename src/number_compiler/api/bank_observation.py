"""Demanded packets for source-authenticated reversal bank projections."""

from __future__ import annotations

from dataclasses import asdict
from typing import TYPE_CHECKING

from number_compiler.api.observation_types import ObservationId
from number_compiler.arithmetic.fields.decimal_pair_partition import (
    DECIMAL_PAIR_BAND_NAMES,
    DECIMAL_PAIR_BANDS,
)

if TYPE_CHECKING:
    from number_compiler.api.cli_types import (
        DoubleReverseObservationOptions,
        ReverseAddObservationOptions,
    )
    from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

_PAIR_DOMAINS = DECIMAL_PAIR_BAND_NAMES
_PAIR_CHANNELS = (*_PAIR_DOMAINS, "carry_xor")


def double_reverse_residue_packet(term: DoubleReverseTerm) -> dict[str, object]:
    from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
        projected_residue_temporal_quotient,
        residue_clock_class_count,
        residue_clock_class_of,
    )

    prefix, action = term.temporal_residue_quotient()
    action.validate_source_authority()
    projected = projected_residue_temporal_quotient(
        action,
        ledger=term.resource_ledger,
        scratch_owner=term.scratch_owner,
    )
    packet: dict[str, object] = asdict(action)
    packet.update(
        moore_class99=residue_clock_class_of(
            action.phase, action.width_in % 2, action.source_mod99, 99
        ),
        moore_classes99=residue_clock_class_count(99),
        moore_class198=residue_clock_class_of(
            action.phase, action.width_in % 2, action.source_mod198, 198
        ),
        moore_classes198=residue_clock_class_count(198),
        prefix_steps=prefix,
        source_generation=prefix,
        target_generation=prefix + action.duration,
        projected_period=projected.packet(),
        scope="source-bound mod-99/198 width quotient; not full digit-word authority",
    )
    return packet


def double_reverse_bank_packet(
    term: DoubleReverseTerm,
    options: DoubleReverseObservationOptions,
    name: ObservationId,
) -> dict[str, object]:
    if name is ObservationId.SPATIAL_BANK_WINDOW:
        window = term.exact_temporal_bank_window(
            options.pair_bank_position, options.bank_morphism_count
        )
        return {
            "physical_prefix": window.physical_prefix,
            "f_steps": window.f_steps,
            "width_in": window.width_in,
            "width_out": window.width_out,
            "final_pair_start": window.final_pair_start,
            "pair_count": window.pair_count,
            "counts": window.counts(),
            "output_words": {
                channel: window.output_word(channel)[0] for channel in _PAIR_CHANNELS
            },
            "target_mod99": window.residue_action.target_mod99,
            "target_mod198": window.residue_action.target_mod198,
            "temporal_period": None,
            "scope": "exact finite causal-cone bank window; no future pumping assertion",
        }
    if name is not ObservationId.SPATIAL_BANK_MORPHISM:
        raise ValueError("unsupported bank observation")
    bank = term.temporal_bank_output_morphism(
        options.pair_bank_position,
        options.bank_morphism_count,
        period=options.grammar_period,
    )
    return {
        "physical_prefix": bank.physical_prefix,
        "f_steps": bank.f_steps,
        "phase_in": bank.phase_in,
        "phase_out": bank.phase_out,
        "width_in": bank.width_in,
        "width_out": bank.width_out,
        "entry_pair_start": bank.pair_start,
        "final_pair_start": bank.final_pair_start,
        "pair_count": bank.pair_count,
        "left_births": bank.left_births,
        "right_births": bank.right_births,
        "left_region": bank.left_region,
        "right_region": bank.right_region,
        "spatial_period": bank.spatial_period,
        "repeat_count": bank.repeats,
        "suffix_length": len(bank.suffix),
        "temporal_preperiod": bank.temporal_preperiod,
        "temporal_period": bank.temporal_period,
        "moore_classes": (
            None if bank.moore_classes is None else dict(bank.moore_classes)
        ),
        "counts": bank.counts(),
        "output_morphisms": {
            channel: bank.output_word(channel) for channel in _PAIR_CHANNELS
        },
        "target_mod99": bank.residue_action.target_mod99,
        "target_mod198": bank.residue_action.target_mod198,
        "scope": "source-certified moving halo and spatial emission; not full-root closure",
    }


def reverse_bank_packet(
    term: ReverseAddPoweredTerm, options: ReverseAddObservationOptions
) -> dict[str, object]:
    bank = term.temporal_spatial_bank_morphism(
        options.pair_bank_position,
        options.bank_morphism_count,
        period=options.grammar_period,
    )
    words = bank.output_words(("coefficient", *_PAIR_DOMAINS))
    output = words["coefficient"]
    from number_compiler.sequences.reverse_add.q19_conditional_stencil import (
        GuardedPairStencil,
    )

    stencil = GuardedPairStencil.from_occurrence(bank.action.owner, bank.action.source)
    count = min(64, bank.count, stencil.source_width // 2 - bank.start)
    inward: dict[str, object] | None = None
    if count > 0:
        selected = stencil.inward_bank_window(
            bank.action.owner, start=bank.start, count=count
        )
        inward = {
            "source_step": bank.action.source.temporal_steps,
            "growth": stencil.source_growth,
            "start": bank.start,
            "count": count,
            "must_may_masks": {
                band.value: selected.must_may_masks(band) for band in DECIMAL_PAIR_BANDS
            },
            "scope": "one source-admitted successor; unresolved reflected carries stay conditional",
        }
    return {
        "inward_harmonic_bank": inward,
        "source_pair_width": bank.action.source.pair_width,
        "temporal_depth": bank.action.steps,
        "pair_start_lsd": bank.start,
        "pair_count": bank.count,
        "period": list(bank.action.period),
        "control_certified": bank.control_certified,
        "growth_count": bank.action.growth_count,
        "final_width": bank.final_width_if_certified,
        "spatial_program_nodes": output.nodes,
        "temporal_program_nodes": bank.action.output_nodes,
        "spatial_repeats": output.repeats,
        "spatial_suffix_length": len(output.suffix),
        "first_pair_coefficients": list(output.slice(0, min(16, bank.count))),
        "five_band_counts": {
            channel: words[channel].counts() for channel in _PAIR_DOMAINS
        },
        "walsh64_gt_high_mod5": (
            list(words["gt_high"].walsh64_mod5(0)) if bank.count >= 64 else None
        ),
        "mod99": bank.residue99().target_mod99,
        "complete_integer_certified": False,
        "scope": "protected source-owned output morphism; not a whole-root temporal power",
    }


def double_reverse_birth_layers_packet(
    term: DoubleReverseTerm, options: DoubleReverseObservationOptions
) -> dict[str, object]:
    from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
        UncertifiedPointedStencilError,
    )

    try:
        certificate = term.birth_layer_periods(
            options.bank_morphism_count, lookback_f_steps=options.open_ring_lookback
        )
    except UncertifiedPointedStencilError as error:
        return {"status": "unavailable", "reason": str(error)}
    return certificate.validated_projection()


def double_reverse_open_ring_packet(
    term: DoubleReverseTerm, options: DoubleReverseObservationOptions
) -> dict[str, object]:
    from number_compiler.sequences.double_reverse.temporal_hashlife_types import (
        UncertifiedPointedStencilError,
    )

    try:
        bank = term.open_temporal_bank_window(
            options.pair_bank_position,
            options.bank_morphism_count,
            lookback_f_steps=options.open_ring_lookback,
        )
    except UncertifiedPointedStencilError as error:
        return {"status": "unavailable", "reason": str(error)}
    counts, words = bank.validated_projection(_PAIR_CHANNELS)
    return {
        "physical_prefix": bank.physical_prefix,
        "f_steps": bank.f_steps,
        "width_in": bank.width_in,
        "width_out": bank.width_out,
        "final_pair_start": bank.final_pair_start,
        "pair_count": bank.pair_count,
        "counts": counts,
        "output_words": {channel: words[channel][0] for channel in _PAIR_CHANNELS},
        "input_period": bank.input_period,
        "moore_classes": bank.moore_classes,
        "moore_preperiod": bank.moore_preperiod,
        "moore_cycle": bank.moore_cycle,
        "temporal_repeat_certified": False,
        "scope": "source-issued finite inlet program; no unbounded source repetition",
    }


def reverse_open_ring_packet(
    term: ReverseAddPoweredTerm, options: ReverseAddObservationOptions
) -> dict[str, object]:
    from number_compiler.sequences.reverse_add.temporal_ring_channels import (
        ring_channel_wire_name,
    )
    from number_compiler.sequences.reverse_add.temporal_ring_harmonics import (
        ReverseTemporalRingRefused,
    )

    try:
        bank = term.temporal_ring_bank(
            options.pair_bank_position, options.bank_morphism_count
        )
    except ReverseTemporalRingRefused as error:
        return {"status": "unavailable", "reason": str(error)}
    domains = bank.validated_pair_domains()
    sources = tuple(source for source, _target in domains)
    targets = tuple(target for _source, target in domains)
    joint_cyclotomic_center = {
        "mod99": bank.global_residues99,
        "mod198": bank.global_residues198,
        "center_domains": bank.center_domains,
        "correlated_carry_phases": tuple(
            tuple(
                {
                    "tick": phase.tick,
                    "width": phase.width,
                    "low_carry": phase.low_carry,
                    "high_carries": phase.high_carries,
                    "middle_transfers": tuple(
                        transfer.value for transfer in phase.middle_transfers
                    ),
                    "first_reset_positions": phase.first_reset_positions,
                    "first_reset_witnesses": tuple(
                        {"position": position, "middle_transfer": transfer.value}
                        for position, transfer in phase.first_reset_witnesses
                    ),
                    "conditional_f5": phase.conditional_f5,
                }
                for phase in frame
            )
            for frame in bank.carry_wire_phases
        ),
        "physical_repeat_certified": False,
    }
    packet: dict[str, object] = {
        "start": bank.start,
        "duration": bank.duration,
        "positions": bank.positions,
        "widths": bank.widths,
        "source_pair_domains": sources,
        "target_pair_domains": targets,
        "harmonics": tuple(
            {
                "position": word.position,
                "channel": ring_channel_wire_name(word.channel),
                "lanes": word.lanes,
                "f5_modes": word.f5_modes,
                "candidate_period": word.candidate_period,
                "future_period_certified": word.future_period_certified,
            }
            for word in bank.bank_words
        ),
        "finite_moore_classes": bank.finite_moore_classes,
        "complete_integer_certified": bank.complete_integer_certified,
        "temporal_repeat_certified": bank.temporal_repeat_certified,
        "joint_cyclotomic_center": joint_cyclotomic_center,
        "scope": "finite conditional inward carry domains; no complete-root jump",
    }
    return packet


def reverse_seed_orbit_packet(term: ReverseAddPoweredTerm) -> dict[str, object]:
    # Read the scheduler's exact Q19 endpoint, the same occurrence demanded by
    # value, width, point, and stream consumers. This observer does not replay
    # the source-root Q19 temporal blocks or claim a fast dyadic Q19 kernel.
    n = term.generation
    if n < 2 or n > 4097:
        return {
            "status": "unavailable",
            "reason": (
                "seed-orbit Q19 source interval requires 2 <= nth <= 4097; "
                "an unrestricted logarithmic Q19 operator is not certified"
            ),
            "logarithmic_q19_power_certified": False,
        }
    from number_compiler.sequences.reverse_add.temporal_seed_morphism import (
        certified_completed_reverse_add_seed_morphism,
    )

    action = certified_completed_reverse_add_seed_morphism(term)
    first, last = action.first, action.last
    return {
        "physical_interval": list(action.physical_interval),
        "duration": action.duration,
        "width_in": first.width,
        "width_out": last.width,
        "growth": action.growth,
        "center_in": list(first.center),
        "center_out": list(last.center),
        "mod99_in": first.residue99,
        "mod99_out": last.residue99,
        "mod198_in": first.residue198,
        "mod198_out": last.residue198,
        "exterior99_out": last.exterior99,
        "exterior198_out": last.exterior198,
        "carry_into_center": last.carry_into_center,
        "carry_out_of_center": last.carry_out_of_center,
        "middle_carry_map": list(last.middle_carry_map),
        "first_non9_from_upper": last.first_non9_from_upper,
        "q19_block_applications": action.q19_block_applications,
        "terminal_occurrence_reused": action.terminal_occurrence_reused,
        "temporal_square_operations": action.temporal_square_operations,
        "whole_word_slp_certified": True,
        "temporal_square_from_actual_root": False,
        "source_independent_repeat_certified": False,
        "logarithmic_q19_power_certified": False,
    }
