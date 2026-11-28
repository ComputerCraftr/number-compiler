"""Demanded packets for source-authenticated reversal bank projections."""

from __future__ import annotations

import os
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
    from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
        CertifiedResidueTemporalAction,
    )
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm
    from number_compiler.sequences.reverse_add.q19_ordered_gram import (
        Q19OrderedGramAction,
    )

_PAIR_DOMAINS = DECIMAL_PAIR_BAND_NAMES
_PAIR_CHANNELS = (*_PAIR_DOMAINS, "carry_xor")


def double_reverse_residue_packet(
    prefix: int,
    action: CertifiedResidueTemporalAction,
) -> dict[str, object]:
    from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
        residue_clock_class_count,
        residue_clock_class_of,
    )

    action.validate_source_authority()
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
        scope="source-bound mod-99/198 width quotient; not full digit-word authority",
    )
    return packet


def double_reverse_residue_period_packet(
    term: DoubleReverseTerm,
    prefix: int,
    action: CertifiedResidueTemporalAction,
) -> dict[str, object]:
    from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
        projected_residue_temporal_quotient,
    )

    projected = projected_residue_temporal_quotient(
        action,
        ledger=term.resource_ledger,
        scratch_owner=term.scratch_owner,
    )
    return {
        "projected_period": projected.packet(),
        "target_generation": prefix + action.duration,
    }


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
    residue = bank.residue99()
    harmonic: dict[str, object] | None = None
    if (
        residue.duration >= 6
        and residue.source_certified
        and not residue.control_needed
    ):
        harmonic = {
            "initial_pair": list(residue.binary_harmonic_phi3),
            "transition_matrix": [[0, 1], [1, 1]],
            "coefficient_field": "F2",
            "clock_unit": "physical-ticks",
            "period_divides": 3,
            "scope": "mod-99 output projection; no digit or carry execution authority",
        }
    return {
        "inward_harmonic_bank": inward,
        "mod99_binary_harmonic_phi3": harmonic,
        "source_carry_phi6": bank.action.owner.issued_carry_phi6_packet(
            bank.action.source
        ),
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
        "mod99": residue.target_mod99,
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
    from number_compiler.resources.metric_keys import reverse_add as reverse_metrics
    from number_compiler.sequences.reverse_add.temporal_seed_morphism import (
        certified_completed_reverse_add_seed_morphism,
    )

    action = certified_completed_reverse_add_seed_morphism(term)
    first, last = action.first, action.last
    counters = term.resource_ledger.counters
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
        "reverse198_out": last.reverse_residue198,
        "reflected_carry_k_parity_out": last.reflected_carry_parity,
        "next_raw_pair198": last.next_raw_residue198,
        "group_ring_carry_correction_mod198": (-99 * last.reflected_carry_parity) % 198,
        "exterior99_out": last.exterior99,
        "exterior198_out": last.exterior198,
        "carry_into_center": last.carry_into_center,
        "carry_out_of_center": last.carry_out_of_center,
        "middle_carry_map": list(last.middle_carry_map),
        "first_non9_from_upper": last.first_non9_from_upper,
        "q19_block_applications": action.q19_block_applications,
        "q19_physical_t2_actions_cumulative": (
            counters.get(reverse_metrics.REVERSE_Q19_PUNCTURED_PHYSICAL_T2_ACTIONS, 0)
        ),
        "q19_broadword_semantic_steps_cumulative": counters.get(
            reverse_metrics.REVERSE_Q19_BROADWORD_SEMANTIC_STEPS, 0
        ),
        "q19_broadword_endpoint_publications_cumulative": counters.get(
            reverse_metrics.REVERSE_Q19_BROADWORD_ENDPOINT_PUBLICATIONS, 0
        ),
        "terminal_occurrence_reused": action.terminal_occurrence_reused,
        "temporal_square_operations": action.temporal_square_operations,
        "whole_word_slp_certified": True,
        "temporal_square_from_actual_root": False,
        "source_independent_repeat_certified": False,
        "logarithmic_q19_power_certified": False,
    }


def _gram_work(counters: dict[str, int]) -> dict[str, int]:
    from number_compiler.resources.metric_keys import reverse_add as keys

    return {
        "conditional_atoms": counters.get(keys.REVERSE_Q19_GRAM_ATOM_BUILDS, 0),
        "source_nodes": counters.get(keys.REVERSE_Q19_GRAM_NODE_VISITS, 0),
        "ordered_compositions": counters.get(keys.REVERSE_Q19_GRAM_COMPOSITIONS, 0),
        "source_guard_nodes": counters.get(keys.REVERSE_Q19_UV_GUARD_NODES, 0),
        "physical_ticks_skipped": counters.get(
            keys.REVERSE_Q19_UV_GRAM_SKIPPED_TICKS, 0
        ),
        "source_guard_transitions": counters.get(
            keys.REVERSE_Q19_UV_GUARD_TRANSITIONS, 0
        ),
        "source_guard_precheck_reads": counters.get(keys.REVERSE_Q19_UV_GUARD_READS, 0),
    }


def _carry_gram_packet(
    generation: int,
    action: Q19OrderedGramAction,
    counters: dict[str, int],
    before: dict[str, int],
) -> dict[str, object]:
    return {
        "source_generation": generation,
        "source_width": action.length,
        "source_positions": [0, action.length],
        "position_order": "least-significant pair first",
        "left_inlet": "carry from less-significant end",
        "right_inlet": "carry from more-significant end",
        "sigma": action.z,
        "modulus": action.modulus,
        "coefficient_order": list(range(action.degree)),
        "channels": ["A", "B", "AB", "A_i B_(i+1)", "A_(i+1) B_i"],
        "rows": [
            {
                "inlets": [index // 2, index % 2],
                "outlets": [row.left_exit, row.right_exit],
                "A": row.a,
                "B": row.b,
                "AB": row.ab,
                "A_i B_(i+1)": row.a_next_b,
                "A_(i+1) B_i": row.next_a_b,
            }
            for index, row in enumerate(action.rows)
        ],
        "work": {k: v - before[k] for k, v in _gram_work(counters).items()},
        "scope": "source-issued pair field and conditional carry correlations",
    }


def reverse_carry_gram_packet(term: ReverseAddPoweredTerm) -> dict[str, object]:
    """Project both directed carry streams of the selected decimal pair field."""
    from number_compiler.sequences.reverse_add.q19_gram_observation import (
        source_carry_gram,
    )

    workspace = term.source_workspace()
    before: dict[str, int] | None = None
    if (
        term.generation in (3, 9)
        and os.environ.get("NUMBER_COMPILER_ENABLE_UV_GRAM") == "1"
    ):
        from number_compiler.sequences.reverse_add.q19_uv_gram import source_uv_gram

        source = workspace.actions.source(workspace.source)
        owner = workspace.adapter.q19_output_owner(source)
        workspace.register_source_payload_audit_contract()
        counters = owner.ledger.counters
        before = _gram_work(counters)
        with source_uv_gram(owner, owner.initial, term.generation) as action:
            if action is not None:
                return _carry_gram_packet(term.generation, action, counters, before)
    if term.generation == 0:
        source = workspace.actions.source(workspace.source)
        owner = workspace.adapter.q19_output_owner(source)
        occurrence = owner.initial
        workspace.register_source_payload_audit_contract()
    else:
        owner, occurrence, _reused, _work = term.completed_q19_occurrence()
        occurrence = owner.apply_pair_step(occurrence)
    counters = owner.ledger.counters
    if before is None:
        before = _gram_work(counters)
    with source_carry_gram(owner, occurrence) as action:
        return _carry_gram_packet(term.generation, action, counters, before)
