"""Demanded packets for source-authenticated reversal bank projections."""

from __future__ import annotations

from dataclasses import asdict
from typing import TYPE_CHECKING

from number_compiler.api.observation_types import ObservationId

if TYPE_CHECKING:
    from number_compiler.api.cli_types import (
        DoubleReverseObservationOptions,
        ReverseAddObservationOptions,
    )
    from number_compiler.sequences.double_reverse.power import DoubleReverseTerm
    from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm

_PAIR_DOMAINS = ("lt_low", "lt_high", "eq", "gt_low", "gt_high")
_PAIR_CHANNELS = (*_PAIR_DOMAINS, "carry_xor")


def double_reverse_residue_packet(term: DoubleReverseTerm) -> dict[str, object]:
    from number_compiler.sequences.double_reverse.temporal_residue_quotient import (
        residue_clock_class_count,
        residue_clock_class_of,
    )

    prefix, action = term.temporal_residue_quotient()
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
                channel: selected.must_may_masks(channel) for channel in _PAIR_DOMAINS
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
