"""Demanded modular and source-bound observations for 2rev10."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import asdict
from typing import TYPE_CHECKING

from number_compiler.api.cli_types import DoubleReverseObservationOptions
from number_compiler.api.json_output import is_string_object_mapping
from number_compiler.api.observation_adapters import (
    Packet,
    observation_options,
    publish_observation,
    publish_views,
)
from number_compiler.api.observation_adapters import (
    admit_noop as admit_noop,
)
from number_compiler.api.observation_adapters import (
    prepare_noop as prepare_noop,
)
from number_compiler.api.observation_types import ObservationId
from number_compiler.api.observation_views import ObservationView as View
from number_compiler.api.query_types import DoubleReverseTermQuery

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


def observe(context: QueryContext, name: ObservationId) -> Packet:
    """Demand either an admitted pointed cylinder or completed endpoint ports."""
    views = context.views_for(name)
    if views:
        return publish_views(
            context, name, {view: _observe(context, name, view) for view in views}
        )
    return _observe(context, name, None)


def _observe(context: QueryContext, name: ObservationId, view: View | None) -> Packet:
    if view is View.MIXED_ADIC:
        from number_compiler.sequences.double_reverse.temporal_mixed_adic_consumer import (
            certified_mixed_adic_packet,
        )

        query = context.request.execution
        if not isinstance(query, DoubleReverseTermQuery):
            raise TypeError("2rev10 mixed-adic observation requires its typed source")
        return publish_observation(
            context,
            name,
            certified_mixed_adic_packet(
                query.seed,
                query.index,
                max_steps=query.max_steps,
                max_state_bits=query.max_state_bits,
            ),
        )
    from number_compiler.api.number_api import DoubleReverseTermPayload

    options = observation_options(context, DoubleReverseObservationOptions)
    payload = context.term.payload
    if not isinstance(payload, DoubleReverseTermPayload):
        raise TypeError("2rev10 observer received a foreign term payload")
    if name is ObservationId.ARITHMETIC_RADIX25_SHIFT:
        result_port = payload.term.source_radix25_shift(places=options.radix_places)
        return publish_observation(
            context,
            name,
            {
                **asdict(result_port),
                "carry_transfer": result_port.carry_transfer,
                "scope": "source-bound radix-2/5 projection; not future branch authority",
            },
        )
    if name is ObservationId.TEMPORAL_BIRTH_LAYERS:
        from number_compiler.api.bank_observation import (
            double_reverse_birth_layers_packet,
        )

        return publish_observation(
            context, name, double_reverse_birth_layers_packet(payload.term, options)
        )
    if name is ObservationId.TEMPORAL_OPEN_RING:
        from number_compiler.api.bank_observation import double_reverse_open_ring_packet

        return publish_observation(
            context, name, double_reverse_open_ring_packet(payload.term, options)
        )
    if view is View.DEFECT_SAMPLES:
        # QueryContext deliberately emits seed-morphism before other temporal
        # observations. If it has already authenticated and sampled the SAME
        # defect dimensions, reuse the issued payload. Do not build a second
        # source cone or independently reconstruct the temporal quotient.
        existing: Mapping[str, object] | None = None
        cached = context.cached_information(ObservationId.TEMPORAL_CLOSED_FORM)
        if cached is not None and is_string_object_mapping(
            views := cached.get("views")
        ):
            source = views.get(View.SOURCE_ACTION.label)
            if is_string_object_mapping(source) and source.get("status") == "available":
                source_value = source.get("value")
                if is_string_object_mapping(source_value):
                    existing = source_value
        shared: dict[str, object] | None = None
        if options.defect_digits > 0 and options.period_samples > 0 and existing:
            period = existing.get("period_observations")
            power = existing.get("power")
            if (
                existing.get("seed") == payload.term.seed
                and existing.get("target_generation") == payload.term.generation
                and is_string_object_mapping(period)
                and period.get("status") == "available"
                and period.get("full_endpoint_suffix_verified") is True
                and is_string_object_mapping(power)
                and type(power.get("source_prefix_generation")) is int
            ):
                # That extra flag verifies the full-word seed-morphism
                # endpoint; it is not part of the standalone defect schema.
                shared = {
                    "seed": payload.term.seed,
                    "target_generation": payload.term.generation,
                    "source_prefix_generation": power["source_prefix_generation"],
                    **{
                        k: v
                        for k, v in period.items()
                        if k != "full_endpoint_suffix_verified"
                    },
                }
        if shared is None:
            from number_compiler.sequences.double_reverse.temporal_defect_period import (
                defect_clock_cli_packet,
            )

            shared = defect_clock_cli_packet(
                payload.term,
                digits=options.defect_digits or 8,
                samples=options.period_samples or 24,
                stride=options.period_stride,
                max_lag=options.period_max_lag,
                prefix_horizon=options.prefix_horizon,
            )
        return publish_observation(
            context, name, shared, coordinates=(("target_generation",),)
        )
    if view is View.SOURCE_ACTION:
        from number_compiler.sequences.double_reverse.temporal_seed_cli import (
            seed_morphism_cli_packet,
        )

        return publish_observation(
            context,
            name,
            seed_morphism_cli_packet(
                payload.term,
                period_samples=options.period_samples,
                defect_digits=options.defect_digits,
                period_stride=options.period_stride,
                period_depth=options.period_depth,
                period_max_lag=options.period_max_lag,
                period_drivers=options.period_drivers,
                prefix_horizon=options.prefix_horizon,
                on_morphism=(
                    context.remember_double_reverse_morphism
                    if {
                        View.RESIDUE,
                        View.RESIDUE_PERIOD,
                        View.ALTERNATING,
                    }.intersection(context.request.views)
                    else None
                ),
            ),
            coordinates=(
                ("target_generation",),
                ("power", "source_prefix_generation"),
            ),
        )
    if view is View.RESIDUE:
        from number_compiler.api.bank_observation import double_reverse_residue_packet

        prefix, action = context.double_reverse_residue()
        return publish_observation(
            context,
            name,
            double_reverse_residue_packet(prefix, action),
            coordinates=(("target_generation",),),
        )
    if view is View.RESIDUE_PERIOD:
        from number_compiler.api.bank_observation import (
            double_reverse_residue_period_packet,
        )

        prefix, action = context.double_reverse_residue()
        return publish_observation(
            context,
            name,
            double_reverse_residue_period_packet(payload.term, prefix, action),
            coordinates=(("target_generation",),),
        )
    if view is View.ALTERNATING:
        from number_compiler.sequences.double_reverse.temporal_laurent_return import (
            source_laurent_accumulator_packet,
        )

        morphism = context.double_reverse_morphism()
        if morphism is None:
            prefix, action = context.double_reverse_residue()
        else:
            prefix, action = morphism.physical_prefix, morphism.residue_action
        return publish_observation(
            context,
            name,
            source_laurent_accumulator_packet(
                payload.term,
                prefix,
                action,
                authenticated_morphism=morphism,
            ),
            coordinates=(("target_generation",),),
        )
    if name is ObservationId.TEMPORAL_CARRY_SAFETY:
        from number_compiler.sequences.double_reverse.temporal_hashlife import (
            UncertifiedPointedStencilError,
        )

        try:
            prefix, source_safety, components = payload.term.temporal_carry_safety()
        except UncertifiedPointedStencilError as exc:
            return publish_observation(
                context, name, {"status": "unavailable", "reason": str(exc)}
            )
        return publish_observation(
            context,
            name,
            {
                "prefix_steps": prefix,
                "source_safety": asdict(source_safety),
                "component_bounds": [asdict(component) for component in components],
                "scope": (
                    "source-derived finite carry constraints; compatible future "
                    "ports do not authorize an entire-word temporal cycle"
                ),
            },
        )
    if name in {
        ObservationId.TEMPORAL_RADIX_WALSH,
        ObservationId.SPATIAL_STENCIL,
        ObservationId.TEMPORAL_BANK,
        ObservationId.SPATIAL_PAIR_BANK,
        ObservationId.SPATIAL_BANK_MORPHISM,
        ObservationId.SPATIAL_BANK_WINDOW,
        ObservationId.TEMPORAL_GRAMMAR,
    }:
        return _observe_double_reverse_cylinder(context, name, payload.term, options)
    if name is not ObservationId.TEMPORAL_CLOSED_FORM:
        raise ValueError("unsupported 2rev10 information observer")
    result = payload.term.temporal_closed_form(
        modulus=options.modulus,
        max_bits=min(
            payload.term.max_state_bits,
            context.request.presentation.max_output_bits,
        ),
    )
    return publish_observation(
        context,
        name,
        {
            "modulus": options.modulus,
            "steps": result.steps,
            "source": result.source,
            "target": result.target,
            "carry_word": result.carry_word,
            "carry_word_modulus": (
                None if options.modulus is None else 10 * options.modulus
            ),
            "carry_transfer": result.carry_transfer.value,
            "carry_correction": result.carry_correction,
            "final_carry": result.final_carry,
            "U": result.U,
            "H": result.H,
            "matrix": result.matrix,
            "phase_in": result.phase_in,
            "phase_out": result.phase_out,
            "left_births": result.left_births,
            "right_births": result.right_births,
            "affine_gain": result.affine_gain,
            "affine_shift": result.affine_shift,
            "prefix_steps": result.prefix_steps,
            "suffix_steps": result.suffix_steps,
            "entry_value": result.entry_value,
            "suffix_phase_in": result.suffix_phase_in,
            "suffix_phase_out": result.suffix_phase_out,
            "suffix_affine_gain": result.suffix_affine_gain,
            "suffix_affine_shift": result.suffix_affine_shift,
            "scope": "source-bound powered SLP endpoint",
        },
        coordinates=(("steps",),),
    )


def _observe_double_reverse_cylinder(
    context: QueryContext,
    name: ObservationId,
    term: DoubleReverseTerm,
    options: DoubleReverseObservationOptions,
) -> Packet:
    from number_compiler.sequences.double_reverse.temporal_hashlife import (
        UncertifiedPointedStencilError,
    )

    try:
        if name is ObservationId.TEMPORAL_RADIX_WALSH:
            joint = term.joint_radix25_temporal_bank(
                options.grammar_position,
                period=options.grammar_period,
                places=options.radix_places,
                walsh_start=options.walsh_start,
            )
            packet = asdict(joint)
            packet["source"]["carry_transfer"] = joint.source.carry_transfer
            return publish_observation(
                context,
                name,
                {
                    **packet,
                    "scope": "source-certified finite temporal halo; borrow ingress remains conditional",
                },
            )
        if name is ObservationId.SPATIAL_PAIR_BANK:
            pair = term.exact_temporal_pair(options.pair_bank_position)
            return publish_observation(
                context,
                name,
                {
                    **asdict(pair),
                    "position_unit": "final_outer_to_inner_pair",
                    "scope": "exact demanded pair in an authenticated finite cylinder",
                },
            )
        if name in {
            ObservationId.SPATIAL_BANK_WINDOW,
            ObservationId.SPATIAL_BANK_MORPHISM,
        }:
            from number_compiler.api.bank_observation import double_reverse_bank_packet

            return publish_observation(
                context, name, double_reverse_bank_packet(term, options, name)
            )
        if name is ObservationId.TEMPORAL_GRAMMAR:
            bank = term.protected_temporal_bank(
                options.grammar_position, period=options.grammar_period
            )
            shape = asdict(bank)
            if bank.relative is None:
                del shape["relative"]
            return publish_observation(
                context,
                name,
                {
                    **shape,
                    "counts": bank.counts(),
                    "represented_steps": bank.represented_steps,
                    "position_unit": "entry_outer_to_inner_pair",
                    "region_unit": "entry_source_half_open_digits",
                    "scope": "source-periodic finite causal halo; not a full-root future certificate",
                },
            )
        if name is ObservationId.SPATIAL_STENCIL:
            stencil = term.pointed_stencil(options.stencil_position)
            return publish_observation(
                context,
                name,
                {
                    "position": options.stencil_position,
                    "position_unit": "lsd_digit",
                    "digit": stencil.digit,
                    "ltgt": stencil.ltgt,
                    "f5": stencil.f5,
                    "moore_state": stencil.moore_state,
                    "width": stencil.width,
                    "phase_in": stencil.phase_in,
                    "phase_out": stencil.phase_out,
                    "prefix_steps": stencil.prefix_steps,
                    "paired_steps": stencil.f_steps,
                    "scope": "source-certified pointed cylinder",
                },
            )
        from number_compiler.sequences.double_reverse.temporal_border_bank import (
            pumped_border_word,
        )

        prefix, envelopes = term.temporal_border_bank()
        rows: list[dict[str, object]] = []
        for envelope in envelopes:
            row: dict[str, object] = asdict(envelope)
            row["exact_sum"] = envelope.exact_sum
            row["forced_next_output"] = envelope.forced_next_output
            if envelope.observer in {"growth", "carry_edge", "reflected_xor"}:
                word = pumped_border_word(
                    envelope.initial_edge, envelope.steps, envelope.observer
                )
                row["forced_word"] = asdict(word)
            rows.append(row)
        return publish_observation(
            context,
            name,
            {
                "prefix_steps": prefix,
                "envelopes": rows,
                "scope": "all inward-carry alternatives of the admitted border",
            },
        )
    except UncertifiedPointedStencilError as exc:
        return publish_observation(
            context, name, {"status": "unavailable", "reason": str(exc)}
        )
