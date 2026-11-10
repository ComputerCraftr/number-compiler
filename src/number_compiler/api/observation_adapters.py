"""Typed adapters from demanded CLI observations to family-owned observers."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import asdict
from types import MappingProxyType
from typing import TYPE_CHECKING, Final, TypeVar

from number_compiler.api.cli_types import (
    CollatzEventObservationOptions,
    CollatzTermObservationOptions,
    CommaObservationOptions,
    DoubleReverseObservationOptions,
    ObservationOptions,
    ReverseAddObservationOptions,
    SpecialObservationOptions,
)
from number_compiler.api.json_output import is_string_object_mapping, json_integers
from number_compiler.api.observation_types import (
    IndexEncoding,
    ObservationId,
    OutputStatus,
    SelectorId,
    output_status,
)
from number_compiler.api.output_schema import (
    JsonValue,
    ObservationPacket,
    VerificationResult,
    observation_packet,
)
from number_compiler.api.query_types import (
    AntihydraVerifyQuery,
    CollatzEventQuery,
    CollatzTermQuery,
    ExecutionQuery,
)
from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.sequences.collatz.observation_kind import (
    CollatzObservationKind,
)

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.cylinder_observation import CollatzObservationContext
    from number_compiler.api.number_api import ProjectedNumberTerm
    from number_compiler.sequences.double_reverse.power import DoubleReverseTerm


Packet = dict[str, JsonValue]
OptionsT = TypeVar("OptionsT", bound=ObservationOptions)
_COLLATZ_OBSERVATION_KINDS: Final[Mapping[ObservationId, CollatzObservationKind]] = (
    MappingProxyType(
        {
            ObservationId.TEMPORAL_CLOCK: CollatzObservationKind.CLOCK,
            ObservationId.ARITHMETIC_MODULAR: CollatzObservationKind.MODULAR,
            ObservationId.ARITHMETIC_TWISTED: CollatzObservationKind.TWISTED,
            ObservationId.ARITHMETIC_HASSE: CollatzObservationKind.HASSE,
            ObservationId.ARITHMETIC_HENSEL: CollatzObservationKind.HENSEL,
            ObservationId.ARITHMETIC_TROPICAL: CollatzObservationKind.TROPICAL,
            ObservationId.ARITHMETIC_FACTOR: CollatzObservationKind.FACTOR,
            ObservationId.SAFETY_EXECUTION: CollatzObservationKind.SAFETY,
        }
    )
)


def _collatz_observation_kind(name: ObservationId) -> CollatzObservationKind:
    if type(name) is not ObservationId:
        raise TypeError("Collatz observation dispatch requires an ObservationId")
    try:
        return _COLLATZ_OBSERVATION_KINDS[name]
    except KeyError as error:
        raise ValueError("unknown Collatz observation") from error


def verify_antihydra(query: ExecutionQuery) -> VerificationResult:
    from number_compiler.sequences.antihydra.certificate import verify_file

    if type(query) is not AntihydraVerifyQuery:
        raise TypeError("certificate adapter received a foreign query")
    try:
        verdict = verify_file(query.certificate)
    except (ValueError, TypeError, OverflowError) as exc:
        verdict = {
            "nonhalting_certified": False,
            "status": OutputStatus.REJECTED.value,
            "reason": str(exc),
        }
    return VerificationResult(
        verdict["nonhalting_certified"] is True,
        json_integers(verdict),
        "nonhalting certified",
    )


def _present_requested_coordinates(
    context: QueryContext, packet: Packet, paths: tuple[tuple[str, ...], ...]
) -> Packet:
    """Re-encode only explicitly named request-coordinate fields.

    Observer payloads also contain ordinary integers that may happen to equal
    the selected index. The paths below name only fields whose contract is the
    requested coordinate; this deliberately does not recursively inspect data.
    """
    index_presentation = context.request.presentation.index
    if index_presentation.encoding is not IndexEncoding.POWER10:
        return packet
    encoded = index_presentation.value(context.request.index)
    root: Packet = dict(packet)
    for path in paths:
        parent = root
        for key in path[:-1]:
            child = parent.get(key)
            if not isinstance(child, dict):
                break
            copied = dict(child)
            parent[key] = copied
            parent = copied
        else:
            key = path[-1]
            value = parent.get(key)
            if type(value) is int and value == context.request.index:
                parent[key] = encoded
    return root


def publish_observation(
    context: QueryContext,
    name: ObservationId,
    packet: Mapping[str, object],
    *,
    coordinates: tuple[tuple[str, ...], ...] = (),
) -> Packet:
    result = _present_requested_coordinates(context, json_integers(packet), coordinates)
    raw_status = result.get("status")
    status = (
        output_status(raw_status)
        if isinstance(raw_status, str)
        else OutputStatus.AVAILABLE
    )
    metadata = _common_metadata(context, name, status=status)
    result["family"] = metadata["family"]
    result["kind"] = metadata["kind"]
    result["index"] = metadata["index"]
    result["index_unit"] = metadata["index_unit"]
    result["status"] = metadata["status"]
    return result


def _common_metadata(
    context: QueryContext,
    name: ObservationId,
    *,
    status: OutputStatus,
) -> ObservationPacket:
    """Return the authoritative common coordinate fields for an observer."""
    return observation_packet(
        family=context.request.family.value,
        kind=name.value,
        index=context.request.presentation_index,
        index_unit=context.request.index_unit.value,
        status=status.value,
    )


def observation_options(context: QueryContext, cls: type[OptionsT]) -> OptionsT:
    options = context.request.observations
    if not isinstance(options, cls):
        raise TypeError("observation adapter received mismatched typed options")
    return options


def prepare_noop(context: QueryContext, term: ProjectedNumberTerm) -> None:
    del context, term


def admit_noop(context: QueryContext) -> None:
    del context


def observe_noop(context: QueryContext, name: ObservationId) -> Packet:
    del context, name
    raise ValueError("family has no information observer")


def observe_double_reverse(context: QueryContext, name: ObservationId) -> Packet:
    """Demand either an admitted pointed cylinder or completed endpoint ports."""
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
    if name is ObservationId.TEMPORAL_DEFECT_CLOCK:
        # QueryContext deliberately emits seed-morphism before other temporal
        # observations. If it has already authenticated and sampled the SAME
        # defect dimensions, reuse the issued payload. Do not build a second
        # source cone or independently reconstruct the temporal quotient.
        existing = context.cached_information(ObservationId.TEMPORAL_SEED_MORPHISM)
        shared: dict[str, object] | None = None
        if options.defect_digits > 0 and options.period_samples > 0 and existing:
            period = existing.get("period_observations")
            power = existing.get("power")
            if (
                existing.get("status") == "available"
                and existing.get("seed") == payload.term.seed
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
    if name is ObservationId.TEMPORAL_SEED_MORPHISM:
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
            ),
            coordinates=(
                ("target_generation",),
                ("power", "source_prefix_generation"),
            ),
        )
    if name is ObservationId.TEMPORAL_RESIDUE99:
        from number_compiler.api.bank_observation import double_reverse_residue_packet

        return publish_observation(
            context,
            name,
            double_reverse_residue_packet(payload.term),
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
            return publish_observation(
                context,
                name,
                {
                    **asdict(bank),
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


def prepare_reverse(context: QueryContext, term: ProjectedNumberTerm) -> None:
    del context, term


def admit_reverse(context: QueryContext) -> None:
    if not context.request.observations.info:
        return
    options = observation_options(context, ReverseAddObservationOptions)
    if not {
        ObservationId.SPATIAL_MIRROR,
        ObservationId.TEMPORAL_STENCIL,
    }.intersection(options.info):
        return
    from number_compiler.api.number_api import PoweredReverseAddTermPayload

    payload = context.raw_projected_term().payload
    if not isinstance(payload, PoweredReverseAddTermPayload):
        raise TypeError("reverse/add query published a foreign term payload")
    if payload.term.maximum_width > options.max_digits:
        raise ValueError("reverse/add observation target exceeds digit budget")


def observe_reverse(context: QueryContext, name: ObservationId) -> Packet:
    options = observation_options(context, ReverseAddObservationOptions)
    from number_compiler.api.number_api import PoweredReverseAddTermPayload

    payload = context.term.payload
    if not isinstance(payload, PoweredReverseAddTermPayload):
        raise TypeError("reverse/add query published a foreign term payload")
    if name is ObservationId.TEMPORAL_MIRRORED_DIAGONAL:
        from number_compiler.sequences.reverse_add.temporal_mirrored_diagonal import (
            MAX_MIRRORED_TICKS,
        )

        if not 1 <= payload.term.generation <= MAX_MIRRORED_TICKS:
            return publish_observation(
                context,
                name,
                {
                    "status": OutputStatus.UNAVAILABLE.value,
                    "reason": "mirrored carry observation exceeds its finite horizon",
                    "max_physical_ticks": MAX_MIRRORED_TICKS,
                },
            )
        return publish_observation(
            context, name, payload.term.temporal_mirrored_diagonal()
        )
    if name is ObservationId.TEMPORAL_SEED_ORBIT:
        from number_compiler.api.bank_observation import reverse_seed_orbit_packet

        return publish_observation(
            context, name, reverse_seed_orbit_packet(payload.term)
        )
    if name is ObservationId.TEMPORAL_OPEN_RING:
        from number_compiler.api.bank_observation import reverse_open_ring_packet

        return publish_observation(
            context, name, reverse_open_ring_packet(payload.term, options)
        )
    if name is ObservationId.TEMPORAL_MACRO:
        return publish_observation(
            context, name, asdict(payload.term.observe_boundary_macro())
        )
    if name is ObservationId.TEMPORAL_RESIDUE99:
        return publish_observation(
            context,
            name,
            asdict(payload.term.temporal_residue99()),
            coordinates=(("duration",),),
        )
    if name is ObservationId.TEMPORAL_ACCUMULATOR99:
        return publish_observation(
            context,
            name,
            payload.term.temporal_accumulator99().packet(),
            coordinates=(("generation",),),
        )
    if name is ObservationId.SPATIAL_BANK_MORPHISM:
        from number_compiler.api.bank_observation import reverse_bank_packet

        return publish_observation(
            context,
            name,
            reverse_bank_packet(payload.term, options),
            coordinates=(("temporal_depth",),),
        )
    if name is ObservationId.TEMPORAL_STENCIL:
        stencil = payload.term.temporal_stencil(
            max_bits=context.request.presentation.max_output_bits,
            max_digits=options.max_digits,
        )
        packet = asdict(stencil)
        packet["carry_transfer"] = stencil.carry_transfer.value
        return publish_observation(
            context,
            name,
            packet,
        )
    if name is ObservationId.SPATIAL_MIRROR:
        from number_compiler.api.cylinder_observation import observe_mirror

        return publish_observation(
            context,
            name,
            observe_mirror(
                payload.term.seed,
                context.request.index,
                base=payload.term.base,
                first_width=options.width,
                max_digits=options.max_digits,
                _term=payload.term,
                _include_metrics=False,
            ),
        )
    raise ValueError("observation has no reverse/add handler")


def prepare_collatz(context: QueryContext, term: ProjectedNumberTerm) -> None:
    if not context.request.observations.info:
        return
    options = observation_options(context, CollatzTermObservationOptions)
    from number_compiler.api.number_api import PoweredCollatzTermPayload

    if not isinstance(term.payload, PoweredCollatzTermPayload):
        raise TypeError("Collatz query published a foreign term payload")
    if ObservationId.TEMPORAL_CLOCK in options.info:
        term.payload.term.prepare_width_spine()
    if {
        ObservationId.TEMPORAL_ACCUMULATOR,
        ObservationId.TEMPORAL_DOUBLE_ACCUMULATOR,
        ObservationId.TEMPORAL_DIAGONAL_CARRY,
        ObservationId.TEMPORAL_MATRIX,
        ObservationId.TEMPORAL_MATRIX_TRACE,
    }.intersection(options.info):
        term.payload.term.prepare_joint_cocycle()
    if {
        ObservationId.TEMPORAL_MACRO,
        ObservationId.TEMPORAL_INNOVATION_BORROW,
    }.intersection(options.info):
        term.payload.term.prepare_innovation_tape(
            complete_word=ObservationId.TEMPORAL_INNOVATION_BORROW in options.info,
            modulus=options.innovation_modulus
            if ObservationId.TEMPORAL_INNOVATION_BORROW in options.info
            else None,
        )


def admit_collatz(context: QueryContext) -> None:
    request = context.request
    if request.selector is not SelectorId.NTH or not request.observations.info:
        return
    options = observation_options(context, CollatzTermObservationOptions)
    if ObservationId.TEMPORAL_CLOCK not in options.info or request.index == 0:
        return
    from number_compiler.api.number_api import PoweredCollatzTermPayload

    payload = context.raw_projected_term().payload
    if not isinstance(payload, PoweredCollatzTermPayload):
        raise TypeError("Collatz query published a foreign term payload")
    if payload.term.maximum_width > options.clock_max_digits:
        raise ValueError("physical clock target exceeds digit budget")


def _event_context(
    context: QueryContext,
) -> CollatzObservationContext:
    from number_compiler.api.cylinder_observation import CollatzObservationContext

    execution = context.request.execution
    if not isinstance(execution, CollatzEventQuery):
        raise TypeError("event observer received a non-event execution query")
    binding = (
        execution.seed,
        execution.events,
        execution.max_events,
        execution.max_digits,
    )
    return context.memoized_collatz_context(
        binding,
        lambda: CollatzObservationContext(
            execution.seed,
            execution.events,
            max_events=execution.max_events,
            max_digits=execution.max_digits,
        ),
    )


def observe_collatz(context: QueryContext, name: ObservationId) -> Packet:
    request = context.request
    if request.selector is SelectorId.EVENTS:
        event_options = observation_options(context, CollatzEventObservationOptions)
        execution = request.execution
        if not isinstance(execution, CollatzEventQuery):
            raise TypeError("event observer received a non-event execution query")
        from number_compiler.api.cylinder_observation import observe_collatz as observe

        packet = observe(
            execution.seed,
            execution.events,
            kind=_collatz_observation_kind(name),
            modulus=event_options.modulus,
            width=(
                event_options.twisted_width
                if name is ObservationId.ARITHMETIC_TWISTED
                else event_options.hasse_order
                if name is ObservationId.ARITHMETIC_HASSE
                else event_options.twisted_width
            ),
            sign=event_options.twisted_sign,
            precision=event_options.precision,
            target=event_options.target,
            s_weight=event_options.s_weight,
            z_weight=event_options.z_weight,
            max_events=execution.max_events,
            max_digits=execution.max_digits,
            _context=_event_context(context),
            _include_metrics=False,
        )
        return publish_observation(
            context, name, packet, coordinates=(("requested_events",),)
        )

    term_options = observation_options(context, CollatzTermObservationOptions)
    execution = request.execution
    if not isinstance(execution, CollatzTermQuery):
        raise TypeError("term observer received a non-term Collatz query")
    from number_compiler.api.number_api import PoweredCollatzTermPayload

    payload = context.term.payload
    if not isinstance(payload, PoweredCollatzTermPayload):
        raise TypeError("Collatz query published a foreign term payload")
    if name is ObservationId.TEMPORAL_CLOCK:
        from number_compiler.api.cylinder_observation import observe_physical_clock

        clock_packet = observe_physical_clock(
            execution.seed,
            execution.index,
            max_ticks=term_options.clock_max_events,
            max_digits=term_options.clock_max_digits,
            _term=payload.term,
            _include_metrics=False,
        )
        return publish_observation(
            context, name, clock_packet, coordinates=(("requested_ticks",),)
        )
    if name is ObservationId.TEMPORAL_DIAGONAL_CARRY:
        from number_compiler.api.collatz_diagonal_observation import diagonal_packet

        return publish_observation(
            context,
            name,
            diagonal_packet(payload.term, max_width=term_options.clock_max_digits),
            coordinates=(("physical_ticks",),),
        )
    if name is ObservationId.TEMPORAL_DOUBLE_ACCUMULATOR:
        weight = payload.term.double_accumulators()
        joint = payload.term.source_image().joint_action if execution.index else None
        if execution.index and joint is None:
            raise ValueError("weighted Collatz observer lost its joint field action")
        return publish_observation(
            context,
            name,
            {
                "source": execution.seed,
                "added": weight.added,
                "subtracted": weight.subtracted,
                "normalized_endpoint": weight.normalized_endpoint,
                "physical_endpoint": weight.physical_endpoint,
                "conservation_difference": weight.added - weight.subtracted,
                "normalized_steps": 0 if joint is None else joint.normalized_steps,
                "physical_ticks": execution.index,
                "phase": 0 if joint is None else joint.phase,
            },
        )
    if name is ObservationId.TEMPORAL_ACCUMULATOR:
        return publish_observation(
            context,
            name,
            asdict(payload.term.accumulator(term_options.accumulator_modulus)),
        )
    if name in {
        ObservationId.TEMPORAL_MACRO,
        ObservationId.TEMPORAL_INNOVATION_BORROW,
    }:
        return publish_observation(
            context,
            name,
            payload.term.observe_boundary_macro(
                modulus=term_options.innovation_modulus
                if name is ObservationId.TEMPORAL_INNOVATION_BORROW
                else None,
                position_spectrum_requests=((6, 0), (10, 0))
                if name is ObservationId.TEMPORAL_INNOVATION_BORROW
                else (),
            ),
        )
    raise ValueError("observation has no Collatz handler")


def admit_comma(context: QueryContext) -> None:
    from number_compiler.api.number_api import CommaTermPayload
    from number_compiler.arithmetic.contracts.unresolved_term import (
        UnresolvedSequenceTerm,
    )
    from number_compiler.sequences.comma.certificates import (
        certificate_status,
        unresolved_boundary,
    )

    request = context.request
    payload = context.raw_projected_term().payload
    if not isinstance(payload, CommaTermPayload):
        raise TypeError("comma query published a foreign term payload")
    if not context.request.observations.info:
        payload.require_certified()
        return
    options = observation_options(context, CommaObservationOptions)
    if request.presentation.no_value and not set(options.info) - {
        ObservationId.METRICS,
        ObservationId.SAFETY_CERTIFICATE,
    }:
        status = certificate_status(
            request.index,
            payload.term.ledger,
            payload.term.max_work,
            global_provider=payload.certificate_provider,
        )
        if status["status"] == "unknown":
            context.unresolved_boundary = unresolved_boundary(request.index)
        return
    try:
        payload.require_certified()
    except UnresolvedSequenceTerm as error:
        if not request.presentation.no_value or set(options.info) - {
            ObservationId.METRICS,
            ObservationId.SAFETY_CERTIFICATE,
        }:
            raise
        context.unresolved_boundary = error


def observe_comma(context: QueryContext, name: ObservationId) -> Packet:
    from number_compiler.api.number_api import CommaTermPayload

    payload = context.term.payload
    if not isinstance(payload, CommaTermPayload):
        raise TypeError("comma query published a foreign term payload")
    if name is ObservationId.SAFETY_CERTIFICATE:
        from number_compiler.sequences.comma.certificates import certificate_status

        packet = certificate_status(
            context.request.index,
            payload.term.ledger,
            payload.term.max_work,
            global_provider=payload.certificate_provider,
        )
        return publish_observation(
            context, name, packet, coordinates=(("requested_index",),)
        )
    payload.require_certified()
    value = (
        payload.term.clock()
        if name is ObservationId.TEMPORAL_CLOCK
        else payload.term.tropical()
    )
    return publish_observation(
        context,
        name,
        {"value": value, "scope": "checked comma-child prefix"},
    )


def admit_fermat(context: QueryContext) -> None:
    options = observation_options(context, SpecialObservationOptions)
    if options.ordered_carry_windows:
        from number_compiler.arithmetic.contracts.input_validation import (
            require_integer,
        )

        require_integer(context.request.index, "Fermat carry source index", 0, 16)


def observe_special(context: QueryContext, name: ObservationId) -> Packet:
    request = context.request
    options = observation_options(context, SpecialObservationOptions)
    if name is ObservationId.NUMBER_THEORY_ROOT:
        from number_compiler.api.cylinder_observation import observe_etale_root

        if options.defect is None:
            raise ValueError("--info root requires --defect")
        packet = observe_etale_root(
            request.family,
            request.index,
            options.defect,
            max_digits=options.max_digits,
        )
        return publish_observation(context, name, packet)

    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

    def resolve_special_packet() -> dict[str, object]:
        resolution = CanonicalSequenceCompiler().resolve_special_theorem(
            request.family.value,
            request.index,
            collect_etale_factor=ObservationId.NUMBER_THEORY_FACTOR in options.info,
            max_factor_products=options.max_factor_products,
            max_candidate_bits=options.max_candidate_bits,
        )
        failure = resolution.source_guard.failure_bit
        status = "unknown" if failure is None else "composite" if failure else "prime"
        return {
            "family": request.family.value,
            "index": request.index,
            "status": status,
            "decided": resolution.decided,
            "method": resolution.projection_method,
            "factor_query_status": resolution.factor_query_status,
            "certificate": (
                None if resolution.primality is None else asdict(resolution.primality)
            ),
            "factor_witness": resolution.factor_witness,
            "factor_target": {
                "family": request.family.value,
                "parameter": request.index,
            },
            "factor_proof": (
                "proper-coefficient-gcd"
                if resolution.factor_witness is not None
                else None
            ),
            "factor_expression": (
                None
                if resolution.composite_exponent_factor is None
                else f"2^{resolution.composite_exponent_factor.exponent}-1"
            ),
            "etale_ring_multiplications": resolution.etale_ring_multiplications,
        }

    special_packet = context.cached_special_packet(resolve_special_packet)
    if name is ObservationId.NUMBER_THEORY_PRIMALITY:
        packet = dict(special_packet)
        if options.ordered_carry_windows:
            if request.family is not FamilyId.FERMAT:
                raise ValueError(
                    "ordered tripling carry source requires a Fermat query"
                )
            from number_compiler.api.fermat_carry_observation import fermat_carry_packet

            packet["ordered_carry_windows"] = fermat_carry_packet(request.index)
        return publish_observation(
            context,
            name,
            packet,
            coordinates=(("index",),),
        )
    if name is ObservationId.NUMBER_THEORY_FACTOR:
        packet = dict(special_packet)
        packet["status"] = (
            "available"
            if packet["factor_witness"] is not None
            or packet["factor_expression"] is not None
            else "not_applicable"
            if packet["status"] == "prime"
            else "unknown"
            if packet["status"] == "unknown"
            else "not_found"
        )
        packet["scope"] = (
            "conditional checked factor output; no factor found does not establish primality"
        )
        return publish_observation(
            context,
            name,
            packet,
            coordinates=(("index",), ("factor_target", "parameter")),
        )
    raise ValueError("observation has no special-number handler")


__all__ = [
    "admit_collatz",
    "admit_comma",
    "admit_noop",
    "admit_reverse",
    "observe_collatz",
    "observe_comma",
    "observe_double_reverse",
    "observe_noop",
    "observe_reverse",
    "observe_special",
    "publish_observation",
    "prepare_collatz",
    "prepare_noop",
    "prepare_reverse",
    "observation_options",
    "verify_antihydra",
]
