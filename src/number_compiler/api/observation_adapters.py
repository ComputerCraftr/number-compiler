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
    ObservationOptions,
    ReverseAddObservationOptions,
    SpecialObservationOptions,
)
from number_compiler.api.json_output import json_integers
from number_compiler.api.observation_types import (
    IndexEncoding,
    ObservationId,
    OutputStatus,
    SelectorId,
    output_status,
)
from number_compiler.api.observation_views import ObservationView as View
from number_compiler.api.output_schema import (
    CollatzCarryBellmanPacket,
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
    ReverseAddTermQuery,
)
from number_compiler.arithmetic.contracts.family_identity import FamilyId
from number_compiler.sequences.collatz.observation_kind import (
    CollatzObservationKind,
)

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.cylinder_observation import CollatzObservationContext
    from number_compiler.api.number_api import ProjectedNumberTerm


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


def publish_views(
    context: QueryContext, name: ObservationId, packets: Mapping[View, Packet]
) -> Packet:
    """Assemble independently admitted views under one information envelope."""
    from number_compiler.api.family_registry import family_spec

    specs = {
        spec.view: spec
        for spec in family_spec(context.request.family).views
        if spec.selector is context.request.selector
    }
    views: dict[str, JsonValue] = {}
    status = OutputStatus.AVAILABLE
    for view, packet in packets.items():
        spec = specs[view]
        view_status = packet["status"]
        if view_status == OutputStatus.UNAVAILABLE:
            status = OutputStatus.UNAVAILABLE
        elif view_status == OutputStatus.UNKNOWN and status is OutputStatus.AVAILABLE:
            status = OutputStatus.UNKNOWN
        views[view.label] = {
            "law": spec.law,
            "clock_unit": spec.clock_unit,
            "coordinate": spec.coordinate,
            "authority_scope": spec.authority_scope,
            "status": view_status,
            "value": {
                key: value
                for key, value in packet.items()
                if key not in {"family", "kind", "index", "index_unit", "status"}
            },
        }
    result = publish_observation(context, name, {"status": status.value})
    result["views"] = views
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

    if (
        name is ObservationId.ARITHMETIC_MODULAR
        and View.ENDPOINT_RESIDUE in context.request.views
    ):
        payload = context.raw_projected_term().payload
        if not isinstance(payload, PoweredReverseAddTermPayload):
            raise TypeError("reverse/add modular endpoint requires a powered term")
        modulus = options.modulus if options.modulus is not None else 257
        packet = publish_observation(
            context,
            name,
            {
                "base": payload.term.base,
                "modulus": modulus,
                "residue": payload.term.modular_residue(modulus),
                "width": payload.term.width(),
            },
        )
        return publish_views(context, name, {View.ENDPOINT_RESIDUE: packet})
    if name is ObservationId.ARITHMETIC_MODULAR:
        from number_compiler.sequences.reverse_add.temporal_residue99 import from_seed

        query = context.request.execution
        if not isinstance(query, ReverseAddTermQuery) or query.base != 10:
            raise ValueError("temporal residue99 requires a decimal reverse/add query")
        packet = publish_observation(
            context,
            name,
            asdict(from_seed(query.seed, query.index)),
            coordinates=(("duration",),),
        )
        return publish_views(context, name, {View.RESIDUE: packet})

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
    if name is ObservationId.TEMPORAL_CLOSED_FORM:
        from number_compiler.api.bank_observation import reverse_seed_orbit_packet

        packet = publish_observation(
            context, name, reverse_seed_orbit_packet(payload.term)
        )
        return publish_views(context, name, {View.SOURCE_ACTION: packet})
    if name is ObservationId.TEMPORAL_OPEN_RING:
        from number_compiler.api.bank_observation import reverse_open_ring_packet

        return publish_observation(
            context, name, reverse_open_ring_packet(payload.term, options)
        )
    if name is ObservationId.TEMPORAL_MACRO:
        return publish_observation(
            context, name, asdict(payload.term.observe_boundary_macro())
        )
    if name is ObservationId.TEMPORAL_ACCUMULATOR:
        packet = publish_observation(
            context,
            name,
            payload.term.temporal_accumulator99().packet(),
            coordinates=(("generation",),),
        )
        return publish_views(context, name, {View.ALTERNATING: packet})
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
        ObservationId.TEMPORAL_DIAGONAL_CARRY,
        ObservationId.TEMPORAL_MATRIX,
        ObservationId.TEMPORAL_MATRIX_TRACE,
    }.intersection(options.info) or (
        ObservationId.TEMPORAL_CARRY_BELLMAN in options.info
        and options.carry_bellman_horizon == 0
    ):
        term.payload.term.prepare_joint_cocycle()
    if ObservationId.TEMPORAL_INNOVATION_BORROW in options.info or (
        ObservationId.TEMPORAL_MACRO in options.info
        and View.EXECUTED_MACROS not in context.request.views
    ):
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
        event_packet = publish_observation(
            context, name, packet, coordinates=(("requested_events",),)
        )
        if name is ObservationId.ARITHMETIC_MODULAR:
            return publish_views(context, name, {View.ENDPOINT_RESIDUE: event_packet})
        return event_packet

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
    if name is ObservationId.TEMPORAL_CARRY_BELLMAN:
        from number_compiler.sequences.collatz.future_carry_bellman import (
            centered_carry_signal,
        )

        cuts = term_options.carry_bellman_cuts
        horizon = term_options.carry_bellman_horizon
        if horizon:
            # A pending odd half-step emits an even value. Positive all-odd
            # admission therefore needs only the authenticated physical endpoint.
            source = payload.term.source_image().endpoint()
            if source % 2 == 0:
                raise ValueError("carry Bellman requires an odd normalized source")
        else:
            seam = payload.term.diagonal_carry_seam()
            if seam.phase:
                raise ValueError("carry Bellman requires a completed normalized step")
            source = seam.normalized_endpoint
        signal = centered_carry_signal(
            source, cuts, horizon=horizon, ledger=payload.term.resource_ledger
        )
        hit, corrected = signal.hits.homogeneous, signal.hits.corrected
        bellman_packet: CollatzCarryBellmanPacket = {
            "law": "homogeneous-centered-carry",
            "multipliers": (3, 5, 15),
            "normalized_source": source,
            "cuts": cuts,
            "normalized_horizon": horizon,
            "physical_horizon": 2 * horizon,
            "first_normalized_offset": hit,
            "first_physical_offset": None if hit is None else 2 * hit,
            "corrected": {
                "law": "centered-minus-power-of-two",
                "numerator_bits": signal.numerator_bits,
                "terminal_numerator_residue": signal.numerator_residue,
                "first_normalized_offset": corrected,
                "first_physical_offset": None if corrected is None else 2 * corrected,
            },
        }
        return publish_observation(context, name, bellman_packet)
    if name is ObservationId.TEMPORAL_ACCUMULATOR:
        packets: dict[View, Packet] = {}
        views = context.views_for(name)
        if View.SINGLE in views:
            packets[View.SINGLE] = publish_observation(
                context,
                name,
                asdict(payload.term.accumulator(term_options.accumulator_modulus)),
            )
        if View.ALTERNATING in views:
            weight = payload.term.double_accumulators()
            joint = (
                payload.term.source_image().joint_action if execution.index else None
            )
            if execution.index and joint is None:
                raise ValueError(
                    "weighted Collatz observer lost its joint field action"
                )
            packets[View.ALTERNATING] = publish_observation(
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
        return publish_views(context, name, {view: packets[view] for view in views})
    if (
        name is ObservationId.TEMPORAL_MACRO
        and View.EXECUTED_MACROS in context.request.views
    ):
        executed_packet = publish_observation(
            context, name, payload.term.observe_executed_macros()
        )
        return publish_views(context, name, {View.EXECUTED_MACROS: executed_packet})
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
        certificate = resolution.primality
        factor_proof = None
        if resolution.factor_witness is not None:
            factor_proof = "proper-coefficient-gcd"
            if (
                certificate is not None
                and certificate.factor_witness == resolution.factor_witness
                and certificate.gcd_witnesses == 0
            ):
                factor_proof = certificate.method
        return {
            "family": request.family.value,
            "index": request.index,
            "status": status,
            "decided": resolution.decided,
            "method": resolution.projection_method,
            "factor_query_status": resolution.factor_query_status,
            "certificate": None if certificate is None else asdict(certificate),
            "factor_witness": resolution.factor_witness,
            "factor_target": {
                "family": request.family.value,
                "parameter": request.index,
            },
            "factor_proof": factor_proof,
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
