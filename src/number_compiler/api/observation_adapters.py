"""Typed adapters from demanded CLI observations to family-owned observers."""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import asdict
from typing import TYPE_CHECKING, TypeVar, cast

from number_compiler.api.cli_types import (
    AntihydraObservationOptions,
    CollatzEventObservationOptions,
    CollatzTermObservationOptions,
    CommaObservationOptions,
    ReverseAddObservationOptions,
    SpecialObservationOptions,
)
from number_compiler.api.output_schema import (
    JsonValue,
    ObservationPacket,
    VerificationResult,
)
from number_compiler.api.query_types import (
    AntihydraVerifyQuery,
    CollatzEventQuery,
    CollatzTermQuery,
    ExecutionQuery,
)

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.cylinder_observation import CollatzObservationContext
    from number_compiler.api.number_api import ProjectedNumberTerm


Packet = dict[str, JsonValue]
OptionsT = TypeVar("OptionsT")


def verify_antihydra(query: ExecutionQuery) -> VerificationResult:
    from number_compiler.sequences.antihydra.certificate import verify_file

    if type(query) is not AntihydraVerifyQuery:
        raise TypeError("certificate adapter received a foreign query")
    try:
        verdict = verify_file(query.certificate)
    except (ValueError, TypeError, OverflowError) as exc:
        verdict = {
            "nonhalting_certified": False,
            "status": "rejected",
            "reason": str(exc),
        }
    return VerificationResult(
        verdict["nonhalting_certified"] is True,
        _packet(verdict),
        "nonhalting certified",
    )


def _packet(value: Mapping[str, object]) -> Packet:
    return {key: cast(JsonValue, item) for key, item in value.items()}


def _present_requested_coordinates(
    context: QueryContext, packet: Packet, paths: tuple[tuple[str, ...], ...]
) -> Packet:
    """Re-encode only explicitly named request-coordinate fields.

    Observer payloads also contain ordinary integers that may happen to equal
    the selected index. The paths below name only fields whose contract is the
    requested coordinate; this deliberately does not recursively inspect data.
    """
    index_presentation = context.request.presentation.index
    if index_presentation.encoding != "power10":
        return packet
    encoded = cast(JsonValue, index_presentation.value(context.request.index))
    root: Packet = dict(packet)
    for path in paths:
        parent = root
        for key in path[:-1]:
            child = parent.get(key)
            if not isinstance(child, dict):
                break
            copied = dict(child)
            parent[key] = cast(JsonValue, copied)
            parent = copied
        else:
            key = path[-1]
            value = parent.get(key)
            if type(value) is int and value == context.request.index:
                parent[key] = encoded
    return root


def _publish(
    context: QueryContext,
    name: str,
    packet: Mapping[str, object],
    *,
    coordinates: tuple[tuple[str, ...], ...] = (),
) -> Packet:
    result = _present_requested_coordinates(context, _packet(packet), coordinates)
    status = result.get("status")
    metadata = _common_metadata(
        context, name, status=status if isinstance(status, str) else "available"
    )
    result["family"] = metadata["family"]
    result["kind"] = metadata["kind"]
    result["index"] = metadata["index"]
    result["index_unit"] = metadata["index_unit"]
    result["status"] = metadata["status"]
    return result


def _common_metadata(
    context: QueryContext, name: str, *, status: str
) -> ObservationPacket:
    """Return the authoritative common coordinate fields for an observer."""
    return {
        "family": context.request.family,
        "kind": name,
        "index": context.request.presentation_index,
        "index_unit": context.request.index_unit,
        "status": status,
    }


def _options(context: QueryContext, cls: type[OptionsT]) -> OptionsT:
    options = context.request.observations
    if not isinstance(options, cls):
        raise TypeError("observation adapter received mismatched typed options")
    return options


def prepare_noop(context: QueryContext, term: ProjectedNumberTerm) -> None:
    del context, term


def admit_noop(context: QueryContext) -> None:
    del context


def observe_noop(context: QueryContext, name: str) -> Packet:
    del context, name
    raise ValueError("family has no information observer")


def prepare_reverse(context: QueryContext, term: ProjectedNumberTerm) -> None:
    del context, term


def admit_reverse(context: QueryContext) -> None:
    if not context.request.observations.info:
        return
    options = _options(context, ReverseAddObservationOptions)
    if "mirror" not in options.info:
        return
    from number_compiler.api.number_api import PoweredReverseAddTermPayload

    payload = context._raw_projected_term().payload
    if not isinstance(payload, PoweredReverseAddTermPayload):
        raise TypeError("reverse/add query published a foreign term payload")
    if payload.term.maximum_width > options.max_digits:
        raise ValueError("mirror target exceeds digit budget")


def observe_reverse(context: QueryContext, name: str) -> Packet:
    options = _options(context, ReverseAddObservationOptions)
    from number_compiler.api.number_api import PoweredReverseAddTermPayload

    payload = context.term.payload
    if not isinstance(payload, PoweredReverseAddTermPayload):
        raise TypeError("reverse/add query published a foreign term payload")
    if name == "boundary-macro":
        return _publish(context, name, asdict(payload.term.observe_boundary_macro()))
    if name == "mirror":
        from number_compiler.api.cylinder_observation import observe_mirror

        return _publish(
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
    options = _options(context, CollatzTermObservationOptions)
    from number_compiler.api.number_api import PoweredCollatzTermPayload

    if not isinstance(term.payload, PoweredCollatzTermPayload):
        raise TypeError("Collatz query published a foreign term payload")
    if "clock" in options.info:
        term.payload.term.prepare_width_spine()
    if "accumulator" in options.info:
        term.payload.term.prepare_joint_cocycle()
    if {"boundary-macro", "innovation-borrow"}.intersection(options.info):
        term.payload.term.prepare_innovation_tape()


def admit_collatz(context: QueryContext) -> None:
    request = context.request
    if request.selector != "nth" or not request.observations.info:
        return
    options = _options(context, CollatzTermObservationOptions)
    if "clock" not in options.info or request.index == 0:
        return
    from number_compiler.api.number_api import PoweredCollatzTermPayload

    payload = context._raw_projected_term().payload
    if not isinstance(payload, PoweredCollatzTermPayload):
        raise TypeError("Collatz query published a foreign term payload")
    if payload.term.maximum_width > options.max_digits:
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
    if context._events is None:
        context._events = CollatzObservationContext(
            execution.seed,
            execution.events,
            max_events=execution.max_events,
            max_digits=execution.max_digits,
        )
    if context._events.binding != binding:
        raise ValueError("event observer context belongs to another request")
    return context._events


def observe_collatz(context: QueryContext, name: str) -> Packet:
    request = context.request
    if request.selector == "events":
        event_options = _options(context, CollatzEventObservationOptions)
        execution = request.execution
        if not isinstance(execution, CollatzEventQuery):
            raise TypeError("event observer received a non-event execution query")
        from number_compiler.api.cylinder_observation import observe_collatz as observe

        packet = observe(
            execution.seed,
            execution.events,
            kind=name,
            modulus=event_options.modulus,
            width=event_options.width,
            sign=event_options.sign,
            precision=event_options.precision,
            target=event_options.target,
            s_weight=event_options.s_weight,
            z_weight=event_options.z_weight,
            max_events=execution.max_events,
            max_digits=execution.max_digits,
            _context=_event_context(context),
            _include_metrics=False,
        )
        return _publish(context, name, packet, coordinates=(("requested_events",),))

    term_options = _options(context, CollatzTermObservationOptions)
    execution = request.execution
    if not isinstance(execution, CollatzTermQuery):
        raise TypeError("term observer received a non-term Collatz query")
    from number_compiler.api.number_api import PoweredCollatzTermPayload

    payload = context.term.payload
    if not isinstance(payload, PoweredCollatzTermPayload):
        raise TypeError("Collatz query published a foreign term payload")
    if name == "clock":
        from number_compiler.api.cylinder_observation import observe_physical_clock

        packet = observe_physical_clock(
            execution.seed,
            execution.index,
            max_ticks=term_options.max_events,
            max_digits=term_options.max_digits,
            _term=payload.term,
            _include_metrics=False,
        )
        return _publish(context, name, packet, coordinates=(("requested_ticks",),))
    if name == "accumulator":
        return _publish(
            context, name, asdict(payload.term.accumulator(term_options.modulus))
        )
    if name in {"boundary-macro", "innovation-borrow"}:
        return _publish(
            context,
            name,
            payload.term.observe_boundary_macro(
                modulus=term_options.modulus if name == "innovation-borrow" else None
            ),
        )
    raise ValueError("observation has no Collatz handler")


def prepare_antihydra(context: QueryContext, term: ProjectedNumberTerm) -> None:
    if not context.request.observations.info:
        return
    options = _options(context, AntihydraObservationOptions)
    from number_compiler.api.number_api import AntihydraTermPayload

    if not isinstance(term.payload, AntihydraTermPayload):
        raise TypeError("Antihydra query published a foreign term payload")
    if "mahler" in options.info:
        term.payload.term.prepare_mahler()


def admit_comma(context: QueryContext) -> None:
    from number_compiler.api.number_api import CommaTermPayload
    from number_compiler.arithmetic.contracts.unresolved_term import (
        UnresolvedSequenceTerm,
    )
    from number_compiler.sequences.comma.certificates import (
        CERTIFIED_MAX_INDEX,
        unresolved_boundary,
    )

    request = context.request
    payload = context._raw_projected_term().payload
    if not isinstance(payload, CommaTermPayload):
        raise TypeError("comma query published a foreign term payload")
    if not context.request.observations.info:
        payload.require_certified()
        return
    options = _options(context, CommaObservationOptions)
    if request.presentation.no_value and not set(options.info) - {
        "metrics",
        "certificate",
    }:
        if request.index > CERTIFIED_MAX_INDEX:
            context.unresolved_boundary = unresolved_boundary(request.index)
        return
    try:
        payload.require_certified()
    except UnresolvedSequenceTerm as error:
        if not request.presentation.no_value or set(options.info) - {
            "metrics",
            "certificate",
        }:
            raise
        context.unresolved_boundary = error


def observe_comma(context: QueryContext, name: str) -> Packet:
    from number_compiler.api.number_api import CommaTermPayload

    payload = context.term.payload
    if not isinstance(payload, CommaTermPayload):
        raise TypeError("comma query published a foreign term payload")
    if name == "certificate":
        from number_compiler.sequences.comma.certificates import certificate_status

        packet = certificate_status(
            context.request.index,
            payload.term.ledger,
            payload.term.max_work,
            shared_cache=payload.term.shared_cache,
            memo=payload.term.certificate_memo,
        )
        return _publish(context, name, packet, coordinates=(("requested_index",),))
    payload.require_certified()
    value = payload.term.clock() if name == "clock" else payload.term.tropical()
    return _publish(
        context,
        name,
        {"value": value, "scope": "checked comma-child prefix"},
    )


def prepare_special(context: QueryContext, term: ProjectedNumberTerm) -> None:
    del context, term


def prepare_comma(context: QueryContext, term: ProjectedNumberTerm) -> None:
    del context, term


def observe_special(context: QueryContext, name: str) -> Packet:
    request = context.request
    options = _options(context, SpecialObservationOptions)
    if name == "root":
        from number_compiler.api.cylinder_observation import observe_etale_root

        if options.defect is None:
            raise ValueError("--info root requires --defect")
        packet = observe_etale_root(
            request.family,
            request.index,
            options.defect,
            max_digits=options.max_digits,
        )
        return _publish(context, name, packet)

    from number_compiler.api.sequence_compiler import CanonicalSequenceCompiler

    if context._special is None:
        resolution = CanonicalSequenceCompiler().resolve_special_theorem(
            request.family,
            request.index,
            collect_etale_factor="factor" in options.info,
            max_factor_products=options.max_factor_products,
            max_candidate_bits=options.max_candidate_bits,
        )
        failure = resolution.source_guard.failure_bit
        status = "unknown" if failure is None else "composite" if failure else "prime"
        context._special = {
            "family": request.family,
            "index": request.index,
            "status": status,
            "decided": resolution.decided,
            "method": resolution.projection_method,
            "factor_query_status": resolution.factor_query_status,
            "certificate": (
                None if resolution.primality is None else asdict(resolution.primality)
            ),
            "factor_witness": resolution.factor_witness,
            "factor_target": {"family": request.family, "parameter": request.index},
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
    if name == "primality":
        packet = dict(context._special)
        return _publish(
            context,
            name,
            packet,
            coordinates=(("index",),),
        )
    if name == "factor":
        packet = dict(context._special)
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
        return _publish(
            context,
            name,
            packet,
            coordinates=(("index",), ("factor_target", "parameter")),
        )
    raise ValueError("observation has no special-number handler")


def observe_antihydra(context: QueryContext, name: str) -> Packet:
    options = _options(context, AntihydraObservationOptions)
    from number_compiler.api.number_api import AntihydraTermPayload

    alias = (
        "twisted"
        if name == "tape" and "twisted" in options.info
        else "tape"
        if name == "twisted" and "tape" in options.info
        else None
    )
    if alias is not None and alias in context._info:
        payload = context.term.payload
        if not isinstance(payload, AntihydraTermPayload):
            raise TypeError("Antihydra query published a foreign term payload")
        payload.term.engine.count("query_observer_reuses")
        packet = dict(context._info[alias])
        packet["kind"] = name
        return packet

    payload = context.term.payload
    if not isinstance(payload, AntihydraTermPayload):
        raise TypeError("Antihydra query published a foreign term payload")
    if name in {"ledger", "modular"}:
        result = payload.term.result()
        centered_odd = (result.returns + result.balance) // 3
        value = (
            {
                "h": result.h,
                "ledger": result.balance,
                "minimum_ledger": result.minimum,
                "first_failure_index": result.first_failure_index,
                "centered_odd_events": centered_odd,
                "odd_a_steps": result.returns - centered_odd,
            }
            if name == "ledger"
            else {"h": result.h % options.modulus, "modulus": options.modulus}
        )
        return _publish(
            context,
            name,
            {
                "value": value,
                "scope": "total arithmetic iteration",
                "requested_returns": context.request.index,
                "completed_returns": result.returns,
                "nonhalting_certified": False,
            },
            coordinates=(("requested_returns",),),
        )

    from number_compiler.api.antihydra_observation import (
        observe_arithmetic_many,
        observe_run,
    )

    if name in {"mahler", "hensel"}:
        if {"mahler", "hensel"}.issubset(options.info):
            packets = observe_arithmetic_many(
                payload.term.result(),
                kinds=("mahler", "hensel"),
                precision=options.precision,
                _include_metrics=False,
            )
            context._info.update(
                {
                    packet_name: _publish(
                        context,
                        packet_name,
                        packet,
                        coordinates=(("requested_returns",),),
                    )
                    for packet_name, packet in packets.items()
                }
            )
            return context._info[name]
        packet = observe_arithmetic_many(
            payload.term.result(),
            kinds=(name,),
            precision=options.precision,
            _include_metrics=False,
        )[name]
        return _publish(context, name, packet, coordinates=(("requested_returns",),))

    packet = observe_run(
        payload.term.physical_run(),
        kind=name,
        modulus=options.modulus,
        width=options.width,
        sign=options.sign,
        precision=options.precision,
        time_width=options.time_width,
        time_sign=options.time_sign,
        max_observer_terms=options.max_observer_terms,
        _include_metrics=False,
    )
    return _publish(context, name, packet, coordinates=(("requested_returns",),))


__all__ = [
    "admit_collatz",
    "admit_comma",
    "admit_noop",
    "admit_reverse",
    "observe_antihydra",
    "observe_collatz",
    "observe_comma",
    "observe_noop",
    "observe_reverse",
    "observe_special",
    "prepare_antihydra",
    "prepare_collatz",
    "prepare_comma",
    "prepare_noop",
    "prepare_reverse",
    "prepare_special",
    "verify_antihydra",
]
