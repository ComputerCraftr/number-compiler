"""Registry-dispatched matrix demands over the selected completed occurrence."""

from __future__ import annotations

from contextlib import ExitStack
from dataclasses import asdict
from importlib import import_module
from typing import TYPE_CHECKING, Protocol, runtime_checkable

from number_compiler.api.matrix_contracts import (
    InnovationMatrixRequest,
    MatrixClock,
    MatrixKind,
    MatrixLaw,
    MatrixRequest,
    NegacyclicMatrixRequest,
    OrderedMatrixRequest,
    SourceTransferRequest,
)
from number_compiler.api.observation_types import ObservationId

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.output_schema import JsonValue


@runtime_checkable
class MatrixObserver(Protocol):
    def __call__(
        self, context: QueryContext, request: MatrixRequest
    ) -> dict[str, object]: ...


def observe_matrix(
    context: QueryContext, name: ObservationId = ObservationId.TEMPORAL_MATRIX
) -> dict[str, JsonValue]:
    from number_compiler.api.family_registry import family_spec
    from number_compiler.api.observation_adapters import publish_observation

    capability = family_spec(context.request.family).matrix
    request = context.request.matrix
    if capability is None or request is None:
        raise ValueError("matrix observation has no admitted registry binding")
    observer = getattr(import_module(capability.module), capability.attribute, None)
    if not isinstance(observer, MatrixObserver):
        raise TypeError("matrix registry binding is not a valid observer")
    packet = dict(
        context.memoized_matrix_observation(lambda: observer(context, request))
    )
    if name is ObservationId.TEMPORAL_MATRIX:
        packet.pop("trace", None)
    packet.setdefault("status", "available")
    kind, law = MatrixKind.SOURCE_TRANSFER, capability.law
    if isinstance(request, OrderedMatrixRequest):
        kind = request.kind
        law = (
            MatrixLaw.ORDERED_CARRY_CONTINUANT
            if kind is MatrixKind.CARRY_CONTINUANT
            else MatrixLaw.ORDERED_DIGIT_CONTINUANT
        )
    elif isinstance(request, InnovationMatrixRequest):
        kind, law = MatrixKind.INNOVATION, MatrixLaw.INNOVATION_MOMENT
    elif isinstance(request, NegacyclicMatrixRequest):
        kind, law = MatrixKind.NEGACYCLIC, MatrixLaw.NEGACYCLIC_AFFINE
    packet["matrix_kind"], packet["law"] = kind.value, law.value
    if isinstance(request, (SourceTransferRequest, NegacyclicMatrixRequest)):
        if capability.clock is MatrixClock.PHYSICAL:
            packet["requested_physical_ticks"] = request.steps
        packet["horizon"] = {
            "ticks": request.steps,
            "unit": capability.clock.value,
        }
        if isinstance(request, SourceTransferRequest):
            packet["coordinate"] = {
                "kind": request.coordinate_kind.value,
                "value": request.coordinate,
            }
        # A finite observation packet cannot be fed back as an issuer token.
        packet["execution_authority"] = False
        packet["source_index"] = context.request.presentation_index
    elif isinstance(request, OrderedMatrixRequest):
        packet["horizon"] = {"ticks": request.steps, "unit": MatrixClock.PHYSICAL.value}
        packet["orientation"] = "later-column-actions-multiply-on-left"
        packet["coefficient_ring"] = {
            "kind": "integers-modulo",
            "modulus": request.modulus,
        }
        packet["authority_scope"] = "detached-source-guarded-observation"
        packet["requested_physical_ticks"] = request.steps
        packet["coordinate"] = {
            "kind": "carry-bits"
            if request.kind is MatrixKind.CARRY_CONTINUANT
            else "decimal-band-digits",
            "value": request.precision
            if request.kind is MatrixKind.CARRY_CONTINUANT
            else request.band_width,
        }
        packet["execution_authority"] = False
        packet["source_index"] = context.request.presentation_index
    return publish_observation(
        context,
        name,
        packet,
        coordinates=(("duration",), ("moment", "duration"))
        if isinstance(request, InnovationMatrixRequest)
        else (),
    )


def source_request(request: MatrixRequest) -> SourceTransferRequest:
    if not isinstance(request, SourceTransferRequest):
        raise TypeError("this family requires a source-transfer matrix")
    return request


def reverse_transfer(
    context: QueryContext, request: MatrixRequest
) -> dict[str, object]:
    from number_compiler.api.reverse_payloads import PoweredReverseAddTermPayload

    payload = context.term.payload
    if not isinstance(payload, PoweredReverseAddTermPayload):
        raise TypeError("reverse matrix received a foreign projected occurrence")
    if isinstance(request, OrderedMatrixRequest):
        from number_compiler.api.ordered_matrix_observation import reverse_ordered

        return reverse_ordered(context, request)
    if isinstance(request, InnovationMatrixRequest):
        result = (
            payload.term.temporal_matrix(
                max_bits=context.request.presentation.max_output_bits
            )
            if request.modulus is None
            else payload.term.temporal_moments(modulus=request.modulus)
        )
        return {**asdict(result), "execution_authority": False}
    from number_compiler.sequences.reverse_add.source_transfer import (
        source_transfer_packet,
    )

    demand = source_request(request)
    return source_transfer_packet(
        payload.term,
        steps=demand.steps,
        pair_depth=coordinate_value(demand),
        trace=demand.trace,
    )


def double_reverse_transfer(
    context: QueryContext, request: MatrixRequest
) -> dict[str, object]:
    from number_compiler.api.reverse_payloads import DoubleReverseTermPayload
    from number_compiler.sequences.double_reverse.source_transfer import (
        source_transfer_packet,
    )

    if isinstance(request, OrderedMatrixRequest):
        from number_compiler.api.ordered_matrix_observation import double_ordered

        return double_ordered(context, request)
    demand = source_request(request)
    payload = context.term.payload
    if not isinstance(payload, DoubleReverseTermPayload):
        raise TypeError("2rev10 matrix received a foreign projected occurrence")
    return source_transfer_packet(
        payload.term,
        steps=demand.steps,
        pair_depth=coordinate_value(demand),
        trace=demand.trace,
    )


def antihydra_transfer(
    context: QueryContext, request: MatrixRequest
) -> dict[str, object]:
    from number_compiler.api.mahler_matrix_observation import center_matrix_packet
    from number_compiler.api.number_api import AntihydraTermPayload

    demand = source_request(request)
    payload = context.term.payload
    if not isinstance(payload, AntihydraTermPayload):
        raise TypeError("Antihydra matrix received a foreign projected occurrence")
    return center_matrix_packet(payload.term.result(), demand.steps, trace=demand.trace)


def coordinate_value(request: SourceTransferRequest) -> int:
    if request.coordinate is None:
        raise ValueError("matrix requires an explicit spatial coordinate")
    return request.coordinate


def collatz_transfer(
    context: QueryContext, request: MatrixRequest
) -> dict[str, object]:
    from number_compiler.api.number_api import PoweredCollatzTermPayload
    from number_compiler.sequences.collatz.named_border_carry_matrix import (
        powered_from_term,
    )

    demand = source_request(request)
    payload = context.term.payload
    if not isinstance(payload, PoweredCollatzTermPayload):
        raise TypeError("Collatz matrix received a foreign projected occurrence")
    # Keep the one-macro no-trace tape/binding workspace charged through
    # construction of its immutable observation packet. Longer spans and
    # traces instead retain the query-owned parity action cache.
    with ExitStack() as single_macro_scope:
        joined = powered_from_term(
            payload.term,
            demand.steps,
            parity_actions_factory=lambda: context.collatz_parity_actions(
                payload.term.resource_ledger
            ),
            trace_required=demand.trace,
            single_macro_scope=single_macro_scope,
        )
        if joined is None:
            return {
                "status": "unavailable",
                "reason": "no admitted border macro covers the requested endpoint horizon",
            }
        return {
            "status": "available",
            "source": joined.source,
            "endpoint": joined.endpoint,
            "physical_ticks": joined.physical_ticks,
            "normalized_steps": joined.units.steps,
            "odd_events": joined.units.odds,
            "units_carry_transfer": asdict(joined.units),
            "forced_tens_carries": joined.forced_tens_carries,
            "source_guard_admitted": True,
            "scope": "source-admitted normalized decimal units transfer; higher inlets remain guarded",
            "physical_repeat_certified": False,
            **(
                joined.trace_packet(
                    normalized_steps=min(joined.units.steps, 64),
                    parity_actions=context.collatz_parity_actions(
                        payload.term.resource_ledger
                    ),
                )
                if demand.trace
                else {}
            ),
        }


def fermat_transfer(context: QueryContext, request: MatrixRequest) -> dict[str, object]:
    from number_compiler.api.elementary_payloads import FermatTermPayload

    payload = context.term.payload
    if not isinstance(payload, FermatTermPayload):
        raise TypeError("Fermat matrix received a foreign projected occurrence")
    if context.request.index > 16:
        raise ValueError("Fermat matrix source index exceeds the admitted bound 16")
    level = (1 << context.request.index) - 1
    if isinstance(request, NegacyclicMatrixRequest):
        from number_compiler.sequences.power_numbers.fermat_negacyclic_halo import (
            demand_fixed_multiplier_halo,
        )

        return demand_fixed_multiplier_halo(
            payload.spec.index, level, request.steps
        ).packet()
    demand = source_request(request)
    result = payload.spec.demand_fermat_powered_port_matrix(
        level,
        demand.steps,
        base=10,
        position=coordinate_value(demand),
    )
    return {**result.packet(trace=demand.trace), "primality_authority": False}


def mersenne_transfer(
    context: QueryContext, request: MatrixRequest
) -> dict[str, object]:
    from number_compiler.api.elementary_payloads import MersenneTermPayload

    demand = source_request(request)
    payload = context.term.payload
    if not isinstance(payload, MersenneTermPayload):
        raise TypeError("Mersenne matrix received a foreign projected occurrence")
    result = payload.spec.demand_mersenne_trace_matrix(
        demand.steps, base=10, position=coordinate_value(demand)
    )
    return {**result.packet(trace=demand.trace), "primality_authority": False}
