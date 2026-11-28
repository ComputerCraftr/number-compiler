"""Lazy observations over a bounded five-reversal source owner."""

from __future__ import annotations

from dataclasses import asdict
from itertools import islice
from typing import TYPE_CHECKING

from number_compiler.api.cli_types import FiveReverseObservationOptions
from number_compiler.api.matrix_contracts import (
    MatrixKind,
    MatrixRequest,
    OrderedMatrixRequest,
    SourceTransferRequest,
)
from number_compiler.api.observation_adapters import (
    admit_noop as admit_noop,
)
from number_compiler.api.observation_adapters import (
    prepare_noop as prepare_noop,
)
from number_compiler.api.observation_types import ObservationId, OutputStatus
from number_compiler.api.observation_views import ObservationView as View
from number_compiler.api.query_types import FiveReverseTermQuery
from number_compiler.api.reverse_payloads import FiveReverseTermPayload

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.output_schema import JsonValue


def observe(context: QueryContext, name: ObservationId) -> dict[str, JsonValue]:
    from number_compiler.api.observation_adapters import (
        publish_observation,
        publish_views,
    )
    from number_compiler.sequences.five_reverse.ports import source_residue45

    options = context.request.observations
    if not isinstance(options, FiveReverseObservationOptions):
        raise TypeError("five-reversal observations need their typed options")
    query = context.request.execution
    if not isinstance(query, FiveReverseTermQuery):
        raise TypeError("five-reversal observer received a foreign query")
    if name is ObservationId.ARITHMETIC_MODULAR:
        packets: dict[View, dict[str, JsonValue]] = {}
        for view in context.views_for(name):
            if view is View.ENDPOINT_RESIDUE:
                packet: dict[str, object] = {
                    "modulus": options.modulus,
                    "residue": source_residue45(query.seed, query.index)
                    % options.modulus,
                    "source_index": context.request.presentation_index,
                    "execution_authority": False,
                }
            else:
                from number_compiler.sequences.five_reverse.quotients import (
                    MovingCutBudgetExceeded,
                )

                try:
                    packet = _digit_field(
                        context, query, options.arithmetic_modular_places
                    )
                except MovingCutBudgetExceeded as exc:
                    packet = {
                        "status": OutputStatus.UNAVAILABLE.value,
                        "reason": str(exc),
                    }
            packets[view] = publish_observation(context, name, packet)
        return publish_views(context, name, packets)
    if name is ObservationId.TEMPORAL_BANK:
        payload = context.term.payload
        if not isinstance(payload, FiveReverseTermPayload):
            raise TypeError("five-reversal bank requires its exact source owner")
        return publish_observation(
            context, name, asdict(payload.term.source_transfer(0))
        )
    if name is ObservationId.TEMPORAL_CLOSED_FORM:
        from number_compiler.sequences.five_reverse.quotients import (
            MovingCutBudgetExceeded,
        )

        try:
            result = _closed_form(context, query, options)
        except MovingCutBudgetExceeded as exc:
            result = {"status": OutputStatus.UNAVAILABLE.value, "reason": str(exc)}
        return publish_views(
            context,
            name,
            {View.CLOSED_ENDPOINT: publish_observation(context, name, result)},
        )
    raise ValueError(f"unsupported five-reversal observation: {name}")


def _physical_suffix(
    context: QueryContext,
    query: FiveReverseTermQuery,
    digits: int,
) -> tuple[int, bool]:
    from number_compiler.sequences.five_reverse.quotients import (
        MAX_MOVING_CUT_DIGIT_ACTIONS,
        MovingCutBudgetExceeded,
        physical_low_band_from_h,
    )

    max_places = min(4096, query.max_state_bits // 4)
    if query.index > query.max_steps or query.seed.bit_length() > query.max_state_bits:
        raise MovingCutBudgetExceeded("physical low band exceeds the source budget")
    if digits > max_places:
        raise MovingCutBudgetExceeded("physical low band exceeds the precision budget")
    if not context.request.presentation.no_value:
        payload = context.term.payload
        if not isinstance(payload, FiveReverseTermPayload):
            raise TypeError("five-reversal band requires its exact source owner")
        return sum(
            digit * 10**position
            for position, digit in enumerate(islice(payload.term.iter_digits(), digits))
        ), True
    # Saturate the user-supplied step limit before multiplying by precision.
    capped_steps = min(query.max_steps, MAX_MOVING_CUT_DIGIT_ACTIONS)
    max_actions = max(1, min(MAX_MOVING_CUT_DIGIT_ACTIONS, capped_steps * max_places))
    return physical_low_band_from_h(
        query.seed,
        query.index,
        digits,
        max_places=max_places,
        max_digit_actions=max_actions,
    ), False


def _digit_field(
    context: QueryContext,
    query: FiveReverseTermQuery,
    places: int,
) -> dict[str, object]:
    from number_compiler.sequences.five_reverse.quotients import (
        digit_field225,
        digit_field_residue,
    )

    state = digit_field225(query.seed, query.index)
    parent = state.residue
    modulus = 9 * 5**places
    materialized = False
    if places <= 2:
        residue = parent % modulus
    else:
        suffix, materialized = _physical_suffix(context, query, places - 1)
        residue = digit_field_residue(suffix, 2 * parent % 9, places)
        if residue % 225 != parent:
            raise ValueError("source-selected field disagrees with its mod-225 parent")
    packet: dict[str, object] = {
        "modulus": modulus,
        "field_residue": residue,
        "field_residue225": parent,
        "base_five_places": places,
        "successor_closed": places <= 2,
        "source_occurrences_materialized": materialized,
        "execution_authority": False,
    }
    if places == 3 and materialized:
        from number_compiler.sequences.five_reverse.ports import FiveCarryPort

        payload = context.term.payload
        if not isinstance(payload, FiveReverseTermPayload):
            raise TypeError("five-reversal field requires its exact source owner")
        port = payload.term.source_transfer(0).initial_port
        head = (
            port.head3 // 100
            if isinstance(port, FiveCarryPort)
            else port.high_digits[0]
        )
        packet["next_field_residue1125"] = state.next_mod1125(leading_source_digit=head)
    return packet


def _closed_form(
    context: QueryContext,
    query: FiveReverseTermQuery,
    options: FiveReverseObservationOptions,
) -> dict[str, object]:
    from number_compiler.sequences.five_reverse.quotients import (
        MovingCutBudgetExceeded,
        h_power_mod,
        reflected_h_source,
    )

    places = options.temporal_closed_form_places
    if (
        query.seed.bit_length() > query.max_state_bits
        or places > query.max_state_bits // 4
    ):
        raise MovingCutBudgetExceeded(
            "H source or precision exceeds the state-bit budget"
        )
    source = reflected_h_source(query.seed, query.index) if query.index else None
    if source is not None and query.max_steps < source.exponent < 2 * places:
        raise MovingCutBudgetExceeded("H projection exceeds its auxiliary step budget")
    packet: dict[str, object] = {
        "decimal_places": places,
        "h_source": None if source is None else source.source,
        "h_exponent": None if source is None else source.exponent,
        "unnormalized_residue": None
        if source is None
        else h_power_mod(
            source.source,
            source.exponent,
            places,
        ),
        "normalization": "5 * decimal-trailing-zero-normalize(H^exponent(source))",
        "initial_value": query.seed if source is None else None,
        "execution_authority": False,
    }
    digits = options.temporal_closed_form_digits
    if digits:
        from number_compiler.arithmetic.fields.radix import (
            digits_lsd,
            value_from_lsd_digits,
        )

        suffix, materialized = _physical_suffix(context, query, digits)
        low_digits = digits_lsd(suffix, 10, digits)
        half_digits = tuple(digit // 2 for digit in low_digits)
        packet.update(
            physical_low_digits=digits,
            physical_low_residue=suffix,
            binary_half_digit_mask_lsd="".join(
                "1" if digit else "0" for digit in half_digits
            ),
            low_first_prefix_base5=value_from_lsd_digits(reversed(half_digits), 5),
            high_first_residue_base5=value_from_lsd_digits(half_digits, 5),
            source_occurrences_materialized=materialized,
        )
    return packet


def matrix(context: QueryContext, request: MatrixRequest) -> dict[str, object]:
    payload = context.term.payload
    if not isinstance(payload, FiveReverseTermPayload):
        raise TypeError("five-reversal matrix requires its exact source owner")
    if isinstance(request, SourceTransferRequest):
        transfer = payload.term.source_transfer(request.steps, trace=request.trace)
        packet = asdict(transfer)
        coefficients = transfer.pascal_innovation()
        if coefficients is not None:
            packet["finite_f5_pascal_coefficients"] = coefficients
        return packet
    if not isinstance(request, OrderedMatrixRequest):
        raise ValueError("five-reversal has no innovation matrix")
    if request.kind is not MatrixKind.DIGIT_BAND:
        raise ValueError("five-reversal has no certified bit-fibre carry projection")
    result = payload.term.digit_band(
        request.steps,
        request.band_width,
        request.modulus,
        coefficients=request.coefficients,
        trace=request.trace,
    )
    return asdict(result)
