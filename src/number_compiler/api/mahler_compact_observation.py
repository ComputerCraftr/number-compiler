"""Serialize demanded finite Mahler actions through the family registry."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.json_output import is_object_sequence, is_string_object_mapping
from number_compiler.api.observation_adapters import (
    Packet,
    publish_observation,
    publish_views,
)
from number_compiler.api.observation_types import ObservationId
from number_compiler.api.observation_views import ObservationView
from number_compiler.resources.ledger import ResourceLedger

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.cli_types import AntihydraObservationOptions
    from number_compiler.sequences.antihydra.runtime import ArithmeticResult


def observe_finite_safety(
    context: QueryContext,
    options: AntihydraObservationOptions,
    result: ArithmeticResult,
) -> Packet:
    from number_compiler.sequences.antihydra.mahler_finite_safety import finite_safety

    horizon, tail = options.safety_horizon, options.fractional_tail
    if horizon is None or tail is None:
        raise ValueError(
            "finite safety requires a horizon and an exact fractional tail"
        )
    return publish_observation(
        context,
        ObservationId.SAFETY_LEDGER,
        {
            **finite_safety(result, tail, horizon),
            "source_binding": result.source_binding,
            "centered_source": result.h - 1,
            "initial_fraction": str(tail),
            "physical_continuation_authorized": False,
        },
    )


def observe_powered_graph(
    context: QueryContext,
    options: AntihydraObservationOptions,
    result: ArithmeticResult,
) -> Packet:
    from number_compiler.sequences.antihydra.mahler_powered_graph import powered_graph

    copies, tail = options.temporal_macro_copies, options.fractional_tail
    if copies is None or tail is None:
        raise ValueError(
            "graph action requires repeated copies and an exact fractional tail"
        )
    name = ObservationId.TEMPORAL_MACRO
    return publish_views(
        context,
        name,
        {
            ObservationView.GRAPH_ACTION: publish_observation(
                context, name, powered_graph(result, tail, copies)
            )
        },
    )


def observe_continued_fraction(
    context: QueryContext, options: AntihydraObservationOptions
) -> Packet:
    from number_compiler.api.number_api import AntihydraTermPayload

    compiler = context.compiler
    if context.request.presentation.no_value and options.info == (
        ObservationId.ARITHMETIC_CONTINUED_FRACTION,
    ):
        # This query has an independent decimal source and no term owner.
        ledger = ResourceLedger(compiler.max_context_nodes, compiler.max_cache_entries)
    else:
        payload = context.term.payload
        if not isinstance(payload, AntihydraTermPayload):
            raise TypeError("continued-fraction observer received a foreign context")
        ledger = payload.term.ledger
    band = options.continued_fraction_band
    if band is None:
        from number_compiler.sequences.antihydra.mahler_continued_fraction_cylinder import (
            continued_fraction_cylinder,
        )

        horizon = options.safety_horizon
        if horizon is None:
            raise ValueError("a CF cylinder requires a physical horizon")
        packet = continued_fraction_cylinder(
            horizon,
            options.continued_fraction_max_coefficients or 20_000,
            ledger=ledger,
            shared_cache=compiler.shared_cache,
        )
    else:
        from number_compiler.sequences.antihydra.mahler_continued_fraction import (
            continued_fraction_band,
        )

        exponent, cut, width, rows = band
        packet = continued_fraction_band(
            exponent,
            cut,
            width,
            rows,
            ledger=ledger,
            shared_cache=compiler.shared_cache,
        )
    context.reserve_observation_storage(ledger, _packet_nodes(packet))
    return publish_observation(
        context, ObservationId.ARITHMETIC_CONTINUED_FRACTION, packet
    )


def _packet_nodes(packet: dict[str, object]) -> int:
    """Charge the bounded continued-fraction payload and its wire projection."""
    pending: list[object] = [packet]
    nodes = 0
    while pending:
        value = pending.pop()
        nodes += 8
        if isinstance(value, int):
            nodes += (2 * value.bit_length() + 63) // 64
        elif isinstance(value, str):
            nodes += len(value)
        elif is_string_object_mapping(value):
            pending.extend(value.values())
        elif is_object_sequence(value):
            pending.extend(value)
    return nodes
