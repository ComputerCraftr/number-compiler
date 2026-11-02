"""Demanded CLI adapter for the Antihydra arithmetic and run observers."""

from __future__ import annotations

from typing import TYPE_CHECKING

from number_compiler.api.antihydra_observation import (
    AntihydraArithmeticKind,
    AntihydraRunKind,
)
from number_compiler.api.cli_types import AntihydraObservationOptions
from number_compiler.api.observation_adapters import (
    Packet,
    observation_options,
    publish_observation,
)
from number_compiler.api.observation_types import ObservationId
from number_compiler.arithmetic.contracts.family_identity import FamilyId

if TYPE_CHECKING:
    from number_compiler.api.cli_context import QueryContext
    from number_compiler.api.number_api import ProjectedNumberTerm

_ARITHMETIC_KIND_BY_OBSERVATION = {
    ObservationId.ARITHMETIC_MAHLER: AntihydraArithmeticKind.MAHLER,
    ObservationId.ARITHMETIC_HENSEL: AntihydraArithmeticKind.HENSEL,
}
_ARITHMETIC_OBSERVATION_BY_KIND = {
    kind: observation for observation, kind in _ARITHMETIC_KIND_BY_OBSERVATION.items()
}
_RUN_KIND_BY_OBSERVATION = {
    ObservationId.TEMPORAL_CLOCK: AntihydraRunKind.CLOCK,
    ObservationId.ARITHMETIC_TWISTED: AntihydraRunKind.TWISTED,
    ObservationId.SPATIAL_TAPE: AntihydraRunKind.TAPE,
    ObservationId.TEMPORAL_SPACETIME: AntihydraRunKind.SPACETIME,
    ObservationId.ARITHMETIC_HASSE: AntihydraRunKind.HASSE,
    ObservationId.ARITHMETIC_TROPICAL: AntihydraRunKind.TROPICAL,
    ObservationId.ARITHMETIC_FACTOR: AntihydraRunKind.FACTOR,
}


def prepare_antihydra(context: QueryContext, term: ProjectedNumberTerm) -> None:
    if not context.request.observations.info:
        return
    options = observation_options(context, AntihydraObservationOptions)
    from number_compiler.api.number_api import AntihydraTermPayload

    if not isinstance(term.payload, AntihydraTermPayload):
        raise TypeError("Antihydra query published a foreign term payload")
    if ObservationId.ARITHMETIC_MAHLER in options.info:
        term.payload.term.prepare_mahler()


def admit_antihydra(context: QueryContext) -> None:
    from number_compiler.api.number_api import AntihydraTermPayload

    term = context.raw_projected_term()
    if context.request.family is not FamilyId.ANTIHYDRA or not isinstance(
        term.payload, AntihydraTermPayload
    ):
        raise TypeError("Antihydra query published a foreign term payload")


def observe_antihydra(context: QueryContext, name: ObservationId) -> Packet:
    options = observation_options(context, AntihydraObservationOptions)
    from number_compiler.api.number_api import AntihydraTermPayload

    alias = (
        ObservationId.ARITHMETIC_TWISTED
        if name is ObservationId.SPATIAL_TAPE
        and ObservationId.ARITHMETIC_TWISTED in options.info
        else ObservationId.SPATIAL_TAPE
        if name is ObservationId.ARITHMETIC_TWISTED
        and ObservationId.SPATIAL_TAPE in options.info
        else None
    )
    cached_alias = None if alias is None else context.cached_information(alias)
    if cached_alias is not None:
        payload = context.term.payload
        if not isinstance(payload, AntihydraTermPayload):
            raise TypeError("Antihydra query published a foreign term payload")
        payload.term.engine.count("query_observer_reuses")
        packet = dict(cached_alias)
        packet["kind"] = name.value
        return packet

    payload = context.term.payload
    if not isinstance(payload, AntihydraTermPayload):
        raise TypeError("Antihydra query published a foreign term payload")
    if name is ObservationId.TEMPORAL_DIAGONAL_CARRY:
        from dataclasses import asdict

        from number_compiler.api.json_output import json_value
        from number_compiler.api.output_schema import AntihydraDiagonalPacket
        from number_compiler.hashlife.execution.dyadic_return_runs import (
            RunArithmeticWorkspace,
        )
        from number_compiler.sequences.antihydra.mahler_carry_quotient import (
            project_weighted_carry,
        )
        from number_compiler.sequences.antihydra.mahler_diagonal_carry import (
            MAX_DIAGONAL_COLUMNS,
        )

        result = payload.term.result()
        workspace = payload.term.arithmetic_image()
        scratch = RunArithmeticWorkspace.for_ledger(
            workspace.ledger, "antihydra_diagonal"
        )
        with scratch.scope():
            carry = project_weighted_carry(workspace, reserve_bits=scratch.require_bits)
            field = (
                carry.x15_morphism(reserve_bits=scratch.require_bits)
                .diagonal_tower()
                .packed_field(
                    options.width,
                    max_columns=MAX_DIAGONAL_COLUMNS,
                    max_observer_terms=options.max_observer_terms,
                    reserve_bits=scratch.require_bits,
                )
            )
            diagonal_packet: AntihydraDiagonalPacket = {
                "family": "antihydra",
                "kind": "temporal.diagonal-carry",
                "source_binding": result.source_binding,
                "requested_returns": result.returns,
                "endpoint": result.h,
                "clock_unit": "macro_returns_after_startup",
                "all_time_claim": False,
                "field": json_value(asdict(field)),
            }
            return publish_observation(
                context, name, diagonal_packet, coordinates=(("requested_returns",),)
            )
    if name in {
        ObservationId.SAFETY_LEDGER,
        ObservationId.ARITHMETIC_MODULAR,
    }:
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
            if name is ObservationId.SAFETY_LEDGER
            else {"h": result.h % options.modulus, "modulus": options.modulus}
        )
        return publish_observation(
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

    if name in {
        ObservationId.ARITHMETIC_MAHLER,
        ObservationId.ARITHMETIC_HENSEL,
    }:
        if {
            ObservationId.ARITHMETIC_MAHLER,
            ObservationId.ARITHMETIC_HENSEL,
        }.issubset(options.info):
            packets = observe_arithmetic_many(
                payload.term.result(),
                kinds=(
                    AntihydraArithmeticKind.MAHLER,
                    AntihydraArithmeticKind.HENSEL,
                ),
                precision=options.precision,
                _include_metrics=False,
            )
            context.remember_information_many(
                {
                    _ARITHMETIC_OBSERVATION_BY_KIND[kind]: publish_observation(
                        context,
                        _ARITHMETIC_OBSERVATION_BY_KIND[kind],
                        packets[kind.value],
                        coordinates=(("requested_returns",),),
                    )
                    for kind in (
                        AntihydraArithmeticKind.MAHLER,
                        AntihydraArithmeticKind.HENSEL,
                    )
                }
            )
            cached_packet = context.cached_information(name)
            if cached_packet is None:
                raise RuntimeError("combined Antihydra observation was not retained")
            return cached_packet
        arithmetic_kind = _ARITHMETIC_KIND_BY_OBSERVATION[name]
        arithmetic_packet = observe_arithmetic_many(
            payload.term.result(),
            kinds=(arithmetic_kind,),
            precision=options.precision,
            _include_metrics=False,
        )[arithmetic_kind.value]
        return publish_observation(
            context,
            name,
            arithmetic_packet,
            coordinates=(("requested_returns",),),
        )

    run_kind = _RUN_KIND_BY_OBSERVATION.get(name)
    if run_kind is None:
        raise ValueError("observation has no Antihydra run handler")
    run_packet = observe_run(
        payload.term.physical_run(),
        kind=run_kind,
        modulus=options.modulus,
        width=options.width,
        sign=options.sign,
        precision=options.precision,
        time_width=options.time_width,
        time_sign=options.time_sign,
        max_observer_terms=options.max_observer_terms,
        _include_metrics=False,
    )
    return publish_observation(
        context, name, run_packet, coordinates=(("requested_returns",),)
    )


__all__ = ["observe_antihydra", "prepare_antihydra"]
