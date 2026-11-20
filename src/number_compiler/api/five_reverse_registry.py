"""Metadata-only registration for the decimal five-reversal family."""

from dataclasses import fields

from number_compiler.api.cli_types import FiveReverseObservationOptions
from number_compiler.api.family_types import (
    AdapterBinding,
    FamilyCapability,
    FamilySpec,
    ObservationValueBinding,
)
from number_compiler.api.matrix_contracts import (
    MatrixCapability,
    MatrixCoordinate,
    MatrixKind,
    MatrixLaw,
)
from number_compiler.api.observation_types import (
    IndexUnit,
    ObservationAdapterBinding,
    ObservationId,
    OptionSpec,
    option_default,
)
from number_compiler.api.query_types import FiveReverseTermQuery

_QUOTIENT_OPTIONS = {
    "temporal_digit_field_places": (
        ObservationId.TEMPORAL_DIGIT_FIELD,
        "number of base-five places in the digit-field residue",
    ),
    "temporal_closed_form_places": (
        ObservationId.TEMPORAL_CLOSED_FORM,
        "decimal precision of the unnormalized H action",
    ),
    "temporal_closed_form_digits": (
        ObservationId.TEMPORAL_CLOSED_FORM,
        "physical low digits demanded from the normalized H action",
    ),
}


def five_reverse_spec(modulus: OptionSpec) -> FamilySpec:
    """Bind the family to the registry-owned modular option declaration."""
    quotient_options = tuple(
        (
            field.name,
            OptionSpec(
                option_default(field.default),
                (_QUOTIENT_OPTIONS[field.name][0],),
                name=field.name,
                help=_QUOTIENT_OPTIONS[field.name][1],
            ),
        )
        for field in fields(FiveReverseObservationOptions)
        if field.name in _QUOTIENT_OPTIONS
    )
    return FamilySpec(
        FamilyCapability(
            IndexUnit.ITERATIONS,
            ("seed",),
            (
                ObservationId.METRICS,
                ObservationId.TEMPORAL_BANK,
                ObservationId.ARITHMETIC_MODULAR,
                ObservationId.TEMPORAL_DIGIT_FIELD,
                ObservationId.TEMPORAL_CLOSED_FORM,
                ObservationId.TEMPORAL_MATRIX,
            ),
        ),
        FiveReverseTermQuery,
        AdapterBinding("number_compiler.api.projections.five_reverse", "project"),
        ObservationAdapterBinding(
            "number_compiler.api.five_reverse_observation",
            "prepare_noop",
            "admit_noop",
            "observe",
        ),
        term_observation=ObservationValueBinding(
            FiveReverseObservationOptions, ("modulus", *_QUOTIENT_OPTIONS)
        ),
        observer_options=(("modulus", modulus), *quotient_options),
        matrix=MatrixCapability(
            "number_compiler.api.five_reverse_observation",
            "matrix",
            MatrixCoordinate.LOW_BORDER,
            4096,
            0,
            default_coordinate=None,
            law=MatrixLaw.GUARDED_REVERSAL_PORT,
            max_trace_steps=128,
            ordered_kinds=(MatrixKind.DIGIT_BAND,),
        ),
    )
