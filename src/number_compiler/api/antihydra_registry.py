"""Metadata-only Antihydra declaration for the canonical family registry."""

from number_compiler.api.cli_types import AntihydraObservationOptions
from number_compiler.api.family_observation_views import family_observation_views
from number_compiler.api.family_types import (
    AdapterBinding,
    FamilyCapability,
    FamilySpec,
    ObservationValueBinding,
)
from number_compiler.api.matrix_contracts import (
    MatrixCapability,
    MatrixCoordinate,
    MatrixLaw,
)
from number_compiler.api.observation_types import (
    IndexUnit,
    ObservationAdapterBinding,
    ObservationId,
    OptionSpec,
    OptionValueKind,
)
from number_compiler.api.query_types import AntihydraTermQuery, AntihydraVerifyQuery
from number_compiler.arithmetic.contracts.family_identity import FamilyId


def antihydra_spec(common_options: tuple[tuple[str, OptionSpec], ...]) -> FamilySpec:
    """Reuse the registry's shared spatial and arithmetic option declarations."""
    return FamilySpec(
        FamilyCapability(
            IndexUnit.MACRO_RETURNS_AFTER_STARTUP,
            (),
            (
                ObservationId.METRICS,
                ObservationId.TEMPORAL_MATRIX,
                ObservationId.SAFETY_LEDGER,
                ObservationId.TEMPORAL_CLOCK,
                ObservationId.ARITHMETIC_MODULAR,
                ObservationId.SPATIAL_TAPE,
                ObservationId.ARITHMETIC_TWISTED,
                ObservationId.TEMPORAL_SPACETIME,
                ObservationId.TEMPORAL_DIAGONAL_CARRY,
                ObservationId.ARITHMETIC_HASSE,
                ObservationId.ARITHMETIC_HENSEL,
                ObservationId.ARITHMETIC_MAHLER,
                ObservationId.ARITHMETIC_CONTINUED_FRACTION,
                ObservationId.TEMPORAL_MACRO,
                ObservationId.ARITHMETIC_TROPICAL,
                ObservationId.ARITHMETIC_FACTOR,
            ),
        ),
        AntihydraTermQuery,
        AdapterBinding("number_compiler.api.projections.antihydra", "project"),
        ObservationAdapterBinding(
            "number_compiler.api.antihydra_adapters",
            "prepare_antihydra",
            "admit_antihydra",
            "observe_antihydra",
        ),
        verify_query_type=AntihydraVerifyQuery,
        verify_flag="verify_nonhalting",
        verification=AdapterBinding(
            "number_compiler.api.observation_adapters", "verify_antihydra"
        ),
        description=(
            "antihydra: --nth uses macro_returns_after_startup; term zero is the seed. "
            "Certificate verification is a separate selector."
        ),
        views=family_observation_views(FamilyId.ANTIHYDRA),
        term_observation=ObservationValueBinding(
            AntihydraObservationOptions,
            (
                "modulus",
                "width",
                "sign",
                "precision",
                "time_width",
                "time_sign",
                "max_observer_terms",
                "safety_horizon",
                "fractional_tail",
                "temporal_macro_copies",
                "continued_fraction_band",
                "continued_fraction_max_coefficients",
            ),
        ),
        observer_options=common_options
        + (
            (
                "safety_horizon",
                OptionSpec(
                    None,
                    (
                        ObservationId.SAFETY_LEDGER,
                        ObservationId.ARITHMETIC_CONTINUED_FRACTION,
                    ),
                    help="finite physical safety ticks, from 0 through 4096",
                ),
            ),
            (
                "fractional_tail",
                OptionSpec(
                    None,
                    (ObservationId.SAFETY_LEDGER, ObservationId.TEMPORAL_MACRO),
                    value_kind=OptionValueKind.RATIONAL,
                    help="exact fractional inlet P/Q for the selected endpoint",
                ),
            ),
            (
                "temporal_macro_copies",
                OptionSpec(None, (ObservationId.TEMPORAL_MACRO,)),
            ),
            (
                "continued_fraction_band",
                OptionSpec(
                    None,
                    (ObservationId.ARITHMETIC_CONTINUED_FRACTION,),
                    value_kind=OptionValueKind.INTEGER_VECTOR,
                    help="diagonal band coordinates N,CUT,WIDTH,ROWS",
                ),
            ),
            (
                "continued_fraction_max_coefficients",
                OptionSpec(
                    None,
                    (ObservationId.ARITHMETIC_CONTINUED_FRACTION,),
                    help="finite CF coefficient limit, from 1 through 100000 (default 20000)",
                ),
            ),
            (
                "max_observer_terms",
                OptionSpec(
                    1_000_000,
                    (
                        ObservationId.TEMPORAL_SPACETIME,
                        ObservationId.TEMPORAL_DIAGONAL_CARRY,
                    ),
                ),
            ),
        ),
        bounded_observations=(ObservationId.ARITHMETIC_CONTINUED_FRACTION,),
        matrix=MatrixCapability(
            "number_compiler.api.matrix_observation",
            "antihydra_transfer",
            MatrixCoordinate.CENTER_SPLIT,
            32,
            256,
            default_coordinate=None,
            law=MatrixLaw.AFFINE_PREFIX_SAFETY,
        ),
    )
