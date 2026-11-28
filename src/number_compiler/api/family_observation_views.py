"""Result-view contracts used by the canonical family registry."""

from number_compiler.api.observation_types import SelectorId
from number_compiler.api.observation_views import ObservationView as View
from number_compiler.api.observation_views import ViewSpec
from number_compiler.arithmetic.contracts.family_identity import FamilyId

_TICKS = "physical-recurrence-ticks"


def family_observation_views(family: FamilyId) -> tuple[ViewSpec, ...]:
    return _VIEWS[family]


_VIEWS: dict[FamilyId, tuple[ViewSpec, ...]] = {
    FamilyId.REVERSE_ADD: (
        ViewSpec(
            View.ENDPOINT_RESIDUE,
            "small-radix-reverse-add-endpoint",
            _TICKS,
            "coefficient-ring",
            "completed-source",
            options=("modulus",),
        ),
        ViewSpec(
            View.RESIDUE,
            "decimal-reverse-add-residue",
            _TICKS,
            "modulus-99",
            "finite-residue",
            default=True,
        ),
        ViewSpec(
            View.ALTERNATING,
            "alternating-reverse-add-accumulator",
            _TICKS,
            "modulus-99",
            "finite-residue",
            default=True,
        ),
        ViewSpec(
            View.SOURCE_ACTION,
            "q19-source-orbit",
            _TICKS,
            "decimal-pair",
            "completed-source",
            default=True,
        ),
    ),
    FamilyId.DOUBLE_REVERSE: (
        ViewSpec(
            View.RESIDUE,
            "decimal-width-residue",
            _TICKS,
            "moduli-99-198",
            "source-guarded",
            default=True,
        ),
        ViewSpec(
            View.MIXED_ADIC,
            "mixed-adic-decimal-port",
            _TICKS,
            "moduli-1980-9900",
            "source-guarded",
        ),
        ViewSpec(
            View.RESIDUE_PERIOD,
            "decimal-residue-return",
            _TICKS,
            "moduli-99-198",
            "source-guarded",
            default=True,
        ),
        ViewSpec(
            View.DEFECT_SAMPLES,
            "finite-carry-defect",
            "four-generation-blocks",
            "decimal-suffix",
            "bounded-samples",
            options=(
                "prefix_horizon",
                "period_samples",
                "defect_digits",
                "period_stride",
                "period_max_lag",
            ),
        ),
        ViewSpec(
            View.ALTERNATING,
            "alternating-laurent-accumulator",
            _TICKS,
            "moduli-198-1980",
            "source-guarded",
            default=True,
        ),
        ViewSpec(
            View.CLOSED_ENDPOINT,
            "reflected-endpoint",
            _TICKS,
            "decimal",
            "completed-source",
            default=True,
            options=("modulus",),
        ),
        ViewSpec(
            View.SOURCE_ACTION,
            "reflected-source-morphism",
            _TICKS,
            "decimal-pair",
            "source-guarded",
            options=(
                "prefix_horizon",
                "period_samples",
                "defect_digits",
                "period_stride",
                "period_depth",
                "period_max_lag",
                "period_drivers",
            ),
        ),
    ),
    FamilyId.COLLATZ: (
        ViewSpec(
            View.ENDPOINT_RESIDUE,
            "collatz-event-residues",
            "accelerated-odd-events",
            "coefficient-ring",
            "finite-residue",
            default=True,
            selector=SelectorId.EVENTS,
            options=("modulus",),
        ),
        ViewSpec(
            View.EXECUTED_MACROS,
            "executed-collatz-macro-coverage",
            _TICKS,
            "initial-source-run",
            "completed-source",
        ),
        ViewSpec(
            View.SINGLE,
            "ordered-collatz-accumulator",
            _TICKS,
            "coefficient-ring",
            "source-guarded",
            default=True,
            options=("accumulator_modulus",),
        ),
        ViewSpec(
            View.ALTERNATING,
            "collatz-added-subtracted",
            _TICKS,
            "physical-operation",
            "source-guarded",
        ),
    ),
    FamilyId.ANTIHYDRA: (
        ViewSpec(
            View.ENDPOINT_RESIDUE,
            "antihydra-endpoint-residue",
            "macro-returns-after-startup",
            "coefficient-ring",
            "finite-residue",
            default=True,
            options=("modulus",),
        ),
        ViewSpec(
            View.FINITE_GUARD,
            "finite-weighted-mahler-guard",
            "physical-recurrence-ticks",
            "dyadic-source-and-rational-fiber",
            "finite-guard",
        ),
        ViewSpec(
            View.FINITE_SAFETY,
            "pointed-rational-mahler-safety",
            "physical-recurrence-ticks",
            "centered-endpoint-and-fractional-tail",
            "finite-rational-safety",
            options=("safety_horizon", "fractional_tail"),
        ),
        ViewSpec(
            View.GRAPH_ACTION,
            "pointed-mahler-closed-row",
            "physical-recurrence-ticks",
            "centered-endpoint-and-fractional-tail",
            "finite-admitted-graph-action",
            default=True,
            options=("temporal_macro_copies", "fractional_tail"),
        ),
    ),
}
