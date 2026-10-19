"""Source-guarded Collatz boundary actions and innovation-borrow clocks.

These are *physical* trailing-decimal return words. They are not global
Hashlife IDs: entry and repetition length are authenticated by the exact
source and its 2-adic valuation. The action completes the final odd division,
so it consumes 3*r+1 or 4*r+1 physical ticks and has phase zero.

Borrow clocks sample a stated subset of *normalized* second-innovation
subtraction branches. They never authorize a successor or an endpoint.
"""

from __future__ import annotations

from contextlib import AbstractContextManager
from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Final, Self

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.hashlife.interfaces.border_macros import BorderWireValue
from number_compiler.resources.construction_scope import RuntimeConstruction
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.resources.metric_keys import collatz as _collatz_keys
from number_compiler.sequences.collatz.border_identity import (
    BOUNDARY_SELECTOR_IDENTITIES,
    CYCLE_26847,
    ENTRY_0563,
    ENTRY_89_AT_NINE,
    ENTRY_421,
    ENTRY_4721,
    ENTRY_26847_PHASES,
    PATH_305,
    PATH_630,
    BoundaryActionIdentity,
    BoundaryPathKind,
    CycleEntryPhase,
    GuardedBorderPath,
    MixedParityMotif,
    cycle_phase,
)
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)
from number_compiler.sequences.collatz.joint_radix_border import JointRadix6Source

COLLATZ_BOUNDARY_MACRO_ACTION_TAG: Final[str] = "collatz-boundary-macro-v2"

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.position_cycle_harmonics import (
        PositionHarmonicSpectrum,
    )
    from number_compiler.sequences.collatz.temporal_run_quotient import (
        CollatzF5AffineAction,
    )

BoundaryTemplateIdentity = BoundaryActionIdentity | MixedParityMotif
_BOUNDARY_PLAN_IDENTITIES = frozenset(BOUNDARY_SELECTOR_IDENTITIES)
_BOUNDARY_METRIC_SUFFIXES: dict[BoundaryActionIdentity, str] = {
    ENTRY_421: "421",
    ENTRY_4721: "4721",
    ENTRY_0563: "0563",
    ENTRY_89_AT_NINE: "989",
    PATH_630: "630",
    PATH_305: "305",
    **{
        entry: "26847" if phase == 0 else f"26847P{phase}"
        for phase, entry in enumerate(ENTRY_26847_PHASES)
    },
}


def boundary_macro_26847_phase(identity: BoundaryActionIdentity) -> int | None:
    """Return a typed cycle occurrence's phase on the five-digit border."""
    return cycle_phase(identity, CYCLE_26847)


def boundary_metric_suffix(identity: BoundaryActionIdentity) -> str:
    """Return the stable schema-eight counter suffix for an action identity."""
    if (
        type(identity) is GuardedBorderPath
        and identity.kind is BoundaryPathKind.THREE_BORDER_RETURN
    ):
        return "6305R"
    try:
        return _BOUNDARY_METRIC_SUFFIXES[identity]
    except KeyError as error:
        raise ValueError("boundary identity has no family counter") from error


def boundary_metric_key(
    identity: BoundaryActionIdentity, metric: _collatz_keys.BoundaryMacroMetric
) -> str:
    """Serialize one measured event without using its spelling as an action ID."""
    return f"collatz_physical_boundary_{boundary_metric_suffix(identity)}_macro_{metric.value}"


@dataclass(frozen=True, slots=True, init=False)
class CollatzBoundaryMacro:
    identity: BoundaryActionIdentity
    source: int
    repetitions: int
    maximum_repetitions: int
    physical_ticks: int
    odd_symbols: int
    endpoint: int
    fields: DyadicTerminalFieldAction
    width_blank: BlankLedger
    _issuer: object = field(repr=False, compare=False, init=False)

    def __init__(self) -> None:
        raise TypeError("Collatz boundary macros are issued by the guarded selector")

    @property
    def normalized_symbols(self) -> int:
        return self.fields.steps

    @property
    def quiet(self) -> bool:
        return self.identity == ENTRY_421

    @property
    def display_label(self) -> str:
        return self.identity.display_label

    def demanded_motif_position_harmonics(
        self,
        radix: int,
        position: int,
        *,
        walsh64: bool = False,
    ) -> PositionHarmonicSpectrum:
        """Read one position over the issued repeated motif, on demand."""
        from number_compiler.sequences.collatz.position_cycle_harmonics import (
            issued_boundary_motif_orbit,
        )

        return issued_boundary_motif_orbit(self).spectrum(
            radix, position, walsh64=walsh64
        )

    def f5_action(self) -> CollatzF5AffineAction:
        """Project the authenticated integer endpoint action onto F5."""
        from number_compiler.sequences.collatz.temporal_f5_observer import (
            project_dyadic_fields_f5,
        )

        return project_dyadic_fields_f5(self.fields)

    def observation(self) -> dict[str, object]:
        return {
            "border": self.identity.observation(run_parameters=(self.repetitions,)),
            "source": self.source,
            "repetitions": self.repetitions,
            "maximum_repetitions": self.maximum_repetitions,
            "physical_ticks": self.physical_ticks,
            "normalized_symbols": self.normalized_symbols,
            "odd_symbols": self.odd_symbols,
            "endpoint": self.endpoint,
            "completed_final_division": True,
            "source_cylinder_bits": self.fields.steps,
            "scope": "authenticated physical boundary prefix, not a global action ID",
        }

    def structural_payload(self) -> tuple[BorderWireValue, ...]:
        """Return the immutable, authority-free shape used by image ports."""
        fields = self.fields
        return (
            COLLATZ_BOUNDARY_MACRO_ACTION_TAG,
            self.identity.structural_key(),
            self.source,
            self.repetitions,
            self.maximum_repetitions,
            self.physical_ticks,
            self.odd_symbols,
            self.endpoint,
            fields.steps,
            fields.gain,
            fields.offset,
            fields.sum_gain,
            fields.sum_offset,
            fields.previous_gain,
            fields.previous_offset,
            *self.width_blank.as_tuple(),
        )


def boundary_macro_plan(
    source: int,
    available_physical_ticks: int,
    *,
    minimum_repetitions: int = 2,
) -> tuple[BoundaryActionIdentity, int, int] | None:
    """Choose an exact guard and extent before allocating powered coefficients."""
    plan = admit_boundary_macro_plan(
        source,
        available_physical_ticks,
        minimum_repetitions=minimum_repetitions,
    )
    if plan is None:
        return None
    return plan.identity, plan.maximum_repetitions, plan.repetitions


@dataclass(frozen=True, slots=True, init=False)
class AdmittedBoundaryMacroPlan:
    """Sealed source-and-clock-bound result of the cheap macro admission."""

    source: int
    available_physical_ticks: int
    minimum_repetitions: int
    identity: BoundaryActionIdentity
    maximum_repetitions: int
    repetitions: int
    _issuer: object = field(repr=False, compare=False, init=False)
    _issued_values: tuple[int, int, int, BoundaryActionIdentity, int, int] = field(
        repr=False, compare=False, init=False
    )

    def issuance_matches(self) -> bool:
        """Check the retained issuance snapshot without exposing its mutable slot."""
        return self._issued_values == (
            self.source,
            self.available_physical_ticks,
            self.minimum_repetitions,
            self.identity,
            self.maximum_repetitions,
            self.repetitions,
        )

    @property
    def normalized_symbols(self) -> int:
        if self.identity in (ENTRY_421, ENTRY_4721, ENTRY_0563):
            return 2 * self.repetitions + 1
        phase = boundary_macro_26847_phase(self.identity)
        if phase is not None:
            return 4 * self.repetitions + 1 - phase
        if self.identity == PATH_630:
            return self.repetitions + 2
        if self.identity == PATH_305:
            return self.repetitions + 1
        if self.identity == ENTRY_89_AT_NINE:
            return self.repetitions
        raise ValueError("boundary plan has an unknown family")

    @property
    def physical_ticks(self) -> int:
        if self.identity == ENTRY_421:
            return 3 * self.repetitions + 1
        if self.identity == ENTRY_4721:
            return 4 * self.repetitions + 1
        if self.identity == ENTRY_0563:
            return 4 * self.repetitions + 1
        phase = boundary_macro_26847_phase(self.identity)
        if phase is not None:
            return 5 * self.repetitions + 1 - phase
        if self.identity == PATH_630:
            return self.repetitions + 3
        if self.identity == PATH_305:
            return self.repetitions + 2
        if self.identity == ENTRY_89_AT_NINE:
            return 2 * self.repetitions
        raise ValueError("boundary plan has an unknown family")


def _issue_boundary_macro(
    identity: BoundaryActionIdentity,
    source: int,
    repetitions: int,
    maximum_repetitions: int,
    physical_ticks: int,
    odd_symbols: int,
    endpoint: int,
    fields: DyadicTerminalFieldAction,
    width_blank: BlankLedger,
) -> CollatzBoundaryMacro:
    macro = object.__new__(CollatzBoundaryMacro)
    for name, value in (
        ("identity", identity),
        ("source", source),
        ("repetitions", repetitions),
        ("maximum_repetitions", maximum_repetitions),
        ("physical_ticks", physical_ticks),
        ("odd_symbols", odd_symbols),
        ("endpoint", endpoint),
        ("fields", fields),
        ("width_blank", width_blank),
        ("_issuer", _BOUNDARY_MACRO_ISSUER),
    ):
        object.__setattr__(macro, name, value)
    return macro


def _issue_boundary_plan(
    source: int,
    available_physical_ticks: int,
    minimum_repetitions: int,
    identity: BoundaryActionIdentity,
    maximum_repetitions: int,
    repetitions: int,
) -> AdmittedBoundaryMacroPlan:
    plan = object.__new__(AdmittedBoundaryMacroPlan)
    values = (
        ("source", source),
        ("available_physical_ticks", available_physical_ticks),
        ("minimum_repetitions", minimum_repetitions),
        ("identity", identity),
        ("maximum_repetitions", maximum_repetitions),
        ("repetitions", repetitions),
        ("_issuer", _BOUNDARY_PLAN_ISSUER),
    )
    for name, value in values:
        object.__setattr__(plan, name, value)
    object.__setattr__(
        plan,
        "_issued_values",
        (
            source,
            available_physical_ticks,
            minimum_repetitions,
            identity,
            maximum_repetitions,
            repetitions,
        ),
    )
    return plan


_BOUNDARY_PLAN_ISSUER = object()


def admit_boundary_macro_plan(
    source: int,
    available_physical_ticks: int,
    *,
    minimum_repetitions: int = 2,
    radix_state: JointRadix6Source | None = None,
    ledger: ResourceLedger | None = None,
) -> AdmittedBoundaryMacroPlan | None:
    """Issue a source-bound guard token for one later coefficient build."""
    if type(source) is not int or source <= 0:
        raise ValueError("Collatz boundary requires a positive integer source")
    if type(available_physical_ticks) is not int or available_physical_ticks < 0:
        raise ValueError("Collatz boundary requires nonnegative physical ticks")
    if type(minimum_repetitions) is not int or minimum_repetitions < 1:
        raise ValueError("minimum boundary repetitions must be positive")
    state = (
        radix_state
        if radix_state is not None
        else JointRadix6Source.from_source(source)
    )
    if type(state) is not JointRadix6Source:
        raise TypeError("boundary selector needs an exact radix-6 source state")
    state.require_source(source)
    if ledger is not None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("boundary candidate metrics require a query ledger")
        ledger.bump(_collatz_keys.COLLATZ_RADIX6_SOURCE_CANDIDATE_CHECKS)
    family = state.candidate_family
    identity: BoundaryActionIdentity
    if family == ENTRY_421 and source > 4:
        identity = ENTRY_421
    elif family == ENTRY_4721:
        identity = ENTRY_4721
    elif family == ENTRY_0563:
        identity = ENTRY_0563
    elif family is not None and family in ENTRY_26847_PHASES:
        identity = family
    elif family == PATH_630:
        identity = PATH_630
    elif family == PATH_305:
        identity = PATH_305
    elif family == ENTRY_89_AT_NINE:
        identity = ENTRY_89_AT_NINE
    else:
        return None

    if identity == ENTRY_421:
        maximum = (state.demand_v2_affine(1, -4) - 1) // 2
        repetitions = min(maximum, (available_physical_ticks - 1) // 3)
    elif identity in (ENTRY_4721, ENTRY_0563):
        maximum = (state.demand_v2_affine(1, 2) - 1) // 2
        repetitions = min(maximum, (available_physical_ticks - 1) // 4)
    elif (boundary_phase := boundary_macro_26847_phase(identity)) is not None:
        valuation = state.demand_v2_affine(13, -(1 << (4 - boundary_phase)))
        maximum = (boundary_phase + valuation - 1) // 4
        repetitions = min(maximum, (available_physical_ticks + boundary_phase - 1) // 5)
    elif identity == PATH_630:
        maximum = v2_positive(3 * ((source - 6) // 20) + 1)
        repetitions = min(maximum, available_physical_ticks - 3)
    elif identity == PATH_305:
        maximum = v2_positive(3 * ((source - 3) // 10) + 1)
        repetitions = min(maximum, available_physical_ticks - 2)
    elif identity == ENTRY_89_AT_NINE:
        maximum = int(state.demand_v2_affine(1, 1))
        repetitions = min(maximum, available_physical_ticks // 2)
    else:
        return None
    if repetitions < minimum_repetitions:
        return None
    return _issue_boundary_plan(
        source,
        available_physical_ticks,
        minimum_repetitions,
        identity,
        maximum,
        repetitions,
    )


def admit_routed_boundary_macro_plan(
    source: int, available_physical_ticks: int
) -> AdmittedBoundaryMacroPlan | None:
    """Admit powered edge macros, or a one-return action filling the query."""
    plan = admit_boundary_macro_plan(
        source,
        available_physical_ticks,
        minimum_repetitions=1,
    )
    if plan is None:
        return plan
    if plan.repetitions >= 2:
        return _issue_boundary_plan(
            plan.source,
            plan.available_physical_ticks,
            2,
            plan.identity,
            plan.maximum_repetitions,
            plan.repetitions,
        )
    # A one-return edge action is useful when it answers the whole remaining
    # query. Inserting it into a long itinerary can preempt a better powered
    # mixed/D8 action and increase real scheduler work.
    is_new_edge_family = plan.identity == ENTRY_0563 or (
        boundary_macro_26847_phase(plan.identity) is not None
    )
    if is_new_edge_family and plan.physical_ticks == available_physical_ticks:
        return plan
    return None


def _build_boundary_action_template(
    identity: BoundaryTemplateIdentity, repetitions: int
) -> tuple[DyadicTerminalFieldAction, int, int, int]:
    """Intern the *full parity action*, including accumulator coefficients.

    Unlike an innovation Moore observer ID, this key represents an exact
    certified affine program, not just equal carry/borrow outputs. The caller
    must still independently authenticate the source's guard and exit.
    """
    if type(repetitions) is not int or repetitions < 1:
        raise ValueError("guarded boundary action needs a positive repeat count")
    if isinstance(identity, MixedParityMotif):
        fields = DyadicTerminalFieldAction.zero_run(0)
        for bit in identity.bits:
            fields = fields.then(
                DyadicTerminalFieldAction.one_run(1)
                if bit
                else DyadicTerminalFieldAction.zero_run(1)
            )
        fields = fields.power(repetitions)
        odd = sum(identity.bits) * repetitions
        ticks = fields.steps + odd
    elif identity == ENTRY_421:
        motif = DyadicTerminalFieldAction.one_run(1).then(
            DyadicTerminalFieldAction.zero_run(1)
        )
        fields = (
            DyadicTerminalFieldAction.zero_run(2)
            .then(motif.power(repetitions - 1))
            .then(DyadicTerminalFieldAction.one_run(1))
        )
        odd = repetitions
        ticks = 3 * repetitions + 1
    elif identity in (ENTRY_4721, ENTRY_0563):
        fields = DyadicTerminalFieldAction.zero_run(1).then(
            DyadicTerminalFieldAction.one_run(2 * repetitions)
        )
        odd = 2 * repetitions
        ticks = 4 * repetitions + 1
    elif (phase := boundary_macro_26847_phase(identity)) is not None:
        fields = DyadicTerminalFieldAction.zero_run(4 - phase)
        if repetitions > 1:
            motif = DyadicTerminalFieldAction.one_run(1).then(
                DyadicTerminalFieldAction.zero_run(3)
            )
            fields = fields.then(motif.power(repetitions - 1))
        fields = fields.then(DyadicTerminalFieldAction.one_run(1))
        odd = repetitions
        ticks = 5 * repetitions + 1 - phase
    elif identity == PATH_630:
        fields = (
            DyadicTerminalFieldAction.zero_run(1)
            .then(DyadicTerminalFieldAction.one_run(1))
            .then(DyadicTerminalFieldAction.zero_run(repetitions))
        )
        odd = 1
        ticks = repetitions + 3
    elif identity == PATH_305:
        fields = DyadicTerminalFieldAction.one_run(1).then(
            DyadicTerminalFieldAction.zero_run(repetitions)
        )
        odd = 1
        ticks = repetitions + 2
    elif identity == ENTRY_89_AT_NINE:
        fields = DyadicTerminalFieldAction.one_run(repetitions)
        odd = repetitions
        ticks = 2 * repetitions
    else:
        raise ValueError("unknown source-certified boundary action")
    if fields.steps + odd != ticks:
        raise AssertionError("guarded template lost its physical tick clock")
    return fields, odd, ticks, fields.source_residue


def _boundary_width_blank(
    identity: BoundaryActionIdentity, source: int, endpoint: int
) -> BlankLedger:
    """Derive the exact physical width extrema from a completed macro."""
    if identity == ENTRY_421:
        raw_last = 2 * endpoint
        last_source, remainder = divmod(4 * raw_last - 4, 3)
        if remainder or last_source % 4:
            raise AssertionError("quiet boundary predecessor is not integral")
        lowest_width = (last_source // 4).bit_length()
        highest_width = source.bit_length()
    elif identity in (ENTRY_4721, ENTRY_0563):
        raw_last = 2 * endpoint
        last_source, remainder = divmod(4 * raw_last - 10, 9)
        if remainder or last_source % 2:
            raise AssertionError("growth boundary predecessor is not integral")
        lowest_width = (source // 2).bit_length()
        highest_width = max(source.bit_length(), raw_last.bit_length())
    elif (phase := boundary_macro_26847_phase(identity)) is not None:
        last_odd, remainder = divmod(2 * endpoint - 1, 3)
        initial_odd = source >> (4 - phase)
        if remainder or initial_odd <= 0:
            raise AssertionError("26847 final odd boundary is invalid")
        lowest_width = last_odd.bit_length()
        highest_width = max(
            source.bit_length(),
            (3 * initial_odd + 1).bit_length(),
            (2 * endpoint).bit_length(),
        )
    elif identity == PATH_630:
        lowest_width = min(source // 2, endpoint).bit_length()
        highest_width = max((3 * (source // 2) + 1).bit_length(), source.bit_length())
    elif identity == PATH_305:
        lowest_width = endpoint.bit_length()
        highest_width = max((3 * source + 1).bit_length(), source.bit_length())
    elif identity == ENTRY_89_AT_NINE:
        lowest_width = source.bit_length()
        highest_width = (2 * endpoint).bit_length()
    else:
        raise ValueError("unknown source-certified boundary action")
    width = source.bit_length()
    return BlankLedger(
        endpoint.bit_length() - width, lowest_width - width, highest_width - width
    )


def validate_boundary_macro(macro: CollatzBoundaryMacro) -> None:
    """Check an issued boundary action without rebuilding its coefficients."""
    if type(macro) is not CollatzBoundaryMacro:
        raise TypeError("expected an issued Collatz boundary macro")
    if getattr(macro, "_issuer", None) is not _BOUNDARY_MACRO_ISSUER:
        raise ValueError("Collatz boundary macro has no producer authority")
    if (
        macro.identity not in _BOUNDARY_PLAN_IDENTITIES
        or type(macro.source) is not int
        or macro.source <= 0
        or type(macro.repetitions) is not int
        or macro.repetitions <= 0
        or type(macro.maximum_repetitions) is not int
        or macro.maximum_repetitions < macro.repetitions
        or type(macro.physical_ticks) is not int
        or type(macro.odd_symbols) is not int
        or type(macro.endpoint) is not int
        or type(macro.fields) is not DyadicTerminalFieldAction
        or not macro.fields.producer_issued
        or type(macro.width_blank) is not BlankLedger
    ):
        raise ValueError("Collatz boundary macro fields are malformed")
    source = macro.source
    if macro.identity == ENTRY_421:
        if source <= 4 or source % 40 != 4:
            raise ValueError("quiet boundary macro has the wrong source guard")
        maximum = (v2_positive(source - 4) - 1) // 2
        normalized, odd, ticks = (
            2 * macro.repetitions + 1,
            macro.repetitions,
            3 * macro.repetitions + 1,
        )
    elif macro.identity == ENTRY_4721:
        if source % 40 != 14:
            raise ValueError("growth boundary macro has the wrong source guard")
        maximum = (v2_positive(source + 2) - 1) // 2
        normalized, odd, ticks = (
            2 * macro.repetitions + 1,
            2 * macro.repetitions,
            4 * macro.repetitions + 1,
        )
    elif macro.identity == ENTRY_0563:
        if source % 40 != 30:
            raise ValueError("0563 boundary macro has the wrong source guard")
        maximum = (v2_positive(source + 2) - 1) // 2
        normalized, odd, ticks = (
            2 * macro.repetitions + 1,
            2 * macro.repetitions,
            4 * macro.repetitions + 1,
        )
    elif (phase := boundary_macro_26847_phase(macro.identity)) is not None:
        guard_modulus = 160 >> phase
        guard_residue = 112 >> phase
        if source % guard_modulus != guard_residue:
            raise ValueError("26847 boundary macro has the wrong phase guard")
        maximum = (phase + v2_positive(13 * source - (1 << (4 - phase))) - 1) // 4
        normalized, odd, ticks = (
            4 * macro.repetitions + 1 - phase,
            macro.repetitions,
            5 * macro.repetitions + 1 - phase,
        )
    elif macro.identity == PATH_630:
        if source % 20 != 6:
            raise ValueError("630 boundary macro has the wrong source guard")
        maximum = v2_positive(3 * ((source - 6) // 20) + 1)
        normalized, odd, ticks = macro.repetitions + 2, 1, macro.repetitions + 3
    elif macro.identity == PATH_305:
        if source % 10 != 3:
            raise ValueError("305 boundary macro has the wrong source guard")
        maximum = v2_positive(3 * ((source - 3) // 10) + 1)
        normalized, odd, ticks = macro.repetitions + 1, 1, macro.repetitions + 2
    else:
        if source % 10 != 9:
            raise ValueError("989 boundary macro has the wrong source guard")
        maximum = v2_positive(source + 1)
        normalized, odd, ticks = (
            macro.repetitions,
            macro.repetitions,
            2 * macro.repetitions,
        )
    denominator = 1 << macro.fields.steps
    endpoint, remainder = divmod(
        macro.fields.gain * source + macro.fields.offset, denominator
    )
    if (
        macro.maximum_repetitions != maximum
        or macro.repetitions > maximum
        or macro.fields.steps != normalized
        or macro.odd_symbols != odd
        or macro.physical_ticks != ticks
        or macro.fields.steps + odd != ticks
        or not macro.fields.certifies(source)
        or remainder != 0
        or endpoint <= 0
        or macro.endpoint != endpoint
        or macro.width_blank != _boundary_width_blank(macro.identity, source, endpoint)
    ):
        raise ValueError("Collatz boundary macro is not an exact guarded action")


_BOUNDARY_MACRO_ISSUER = object()


class BoundaryActionTemplateMemo:
    """Per-query, ledger-accounted templates for exact guarded parity actions."""

    def __init__(self, ledger: ResourceLedger) -> None:
        if type(ledger) is not ResourceLedger:
            raise TypeError("boundary action templates require their query ledger")
        self.ledger = ledger
        self._closed = False
        self._closing = False
        self._scratch_owner: int | None = None
        self._templates: (
            OwnedMemo[
                tuple[BoundaryTemplateIdentity, int],
                tuple[
                    BoundaryTemplateIdentity,
                    int,
                    tuple[DyadicTerminalFieldAction, int, int, int],
                ],
            ]
            | None
        ) = None

    def __enter__(self) -> Self:
        if self._closed or self._closing:
            raise RuntimeError("boundary action template memo is closed")
        return self

    def __exit__(self, *_args: object) -> None:
        self.dispose()

    def dispose(self) -> None:
        """Release the memo; retain a retry path if ledger cleanup fails."""
        if self._closed:
            return
        self._closing = True
        if self._templates is not None:
            self._templates.dispose()
        if self._scratch_owner is not None:
            self.ledger.mark_disposed(self._scratch_owner)
        self._closing = False
        self._closed = True

    def scratch(self, *, nodes: int) -> AbstractContextManager[None]:
        """Reserve bounded selector/construction temporaries on the query ledger."""
        if self._closed or self._closing:
            raise RuntimeError("boundary action template memo is closed")
        if self._scratch_owner is None:
            self._scratch_owner = self.ledger.register(
                f"collatz-boundary-template-scratch-{self.ledger.owner_count}",
                "temporary",
            )
        return self.ledger.reservation(self._scratch_owner, nodes=nodes)

    def _memo(
        self,
    ) -> OwnedMemo[
        tuple[BoundaryTemplateIdentity, int],
        tuple[
            BoundaryTemplateIdentity,
            int,
            tuple[DyadicTerminalFieldAction, int, int, int],
        ],
    ]:
        if self._templates is None:
            with RuntimeConstruction(self.ledger):
                owner = self.ledger.register(
                    f"collatz-boundary-action-templates-{self.ledger.owner_count}",
                    "query_memo",
                )

                def template_cost(
                    _key: tuple[BoundaryTemplateIdentity, int],
                    value: tuple[
                        BoundaryTemplateIdentity,
                        int,
                        tuple[DyadicTerminalFieldAction, int, int, int],
                    ],
                ) -> int:
                    template = value[2]
                    fields = template[0]
                    return (
                        8
                        + (
                            2 + len(value[0].bits)
                            if isinstance(value[0], MixedParityMotif)
                            else len(value[0].cycle.digits)
                            if isinstance(value[0], CycleEntryPhase)
                            else 1
                        )
                        + sum(
                            (max(1, component.bit_length()) + 63) // 64
                            for component in (
                                fields.steps,
                                fields.gain,
                                fields.offset,
                                fields.sum_gain,
                                fields.sum_offset,
                                fields.previous_gain,
                                fields.previous_offset,
                                template[1],
                                template[2],
                                template[3],
                            )
                        )
                    )

                templates = OwnedMemo(
                    self.ledger,
                    owner,
                    node_cost=template_cost,
                    evictable=True,
                )
                self.ledger.register_execution_root(self)
                for counter in (
                    "lookups",
                    "hits",
                    "misses",
                    "publications",
                    "bypasses",
                ):
                    self.ledger.bump(f"collatz_boundary_template_{counter}", 0)
            self._templates = templates
        return self._templates

    def get(
        self, identity: BoundaryTemplateIdentity, repetitions: int
    ) -> tuple[DyadicTerminalFieldAction, int, int, int]:
        if self._closed or self._closing:
            raise RuntimeError("boundary action template memo is closed")
        if (
            type(identity) not in (CycleEntryPhase, GuardedBorderPath, MixedParityMotif)
            or type(repetitions) is not int
        ):
            raise TypeError("boundary action template key is malformed")
        if isinstance(identity, MixedParityMotif):
            identity.require_valid()
        if isinstance(identity, (CycleEntryPhase, GuardedBorderPath)) and (
            identity not in _BOUNDARY_PLAN_IDENTITIES
        ):
            raise ValueError("unknown Collatz boundary action identity")
        if repetitions < 1:
            raise ValueError("boundary action repeat count must be positive")
        key = identity, repetitions
        self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_LOOKUPS)
        memo = self._memo()
        cached = memo.get(key)
        if cached is not None:
            if (
                type(cached) is not tuple
                or len(cached) != 3
                or cached[0] != identity
                or cached[1] != repetitions
                or type(cached[2]) is not tuple
                or len(cached[2]) != 4
                or type(cached[2][0]) is not DyadicTerminalFieldAction
                or not cached[2][0].producer_issued
                or any(type(value) is not int for value in cached[2][1:])
            ):
                raise ValueError("cached boundary action template is malformed")
            template = cached[2]
            fields, odd, ticks, guard = template
            self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_VALIDATIONS)
            self.ledger.bump(
                _collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_VALIDATION_OPERAND_BITS,
                fields.gain.bit_length()
                + fields.offset.bit_length()
                + guard.bit_length(),
            )
            if (
                fields.steps <= 0
                or fields.steps + odd != ticks
                or not 0 <= guard < fields.source_modulus
                or (fields.gain * guard + fields.offset) % fields.source_modulus != 0
            ):
                raise ValueError("cached boundary action template is inconsistent")
            self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_HITS)
            return template
        self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_MISSES)
        if isinstance(identity, MixedParityMotif):
            width = len(identity.bits) * repetitions
            with self.scratch(nodes=128 + 32 * ((2 * width + 63) // 64)):
                self.ledger.bump(
                    _collatz_keys.COLLATZ_MIXED_CLOCK_COEFFICIENT_CONSTRUCTIONS
                )
                self.ledger.bump(
                    _collatz_keys.COLLATZ_MIXED_CLOCK_REQUESTED_GUARD_BITS, width
                )
                template = _build_boundary_action_template(identity, repetitions)
        else:
            template = _build_boundary_action_template(identity, repetitions)
        bound_template = identity, repetitions, template
        try:
            memo[key] = bound_template
        except BlockContextBudgetExceeded:
            self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_BYPASSES)
        else:
            self.ledger.bump(_collatz_keys.COLLATZ_BOUNDARY_TEMPLATE_PUBLICATIONS)
        return template


def select_boundary_macro(
    source: int,
    available_physical_ticks: int,
    *,
    minimum_repetitions: int = 2,
    templates: BoundaryActionTemplateMemo | None = None,
) -> CollatzBoundaryMacro | None:
    """Select a *completed* macro prefix without enumerating Collatz terms.

    A quiet period begins at x = 4 (mod 40), x > 4, under
    Q(x) = (3*x+4)/4, Q(x)-4=(3/4)*(x-4).
    A growth period begins at x = 14 (mod 40), under
    G(x) = (9*x+10)/4, G(x)+2=(9/4)*(x+2).
    In both cases each complete return consumes two guard bits. The
    additional physical even step closes the pending odd half-step.
    """
    plan = admit_boundary_macro_plan(
        source,
        available_physical_ticks,
        minimum_repetitions=minimum_repetitions,
    )
    if plan is None:
        return None
    return select_admitted_boundary_macro(plan, templates=templates)


def select_admitted_boundary_macro(
    plan: AdmittedBoundaryMacroPlan,
    *,
    templates: BoundaryActionTemplateMemo | None = None,
) -> CollatzBoundaryMacro:
    """Build the exact action once from an issued, validated source plan."""
    validate_admitted_boundary_macro_plan(plan)
    identity = plan.identity
    maximum = plan.maximum_repetitions
    repetitions = plan.repetitions
    if templates is not None and type(templates) is not BoundaryActionTemplateMemo:
        raise TypeError("boundary macro requires its ledger-owned template memo")
    fields, odd, ticks, guard = (
        templates.get(identity, repetitions)
        if templates is not None
        else _build_boundary_action_template(identity, repetitions)
    )
    # Recheck the exact source cylinder without reconstructing the action.
    denominator = 1 << fields.steps
    source = plan.source
    if source % denominator != guard or fields.steps + odd != ticks:
        raise AssertionError("guarded Collatz boundary word lost its source cylinder")
    if ticks > plan.available_physical_ticks:
        raise AssertionError("guarded Collatz boundary exceeds its admitted clock")
    endpoint, remainder = divmod(fields.gain * source + fields.offset, denominator)
    if remainder or endpoint <= 0:
        raise AssertionError("guarded Collatz endpoint is not exact")
    blank = _boundary_width_blank(identity, source, endpoint)
    return _issue_boundary_macro(
        identity,
        source,
        repetitions,
        maximum,
        ticks,
        odd,
        endpoint,
        fields,
        blank,
    )


def validate_admitted_boundary_macro_plan(plan: AdmittedBoundaryMacroPlan) -> None:
    """Check plan issuance and shape without reserving arithmetic resources."""
    if (
        type(plan) is not AdmittedBoundaryMacroPlan
        or getattr(plan, "_issuer", None) is not _BOUNDARY_PLAN_ISSUER
        or type(plan.source) is not int
        or type(plan.available_physical_ticks) is not int
        or type(plan.minimum_repetitions) is not int
        or type(plan.identity) not in (CycleEntryPhase, GuardedBorderPath)
        or type(plan.maximum_repetitions) is not int
        or type(plan.repetitions) is not int
        or not plan.issuance_matches()
    ):
        raise ValueError("boundary macro plan has no valid admission authority")
    maximum = plan.maximum_repetitions
    repetitions = plan.repetitions
    if (
        plan.identity not in _BOUNDARY_PLAN_IDENTITIES
        or maximum < repetitions
        or repetitions < plan.minimum_repetitions
    ):
        raise ValueError("boundary macro plan has inconsistent extent")


__all__ = [
    "AdmittedBoundaryMacroPlan",
    "BoundaryActionTemplateMemo",
    "CollatzBoundaryMacro",
    "admit_boundary_macro_plan",
    "admit_routed_boundary_macro_plan",
    "boundary_macro_26847_phase",
    "boundary_macro_plan",
    "boundary_metric_suffix",
    "boundary_metric_key",
    "select_admitted_boundary_macro",
    "select_boundary_macro",
    "validate_admitted_boundary_macro_plan",
    "validate_boundary_macro",
]
