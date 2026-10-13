"""Source-guarded Collatz 421/4721 boundary actions and innovation-borrow clocks.

These are *physical* trailing-decimal return words. They are not global
Hashlife IDs: entry and repetition length are authenticated by the exact
source and its 2-adic valuation. The action completes the final odd division,
so it consumes 3*r+1 or 4*r+1 physical ticks and has phase zero.

Borrow clocks sample a stated subset of *normalized* second-innovation
subtraction branches. They never authorize a successor or an endpoint.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import TYPE_CHECKING, Self

from number_compiler.arithmetic.contracts.block_effect import (
    BlockContextBudgetExceeded,
)
from number_compiler.arithmetic.fields.blank_ledger import BlankLedger
from number_compiler.arithmetic.fields.two_adic import v2_positive
from number_compiler.resources.ledger import OwnedMemo, ResourceLedger
from number_compiler.sequences.collatz.dyadic_terminal_cocycle import (
    DyadicTerminalFieldAction,
)

if TYPE_CHECKING:
    from number_compiler.sequences.collatz.temporal_run_quotient import (
        CollatzF5AffineAction,
    )


@dataclass(frozen=True, slots=True, init=False)
class CollatzBoundaryMacro:
    family: str
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

    @classmethod
    def _issue(
        cls,
        family: str,
        source: int,
        repetitions: int,
        maximum_repetitions: int,
        physical_ticks: int,
        odd_symbols: int,
        endpoint: int,
        fields: DyadicTerminalFieldAction,
        width_blank: BlankLedger,
    ) -> CollatzBoundaryMacro:
        macro = object.__new__(cls)
        for name, value in (
            ("family", family),
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

    @property
    def normalized_symbols(self) -> int:
        return self.fields.steps

    @property
    def quiet(self) -> bool:
        return self.family == "421"

    def f5_action(self) -> CollatzF5AffineAction:
        """Project the authenticated integer endpoint action onto F5."""
        from number_compiler.sequences.collatz.temporal_f5_observer import (
            CollatzF5AffineAction,
        )

        inverse_denominator = pow(2, -self.fields.steps, 5)
        return CollatzF5AffineAction(
            self.fields.gain * inverse_denominator % 5,
            self.fields.offset * inverse_denominator % 5,
        )

    def observation(self) -> dict[str, int | str | bool]:
        return {
            "family_word": self.family,
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

    def structural_payload(self) -> tuple[object, ...]:
        """Return the immutable, authority-free shape used by image ports."""
        fields = self.fields
        return (
            "collatz-boundary-macro-v1",
            self.family,
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
) -> tuple[str, int, int] | None:
    """Choose an exact guard and extent before allocating powered coefficients."""
    plan = admit_boundary_macro_plan(
        source,
        available_physical_ticks,
        minimum_repetitions=minimum_repetitions,
    )
    if plan is None:
        return None
    return plan.family, plan.maximum_repetitions, plan.repetitions


@dataclass(frozen=True, slots=True, init=False)
class AdmittedBoundaryMacroPlan:
    """Sealed source-and-clock-bound result of the cheap macro admission."""

    source: int
    available_physical_ticks: int
    minimum_repetitions: int
    family: str
    maximum_repetitions: int
    repetitions: int
    _issuer: object = field(repr=False, compare=False, init=False)
    _issued_values: tuple[object, ...] = field(repr=False, compare=False, init=False)

    @classmethod
    def _issue(
        cls,
        source: int,
        available_physical_ticks: int,
        minimum_repetitions: int,
        family: str,
        maximum_repetitions: int,
        repetitions: int,
    ) -> AdmittedBoundaryMacroPlan:
        plan = object.__new__(cls)
        values = (
            ("source", source),
            ("available_physical_ticks", available_physical_ticks),
            ("minimum_repetitions", minimum_repetitions),
            ("family", family),
            ("maximum_repetitions", maximum_repetitions),
            ("repetitions", repetitions),
            ("_issuer", _BOUNDARY_PLAN_ISSUER),
        )
        for name, value in values:
            object.__setattr__(plan, name, value)
        object.__setattr__(
            plan, "_issued_values", tuple(value for _, value in values[:-1])
        )
        return plan


_BOUNDARY_PLAN_ISSUER = object()


def admit_boundary_macro_plan(
    source: int,
    available_physical_ticks: int,
    *,
    minimum_repetitions: int = 2,
) -> AdmittedBoundaryMacroPlan | None:
    """Issue a source-bound guard token for one later coefficient build."""
    if type(source) is not int or source <= 0:
        raise ValueError("Collatz boundary requires a positive integer source")
    if type(available_physical_ticks) is not int or available_physical_ticks < 0:
        raise ValueError("Collatz boundary requires nonnegative physical ticks")
    if type(minimum_repetitions) is not int or minimum_repetitions < 1:
        raise ValueError("minimum boundary repetitions must be positive")
    if source > 4 and source % 40 == 4:
        family, valuation, period = "421", v2_positive(source - 4), 3
    elif source % 40 == 14:
        family, valuation, period = "4721", v2_positive(source + 2), 4
    elif source % 20 == 6:
        family, period = "630", 1
        maximum = v2_positive(3 * ((source - 6) // 20) + 1)
    elif source % 10 == 9:
        family, period = "989", 2
        maximum = v2_positive(source + 1)
    else:
        return None
    if family in ("421", "4721"):
        maximum = (valuation - 1) // 2
        repetitions = min(maximum, (available_physical_ticks - 1) // period)
    elif family == "630":
        repetitions = min(maximum, available_physical_ticks - 3)
    else:
        repetitions = min(maximum, available_physical_ticks // 2)
    if repetitions < minimum_repetitions:
        return None
    return AdmittedBoundaryMacroPlan._issue(
        source,
        available_physical_ticks,
        minimum_repetitions,
        family,
        maximum,
        repetitions,
    )


def _build_boundary_action_template(
    family: str, repetitions: int
) -> tuple[DyadicTerminalFieldAction, int, int, int]:
    """Intern the *full parity action*, including accumulator coefficients.

    Unlike an innovation Moore observer ID, this key represents an exact
    certified affine program, not just equal carry/borrow outputs. The caller
    must still independently authenticate the source's guard and exit.
    """
    if type(repetitions) is not int or repetitions < 1:
        raise ValueError("guarded boundary action needs a positive repeat count")
    if family == "421":
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
    elif family == "4721":
        fields = DyadicTerminalFieldAction.zero_run(1).then(
            DyadicTerminalFieldAction.one_run(2 * repetitions)
        )
        odd = 2 * repetitions
        ticks = 4 * repetitions + 1
    elif family == "630":
        fields = (
            DyadicTerminalFieldAction.zero_run(1)
            .then(DyadicTerminalFieldAction.one_run(1))
            .then(DyadicTerminalFieldAction.zero_run(repetitions))
        )
        odd = 1
        ticks = repetitions + 3
    elif family == "989":
        fields = DyadicTerminalFieldAction.one_run(repetitions)
        odd = repetitions
        ticks = 2 * repetitions
    else:
        raise ValueError("unknown source-certified boundary action")
    if fields.steps + odd != ticks:
        raise AssertionError("guarded template lost its physical tick clock")
    return fields, odd, ticks, fields.source_residue


def _boundary_width_blank(family: str, source: int, endpoint: int) -> BlankLedger:
    """Derive the exact physical width extrema from a completed macro."""
    if family == "421":
        raw_last = 2 * endpoint
        last_source, remainder = divmod(4 * raw_last - 4, 3)
        if remainder or last_source % 4:
            raise AssertionError("quiet boundary predecessor is not integral")
        lowest_width = (last_source // 4).bit_length()
        highest_width = source.bit_length()
    elif family == "4721":
        raw_last = 2 * endpoint
        last_source, remainder = divmod(4 * raw_last - 10, 9)
        if remainder or last_source % 2:
            raise AssertionError("growth boundary predecessor is not integral")
        lowest_width = (source // 2).bit_length()
        highest_width = max(source.bit_length(), raw_last.bit_length())
    elif family == "630":
        lowest_width = min(source // 2, endpoint).bit_length()
        highest_width = max((3 * (source // 2) + 1).bit_length(), source.bit_length())
    elif family == "989":
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
        macro.family not in ("421", "4721", "630", "989")
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
    if macro.family == "421":
        if source <= 4 or source % 40 != 4:
            raise ValueError("quiet boundary macro has the wrong source guard")
        maximum = (v2_positive(source - 4) - 1) // 2
        normalized, odd, ticks = (
            2 * macro.repetitions + 1,
            macro.repetitions,
            3 * macro.repetitions + 1,
        )
    elif macro.family == "4721":
        if source % 40 != 14:
            raise ValueError("growth boundary macro has the wrong source guard")
        maximum = (v2_positive(source + 2) - 1) // 2
        normalized, odd, ticks = (
            2 * macro.repetitions + 1,
            2 * macro.repetitions,
            4 * macro.repetitions + 1,
        )
    elif macro.family == "630":
        if source % 20 != 6:
            raise ValueError("630 boundary macro has the wrong source guard")
        maximum = v2_positive(3 * ((source - 6) // 20) + 1)
        normalized, odd, ticks = macro.repetitions + 2, 1, macro.repetitions + 3
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
        or macro.width_blank != _boundary_width_blank(macro.family, source, endpoint)
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
        self._templates: (
            OwnedMemo[
                tuple[str, int],
                tuple[
                    str,
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
        self._closing = False
        self._closed = True

    def _memo(
        self,
    ) -> OwnedMemo[
        tuple[str, int],
        tuple[str, int, tuple[DyadicTerminalFieldAction, int, int, int]],
    ]:
        if self._templates is None:
            owner = self.ledger.register(
                f"collatz-boundary-action-templates-{self.ledger.owner_count}",
                "query_memo",
            )

            def template_cost(
                _key: tuple[str, int],
                value: tuple[
                    str,
                    int,
                    tuple[DyadicTerminalFieldAction, int, int, int],
                ],
            ) -> int:
                template = value[2]
                fields = template[0]
                return 8 + sum(
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

            self._templates = OwnedMemo(
                self.ledger,
                owner,
                node_cost=template_cost,
                evictable=True,
            )
            self.ledger.register_execution_root(self)
            for counter in ("lookups", "hits", "misses", "publications", "bypasses"):
                self.ledger.bump(f"collatz_boundary_template_{counter}", 0)
        return self._templates

    def get(
        self, family: str, repetitions: int
    ) -> tuple[DyadicTerminalFieldAction, int, int, int]:
        if self._closed or self._closing:
            raise RuntimeError("boundary action template memo is closed")
        if type(family) is not str or type(repetitions) is not int:
            raise TypeError("boundary action template key is malformed")
        key = family, repetitions
        self.ledger.bump("collatz_boundary_template_lookups")
        memo = self._memo()
        cached = memo.get(key)
        if cached is not None:
            self.ledger.bump("collatz_boundary_template_hits")
            if (
                type(cached) is not tuple
                or len(cached) != 3
                or cached[0] != family
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
            if (
                fields.steps <= 0
                or fields.steps + odd != ticks
                or fields.source_residue != guard
            ):
                raise ValueError("cached boundary action template is inconsistent")
            return template
        self.ledger.bump("collatz_boundary_template_misses")
        template = _build_boundary_action_template(family, repetitions)
        bound_template = family, repetitions, template
        try:
            memo[key] = bound_template
        except BlockContextBudgetExceeded:
            self.ledger.bump("collatz_boundary_template_bypasses")
        else:
            self.ledger.bump("collatz_boundary_template_publications")
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
    """Build the exact action once from an unforgeable admitted source plan."""
    if (
        type(plan) is not AdmittedBoundaryMacroPlan
        or getattr(plan, "_issuer", None) is not _BOUNDARY_PLAN_ISSUER
        or type(plan.source) is not int
        or type(plan.available_physical_ticks) is not int
        or type(plan.minimum_repetitions) is not int
        or type(plan.family) is not str
        or type(plan.maximum_repetitions) is not int
        or type(plan.repetitions) is not int
        or plan._issued_values
        != (
            plan.source,
            plan.available_physical_ticks,
            plan.minimum_repetitions,
            plan.family,
            plan.maximum_repetitions,
            plan.repetitions,
        )
    ):
        raise ValueError("boundary macro plan has no valid admission authority")
    family = plan.family
    maximum = plan.maximum_repetitions
    repetitions = plan.repetitions
    if (
        family not in ("421", "4721", "630", "989")
        or maximum < repetitions
        or repetitions < plan.minimum_repetitions
    ):
        raise ValueError("boundary macro plan has inconsistent extent")
    if templates is not None and type(templates) is not BoundaryActionTemplateMemo:
        raise TypeError("boundary macro requires its ledger-owned template memo")
    fields, odd, ticks, guard = (
        templates.get(family, repetitions)
        if templates is not None
        else _build_boundary_action_template(family, repetitions)
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
    blank = _boundary_width_blank(family, source, endpoint)
    return CollatzBoundaryMacro._issue(
        family,
        source,
        repetitions,
        maximum,
        ticks,
        odd,
        endpoint,
        fields,
        blank,
    )


__all__ = [
    "AdmittedBoundaryMacroPlan",
    "BoundaryActionTemplateMemo",
    "CollatzBoundaryMacro",
    "admit_boundary_macro_plan",
    "boundary_macro_plan",
    "select_admitted_boundary_macro",
    "select_boundary_macro",
    "validate_boundary_macro",
]
