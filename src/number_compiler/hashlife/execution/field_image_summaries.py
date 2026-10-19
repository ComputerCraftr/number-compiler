"""Concrete and parametric range summaries retained by completed field images."""

from __future__ import annotations

from dataclasses import dataclass

from number_compiler.hashlife.execution.continuations.higher_interfaces import (
    HigherLocalInterfaceArena,
)
from number_compiler.hashlife.execution.continuations.higher_types import (
    FieldAtomSort,
    HigherExpressionID,
)
from number_compiler.hashlife.execution.field_image_domains import FieldInterfaceArena
from number_compiler.hashlife.interfaces.semantic_structures import LocalInterfaceID
from number_compiler.resources.metric_keys import (
    hashlife_execution as _execution_keys,
)


@dataclass(frozen=True, slots=True)
class FieldImageSummary:
    activity: bool
    first_active: int | None
    last_active: int | None
    extent: int
    growth: int = 0
    terminated: bool = False

    def __post_init__(self) -> None:
        if type(self.activity) is not bool or type(self.terminated) is not bool:
            raise TypeError("image activity and termination require booleans")
        if type(self.extent) is not int or type(self.growth) is not int:
            raise TypeError("image extent metadata requires exact integers")
        if self.extent < 0:
            raise ValueError("negative image extent")
        for value in (self.first_active, self.last_active):
            if value is not None and (
                type(value) is not int or not 0 <= value < self.extent
            ):
                raise ValueError("activity coordinate is outside the image extent")
        if (self.first_active is None) != (self.last_active is None):
            raise ValueError("activity endpoints must agree on emptiness")
        if self.activity != (self.first_active is not None):
            raise ValueError("activity flag disagrees with endpoints")
        if (
            self.first_active is not None
            and self.last_active is not None
            and self.first_active > self.last_active
        ):
            raise ValueError("image activity endpoints are reversed")


@dataclass(frozen=True, slots=True)
class ParametricFieldRangeSummary:
    """Exact range functions, separate from the local presence interface.

    These are unevaluated occurrence metadata, not a certified concrete seam.
    Parent growth uses the composer's biased encoding; leaf growth is Boolean.
    """

    activity: HigherExpressionID
    first_active: HigherExpressionID
    last_active: HigherExpressionID
    extent: HigherExpressionID
    growth: HigherExpressionID

    def __post_init__(self) -> None:
        values = self.expressions()
        for value in values:
            if type(value) is not HigherExpressionID:
                raise TypeError("range summaries require higher expression handles")
            HigherExpressionID.__post_init__(value)
        if any(value.owner is not values[0].owner for value in values):
            raise ValueError("range summary expressions have different owners")

    def expressions(self) -> tuple[HigherExpressionID, ...]:
        return (
            self.activity,
            self.first_active,
            self.last_active,
            self.extent,
            self.growth,
        )


@dataclass(frozen=True, slots=True)
class ParametricFieldImageSummary:
    """Canonical summary functions owned by a bounded local interface.

    ``extent_bound`` is admission geometry only.  Activity and exact extent
    remain functions of the incoming port and are bound at observation time.
    """

    interface: LocalInterfaceID
    extent_bound: int
    range_summary: ParametricFieldRangeSummary | None = None

    def __post_init__(self) -> None:
        if type(self.interface) is not LocalInterfaceID:
            raise TypeError("parametric summary requires a local interface ID")
        if type(self.extent_bound) is not int or self.extent_bound < 0:
            raise ValueError("parametric summary requires a nonnegative extent bound")
        if self.range_summary is not None:
            if type(self.range_summary) is not ParametricFieldRangeSummary:
                raise TypeError("parametric range summary requires its canonical type")
            self.range_summary.__post_init__()

    def validate_range(self, interfaces: FieldInterfaceArena) -> None:
        """Check allocated handles, exact sorts and the admitted boundary inputs."""
        self.__post_init__()
        summary = self.range_summary
        if summary is None:
            return
        if not isinstance(interfaces, HigherLocalInterfaceArena):
            raise TypeError("range expressions require a higher semantic interface")
        interfaces.ledger.bump(_execution_keys.FIELD_RANGE_SUMMARY_VALIDATIONS)
        local = interfaces.resolve(self.interface)
        signature = interfaces.interface(local.signature)
        inputs = {port.variable for port in signature.inputs}
        width = self.extent_bound
        boolean = FieldAtomSort("boolean", 2)
        sorts = (
            boolean,
            FieldAtomSort("field-active-position", width + 1),
            FieldAtomSort("field-active-position", width + 1),
            boolean if width == 1 else FieldAtomSort("field-active-extent", width + 1),
            boolean
            if width == 1
            else FieldAtomSort("field-growth-biased", 2 * width + 1),
        )
        for expression, expected in zip(summary.expressions(), sorts, strict=True):
            interfaces.ledger.bump(
                _execution_keys.FIELD_RANGE_SUMMARY_VALIDATION_EXPRESSIONS
            )
            node = interfaces.semantics.expression(expression)
            if node.sort != expected:
                raise ValueError("range summary expression has another extent sort")
            if (
                not set(interfaces.semantics.component_free_variables(expression))
                <= inputs
            ):
                raise ValueError("range summary has unbound occurrence inputs")


FieldImageSummaryRef = FieldImageSummary | ParametricFieldImageSummary
