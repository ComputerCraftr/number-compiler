"""Typed result views carried by the existing observation registry."""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TYPE_CHECKING

from number_compiler.api.json_output import is_object_sequence
from number_compiler.api.observation_types import ObservationId, SelectorId

if TYPE_CHECKING:
    from collections.abc import Mapping


class ObservationView(Enum):
    ENDPOINT_RESIDUE = (ObservationId.ARITHMETIC_MODULAR, "endpoint")
    RESIDUE = (ObservationId.ARITHMETIC_MODULAR, "residue")
    DIGIT_FIELD = (ObservationId.ARITHMETIC_MODULAR, "digit-field")
    MIXED_ADIC = (ObservationId.ARITHMETIC_MODULAR, "mixed-adic")
    RESIDUE_PERIOD = (ObservationId.TEMPORAL_CLOCK, "residue-period")
    DEFECT_SAMPLES = (ObservationId.TEMPORAL_CLOCK, "defect-samples")
    SINGLE = (ObservationId.TEMPORAL_ACCUMULATOR, "single")
    ALTERNATING = (ObservationId.TEMPORAL_ACCUMULATOR, "alternating")
    CLOSED_ENDPOINT = (ObservationId.TEMPORAL_CLOSED_FORM, "endpoint")
    SOURCE_ACTION = (ObservationId.TEMPORAL_CLOSED_FORM, "source-action")
    FINITE_GUARD = (ObservationId.SAFETY_LEDGER, "finite-guard")
    FINITE_SAFETY = (ObservationId.SAFETY_LEDGER, "finite-safety")
    GRAPH_ACTION = (ObservationId.TEMPORAL_MACRO, "graph-action")
    EXECUTED_MACROS = (ObservationId.TEMPORAL_MACRO, "executed")

    def __init__(self, category: ObservationId, label: str) -> None:
        self.category = category
        self.label = label


VIEW_FLAGS = {
    ObservationId.ARITHMETIC_MODULAR: "arithmetic-modular-kind",
    ObservationId.TEMPORAL_CLOCK: "temporal-clock-detail",
    ObservationId.TEMPORAL_ACCUMULATOR: "temporal-accumulator-kind",
    ObservationId.TEMPORAL_CLOSED_FORM: "temporal-closed-form-kind",
    ObservationId.SAFETY_LEDGER: "safety-ledger-detail",
    ObservationId.TEMPORAL_MACRO: "temporal-macro-kind",
}


@dataclass(frozen=True, slots=True)
class ViewSpec:
    view: ObservationView
    law: str
    clock_unit: str
    coordinate: str
    authority_scope: str
    default: bool = False
    selector: SelectorId = SelectorId.NTH
    options: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if (
            type(self.view) is not ObservationView
            or type(self.selector) is not SelectorId
        ):
            raise TypeError("view declarations require typed identities")
        if type(self.default) is not bool or type(self.options) is not tuple:
            raise TypeError("view defaults and options require immutable declarations")

    @property
    def category(self) -> ObservationId:
        return self.view.category


def select_views(
    specs: tuple[ViewSpec, ...],
    selector: SelectorId,
    information: tuple[ObservationId, ...],
    values: Mapping[str, object],
) -> tuple[ObservationView, ...]:
    selected: list[ObservationView] = []
    for category, flag in VIEW_FLAGS.items():
        raw = values.get(flag.replace("-", "_"))
        if raw is None and category not in information:
            continue
        allowed = tuple(
            s for s in specs if s.category is category and s.selector is selector
        )
        if raw is None:
            selected.extend(spec.view for spec in allowed if spec.default)
            continue
        if category not in information:
            raise ValueError(f"--{flag} requires --info {category}")
        if not is_object_sequence(raw):
            raise TypeError(f"--{flag} needs repeatable view names")
        by_label = {spec.view.label: spec.view for spec in allowed}
        for label in raw:
            if type(label) is not str or label not in by_label:
                raise ValueError(f"--{flag} has an unsupported view for this selector")
            view = by_label[label]
            if view not in selected:
                selected.append(view)
    return tuple(selected)
