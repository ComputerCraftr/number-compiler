"""One query owner for a typed term and its explicitly requested observations."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.api.cli_render import _metrics_json
from number_compiler.api.cli_types import QueryRequest
from number_compiler.api.family_registry import resolve_observation_adapter
from number_compiler.api.number_api import NumberCompiler, ProjectedNumberTerm
from number_compiler.api.observation_types import (
    ObservationCategory,
    ObservationId,
    OutputStatus,
    SelectorId,
)
from number_compiler.api.output_schema import JsonValue, observation_packet
from number_compiler.api.query_types import TermQuery
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm

if TYPE_CHECKING:
    from number_compiler.api.cylinder_observation import CollatzObservationContext
    from number_compiler.api.family_registry import ResolvedObservationAdapter


class QueryContext:
    """Memoize only work owned by one already-validated public query."""

    def __init__(self, request: QueryRequest, compiler: NumberCompiler) -> None:
        self.request = request
        self.compiler = compiler
        # Do not import even the selected family's observer module until a
        # detailed observation is actually demanded. In particular, the
        # temporal summary is a snapshot of the query request, not an observer
        # initialization hook.
        self._observer: ResolvedObservationAdapter | None = None
        self._raw_term: ProjectedNumberTerm | None = None
        self._term_prepared = False
        self._observation_extents_admitted = False
        self._events: CollatzObservationContext | None = None
        self._special: dict[str, object] | None = None
        self._info: dict[ObservationId, dict[str, JsonValue]] = {}
        self.unresolved_boundary: UnresolvedSequenceTerm | None = None

    def _detailed_observation_names(self) -> tuple[ObservationId, ...]:
        return tuple(
            name
            for name in self.request.observations.info
            if name not in {ObservationId.METRICS, ObservationId.TEMPORAL}
        )

    def _adapter_observation_names(self) -> tuple[ObservationId, ...]:
        return tuple(
            name
            for name in self.request.observations.info
            if name is not ObservationId.TEMPORAL
        )

    def _observation_adapter(self) -> ResolvedObservationAdapter:
        if self._observer is None:
            requested = self._adapter_observation_names()
            if not requested:
                raise RuntimeError("no detailed observation adapter is demanded")
            self._observer = resolve_observation_adapter(
                self.request.family, requested[0]
            )
        return self._observer

    def admit_observation_extents(self) -> None:
        """Admit observer-specific extents before rendering or observation."""
        if self._observation_extents_admitted:
            return
        if self._adapter_observation_names():
            self._observation_adapter().admit(self)
        self._observation_extents_admitted = True

    def _raw_projected_term(self) -> ProjectedNumberTerm:
        """Return the projected occurrence without preparing demanded observers."""
        if self.request.selector is not SelectorId.NTH:
            raise ValueError(
                "event/certificate requests do not select an ordinary term"
            )
        if self._raw_term is None:
            self._raw_term = self.compiler.project(
                cast(TermQuery, self.request.execution)
            )
        return self._raw_term

    @property
    def term(self) -> ProjectedNumberTerm:
        if self.request.selector is not SelectorId.NTH:
            raise ValueError(
                "event/certificate requests do not select an ordinary term"
            )
        self.admit_observation_extents()
        term = self._raw_projected_term()
        if not self._term_prepared and self._detailed_observation_names():
            self._observation_adapter().prepare(self, term)
            self._term_prepared = True
        return term

    def information(self) -> dict[str, dict[str, JsonValue]]:
        """Evaluate demanded observers once and report metrics last."""
        requested_info = self.request.observations.info
        # A source-certified seed-orbit observer may authorize a longer exact
        # prefix than older 32-tick observations.  Issue that same-source
        # certificate first so requested observers do not depend on --info
        # command-line order.  Output still follows requested_info below.
        if (
            ObservationId.TEMPORAL_SEED_MORPHISM in requested_info
            and ObservationId.TEMPORAL_SEED_MORPHISM not in self._info
        ):
            self._info[ObservationId.TEMPORAL_SEED_MORPHISM] = self._observe(
                ObservationId.TEMPORAL_SEED_MORPHISM
            )
        for name in requested_info:
            if name is ObservationId.METRICS or name in self._info:
                continue
            self._info[name] = (
                self._temporal_summary()
                if name is ObservationId.TEMPORAL
                else self._observe(name)
            )

        index_exponent = self.request.presentation.index.exponent
        if (
            ObservationId.METRICS in requested_info
            and ObservationId.METRICS not in self._info
        ):
            if index_exponent is None:
                metrics = _metrics_json(self.term)
            else:
                presentation_index = cast(
                    dict[str, int | str], self.request.presentation_index
                )
                metrics = _metrics_json(
                    self.term,
                    coordinate=(
                        self.request.index,
                        f"(10**{index_exponent})",
                        presentation_index,
                    ),
                )
            packet = cast(dict[str, JsonValue], metrics)
            self._info[ObservationId.METRICS] = packet

        for name, packet in self._info.items():
            raw_status = packet.get("status")
            status = (
                raw_status
                if isinstance(raw_status, str)
                else OutputStatus.AVAILABLE.value
            )
            metadata = cast(
                dict[str, JsonValue],
                observation_packet(
                    family=self.request.family.value,
                    kind=name.value,
                    index=self.request.presentation_index,
                    index_unit=self.request.index_unit.value,
                    status=status,
                ),
            )
            packet.update(metadata)
        return {name.value: self._info[name] for name in requested_info}

    def _observe(self, name: ObservationId) -> dict[str, JsonValue]:
        if name is ObservationId.TEMPORAL_MATRIX:
            from number_compiler.api.matrix_observation import observe_matrix

            return observe_matrix(self)
        return self._observation_adapter().observe(self, name)

    def _temporal_summary(self) -> dict[str, JsonValue]:
        """Read request coordinates and any already-published projection metadata."""
        from number_compiler.api.family_registry import family_spec

        spec = family_spec(self.request.family)
        selector = self.request.selector
        details = tuple(
            item.identifier.value
            for item in spec.observation_specs
            if selector in item.selectors
            and item.identifier is not ObservationId.TEMPORAL
            and item.category is ObservationCategory.TEMPORAL
        )
        term = self._raw_term
        width: JsonValue = None
        if term is not None and term.metrics.width is not None:
            from number_compiler.arithmetic.fields.symbolic_extent import (
                extent_json_value,
            )

            width = cast(JsonValue, extent_json_value(term.metrics.width))
        return {
            "family": self.request.family.value,
            "kind": ObservationId.TEMPORAL.value,
            "index": cast(JsonValue, self.request.presentation_index),
            "index_unit": self.request.index_unit.value,
            "status": OutputStatus.SNAPSHOT.value,
            "clocks": {
                "requested": {
                    "value": cast(JsonValue, self.request.presentation_index),
                    "unit": self.request.index_unit.value,
                    "source": "request_coordinate",
                }
            },
            "available_details": details,
            "measurements": {
                "projection_width": width,
                "projection_published": term is not None,
            },
            "scope": "query_snapshot_only",
        }


def information_unresolved(info: dict[str, dict[str, JsonValue]]) -> bool:
    return any(
        isinstance(packet.get("status"), str)
        and packet["status"] in {OutputStatus.UNKNOWN, OutputStatus.UNAVAILABLE}
        for packet in info.values()
    )


__all__ = ["QueryContext", "information_unresolved"]
