"""One query owner for a typed term and its explicitly requested observations."""

from __future__ import annotations

from typing import TYPE_CHECKING, cast

from number_compiler.api.cli_render import _metrics_json
from number_compiler.api.cli_types import QueryRequest
from number_compiler.api.family_registry import resolve_observation_adapter
from number_compiler.api.number_api import NumberCompiler, ProjectedNumberTerm
from number_compiler.api.output_schema import JsonValue
from number_compiler.api.query_types import TermQuery
from number_compiler.arithmetic.contracts.unresolved_term import UnresolvedSequenceTerm

if TYPE_CHECKING:
    from number_compiler.api.cylinder_observation import CollatzObservationContext


class QueryContext:
    """Memoize only work owned by one already-validated public query."""

    def __init__(self, request: QueryRequest, compiler: NumberCompiler) -> None:
        self.request = request
        self.compiler = compiler
        self._observer = resolve_observation_adapter(request.family)
        self._raw_term: ProjectedNumberTerm | None = None
        self._term_prepared = False
        self._observation_extents_admitted = False
        self._events: CollatzObservationContext | None = None
        self._special: dict[str, object] | None = None
        self._info: dict[str, dict[str, JsonValue]] = {}
        self.unresolved_boundary: UnresolvedSequenceTerm | None = None

    def admit_observation_extents(self) -> None:
        """Admit observer-specific extents before rendering or observation."""
        if self._observation_extents_admitted:
            return
        self._observer.admit(self)
        self._observation_extents_admitted = True

    def _raw_projected_term(self) -> ProjectedNumberTerm:
        """Return the projected occurrence without preparing demanded observers."""
        if self.request.selector != "nth":
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
        if self.request.selector != "nth":
            raise ValueError(
                "event/certificate requests do not select an ordinary term"
            )
        self.admit_observation_extents()
        term = self._raw_projected_term()
        if not self._term_prepared:
            self._observer.prepare(self, term)
            self._term_prepared = True
        return term

    def information(self) -> dict[str, dict[str, JsonValue]]:
        """Evaluate demanded observers once and report metrics last."""
        requested_info = self.request.observations.info
        for name in requested_info:
            if name == "metrics" or name in self._info:
                continue
            self._info[name] = self._observe(name)

        index_exponent = self.request.presentation.index.exponent
        if "metrics" in requested_info and "metrics" not in self._info:
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
            self._info["metrics"] = packet

        for name, packet in self._info.items():
            packet.update(
                family=self.request.family,
                kind=name,
                index=cast(JsonValue, self.request.presentation_index),
                index_unit=self.request.index_unit,
            )
            packet.setdefault("status", "available")
        return {name: self._info[name] for name in requested_info}

    def _observe(self, name: str) -> dict[str, JsonValue]:
        return self._observer.observe(self, name)


def information_unresolved(info: dict[str, dict[str, JsonValue]]) -> bool:
    return any(
        isinstance(packet.get("status"), str)
        and packet["status"] in {"unknown", "unavailable"}
        for packet in info.values()
    )


__all__ = ["QueryContext", "information_unresolved"]
