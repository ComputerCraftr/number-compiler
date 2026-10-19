"""Construction authority below every exact-tree allocator and point observer.

Legacy tree builders outside a point request are original-input APIs. Within a
point request only a validated original-source scope may allocate exact nodes;
endpoint lowering cannot override a point observer's read-only scope.
"""

from __future__ import annotations

from collections.abc import Callable, Generator
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass
from functools import wraps
from typing import TYPE_CHECKING, ParamSpec, TypeVar

from number_compiler.arithmetic.contracts.scoped_handles import (
    ArenaToken,
    ExactSource,
    LoweringCapability,
)

if TYPE_CHECKING:
    from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
    from number_compiler.arithmetic.fields.dyadic_tile import DyadicSpan


_P = ParamSpec("_P")
_R = TypeVar("_R")
_POINT_REQUEST: ContextVar[bool] = ContextVar("exact_tree_point_request", default=False)
_SOURCE_PERMIT: ContextVar[ExactSource | None] = ContextVar(
    "exact_tree_original_source", default=None
)


class ExactTreeConstructionForbidden(RuntimeError):
    """An observer attempted an exact-tree allocation, including a warm lookup."""


def require_exact_construction() -> None:
    if _POINT_REQUEST.get() and _SOURCE_PERMIT.get() is None:
        raise ExactTreeConstructionForbidden(
            "point/width observers may read sources but cannot construct exact trees"
        )


def source_reads_only(function: Callable[_P, _R]) -> Callable[_P, _R]:
    """Guard the entire call, including warm, zero-generation, and exterior paths."""

    @wraps(function)
    def guarded(*args: _P.args, **kwargs: _P.kwargs) -> _R:
        point = _POINT_REQUEST.set(True)
        permit = _SOURCE_PERMIT.set(None)
        try:
            return function(*args, **kwargs)
        finally:
            _SOURCE_PERMIT.reset(permit)
            _POINT_REQUEST.reset(point)

    return guarded


def exact_constructor(function: Callable[_P, _R]) -> Callable[_P, _R]:
    """Reject before allocating temporary words or consulting an exact interner."""

    @wraps(function)
    def guarded(*args: _P.args, **kwargs: _P.kwargs) -> _R:
        require_exact_construction()
        return function(*args, **kwargs)

    return guarded


@dataclass(frozen=True, slots=True)
class OriginalSourceConstruction:
    """Authority tied to one immutable caller-supplied original source."""

    source: ExactSource

    def __post_init__(self) -> None:
        self.validate_source()
        if _POINT_REQUEST.get():
            raise ExactTreeConstructionForbidden(
                "a point request cannot mint original-source construction authority"
            )

    def validate_source(self, expected: ExactSource | None = None) -> ExactSource:
        """Validate authority payload before equality checks or retained mutation."""
        if (
            type(self) is not OriginalSourceConstruction
            or type(self.source) is not ExactSource
        ):
            raise TypeError("original construction requires an immutable exact source")
        ExactSource.__post_init__(self.source)
        if expected is not None and self.source != expected:
            raise ValueError("source construction authority belongs to another source")
        return self.source

    @contextmanager
    def allow(
        self, values: tuple[int, ...], blank: int, length: int
    ) -> Generator[None, None, None]:
        if _POINT_REQUEST.get():
            raise ExactTreeConstructionForbidden(
                "a point request cannot enter an unrestricted source-construction scope"
            )
        self._validate(values, blank, length)
        permit = _SOURCE_PERMIT.set(self.source)
        try:
            yield
        finally:
            _SOURCE_PERMIT.reset(permit)

    def _validate(self, values: tuple[int, ...], blank: int, length: int) -> None:
        source = OriginalSourceConstruction.validate_source(self)
        if (
            type(values) is not tuple
            or type(blank) is not int
            or type(length) is not int
            or any(type(value) is not int for value in values)
        ):
            raise TypeError(
                "original source symbols, blank, and extent must be integers"
            )
        if (
            values != source.digits
            or blank != source.blank
            or length < len(values)
            or (source.extent is not None and length > source.extent)
        ):
            raise ValueError(
                "construction does not match the authorized original source"
            )

    def construct(
        self, geometry: SourceGeometry, values: tuple[int, ...], blank: int, length: int
    ) -> DyadicSpan:
        """Run only the source allocator; never lend a scope to caller code."""
        from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry

        if type(geometry) is not SourceGeometry or geometry._construction is not self:
            raise ValueError("source allocation authority belongs to another geometry")
        self._validate(values, blank, length)
        permit = _SOURCE_PERMIT.set(self.source)
        try:
            return SourceGeometry._source_span(geometry, values, blank, length)
        finally:
            _SOURCE_PERMIT.reset(permit)


def require_endpoint_construction() -> None:
    if _POINT_REQUEST.get():
        raise ExactTreeConstructionForbidden(
            "endpoint lowering cannot authorize construction inside a point request"
        )


@contextmanager
def endpoint_construction(
    owner: ArenaToken, capability: LoweringCapability
) -> Generator[None, None, None]:
    """Explicit future-tree construction cannot be entered by a point callback."""
    if not isinstance(capability, LoweringCapability) or capability.owner is not owner:
        raise ValueError("foreign or missing endpoint lowering capability")
    require_endpoint_construction()
    yield
