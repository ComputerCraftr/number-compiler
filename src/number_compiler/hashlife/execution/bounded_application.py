"""Certified family admission to the canonical tile executor."""

from __future__ import annotations

from collections.abc import Sequence
from typing import Protocol, TypeAlias

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.contracts.temporal_family import (
    TemporalFamilyCertificate,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.projection.microblock_cache import MicroblockCache
from number_compiler.resources.ledger import ResourceLedger


class LazyProjection(Protocol):
    ledger: ResourceLedger

    def point(self, position: int) -> int: ...

    def active_width(self) -> int: ...

    def retained_entries(self) -> int: ...


BoundedTemporalApplication: TypeAlias = LazyProjection


def build_bounded_application(
    effect: BlockEffect,
    source: Sequence[int],
    *,
    logical_length: int,
    certificate: TemporalFamilyCertificate | None = None,
    ledger: ResourceLedger | None = None,
    compiler: LazyCompiler | None = None,
    source_geometry: SourceGeometry | None = None,
    microblocks: MicroblockCache | None = None,
) -> BoundedTemporalApplication | None:
    """Build a certified tile executor without a continuation fallback."""
    if certificate is None:
        return None
    certificate.validate(effect)
    resources = ResourceLedger() if ledger is None else ledger
    if compiler is None:
        compiler = LazyCompiler(resources)
        effect = compiler.import_effect(effect)
    elif compiler.ledger is not resources:
        raise ValueError("compiler belongs to another index")
    if source_geometry is None or source_geometry.ledger is not resources:
        raise ValueError("certified family execution requires owned source geometry")
    if microblocks is None or microblocks.ledger is not resources:
        raise ValueError("certified family execution requires owned microblocks")
    from number_compiler.sequences.runtime_router import (
        build_certified_field_application,
    )

    return build_certified_field_application(
        effect,
        source,
        logical_length=logical_length,
        certificate=certificate,
        ledger=resources,
        compiler=compiler,
        source_geometry=source_geometry,
        microblocks=microblocks,
    )


__all__ = [
    "BoundedTemporalApplication",
    "LazyProjection",
    "build_bounded_application",
]
