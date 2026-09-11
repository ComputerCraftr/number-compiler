"""Certified arithmetic-family admission to the canonical tile executor."""

from __future__ import annotations

from collections.abc import Sequence

from number_compiler.arithmetic.contracts.block_effect import BlockEffect
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.arithmetic.contracts.temporal_family import (
    TemporalFamilyCertificate,
)
from number_compiler.hashlife.actions.lazy_compiler import LazyCompiler
from number_compiler.hashlife.execution.bounded_application import (
    BoundedTemporalApplication,
)
from number_compiler.projection.microblock_cache import MicroblockCache
from number_compiler.resources.ledger import ResourceLedger


def build_certified_field_application(
    effect: BlockEffect,
    source: Sequence[int],
    *,
    logical_length: int,
    certificate: TemporalFamilyCertificate,
    ledger: ResourceLedger,
    compiler: LazyCompiler,
    source_geometry: SourceGeometry,
    microblocks: MicroblockCache,
) -> BoundedTemporalApplication:
    """Return a verified family application or fail before generic execution."""
    certificate.validate(effect)
    if (
        type(source_geometry) is not SourceGeometry
        or type(microblocks) is not MicroblockCache
    ):
        raise TypeError("certified family execution requires exact owned resources")
    if (
        compiler.ledger is not ledger
        or source_geometry.ledger is not ledger
        or microblocks.ledger is not ledger
    ):
        raise ValueError("certified family execution requires one index ledger")
    # Admission must be complete before the rejection counter changes.  In
    # particular, a caller cannot attach a valid certificate to an equivalent
    # but foreign compiler node and use this fail-closed seam as a late probe.
    compiler.reference(effect)
    if type(logical_length) is not int or logical_length < len(source):
        raise ValueError("certified family execution requires its exact source extent")
    source_geometry.require_source(source, effect.blank)
    if certificate.family not in ("reverse-add", "collatz"):
        raise ValueError("unknown certified temporal family")
    from number_compiler.hashlife.observation.tile_projection import (
        build_tile_projection,
    )

    return build_tile_projection(effect, source_geometry)


__all__ = ["build_certified_field_application"]
