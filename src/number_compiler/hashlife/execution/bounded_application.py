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
from number_compiler.hashlife.execution.tile_execution_adapter import FamilyTileHooks
from number_compiler.projection.microblock_cache import MicroblockCache
from number_compiler.resources.ledger import ResourceLedger


class LazyProjection(Protocol):
    ledger: ResourceLedger

    def point(self, position: int) -> int: ...

    def active_width(self) -> int: ...

    def retained_entries(self) -> int: ...


BoundedTemporalApplication: TypeAlias = LazyProjection


def validate_certified_application_inputs(
    effect: BlockEffect,
    source: Sequence[int],
    *,
    logical_length: int,
    certificate: TemporalFamilyCertificate,
    ledger: ResourceLedger,
    compiler: LazyCompiler,
    source_geometry: SourceGeometry,
    microblocks: MicroblockCache,
) -> None:
    """Validate the common source-bound certificate contract before dispatch."""
    _validate_certificate_binding(effect, certificate)
    _validate_application_resources(
        effect,
        source,
        logical_length=logical_length,
        ledger=ledger,
        compiler=compiler,
        source_geometry=source_geometry,
        microblocks=microblocks,
        certificate=certificate,
    )


def _validate_certificate_binding(
    effect: BlockEffect,
    certificate: TemporalFamilyCertificate,
) -> None:
    certificate.validate(effect)


def _validate_application_resources(
    effect: BlockEffect,
    source: Sequence[int],
    *,
    logical_length: int,
    ledger: ResourceLedger,
    compiler: LazyCompiler,
    source_geometry: SourceGeometry,
    microblocks: MicroblockCache,
    certificate: TemporalFamilyCertificate,
) -> None:
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
    if type(logical_length) is not int or logical_length < len(source):
        raise ValueError("certified family execution requires its exact source extent")
    source_geometry.require_source(source, effect.blank)
    if certificate.family not in ("reverse-add", "collatz"):
        raise ValueError("unknown certified temporal family")


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
    family_hooks: FamilyTileHooks | None = None,
) -> BoundedTemporalApplication | None:
    """Build a certified tile executor without a continuation fallback."""
    if certificate is None:
        return None
    _validate_certificate_binding(effect, certificate)
    resources = ResourceLedger() if ledger is None else ledger
    if family_hooks is not None and type(family_hooks) is not FamilyTileHooks:
        raise TypeError("certified execution requires canonical family hooks")
    if compiler is None:
        compiler = LazyCompiler(resources, family_hooks=family_hooks)
        effect = compiler.import_effect(effect)
    elif compiler.ledger is not resources:
        raise ValueError("compiler belongs to another index")
    elif family_hooks is not None:
        compiler.bind_family_hooks(family_hooks)
    if source_geometry is None or source_geometry.ledger is not resources:
        raise ValueError("certified family execution requires owned source geometry")
    if microblocks is None or microblocks.ledger is not resources:
        raise ValueError("certified family execution requires owned microblocks")
    _validate_application_resources(
        effect,
        source,
        logical_length=logical_length,
        ledger=resources,
        compiler=compiler,
        source_geometry=source_geometry,
        microblocks=microblocks,
        certificate=certificate,
    )
    compiler.reference(effect)
    from number_compiler.hashlife.observation.tile_projection import (
        build_tile_projection,
    )

    return build_tile_projection(effect, source_geometry, family_hooks=family_hooks)


__all__ = [
    "BoundedTemporalApplication",
    "LazyProjection",
    "build_bounded_application",
    "validate_certified_application_inputs",
]
