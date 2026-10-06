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
    validate_certified_application_inputs,
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
    validate_certified_application_inputs(
        effect,
        source,
        logical_length=logical_length,
        certificate=certificate,
        ledger=ledger,
        compiler=compiler,
        source_geometry=source_geometry,
        microblocks=microblocks,
    )
    family_hooks = compiler.family_hooks
    pair_transfer_factory = None
    if certificate.family == "collatz":
        from number_compiler.sequences.collatz.tile_family_hooks import (
            collatz_tile_hooks_for_effect,
        )

        canonical_hooks = collatz_tile_hooks_for_effect(effect)
        if canonical_hooks is None:
            raise ValueError("certified Collatz execution received another effect")
        if family_hooks is not None and family_hooks is not canonical_hooks:
            raise ValueError("certified Collatz compiler has another family adapter")
        family_hooks = canonical_hooks
        if family_hooks.owns_compatibility(effect):
            effect = family_hooks.lower_compatibility(effect, compiler)
        else:
            from number_compiler.arithmetic.contracts.kernel_admission import (
                admit_effect,
            )

            # Pure admission precedes binding so an unsupported certificate
            # cannot leave family state attached to a reusable compiler.
            admit_effect(effect, family_hooks=family_hooks)
            if compiler.family_hooks is None:
                compiler.bind_family_hooks(family_hooks)
    else:
        if family_hooks is not None:
            raise ValueError("reverse/add compiler has another family adapter")
        from number_compiler.sequences.reverse_add.tile_pair_transfer import (
            ReverseAddFinitePairTransferFactory,
        )

        pair_transfer_factory = ReverseAddFinitePairTransferFactory()
    # Admission must be complete before the rejection counter changes. In
    # particular, an equivalent but foreign compiler node cannot use this
    # fail-closed seam as a late probe.
    compiler.reference(effect)
    from number_compiler.hashlife.observation.tile_projection import (
        build_tile_projection,
    )

    return build_tile_projection(
        effect,
        source_geometry,
        family_hooks=family_hooks,
        pair_transfer_factory=pair_transfer_factory,
    )


__all__ = ["build_certified_field_application"]
