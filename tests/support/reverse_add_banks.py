"""One live source owner shared by reverse/add bank consumer regressions."""

from __future__ import annotations

from collections.abc import Iterator
from contextlib import contextmanager

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.q19_border_control import (
    CertifiedBorderGrowth,
)
from number_compiler.sequences.reverse_add.q19_controlled_gt_bank import (
    SourceGuardedGTBankAction,
)
from number_compiler.sequences.reverse_add.q19_output import (
    ReversePairQ19OutputOwner,
)
from number_compiler.sequences.reverse_add.q19_spatial_bank_morphism import (
    ReverseAddSpatialBankMorphism,
)

from .reverse_add_sources import periodic_reverse_add_source


@contextmanager
def _source_guarded_periodic_context(
    *, include_spatial: bool
) -> Iterator[
    tuple[
        ResourceLedger,
        ReversePairQ19OutputOwner,
        CertifiedBorderGrowth,
        SourceGuardedGTBankAction,
        ReverseAddSpatialBankMorphism | None,
    ]
]:
    seed = periodic_reverse_add_source((5, 16), seed=9323)
    ledger = ResourceLedger()
    owner = ReversePairQ19OutputOwner(ledger, digits_lsd(seed, 10), base=10)
    try:
        certificate = owner.certify_border_growth(
            owner.initial, steps=8, window_digits=6
        )
        bank = owner.authorize_controlled_gt_bank(
            owner.initial,
            steps=8,
            coordinate=200,
            period_size=2,
            growth_control=certificate,
        )
        spatial = (
            owner.authorize_spatial_bank_morphism(
                owner.initial,
                steps=8,
                start=200,
                count=8,
                growth_control=certificate,
                period_size=2,
            )
            if include_spatial
            else None
        )
        yield ledger, owner, certificate, bank, spatial
    finally:
        owner.dispose()
        assert ledger.entries == ledger.nodes == 0


@contextmanager
def source_guarded_periodic_banks() -> Iterator[
    tuple[
        ResourceLedger,
        ReversePairQ19OutputOwner,
        CertifiedBorderGrowth,
        SourceGuardedGTBankAction,
        ReverseAddSpatialBankMorphism,
    ]
]:
    with _source_guarded_periodic_context(include_spatial=True) as parts:
        ledger, owner, certificate, bank, spatial = parts
        assert spatial is not None
        yield ledger, owner, certificate, bank, spatial


@contextmanager
def source_guarded_periodic_temporal_bank() -> Iterator[
    tuple[
        ResourceLedger,
        ReversePairQ19OutputOwner,
        CertifiedBorderGrowth,
        SourceGuardedGTBankAction,
    ]
]:
    with _source_guarded_periodic_context(include_spatial=False) as parts:
        ledger, owner, certificate, bank, _spatial = parts
        yield ledger, owner, certificate, bank


__all__ = [
    "source_guarded_periodic_banks",
    "source_guarded_periodic_temporal_bank",
]
