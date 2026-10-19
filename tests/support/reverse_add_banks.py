"""One live source owner shared by reverse/add bank consumer regressions."""

from __future__ import annotations

from collections.abc import Generator
from contextlib import contextmanager
from random import Random

from number_compiler.arithmetic.fields.radix import digits_lsd
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.reverse_add.mixed_periodic_bank import (
    required_protected_halo,
)
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

from .reverse_add_sources import (
    periodic_reverse_add_source,
    reverse_add_source_from_pair_sums,
)


def _compact_temporal_source() -> int:
    """Build only the source window needed by the temporal bank fixture.

    The spatial-bank fixtures intentionally keep a wide repeated source. The
    temporal-only consumer needs a protected neighbourhood around pair 200,
    not hundreds of additional periodic cells on either side.
    """
    period = (5, 16)
    steps = 8
    coordinate = 200
    halo = required_protected_halo(len(period), steps) + 2
    half_width = coordinate + halo + 1
    rng = Random(9323)
    pair_sums = [rng.randrange(1, 19)] + [
        rng.randrange(19) for _ in range(half_width - 1)
    ]
    for pair_position in range(coordinate - halo, coordinate + halo + 1):
        # Q19 pair coordinate p is the p-th generated half-word cell. The
        # original fixture starts this period at pair 96, so pair 200 is its
        # 105th cell and carries the first symbol, 5.
        pair_sums[pair_position] = period[(pair_position - coordinate) % len(period)]

    return reverse_add_source_from_pair_sums(pair_sums, rng=rng)


@contextmanager
def _source_guarded_periodic_context(
    *, include_spatial: bool
) -> Generator[
    tuple[
        ResourceLedger,
        ReversePairQ19OutputOwner,
        CertifiedBorderGrowth,
        SourceGuardedGTBankAction,
        ReverseAddSpatialBankMorphism | None,
    ],
    None,
    None,
]:
    seed = (
        periodic_reverse_add_source((5, 16), seed=9323)
        if include_spatial
        else _compact_temporal_source()
    )
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
def source_guarded_periodic_banks() -> Generator[
    tuple[
        ResourceLedger,
        ReversePairQ19OutputOwner,
        CertifiedBorderGrowth,
        SourceGuardedGTBankAction,
        ReverseAddSpatialBankMorphism,
    ],
    None,
    None,
]:
    with _source_guarded_periodic_context(include_spatial=True) as parts:
        ledger, owner, certificate, bank, spatial = parts
        assert spatial is not None
        yield ledger, owner, certificate, bank, spatial


@contextmanager
def source_guarded_periodic_temporal_bank() -> Generator[
    tuple[
        ResourceLedger,
        ReversePairQ19OutputOwner,
        CertifiedBorderGrowth,
        SourceGuardedGTBankAction,
    ],
    None,
    None,
]:
    with _source_guarded_periodic_context(include_spatial=False) as parts:
        ledger, owner, certificate, bank, _spatial = parts
        yield ledger, owner, certificate, bank


__all__ = [
    "source_guarded_periodic_banks",
    "source_guarded_periodic_temporal_bank",
]
