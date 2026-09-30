"""Complete bounded counts for source-free reverse/add successor images."""

import pytest

from devtools.verification.reverse_successor_image_audit import audit_width


@pytest.mark.parametrize(
    ("width", "no_sources", "no_images", "growth_sources", "growth_images", "images"),
    (
        (4, 181, 181, 180, 99, 280),
        (5, 1805, 1805, 1805, 1040, 2845),
        (6, 3430, 3430, 3429, 1080, 4510),
        (7, 34295, 33485, 34295, 11705, 45190),
        (8, 65161, 65080, 65160, 12429, 77509),
    ),
)
def test_complete_successor_image_identity(
    width: int,
    no_sources: int,
    no_images: int,
    growth_sources: int,
    growth_images: int,
    images: int,
) -> None:
    actual = audit_width(width)
    assert (actual.no_growth.sources, actual.no_growth.images) == (
        no_sources,
        no_images,
    )
    assert (actual.growth.sources, actual.growth.images) == (
        growth_sources,
        growth_images,
    )
    assert actual.images == images

    # Retaining source Gamma together with the image defeats every alias.
    assert actual.no_growth.provenance_images == no_sources
    assert actual.growth.provenance_images == growth_sources
