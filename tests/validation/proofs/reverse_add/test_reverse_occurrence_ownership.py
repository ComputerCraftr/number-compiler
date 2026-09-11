"""Exact oracle regression; these objects are not production carriers."""

import pytest

from devtools.proofs.reverse_spacetime import (
    ReverseAddCausalSpacetimeEngine,
    ReverseAddPairField,
)


@pytest.mark.parametrize("warm", (False, True))
@pytest.mark.parametrize("steps", (0, 1))
def test_reverse_occurrence_foreign_owner_rejected_before_lookup(
    warm: bool, steps: int
) -> None:
    left = ReverseAddCausalSpacetimeEngine(base=10)
    right = ReverseAddCausalSpacetimeEngine(base=10)
    local = left.forcing_image(ReverseAddPairField.from_pair((2,), base=10))
    foreign = right.forcing_image(ReverseAddPairField.from_pair((8,), base=10))
    assert local.occurrence_id == foreign.occurrence_id
    if warm:
        left.advance_forcing_power(local, 1)
    with pytest.raises(ValueError, match="foreign"):
        left.advance_forcing_power(foreign, steps)
    with pytest.raises(ValueError, match="foreign"):
        left.forcing.pair_span(foreign)
