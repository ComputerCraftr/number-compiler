"""Public reverse projection cache keeps its source binding authority."""

import pytest

from number_compiler.sequences.reverse_add.power import ReverseAddPoweredTerm


def test_public_reverse_warm_projection_validates_binding_before_cache_hit() -> None:
    term = ReverseAddPoweredTerm(196, 2)
    expected = term.digit(0)
    before_hits = term._ledger.counters.get("source_image_projection_hits", 0)
    original = term.seed
    term.seed = original + 1
    try:
        with pytest.raises(ValueError, match="binding changed"):
            term.digit(0)
        assert (
            term._ledger.counters.get("source_image_projection_hits", 0) == before_hits
        )
    finally:
        term.seed = original
    assert term.digit(0) == expected
