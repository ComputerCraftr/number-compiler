"""Exact oracle regression; these objects are not production carriers."""

import inspect

from devtools.verification.forcing_morphism import ReverseAddForcingMorphismArena


def test_reverse_forcing_source_key_uses_packed_cut_not_row_length_vector() -> None:
    source = inspect.getsource(ReverseAddForcingMorphismArena.source_key)
    assert "ReverseAddCarryCutState" in source
    assert "row.length" not in source
    assert "tile_ids" not in source
