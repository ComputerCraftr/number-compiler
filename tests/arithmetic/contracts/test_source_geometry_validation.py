"""Source geometry validates each distinct source authority exactly once."""

from __future__ import annotations

import pytest

from number_compiler.arithmetic.contracts.exact_tree_context import (
    OriginalSourceConstruction,
)
from number_compiler.arithmetic.contracts.scoped_handles import ExactSource
from number_compiler.arithmetic.contracts.source_geometry import SourceGeometry
from number_compiler.resources.ledger import ResourceLedger


@pytest.mark.parametrize("provide_construction", (False, True))
def test_source_geometry_validates_the_source_once(
    provide_construction: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = ExactSource((1, 0), 2, blank=2, extent=2)
    construction = OriginalSourceConstruction(source) if provide_construction else None
    calls = 0
    original = ExactSource.__post_init__

    def counted_validation(value: ExactSource) -> None:
        nonlocal calls
        calls += 1
        original(value)

    monkeypatch.setattr(ExactSource, "__post_init__", counted_validation)

    SourceGeometry(ResourceLedger(), source, construction)

    assert calls == 1
