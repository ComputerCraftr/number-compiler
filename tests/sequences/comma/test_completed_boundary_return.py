"""Compact boundary publication preserves indexed arithmetic without its storage."""

from dataclasses import replace
from typing import Literal

import pytest

from number_compiler.sequences.comma import boundary_return
from number_compiler.sequences.comma.boundary_quotient import (
    BoundaryState,
    construct_completed_return,
    construct_macro,
)


@pytest.mark.parametrize("grouped", [False, True])
@pytest.mark.parametrize(
    ("kind", "a", "phase"),
    [("N", 2, 10), ("Z", 2, 10), ("N", 9, 5), ("Z", 5, 923)],
)
def test_compact_return_matches_indexed_header(
    kind: Literal["N", "Z"], a: int, phase: int, grouped: bool
) -> None:
    source = BoundaryState(kind, a, phase)
    indexed = construct_macro(source, grouped_near=grouped)
    compact = construct_completed_return(source, grouped_near=grouped)
    for field in (
        "source",
        "outcome",
        "exponent_delta",
        "destination_a",
        "weight",
        "endpoint",
        "ordered_children",
    ):
        assert getattr(compact, field) == getattr(indexed, field)
    assert not hasattr(compact, "sector_fragments")
    assert not hasattr(compact, "prefix_weights")
    boundary_return._completed_macro_return_component_seal(compact)


def test_compact_return_does_not_build_an_index(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def forbidden(*args: object, **kwargs: object) -> None:
        raise AssertionError("unused indexed publication")

    monkeypatch.setattr(boundary_return, "_indexed_macro", forbidden)
    compact = construct_completed_return(BoundaryState("N", 2, 10))
    assert compact.ordered_children


def test_compact_return_rejects_changed_header_and_foreign_seal() -> None:
    original = construct_completed_return(BoundaryState("N", 2, 10))
    changed = replace(original, exponent_delta=original.exponent_delta + 1)
    object.__setattr__(changed, "_component_seal", original._component_seal)
    with pytest.raises(ValueError, match="mismatch"):
        boundary_return._completed_macro_return_component_seal(changed)
    object.__setattr__(original, "destination_a", None)
    with pytest.raises(ValueError, match="ordered children"):
        boundary_return._completed_macro_return_component_seal(original)
