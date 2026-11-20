"""Compact source MDD evaluation and adversarial structure checks."""

import pytest

from number_compiler.sequences.comma.boundary_quotient import BoundaryState
from number_compiler.sequences.comma.future_source_mdd import (
    FutureSourceMDD,
    SourceBranch,
    SourceLeaf,
)


def test_source_mdd_uses_phase_and_family_root() -> None:
    nodes = (SourceLeaf(0), SourceLeaf(1), SourceBranch(0, (0, 1, 0)))
    source_map = FutureSourceMDD(nodes, (2,) * 8 + (1,) * 8)
    assert source_map.validate(2)
    for phase in range(924):
        assert source_map.lookup(BoundaryState("N", 2, phase)) == (phase % 3 == 1)
        assert source_map.lookup(BoundaryState("Z", 9, phase)) == 1


def test_source_mdd_rejects_bad_roots_children_and_axis_order() -> None:
    leaves = (SourceLeaf(0), SourceLeaf(1))
    assert not FutureSourceMDD(leaves, (2,) * 16).validate(2)
    cyclic = FutureSourceMDD(leaves + (SourceBranch(0, (0, 1, 2)),), (2,) * 16)
    assert not cyclic.validate(2)
    nodes = leaves + (SourceBranch(0, (0, 1, 0)), SourceBranch(0, (2, 0, 1)))
    assert not FutureSourceMDD(nodes, (3,) * 16).validate(2)
    assert not FutureSourceMDD(leaves, (0,) * 16).validate(2)
    assert FutureSourceMDD((SourceLeaf(0), SourceLeaf(999)), (0,) * 16).validate(1)
    assert not FutureSourceMDD((SourceLeaf(0), SourceLeaf(999)), (1,) * 16).validate(1)


def test_source_node_is_intrinsically_immutable() -> None:
    leaf = SourceLeaf(0)
    with pytest.raises(AttributeError):
        object.__setattr__(leaf, "cid", 1)


def test_direct_lookup_rejects_cyclic_or_unknown_nodes() -> None:
    cyclic = FutureSourceMDD((SourceBranch(0, (0, 0, 0)),), (0,) * 16)
    with pytest.raises(ValueError, match="topologically ordered"):
        cyclic.lookup(BoundaryState("N", 2, 0))
    forged = FutureSourceMDD((SourceLeaf(0),), (0,) * 16)
    with pytest.raises(AttributeError):
        object.__setattr__(forged, "nodes", (object(),))
    unknown = FutureSourceMDD._make(((object(),), (0,) * 16))
    with pytest.raises(ValueError, match="malformed future source branch"):
        unknown.lookup(BoundaryState("N", 2, 0))
