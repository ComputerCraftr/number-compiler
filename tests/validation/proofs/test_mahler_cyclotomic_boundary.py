"""Independent bounded checks of the signed current-tail cylinder boundary."""

from fractions import Fraction
from itertools import pairwise, product
from typing import cast

import pytest

from devtools.experiments.antihydra.barrier_search import tail_refinement
from devtools.experiments.antihydra.source_safety import (
    SignedTailBoundary,
    SourceBlockID,
    SourceSafetyWorkspace,
)
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational
from number_compiler.arithmetic.fields.root_semifield import RootSemifieldElement
from number_compiler.resources.ledger import ResourceLedger


def _reference(source: int, width: int) -> tuple[tuple[int, ...], int, bool]:
    word: list[int] = []
    initial = source
    lo, hi = Fraction(0), Fraction(1, 2)
    for i in range(width):
        word.append(source % 2)
        source = (3 * source + 1) // 2
        scale = Fraction(3, 2) ** (i + 1)
        lo = max(lo, source / scale - initial)
        hi = min(hi, (source + Fraction(1, 2)) / scale - initial)
    signed = sum((1 - 2 * e) * 3 ** (width - 1 - j) * 2**j for j, e in enumerate(word))
    return tuple(word), signed, lo < hi


@pytest.mark.parametrize(
    "width,boundary,total", [(6, {9, 13, 45}, 18), (12, {521, 777, 2569}, 201)]
)
def test_source_census_preserves_original_guard_and_refines_tail(
    width: int, boundary: set[int], total: int
) -> None:
    workspace = SourceSafetyWorkspace(
        ResourceLedger(max_nodes=20000, max_cache_entries=40000)
    )
    unresolved: set[int] = set()
    positive: set[int] = set()
    for residue in range(1 << width):
        handle = workspace.cylinder(width, residue)
        block = workspace.view(handle)
        tail = workspace.tail_boundary(handle)
        _, signed, live = _reference(residue, width)
        assert signed == tail.numerator
        assert tail.interval == (
            ExactRational(signed - 2**width, 3**width),
            ExactRational(signed + 2**width, 3**width),
        )
        assert live == (not block.guard.empty)
        assert tail.cone == (signed + 2**width, 2**width - signed)
        assert signed % 2 == 1  # Endpoint equality cannot occur for positive widths.
        if live:
            assert tail.classification != "nonpositive"
            (unresolved if tail.classification == "boundary" else positive).add(residue)
    assert unresolved == boundary
    assert len(unresolved | positive) == total
    assert len(positive) == total - 3


def test_six_bit_no_adjacent_ones_boundary_is_exact() -> None:
    raw: list[tuple[int, ...]] = []
    admissible: list[str] = []
    for word in product((0, 1), repeat=6):
        signed = sum((1 - 2 * e) * 3 ** (5 - j) * 2**j for j, e in enumerate(word))
        if -64 < signed <= 64:
            raw.append(word)
            if all(a + b < 2 for a, b in pairwise(word)):
                admissible.append("".join(map(str, word)))
    assert len(raw) == 10
    assert admissible == ["100100", "100101", "101000"]


def test_boundary_only_refinement_reproduces_depth_census() -> None:
    ledger = ResourceLedger(max_nodes=10000, max_cache_entries=20000)
    workspace = SourceSafetyWorkspace(ledger, max_width=18)
    frontier: tuple[SourceBlockID, ...] = (workspace.cylinder(0, 0),)
    counts: list[int] = []
    for depth in range(1, 19):
        children = tuple(
            child for parent in frontier for child in workspace.refine_tail(parent)
        )
        frontier = tuple(
            child
            for child in children
            if workspace.tail_boundary(child).classification == "boundary"
        )
        if depth >= 6:
            counts.append(len(frontier))
        if depth == 12:
            assert {workspace.view(node).residue for node in frontier} == {
                521,
                777,
                2569,
            }
    assert counts == [3, 3, 3, 4, 2, 2, 3, 2, 2, 3, 2, 3, 4]
    assert {workspace.view(node).residue % 256 for node in frontier} == {9}
    assert ledger.counters["safety_tail_refinements"] < 150


@pytest.mark.parametrize("bit", (0, 1))
@pytest.mark.parametrize("count", (0, 1, 2, 7, 64))
def test_powered_runs_match_reflected_cone_matrices(bit: int, count: int) -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger(), max_width=70)
    initial = workspace.cylinder(6, 9)
    a, b = workspace.tail_boundary(initial).cone
    result = workspace.extend_run(initial, bit, count)
    cone = workspace.tail_boundary(result).cone
    p, q = 3**count, 2**count
    expected = (p * a, q * b - (p - q) * a) if not bit else (q * a - (p - q) * b, p * b)
    assert cone == expected
    assert workspace.view(result).width == 6 + count
    if not count:
        assert result == initial
    else:
        assert (
            workspace.ledger.counters["safety_tail_run_compositions"]
            <= 2 * count.bit_length()
        )


def test_positive_current_tail_is_not_all_shift_safety(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger())
    positive = workspace.cylinder(1, 0)  # N=1 lies on the boundary, so use 00.
    positive = workspace.extend_run(positive, 0, 1)
    assert workspace.tail_boundary(positive).classification == "positive"
    # An already positive time-zero tail can still have an impossible later 11.
    later_failure = workspace.extend_run(positive, 1, 2)
    assert workspace.tail_boundary(later_failure).classification == "positive"
    assert workspace.view(later_failure).guard.empty

    def forbidden(*_args: object) -> None:
        raise AssertionError("terminal current-tail query attempted source refinement")

    monkeypatch.setattr(workspace, "compose", forbidden)
    assert workspace.refine_tail(positive) == ()


def test_threshold_equality_and_source_authority() -> None:
    assert SignedTailBoundary(2, 2, 3).classification == "boundary"
    assert SignedTailBoundary(-2, 2, 3).classification == "nonpositive"
    first, second = (
        SourceSafetyWorkspace(ResourceLedger()),
        SourceSafetyWorkspace(ResourceLedger()),
    )
    handle = first.cylinder(6, 9)
    with pytest.raises(ValueError, match="different arena"):
        second.tail_boundary(handle)
    first.close()
    with pytest.raises(ValueError, match="closed"):
        first.tail_boundary(handle)


def test_research_driver_keeps_sign_and_global_safety_separate() -> None:
    report = tail_refinement(12, 2000)
    assert report["status"] == "FINITE_CURRENT_TAIL_BOUNDARIES"
    raw_records = report["records"]
    assert isinstance(raw_records, list)
    records = cast(list[object], raw_records)
    assert records
    final = records[-1]
    assert isinstance(final, dict)
    raw_boundaries = cast(object, final["boundaries"])
    assert isinstance(raw_boundaries, list)
    boundaries: list[object] = cast(list[object], raw_boundaries)
    rows: list[dict[str, object]] = []
    for entry in boundaries:
        assert isinstance(entry, dict)
        rows.append(cast(dict[str, object], entry))
    assert {entry["residue"] for entry in rows} == {521, 777, 2569}
    assert {entry["width"] for entry in rows} == {12}
    assert report["scope"] == "all_residues_current_tail"
    assert report["retained_nodes_after_close"] == 0
    assert report["global_safety_decided"] is False
    assert report["nonhalting_certified"] is False
    refused = tail_refinement(12, 2)
    assert refused["status"] == "BUDGET_EXHAUSTED"
    assert refused["retained_nodes_after_close"] == 0


@pytest.mark.parametrize("residue", (9, 13, 45))
def test_root_cone_uses_shared_partial_subtraction(residue: int) -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger())
    handle = workspace.cylinder(6, residue)
    a, b = workspace.root_boundary(handle)
    unit = RootSemifieldElement.one()
    dilation = RootSemifieldElement(ExactRational(3, 2))
    assert a.root_sum(b) == unit
    for bit in (0, 1):
        child = workspace.extend_run(handle, bit, 1)
        tail = workspace.tail_boundary(child)
        if min(tail.cone) < 0:
            with pytest.raises(ValueError, match="nonnegative"):
                workspace.root_boundary(child)
            with pytest.raises(ValueError, match="nonnegative"):
                unit.root_difference(dilation.multiply(b if bit else a))
        else:
            left, right = workspace.root_boundary(child)
            if bit:
                assert right == dilation.multiply(b)
                assert left == unit.root_difference(right)
            else:
                assert left == dilation.multiply(a)
                assert right == unit.root_difference(left)
    assert workspace.ledger.counters["safety_root_projections"] == 3
    assert workspace.ledger.counters["safety_root_projection_failures"] == 1
    assert workspace.ledger.counters["safety_root_operand_bits"] > 0
