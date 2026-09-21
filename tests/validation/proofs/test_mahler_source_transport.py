"""Exact independent references for joint source/high-fiber safety transport."""

from dataclasses import replace
from fractions import Fraction

import pytest

from devtools.experiments.antihydra.barrier_search import fractional_refinement
from devtools.experiments.antihydra.source_safety import (
    SourceSafetyWorkspace,
    event_prime_lanes,
    source_event,
)
from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.arithmetic.fields.consumer_pullback import ExactRational as Q
from number_compiler.resources.ledger import ResourceLedger


def _bounds(source: int, steps: int) -> tuple[int, Fraction, Fraction, int, int]:
    d, lo, hi, scale, ledger, minimum = (
        source,
        Fraction(0),
        Fraction(1, 2),
        Fraction(1),
        0,
        0,
    )
    for _ in range(steps):
        ledger += 2 if d % 2 else -1
        minimum = min(minimum, ledger)
        d = (3 * d + 1) // 2
        scale *= Fraction(3, 2)
        lo = max(lo, d / scale - source)
        hi = min(hi, (d + Fraction(1, 2)) / scale - source)
    return d, lo, hi, ledger, minimum


def _f(value: Q) -> Fraction:
    return Fraction(value.numerator, value.denominator)


@pytest.mark.parametrize("width", (0, 1, 2, 3, 6, 12))
def test_complete_cylinder_census_against_independent_intersection(width: int) -> None:
    ledger = ResourceLedger(max_nodes=20000, max_cache_entries=40000)
    workspace = SourceSafetyWorkspace(ledger)
    survivors = set()
    for r in range(1 << width):
        block = workspace.view(workspace.cylinder(width, r))
        d, lo, hi, balance, minimum = _bounds(r, width)
        assert (block.endpoint, block.ledger_delta, block.ledger_minimum) == (
            d,
            balance,
            minimum,
        )
        assert block.guard.empty == (lo >= hi)
        if lo < hi:
            assert (_f(block.guard.lower), _f(block.guard.upper)) == (lo, hi)
            survivors.add(r)
        assert _f(block.fractional.scale) == Fraction(3, 2) ** width
        assert _f(block.fractional.offset) == Fraction(3, 2) ** width * r - d
    if width == 12:
        assert len(survivors) == 201
        assert {r % 64 for r in survivors} == {
            0,
            4,
            6,
            9,
            13,
            14,
            16,
            20,
            21,
            24,
            30,
            32,
            37,
            45,
            46,
            52,
            53,
            56,
        }
    assert ledger.nodes == ledger.counters["safety_blocks_constructed"]


@pytest.mark.parametrize("source", (0, 1, 7, 64, 4095, 2**100 + 37))
def test_symbolic_high_fiber_and_parenthesizations(source: int) -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger())
    width = 12
    whole = workspace.cylinder(width, source % (1 << width))
    block = workspace.view(whole)
    d, lo, hi, delta, minimum = _bounds(source, width)
    assert block.endpoint + 3**width * (source >> width) == d
    assert block.ledger_delta == delta and block.ledger_minimum == minimum
    if lo < hi:
        assert (_f(block.guard.lower), _f(block.guard.upper)) == (lo, hi)
    for split in range(1, width):
        first = workspace.cylinder(split, source % (1 << split))
        middle = _bounds(source, split)[0]
        second = workspace.cylinder(width - split, middle % (1 << (width - split)))
        assert workspace.compose(first, second) == whole
    before = dict(workspace.ledger.counters)
    assert workspace.cylinder(width, source % (1 << width)) == whole
    assert (
        workspace.ledger.counters["safety_blocks_constructed"]
        == before["safety_blocks_constructed"]
    )


def test_workspace_authority_and_atomic_budget_refusal() -> None:
    first = SourceSafetyWorkspace(ResourceLedger())
    second = SourceSafetyWorkspace(ResourceLedger())
    with pytest.raises(ValueError, match="different arena"):
        second.view(first.cylinder(1, 0))
    ledger = ResourceLedger(max_nodes=0)
    limited = SourceSafetyWorkspace(ledger, max_width=12)
    with pytest.raises(BlockContextBudgetExceeded):
        limited.cylinder(1, 0)
    assert ledger.entries == ledger.nodes == 0
    with pytest.raises(BlockContextBudgetExceeded):
        limited.cylinder(10**9, 0)
    assert ledger.entries == ledger.nodes == 0


def test_source_event_selects_one_root_branch_and_correlates_prime_lanes() -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger())
    event = source_event(workspace, 2, Q(1, 4))
    assert (event.exponent, event.endpoint, event.next_fraction) == (2, 5, Q(1, 16))
    assert all(
        before != 0 and after != 0 for _, before, after in event_prime_lanes(event)
    )
    # The archive's q=3 and q=4 children of w=1 are in its unrestricted tree,
    # but their original real-x prefixes fail; q=3 even has a safe endpoint.
    for source in (4, 8):
        with pytest.raises(ValueError, match="fractional safety guard"):
            source_event(workspace, source, Q(1, 4))
    with pytest.raises(ValueError, match="exponent"):
        event_prime_lanes(replace(event, exponent=3))
    with pytest.raises(ValueError, match="source binding"):
        event_prime_lanes(replace(event, endpoint=6))


def test_closed_zero_boundary_and_non_dyadic_scope() -> None:
    event = source_event(SourceSafetyWorkspace(ResourceLedger()), 1, Q(1, 3))
    assert event.next_fraction == Q(0)
    with pytest.raises(ValueError, match="dyadic"):
        event_prime_lanes(event)


def test_guarded_refinement_preserves_all_families_and_does_not_certify_infinity() -> (
    None
):
    result = fractional_refinement(2, 1000)
    records = result["records"]
    assert isinstance(records, list)
    assert [row["nonempty_cylinders"] for row in records] == [18, 201]
    assert result["status"] == "FINITE_PREFIXES_ONLY"
    assert result["global_safety_decided"] is False
    assert result["nonhalting_certified"] is False
    refused = fractional_refinement(2, 1)
    assert refused["status"] == "BUDGET_EXHAUSTED"
    assert refused["records"] == []


def test_two_workspaces_can_share_a_ledger_without_sharing_authority() -> None:
    ledger = ResourceLedger()
    first, second = SourceSafetyWorkspace(ledger), SourceSafetyWorkspace(ledger)
    a, b = first.cylinder(2, 0), second.cylinder(2, 0)
    assert first.view(a) == second.view(b)
    with pytest.raises(ValueError, match="different arena"):
        first.view(b)


@pytest.mark.parametrize("source", range(1, 65))
def test_event_guard_is_source_selected_not_supplied_menu(source: int) -> None:
    workspace = SourceSafetyWorkspace(ResourceLedger())
    q = (source & -source).bit_length()
    _, lo, hi, _, _ = _bounds(source, q)
    for t in (lo, (lo + hi) / 2, hi):
        fraction = Q(t.numerator, t.denominator)
        if lo <= t < hi:
            event = source_event(workspace, source, fraction)
            assert event.exponent == q
            assert _f(event.next_fraction) == Fraction(3, 2) ** q * t - Fraction(1, 2)
        else:
            with pytest.raises(ValueError, match="fractional safety guard"):
                source_event(workspace, source, fraction)
