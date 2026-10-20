"""Complete physical boundary coverage, independently checked by integers."""

import pytest

from number_compiler.arithmetic.functions.finite_observer import (
    minimize_finite_observer,
)
from number_compiler.sequences.collatz.decimal_boundary import (
    physical_boundary_edge,
    physical_digit_successor,
)


def test_all_twenty_guards_cover_the_fifteen_physical_edges() -> None:
    edges: set[tuple[int, int]] = set()
    for residue in range(20):
        for high in (1, 2, 31):
            source = 20 * high + residue
            edge = physical_boundary_edge(source)
            target = 3 * source + 1 if source & 1 else source // 2
            assert edge.residue20 == residue
            assert edge.source_digit == source % 10
            assert edge.inward_bit == (source // 10) % 2
            assert edge.target_digit == target % 10
            edges.add((edge.source_digit, edge.target_digit))
    assert len(edges) == 15


def test_present_digit_observation_has_ten_moore_classes() -> None:
    rows = tuple(
        tuple(physical_digit_successor(digit, inward) for inward in (0, 1))
        for digit in range(10)
    )
    minimized = minimize_finite_observer(rows, tuple(range(10)))
    assert minimized.classes == 10


@pytest.mark.parametrize(("digit", "inward"), ((True, 0), (10, 0), (0, True), (0, 2)))
def test_physical_boundary_rejects_unadmitted_ports(digit: int, inward: int) -> None:
    with pytest.raises(ValueError):
        physical_digit_successor(digit, inward)
