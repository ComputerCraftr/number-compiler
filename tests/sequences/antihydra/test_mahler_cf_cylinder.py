"""Independent rational checks for the finite powers-of-five CF cylinder."""

from fractions import Fraction

import pytest

from number_compiler.arithmetic.automata.carry_spacetime_trace import Pow5SpatialTrace
from number_compiler.arithmetic.fields.ordered_matrix import Matrix2
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.antihydra.mahler_continued_fraction_cylinder import (
    continued_fraction_cylinder,
)
from number_compiler.sequences.antihydra.mahler_pow5_ordered_blocks import (
    Pow5OrderedBlock,
    Pow5OrderedBlockSource,
)
from tests.sequences.antihydra.test_mahler_continued_fraction import literal_matrix


def literal_forces(
    matrix: tuple[tuple[int, int], tuple[int, int]], horizon: int
) -> bool:
    (q, previous_q), (p, previous_p) = matrix
    left, right = sorted((Fraction(p, q), Fraction(p + previous_p, q + previous_q)))
    for _ in range(horizon):
        if not 0 <= left < right <= Fraction(1, 2):
            return False
        if right <= Fraction(1, 3):
            left, right = 3 * left / 2, 3 * right / 2
        elif left >= Fraction(1, 3):
            left, right = (3 * left - 1) / 2, (3 * right - 1) / 2
        else:
            return False
    return 0 <= left < right <= Fraction(1, 2)


def literal_cylinder(
    horizon: int, budget: int
) -> tuple[int, tuple[tuple[int, int], tuple[int, int]]]:
    """Read one physical coefficient at a time and restart the literal test."""
    digits: list[int] = []
    exponent = 1
    while len(digits) < budget:
        for char in str(int.__pow__(5, exponent)):
            if len(digits) == budget:
                break
            digits.append(int(char))
            matrix = literal_matrix(digits)
            if literal_forces(matrix, horizon):
                return len(digits), matrix
        exponent += 1
    raise AssertionError("literal fixture exhausted")


@pytest.mark.parametrize("horizon", (0, 1, 3, 10, 20, 32, 64, 96, 128, 256, 512))
def test_cylinder_uses_the_first_decisive_physical_prefix(horizon: int) -> None:
    expected_count, expected_matrix = literal_cylinder(horizon, 500)
    result = continued_fraction_cylinder(horizon, 500, ledger=ResourceLedger())
    assert result["status"] == "available"
    assert result["coefficient_count"] == expected_count
    assert result["matrix"] == expected_matrix
    assert result["horizon"] == horizon
    (q, previous_q), (p, previous_p) = expected_matrix
    low, high = sorted((Fraction(p, q), Fraction(p + previous_p, q + previous_q)))
    assert result["fraction_lower"] == {
        "numerator": low.numerator,
        "denominator": low.denominator,
    }
    assert result["fraction_upper"] == {
        "numerator": high.numerator,
        "denominator": high.denominator,
    }


def test_cylinder_returns_unknown_when_budget_exhausted() -> None:
    ledger = ResourceLedger()
    result = continued_fraction_cylinder(100, 1, ledger=ledger)
    assert result["status"] == "unknown"
    assert result["coefficient_count"] == 1
    assert ledger.nodes == 0


@pytest.mark.parametrize(("max_nodes", "already_used"), [(512, 0), (10000, 1)])
def test_tight_remaining_budget_keeps_pointed_source(
    max_nodes: int, already_used: int, monkeypatch: pytest.MonkeyPatch
) -> None:
    def eager_block(
        _source: Pow5OrderedBlockSource, _rows: int, _limit: int
    ) -> Pow5OrderedBlock:
        pytest.fail("packed lookahead must follow capacity admission")

    monkeypatch.setattr(Pow5OrderedBlockSource, "next_block", eager_block)
    ledger = ResourceLedger(max_nodes=max_nodes)
    owner = ledger.register("test live owner", "cf test")
    ledger.reserve(owner, nodes=already_used)
    result = continued_fraction_cylinder(20, 64, ledger=ledger)
    count, matrix = literal_cylinder(20, 64)
    assert result["coefficient_count"] == count
    assert result["matrix"] == matrix
    assert ledger.nodes == already_used
    assert ledger.entries == 0


def test_full_horizon_cylinder_is_decisive_at_exactly_its_last_coefficient(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    blocks: list[Pow5OrderedBlock] = []
    refined_blocks: list[Pow5OrderedBlock] = []
    next_block = Pow5OrderedBlockSource.next_block
    segment = Pow5OrderedBlock.segment

    def issued(
        source: Pow5OrderedBlockSource, max_rows: int, max_coefficients: int
    ) -> Pow5OrderedBlock:
        result = next_block(source, max_rows, max_coefficients)
        blocks.append(result)
        return result

    def refined(block: Pow5OrderedBlock, start: int, length: int) -> Matrix2:
        assert 0 < length < block.coefficient_count
        refined_blocks.append(block)
        return segment(block, start, length)

    monkeypatch.setattr(Pow5OrderedBlockSource, "next_block", issued)
    monkeypatch.setattr(Pow5OrderedBlock, "segment", refined)
    ledger = ResourceLedger(max_nodes=10_000)
    result = continued_fraction_cylinder(4096, 20000, ledger=ledger)
    assert result["status"] == "available"
    assert len(blocks) < 39
    assert refined_blocks and all(block is blocks[-1] for block in refined_blocks)
    count = result["coefficient_count"]
    assert isinstance(count, int) and count == 540
    digits: list[int] = []
    exponent = 1
    while len(digits) < count:
        digits.extend(int(char) for char in str(int.__pow__(5, exponent)))
        exponent += 1
    expected = literal_matrix(digits[:count])
    assert result["matrix"] == expected
    assert literal_forces(expected, 4096)
    assert not literal_forces(literal_matrix(digits[: count - 1]), 4096)
    assert ledger.nodes == ledger.entries == 0


def test_full_horizon_consumes_spatial_children_and_compact_word(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    issued: list[tuple[int, int]] = []
    action = Pow5SpatialTrace.issue

    def watch(
        trace: Pow5SpatialTrace, packed: int, width: int, span: int
    ) -> tuple[tuple[int, int], ...]:
        issued.append((width, span))
        return action(trace, packed, width, span)

    def forbidden(*_args: object, **_kwargs: object) -> None:
        pytest.fail("a spatial cylinder must fold its issued ordered coefficients")

    monkeypatch.setattr(Pow5SpatialTrace, "issue", watch)
    monkeypatch.setattr(Pow5OrderedBlockSource, "_geometric_rows", forbidden)
    monkeypatch.setattr(
        "number_compiler.arithmetic.automata.ledgered_slp.LedgerSLPArena.terminal",
        forbidden,
    )
    ledger = ResourceLedger(max_nodes=10_000)
    found = continued_fraction_cylinder(4096, 20_000, ledger=ledger)
    assert found["status"] == "available"
    assert found["coefficient_count"] == 540
    assert any(width + span > 16 and span > 1 for width, span in issued)
    assert ledger.nodes == ledger.entries == 0


@pytest.mark.parametrize(
    ("horizon", "uses_spatial"), [(0, False), (63, False), (64, True), (65, True)]
)
def test_short_horizon_spatial_admission(
    horizon: int, uses_spatial: bool, monkeypatch: pytest.MonkeyPatch
) -> None:
    issued = 0
    action = Pow5SpatialTrace.issue

    def watch(
        trace: Pow5SpatialTrace, packed: int, width: int, span: int
    ) -> tuple[tuple[int, int], ...]:
        nonlocal issued
        issued += 1
        return action(trace, packed, width, span)

    monkeypatch.setattr(Pow5SpatialTrace, "issue", watch)
    ledger = ResourceLedger(max_nodes=10_000)
    result = continued_fraction_cylinder(horizon, 64, ledger=ledger)
    count, matrix = literal_cylinder(horizon, 64)
    assert result["status"] == "available"
    assert result["coefficient_count"] == count
    assert result["matrix"] == matrix
    assert bool(issued) is uses_spatial
    assert ledger.nodes == ledger.entries == 0
