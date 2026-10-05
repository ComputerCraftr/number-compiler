"""Independent word checks for the candidate recursive comma observation."""

from __future__ import annotations

from itertools import product

import pytest

from devtools.verification.comma_pair_language import (
    PAIR_IDENTITY,
    PairLanguage,
    audit_pair_quotients,
    even_port_key,
    pair_block_levels,
    physical_port_leaf,
)
from number_compiler.arithmetic.carry.carry_monoid import CarryFn


def _literal_language(sums: tuple[int, ...]) -> PairLanguage:
    defects = tuple(value - 9 for value in sums)
    live = tuple(value for value in defects if value)
    domain = (
        CarryFn.ID if not live else CarryFn.CONST1 if live[-1] > 0 else CarryFn.CONST0
    )
    return PairLanguage(
        len(sums) % 4,
        domain,
        sum(defects) % 2,
        sum(value * 2**i for i, value in enumerate(defects)) % 5,
        None if not live else (live[0] + 9) // 2 % 5,
    )


def test_recursive_merge_matches_all_three_leaf_words_and_parenthesizations() -> None:
    for values in product(range(19), repeat=3):
        a, b, c = (PairLanguage.leaf(value) for value in values)
        expected = _literal_language(values)
        assert a.then(b).then(c) == a.then(b.then(c)) == expected
        assert PAIR_IDENTITY.then(expected) == expected.then(PAIR_IDENTITY) == expected
    # Long neutral prefixes change the skew phase, never the first defect.
    neutral = PairLanguage.leaf(9)
    for _ in range(12):
        neutral = neutral.then(neutral)
    assert neutral.first is None
    assert neutral.then(PairLanguage.leaf(18)).first == 4


@pytest.mark.parametrize("level", range(11))
def test_completed_child_pair_blocks_match_independent_physical_trace(
    level: int,
) -> None:
    for block in pair_block_levels(level)[-1]:
        f, d = block.leading, block.source
        value = d
        weight = 0
        sums = []
        middle = None
        for position in range(block.width):
            previous = (value - f) % 10
            if position == block.width // 2:
                middle = (value + previous) // 2 % 5
            sums.append(value + previous)
            weight += value + int(9 - f <= value < 9) if f < 9 else value + 1
            value = previous or (10 - f)
        assert block.endpoint == value
        assert block.weight == weight
        assert block.language == _literal_language(tuple(sums))
        assert block.midpoint == middle


def test_q86_is_a_reduced_weighted_response_not_an_exact_occurrence() -> None:
    rows = audit_pair_quotients()
    assert rows[0].reduced_actions == 90
    assert rows[0].punctured_conflicts > 0
    for row in rows[1:]:
        assert row.reduced_actions == row.candidate_classes == 86
        assert row.midpoint_classes == row.first_defect_classes == 86
        assert row.punctured_conflicts == 0
        assert row.exact_occurrences == 90
        assert row.endpoint_conflicts == 4
    assert rows[1].bare_residue_conflicts == 0
    assert {row.bare_residue_conflicts for row in rows[2:]} == {9}


def test_even_sector_five_alias_needs_occurrence_for_partial_selection() -> None:
    lower, upper = physical_port_leaf(5, 1), physical_port_leaf(5, 6)
    assert lower.weight == 1
    assert upper.weight == 7
    a, b = lower.then(upper), upper.then(lower)
    assert a.weight == b.weight == 8
    assert (a.endpoint, b.endpoint) == (1, 6)
    # At row 1, the lower occurrence has left its first child; the upper has not.
    assert not 1 < lower.weight
    assert 1 < upper.weight
    assert a.then(a).weight == b.then(b).weight == 16
    with pytest.raises(ValueError, match="seam bindings"):
        a.then(b)


@pytest.mark.parametrize("value", [-1, 19, True, 1.5])
def test_pair_language_rejects_non_decimal_leaf(value: int) -> None:
    with pytest.raises(ValueError, match="decimal sum"):
        PairLanguage.leaf(value)


def test_even_response_key_preserves_recursive_endpoint_and_weight() -> None:
    for layer in pair_block_levels(10)[1:]:
        responses: dict[tuple[int, int], tuple[tuple[int, int], int]] = {}
        for block in layer:
            key = even_port_key(block.leading, block.source)
            response = even_port_key(block.leading, block.endpoint), block.weight
            assert responses.setdefault(key, response) == response
        assert len(responses) == 86
    # Width one is deliberately excluded from this congruence.
    assert even_port_key(5, 1) == even_port_key(5, 6)
    assert physical_port_leaf(5, 1).weight != physical_port_leaf(5, 6).weight
