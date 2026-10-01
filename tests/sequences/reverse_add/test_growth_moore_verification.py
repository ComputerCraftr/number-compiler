"""The finite G161/P7 audit preserves D5 outputs and open terminal kinds."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from devtools.verification import exact_oracle
from devtools.verification._reverse_growth_moore_tables import load_growth_tables
from devtools.verification.reverse_growth_moore import (
    ABSENT_RESULT,
    EXIT_RESULT,
    G161_CLASS_COUNT,
    G161_TRANSITIONS,
    GROWTH_REFINEMENT_HISTORY,
    P7_Q11_GROUPS,
    Q11_TO_P7,
    BoundedGrowthWordAction,
    GrowthAbsent,
    GrowthExit,
    audit_d5_growth_projection,
    audit_growth_moore,
    growth_action_for_p7_word,
)


def test_growth_refinement_is_the_g161_p7_fixed_point() -> None:
    with exact_oracle():
        report = audit_growth_moore()
    assert GROWTH_REFINEMENT_HISTORY == (
        2,
        21,
        78,
        120,
        142,
        153,
        158,
        160,
        161,
        161,
    )
    assert G161_CLASS_COUNT == 161
    assert report["growth_ports"] == 7
    assert Q11_TO_P7 == (0, 1, 2, 3, 4, 5, 6, 6, 6, 6, 6)
    assert P7_Q11_GROUPS == (
        (0,),
        (1,),
        (2,),
        (3,),
        (4,),
        (5,),
        (6, 7, 8, 9, 10),
    )
    assert report["source_selected_schedule"] is False
    assert report["production_admission"] is False


def test_g161_projection_matches_each_literal_d5_source_and_return() -> None:
    with exact_oracle():
        report = audit_d5_growth_projection()
    assert report.source_fields == report.projected_successors == 3610
    assert (report.growth_rows, report.no_growth_rows, report.exit_rows) == (
        1805,
        1805,
        1805,
    )
    assert report.absent_columns > 0
    assert report.production_admission is False


def test_exit_and_absent_are_distinct_typed_weighted_terminals() -> None:
    assert type(EXIT_RESULT) is GrowthExit
    assert type(ABSENT_RESULT) is GrowthAbsent
    assert any(type(target) is GrowthExit for row in G161_TRANSITIONS for target in row)
    assert any(
        type(target) is GrowthAbsent for row in G161_TRANSITIONS for target in row
    )

    with exact_oracle():
        suffix = BoundedGrowthWordAction.primitive(0)
        for terminal_type in (GrowthExit, GrowthAbsent):
            state, port = next(
                (state, port)
                for state, row in enumerate(G161_TRANSITIONS)
                for port, target in enumerate(row)
                if type(target) is terminal_type
            )
            first = BoundedGrowthWordAction.primitive(port)
            result = first.then(suffix).at(state)
            assert type(result.target) is terminal_type
            assert result.steps == 1


def test_weighted_p7_power_composes_finite_lanes_without_a_retained_word() -> None:
    with exact_oracle():
        unit = growth_action_for_p7_word((0, 5, 6))
        powered = unit.power(25)
        reference = BoundedGrowthWordAction.identity()
        for _ in range(25):
            reference = reference.then(unit)
    assert powered == reference
    assert len(powered.targets) == len(powered.growth) == len(powered.steps) == 161
    assert "word" not in powered.__dataclass_fields__


def test_growth_table_fixture_loader_preserves_tuple_shapes_and_rejects_corruption(
    tmp_path: Path,
) -> None:
    fixture_path = (
        Path(__file__).resolve().parents[3]
        / "devtools"
        / "verification"
        / "data"
        / "reverse_growth_g161.json"
    )
    payload = json.loads(fixture_path.read_text(encoding="utf-8"))
    tables = load_growth_tables()
    assert len(tables.temporal_transitions) == tables.temporal_t191_classes == 191
    assert all(
        len(row) == tables.spatial_q11_classes for row in tables.temporal_transitions
    )
    assert len(tables.d5_macro_pairs) == 930
    assert len(tables.d5_field_to_macro) == 3610

    payload["TEMPORAL_TRANSITIONS"][0][0] = True
    corrupted_path = tmp_path / "corrupted-growth.json"
    corrupted_path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(ValueError, match="exact integer"):
        load_growth_tables(corrupted_path)
