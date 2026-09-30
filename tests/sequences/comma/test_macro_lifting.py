"""Adversarial checks for symbolic exponent-ray certificate obligations."""

import json
from dataclasses import replace
from pathlib import Path

import pytest

from devtools.experiments.comma.boundary_quotient_audit import (
    generate_shard,
    summarize_shards,
)
from devtools.experiments.comma.macro_lifting import check_macro_lifting
from number_compiler.sequences.comma.boundary_quotient import (
    AffineWeight,
    BoundaryState,
    construct_macro,
)


def test_lifting_checks_all_prefixes_and_both_fork_children() -> None:
    macro = construct_macro(BoundaryState("N", 2, 10))
    assert check_macro_lifting(macro) == len(macro.sector_fragments)
    with pytest.raises(ValueError, match="missing or reordered fork alternatives"):
        check_macro_lifting(replace(macro, ordered_children=macro.ordered_children[:1]))
    bad_prefix = (
        macro.prefix_weights[0],
        AffineWeight(0, 0, 1),
    ) + macro.prefix_weights[2:]
    with pytest.raises(ValueError, match="partial-selection prefix"):
        check_macro_lifting(replace(macro, prefix_weights=bad_prefix))


def test_matching_sample_weight_does_not_certify_a_symbolic_macro() -> None:
    macro = construct_macro(BoundaryState("N", 2, 10))
    sample_only = AffineWeight(0, macro.weight.evaluate(10), 1)
    assert sample_only.evaluate(10) == macro.weight.evaluate(10)
    assert sample_only.evaluate(934) != macro.weight.evaluate(934)
    with pytest.raises(ValueError, match="terminal elapsed weight"):
        check_macro_lifting(replace(macro, weight=sample_only))


def test_forged_cycle_guard_or_phase_cannot_lift() -> None:
    macro = construct_macro(BoundaryState("Z", 4, 12))
    assert check_macro_lifting(macro) > 0
    index = next(i for i, f in enumerate(macro.sector_fragments) if f.period)
    fragment = macro.sector_fragments[index]
    for forged in (
        replace(fragment, maximum_guard=fragment.maximum_guard - 1),
        replace(fragment, entering_digit=(fragment.entering_digit + 1) % 10),
    ):
        fragments = (
            macro.sector_fragments[:index]
            + (forged,)
            + macro.sector_fragments[index + 1 :]
        )
        with pytest.raises(ValueError, match="cycle transfer|phase binding"):
            check_macro_lifting(replace(macro, sector_fragments=fragments))


def test_landmine_certificate_cannot_publish_a_child() -> None:
    macro = construct_macro(BoundaryState("Z", 4, 12))
    assert macro.outcome == "landmine"
    with pytest.raises(ValueError, match="landmine has a successor"):
        check_macro_lifting(
            replace(macro, ordered_children=(BoundaryState("N", 2, 14),))
        )


def test_near_run_lifting_rejects_hidden_crossing_and_wrong_weight() -> None:
    macro = construct_macro(BoundaryState("Z", 2, 10))
    assert check_macro_lifting(macro) > 0
    index = next(i for i, f in enumerate(macro.sector_fragments) if f.literal_steps > 1)
    fragment = macro.sector_fragments[index]
    for forged in (
        replace(fragment, literal_increment=fragment.literal_increment + 1),
        replace(fragment, literal_steps=fragment.literal_steps + 10),
    ):
        fragments = (
            macro.sector_fragments[:index]
            + (forged,)
            + macro.sector_fragments[index + 1 :]
        )
        with pytest.raises(ValueError, match="Near run"):
            check_macro_lifting(replace(macro, sector_fragments=fragments))


@pytest.mark.parametrize(
    "row,reason",
    [
        ([True, [], 0, 1], "unordered"),
        ([0, [1], 0, 1], "incomplete comma fork"),
        ([0, [1, 1], 1, 1], "unbound comma fork"),
        ([0, [], -1, 1], "construction counts"),
        ([0, [], 0, 0], "construction counts"),
    ],
)
def test_audit_merge_rejects_malformed_or_partial_alternatives(
    tmp_path: Path, row: list[object], reason: str
) -> None:
    path = tmp_path / "shard.json"
    path.write_text(json.dumps({"schema": 1, "start": 0, "stop": 1, "rows": [row]}))
    with pytest.raises(ValueError, match=reason):
        summarize_shards([path])


def test_audit_merge_requires_complete_unique_state_coverage(tmp_path: Path) -> None:
    path = tmp_path / "shard.json"
    path.write_text(json.dumps(generate_shard(0, 1)))
    with pytest.raises(ValueError, match="incomplete comma quotient audit"):
        summarize_shards([path])
    with pytest.raises(ValueError, match="duplicate comma quotient state"):
        summarize_shards([path, path])
