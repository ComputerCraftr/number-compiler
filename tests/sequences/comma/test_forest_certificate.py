"""Finite forest evidence and fail-closed public A367620 admission."""

from __future__ import annotations

from tests.support.comma_oracles import assert_phase_period

import json
import gzip
from pathlib import Path

import pytest

from devtools.experiments.comma.forest_certificate import (
    ROOTS,
    _boundary_children,
    _literal_children,
    _parent_if_any,
    _phase_period,
    evidence_summary,
)
from devtools.experiments.comma.closed_region_certificate import (
    generate_closed_region,
    verify_closed_region,
)
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma.certificates import (
    CERTIFIED_MAX_INDEX,
    UnresolvedCommaTerm,
    certificate_status,
    require_certified_index,
)


def test_finite_forest_and_first_fork_are_reproducible() -> None:
    expected = json.loads(
        (
            Path(__file__).parents[3]
            / "devtools/experiments/comma/forest_evidence.json"
        ).read_text(encoding="utf-8")
    )
    actual = evidence_summary()
    assert actual["roots_exhausted"] == expected["excluded_roots_exhausted"]
    for name in (
        "sector_entries",
        "boundary_steps",
        "maximum_decimal_digits",
        "trace_sha256",
        "first_fork_value",
        "first_fork_children",
        "charged_work",
    ):
        assert actual[name] == expected[name]
    assert actual["first_fork_index"] == expected["first_fork_index_one_based"]
    assert actual["formal_prefix_checked"] is False


def test_boundary_formula_matches_independent_nine_candidate_rule() -> None:
    for exponent in (2, 3, 10, 100):
        scale = 10**exponent
        for f in range(1, 10):
            boundary = (f + 1) * scale if f < 9 else 10 * scale
            for k in range(max(f * scale, boundary - 110), boundary):
                assert _boundary_children(k, f, scale) == _literal_children(k)


def test_phase_period_matches_independent_literal_word() -> None:
    assert_phase_period(_phase_period)


def test_small_root_partition_has_every_child_once() -> None:
    for n in range(1, 100):
        parents = [k for k in range(1, n) if n in _literal_children(k)]
        assert len(parents) <= 1
        assert (_parent_if_any(n) is None) == (n in ROOTS)
        assert parents == ([] if n in ROOTS else [_parent_if_any(n)])


def test_every_three_digit_node_has_the_pinned_smaller_parent() -> None:
    for n in range(100, 1000):
        parent = _parent_if_any(n)
        assert parent is not None and 0 < parent < n
        assert n in _literal_children(parent)


def test_public_certificate_rejects_beyond_checked_prefix() -> None:
    assert 20 in ROOTS and len(ROOTS) == 50
    ledger = ResourceLedger()
    beyond = CERTIFIED_MAX_INDEX + 1
    status = certificate_status(beyond, ledger, 1_000_000)
    assert status["status"] == "unknown"
    assert status["certified_max_index"] == CERTIFIED_MAX_INDEX
    assert status["isabelle_instance_checked"] is False
    with pytest.raises(UnresolvedCommaTerm) as error:
        require_certified_index(beyond, ledger, 1_000_000)
    assert error.value.diagnostic()["requested_index"] == beyond
    assert ledger.counters == {"comma_certificate_work": 1}


def test_right_fork_closed_region_certificate_is_independently_checked(
    tmp_path: Path,
) -> None:
    path = tmp_path / "right-child.jsonl.gz"
    generated = generate_closed_region(path, include_excluded_roots=False)
    checked = verify_closed_region(path)
    assert generated == checked
    assert checked.entries == 405
    assert checked.boundary_steps == 2466
    assert checked.maximum_decimal_digits == 40
    assert checked.maximum_boundary_run == 15


def test_closed_region_checker_rejects_changed_phase_count(tmp_path: Path) -> None:
    path = tmp_path / "right-child.jsonl.gz"
    generate_closed_region(path, include_excluded_roots=False)
    with gzip.open(path, "rt", encoding="ascii") as stream:
        lines = stream.readlines()
    first = json.loads(lines[1])
    first["cycles"] += 1
    lines[1] = json.dumps(first, sort_keys=True, separators=(",", ":")) + "\n"
    with gzip.open(path, "wt", encoding="ascii") as stream:
        stream.writelines(lines)
    with pytest.raises(ValueError, match="cycle count"):
        verify_closed_region(path)
