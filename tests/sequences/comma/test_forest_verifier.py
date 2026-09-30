"""Focused unit tests for the production streaming forest checker."""

from __future__ import annotations

import gzip
import json
from pathlib import Path
from typing import Any

import pytest

from number_compiler.arithmetic.contracts.block_effect import BlockContextBudgetExceeded
from number_compiler.resources.ledger import ResourceLedger
from number_compiler.sequences.comma.forest_verifier import (
    _check_forest_row,
    _literal_children,
    _parse_line,
    _phase_period,
    _prefix_to_first_fork,
    _small_roots,
    verify_forest_certificate,
)
from tests.support.comma_oracles import assert_phase_period


def _canonical_line(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
        + "\n"
    ).encode("ascii")


def _packaged_first_rows() -> tuple[dict[str, Any], dict[str, Any]]:
    path = (
        Path(__file__).parents[3]
        / "src/number_compiler/kernels/comma_prefix_v1.jsonl.gz"
    )
    with gzip.open(path, "rt", encoding="ascii") as stream:
        header = json.loads(stream.readline())
        row = json.loads(stream.readline())
    assert type(header) is dict and type(row) is dict
    return header, row


def _write_records(
    path: Path,
    header: dict[str, Any],
    row: dict[str, Any] | None = None,
) -> None:
    with gzip.open(path, "wb") as stream:
        stream.write(_canonical_line(header))
        if row is not None:
            stream.write(_canonical_line(row))


def test_production_checker_recomputes_root_partition_and_first_fork() -> None:
    ledger = ResourceLedger()
    roots = _small_roots(ledger, 2_000)
    assert len(roots) == 50
    assert 20 in roots
    assert _literal_children(20) == (22,)

    index, value, children, _ = _prefix_to_first_fork(ledger, 20_000)
    assert (index, value, children) == (
        412_987_859,
        19_999_999_918,
        (19_999_999_999, 20_000_000_000),
    )


def test_canonical_json_parser_rejects_duplicate_keys_and_noncanonical_lines() -> None:
    assert _parse_line(b'{"a":1,"b":2}\n') == {"a": 1, "b": 2}
    with pytest.raises(ValueError, match="duplicate JSON key"):
        _parse_line(b'{"a":1,"a":1}\n')
    with pytest.raises(ValueError, match="not canonical"):
        _parse_line(b'{ "a": 1}\n')


def test_phase_period_matches_literal_decimal_child_recurrence() -> None:
    assert_phase_period(_phase_period)


def test_near_boundary_zero_cycle_row_does_not_apply_skip_guard() -> None:
    ledger = ResourceLedger()
    row = {
        "source": "190",
        "entry": "190",
        "cycles": 0,
        "boundary_steps": 2,
        "exits": ["203"],
    }
    assert _check_forest_row(row, 190, 190, ledger, 100) == (203,)


def test_failed_header_check_releases_frontier_reservations(tmp_path: Path) -> None:
    path = tmp_path / "malformed.jsonl.gz"
    with gzip.open(path, "wb") as stream:
        stream.write(b'{"schema":"wrong"}\n')
    ledger = ResourceLedger(max_nodes=128)
    with pytest.raises(ValueError, match="unsupported comma forest"):
        verify_forest_certificate(path, ledger, 20_000)
    assert ledger.entries == 0
    assert ledger.nodes == 0
    assert all(not row.entries and not row.nodes for row in ledger.inventory())


def test_truncated_forest_after_header_releases_seed_frontier(tmp_path: Path) -> None:
    header, _ = _packaged_first_rows()
    path = tmp_path / "truncated.jsonl.gz"
    _write_records(path, header)
    verifier_ledger = ResourceLedger(max_nodes=128)
    with pytest.raises(ValueError, match="truncated or oversized"):
        verify_forest_certificate(path, verifier_ledger, 20_000)
    assert verifier_ledger.entries == 0
    assert verifier_ledger.nodes == 0


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        ("missing-root", "source partition"),
        ("missing-right-child", "source partition"),
        ("wrong-prefix-index", "prefix differs"),
        ("wrong-prefix-children", "prefix differs"),
    ],
)
def test_header_mutations_are_rejected_before_frontier_publication(
    tmp_path: Path, mutation: str, message: str
) -> None:
    header, _ = _packaged_first_rows()
    sources = list(header["sources"])
    prefix = dict(header["prefix"])
    altered = dict(header)
    if mutation == "missing-root":
        sources.pop(0)
        altered["sources"] = sources
    elif mutation == "missing-right-child":
        sources.pop()
        altered["sources"] = sources
    elif mutation == "wrong-prefix-index":
        prefix["index"] += 1
        altered["prefix"] = prefix
    else:
        prefix["children"] = ["19999999999"]
        altered["prefix"] = prefix
    path = tmp_path / f"{mutation}.jsonl.gz"
    _write_records(path, altered)
    ledger = ResourceLedger(max_nodes=128)
    with pytest.raises(ValueError, match=message):
        verify_forest_certificate(path, ledger, 20_000)
    assert ledger.entries == 0
    assert ledger.nodes == 0


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        ("forged-exits", "literal expansion"),
        ("wrong-cycles", "literal expansion"),
        ("extra-field", "malformed comma forest row"),
    ],
)
def test_forged_or_incomplete_first_row_is_rejected_and_released(
    tmp_path: Path, mutation: str, message: str
) -> None:
    header, row = _packaged_first_rows()
    altered = dict(row)
    if mutation == "forged-exits":
        altered["exits"] = [*altered["exits"], "999"]
    elif mutation == "wrong-cycles":
        altered["cycles"] += 1
    else:
        altered["unbound"] = True
    path = tmp_path / f"{mutation}.jsonl.gz"
    _write_records(path, header, altered)
    ledger = ResourceLedger(max_nodes=128)
    with pytest.raises(ValueError, match=message):
        verify_forest_certificate(path, ledger, 20_000)
    assert ledger.entries == 0
    assert ledger.nodes == 0


def test_budget_refusal_is_charged_without_partial_frontier(tmp_path: Path) -> None:
    path = tmp_path / "unread.jsonl.gz"
    with gzip.open(path, "wb") as stream:
        stream.write(b"unused\n")
    ledger = ResourceLedger(max_nodes=128)
    with pytest.raises(BlockContextBudgetExceeded):
        verify_forest_certificate(path, ledger, 10)
    assert ledger.entries == 0
    assert ledger.nodes == 0
    assert ledger.counters["comma_certificate_budget_refusals"] == 1


def test_expected_hash_is_checked_before_frontier_publication(tmp_path: Path) -> None:
    path = tmp_path / "wrong-hash.jsonl.gz"
    with gzip.open(path, "wb") as stream:
        stream.write(b"unused\n")
    ledger = ResourceLedger()
    with pytest.raises(ValueError, match="checksum"):
        verify_forest_certificate(path, ledger, 2_000, expected_sha256="0" * 64)
    assert ledger.entries == 0
    assert ledger.nodes == 0
