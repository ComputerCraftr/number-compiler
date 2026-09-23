"""Independent scope checks for the bounded joint source audit."""

from __future__ import annotations

import sys
from typing import Any, cast

import pytest

from devtools.experiments.antihydra.barrier_search import main
from devtools.experiments.antihydra.future_grammar import ReachableFutureGrammar
from devtools.experiments.antihydra.joint_future_quotient import (
    _row,
    audit_collatz_sources,
    audit_joint_future,
)
from devtools.experiments.antihydra.source_safety import SourceSafetyWorkspace
from number_compiler.arithmetic.fields.branch_quotients import (
    BranchChoiceSuffix,
    PrimeBucketWorkspace,
)
from number_compiler.resources.ledger import ResourceLedger


def test_joint_refinement_reports_only_observed_reuse() -> None:
    result = audit_joint_future(depth=8, max_event=3, primes=(5, 7, 11))
    typed = cast(dict[str, Any], result)
    assert typed["rows"] == 45
    assert typed["truncated_legal_domains"] > 0
    assert typed["refinements"]["deck"]["diagnostic_conflicts"] > 0
    assert (
        typed["refinements"]["deck"]["first_diagnostic_conflict"]["first"]["source"] > 0
    )
    assert typed["refinements"]["deck_suffix"]["repeated_keys"] > 0
    assert typed["refinements"]["full"]["repeated_keys"] == 0
    assert result["all_time_safety_certified"] is False
    assert result["source_occurrences_merged"] is False
    assert typed["work"]["joint_source_rows"] == typed["rows"]


def test_high_fiber_probe_exposes_parameterized_endpoint_difference() -> None:
    result = cast(
        dict[str, Any],
        audit_joint_future(
            depth=8,
            max_event=3,
            primes=(5, 7, 11),
            high_fiber_probes=True,
        ),
    )
    assert result["rows"] == 156
    assert result["distinct_coarse_outputs"] == 2
    assert sum(item["count"] for item in result["coarse_output_histogram"]) == 156
    full = result["refinements"]["full"]
    assert full["repeated_keys"] > 0
    assert full["conflicts"] == 0
    assert full["diagnostic_conflicts"] > 0
    witness = full["first_diagnostic_conflict"]
    assert witness["first"]["high_fiber_probe"] != witness["second"]["high_fiber_probe"]
    assert witness["first"]["event_endpoint"] != witness["second"]["event_endpoint"]
    assert result["retained_nodes"] == result["retained_entries"] == 0


def test_fractional_probe_finds_exact_fixed_key_safety_conflict() -> None:
    result = cast(
        dict[str, Any],
        audit_joint_future(
            depth=8,
            primes=(5, 7, 11),
            fractional_probes=True,
        ),
    )
    assert result["status"] == "FINITE_CONFLICT"
    assert result["distinct_coarse_outputs"] > 2
    assert result["work"]["joint_fraction_safe_intersections"] > 0
    full = result["refinements"]["full"]
    assert full["conflicts"] > 0
    assert result["refinements"]["fraction_exact_diagnostic"]["conflicts"] == 0
    assert "not the fixed blank-tape" in result["witness_scope"]
    witness = full["first_conflict"]
    assert witness["first"]["source"] == witness["second"]["source"]
    assert witness["first"]["fraction"] != witness["second"]["fraction"]
    assert witness["first_output"][1] != witness["second_output"][1]
    assert result["retained_nodes"] == result["retained_entries"] == 0


def test_joint_rejects_forged_choice_and_foreign_source() -> None:
    ledger = ResourceLedger(max_nodes=10000, max_cache_entries=10000)
    workspace = SourceSafetyWorkspace(ledger, max_width=6)
    grammar = ReachableFutureGrammar(workspace, max_event=3)
    parent = grammar.root
    child = grammar.edge(parent, 1).child
    bank = PrimeBucketWorkspace(ledger)
    mahler = {5: bank.partition("mahler", 5)}
    collatz = {5: bank.partition("collatz", 5)}
    bank.close()
    from devtools.experiments.antihydra.event_domain import (
        source_event_exponent_domain,
    )

    domain = source_event_exponent_domain(workspace, parent)
    with pytest.raises(ValueError, match="source-admitted menu"):
        _row(
            grammar,
            parent,
            child,
            1,
            (2,),
            domain,
            BranchChoiceSuffix(),
            BranchChoiceSuffix(),
            1,
            mahler,
            collatz,
        )
    foreign = SourceSafetyWorkspace(
        ResourceLedger(max_nodes=10000, max_cache_entries=10000), max_width=6
    )
    with pytest.raises((TypeError, ValueError)):
        grammar.edge(foreign.cylinder(0, 0), 1)


def test_collatz_audit_derives_its_own_accelerated_q() -> None:
    result = audit_collatz_sources(max_odd_source=31, primes=(5, 7))
    typed = cast(dict[str, Any], result)
    assert result["rows"] == 16
    assert result["shared_mahler_q_claimed"] is False
    assert typed["work"]["joint_collatz_source_rows"] == 16
    assert result["all_time_safety_certified"] is False


def test_joint_budget_refusal_cleans_all_workspace_owners() -> None:
    for result in (
        audit_joint_future(depth=2, primes=(5,), max_nodes=1),
        audit_collatz_sources(max_odd_source=31, primes=(5,), max_nodes=1),
    ):
        typed = cast(dict[str, Any], result)
        assert result["status"] == "BUDGET_EXHAUSTED"
        assert result["rows"] == 0
        assert result["retained_nodes"] == 0
        assert result["retained_entries"] == 0
        assert typed["work"]["joint_budget_refusals"] == 1


def test_existing_barrier_entry_point_exposes_joint_mode(
    monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(
        sys, "argv", ["barrier_search", "--mode", "joint", "--rounds", "2"]
    )
    main()
    import json

    report: dict[str, Any] = json.loads(capsys.readouterr().out)
    assert report["mahler"]["event_bound"] == 3
    assert report["collatz"]["source_horizon"] == 255

    monkeypatch.setattr(
        sys,
        "argv",
        [
            "barrier_search",
            "--mode",
            "joint",
            "--joint-depth",
            "9",
            "--joint-collatz-sources",
            "127",
        ],
    )
    main()
    expanded: dict[str, Any] = json.loads(capsys.readouterr().out)
    assert expanded["mahler"]["records"][-1]["depth"] == 9
    assert expanded["collatz"]["rows"] == 64
