"""Run-bound reuse of repository-policy results fails closed."""

from __future__ import annotations

import hashlib
import json
import sys
from pathlib import Path
from types import MappingProxyType

import pytest

from devtools.checks import policy_report_handoff
from devtools.checks.validation_policy import PYTEST_RUNNER_ENV
from devtools.git_source import GitSource
from devtools.runs import EvidenceRun


def _fixed_git_source(_root: Path) -> GitSource:
    return GitSource("commit-id", "tree-id", "sha1", False)


def _empty_tool_versions(_root: Path) -> dict[str, str]:
    return {}


def _policy_report() -> dict[str, object]:
    return {
        "max_source_lines": 1000,
        "clone_minimum_expression_statement_nodes": 24,
        "clone_minimum_statements": 3,
        "clone_minimum_single_statement_operations": 3,
        "source_line_violations": [],
        "isabelle_session_option_violations": [],
        "ownership_violations": [],
        "validation_entrypoint_violations": [],
        "semantic_name_violations": [],
        "border_registry_violations": [],
        "recursion_cycles": [],
        "duplicate_bodies": [],
        "package_violations": [],
    }


def _sealed_run(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[Path, Path, dict[str, str | bool], dict[str, object]]:
    root = tmp_path / "source"
    root.mkdir()
    run_path = tmp_path / "run-unique-1"
    run_path.mkdir()
    source: dict[str, str | bool] = {
        "git_commit": "commit-id",
        "git_tree": "tree-id",
        "git_object_format": "sha1",
        "git_dirty": False,
    }
    monkeypatch.setattr(policy_report_handoff, "git_source", _fixed_git_source)
    report_bytes = json.dumps(_policy_report(), sort_keys=True).encode("utf-8")
    (run_path / "policy.log").write_bytes(report_bytes)
    digest = hashlib.sha256(report_bytes).hexdigest()
    policy: dict[str, object] = {
        "name": "policy",
        "outcome": "completed",
        "process_outcome": "completed",
        "child_returncode": 0,
        "cleanup_confirmed": True,
        "cwd": str(root),
        "command": [sys.executable, "-m", "devtools.checks.repository_policy"],
        "git_source_before": source,
        "git_source_after": source,
        "git_state_stable_for_mode": True,
        "proof_generation": "policy-generation",
        "repository_policy_sha256": digest,
    }
    (run_path / "policy.json").write_text(json.dumps(policy), encoding="utf-8")
    token: dict[str, object] = {
        "version": 1,
        "run_path": str(run_path.resolve()),
        "run_id": run_path.name,
        "source_root": str(root.resolve()),
        "source": source,
        "pytest_generation": "pytest-generation",
        "policy_generation": "policy-generation",
        "sha256": digest,
    }
    monkeypatch.setenv(policy_report_handoff.POLICY_REPORT_ENV, json.dumps(token))
    monkeypatch.setenv(PYTEST_RUNNER_ENV, "pytest-generation")
    return root, run_path, source, token


def test_report_handoff_returns_immutable_tuple_schema(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root, _run_path, _source, _token = _sealed_run(tmp_path, monkeypatch)

    report = policy_report_handoff.load_policy_report(root)

    assert report is not None
    assert report["max_source_lines"] == 1000
    assert report["source_line_violations"] == ()
    assert report["duplicate_bodies"] == ()
    assert isinstance(report, MappingProxyType)


@pytest.mark.parametrize(
    "fault",
    (
        "digest",
        "run_id",
        "source_root",
        "source_tree",
        "pytest_generation",
        "policy_generation",
        "policy_outcome",
        "violations",
        "integer_schema",
    ),
)
def test_report_handoff_rejects_stale_or_forged_payloads(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fault: str
) -> None:
    root, run_path, _source, token = _sealed_run(tmp_path, monkeypatch)
    policy_path = run_path / "policy.json"
    policy = json.loads(policy_path.read_text(encoding="utf-8"))
    report_path = run_path / "policy.log"
    report = json.loads(report_path.read_text(encoding="utf-8"))

    if fault == "digest":
        token["sha256"] = "0" * 64
    elif fault == "run_id":
        token["run_id"] = "another-run"
    elif fault == "source_root":
        token["source_root"] = str(tmp_path / "other-source")
    elif fault == "source_tree":
        token_source = token["source"]
        assert isinstance(token_source, dict)
        token_source["git_tree"] = "stale-tree"
    elif fault == "pytest_generation":
        monkeypatch.setenv(PYTEST_RUNNER_ENV, "another-generation")
    elif fault == "policy_generation":
        token["policy_generation"] = "another-policy-generation"
    elif fault == "policy_outcome":
        policy["outcome"] = "failed"
        policy_path.write_text(json.dumps(policy), encoding="utf-8")
    elif fault == "violations":
        report["ownership_violations"] = ["injected violation"]
    elif fault == "integer_schema":
        report["max_source_lines"] = True
    if fault in {"violations", "integer_schema"}:
        report_bytes = json.dumps(report, sort_keys=True).encode("utf-8")
        report_path.write_bytes(report_bytes)
        digest = hashlib.sha256(report_bytes).hexdigest()
        token["sha256"] = digest
        policy["repository_policy_sha256"] = digest
        policy_path.write_text(json.dumps(policy), encoding="utf-8")
    monkeypatch.setenv(policy_report_handoff.POLICY_REPORT_ENV, json.dumps(token))

    assert policy_report_handoff.load_policy_report(root) is None


def test_report_handoff_is_absent_without_a_runner_token(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.delenv(policy_report_handoff.POLICY_REPORT_ENV, raising=False)
    monkeypatch.delenv(PYTEST_RUNNER_ENV, raising=False)

    assert policy_report_handoff.load_policy_report(tmp_path) is None


def test_producer_binds_owned_cwd_and_only_hands_off_for_all_suite(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    source = GitSource("commit-id", "tree-id", "sha1", False).as_dict()
    monkeypatch.setattr("devtools.git_source.git_source", _fixed_git_source)
    monkeypatch.setattr("devtools.runs.tool_versions", _empty_tool_versions)
    root = tmp_path / "source"
    root.mkdir()
    run = EvidenceRun(
        root=root,
        output_dir=tmp_path / "run-unique-1",
        command=(sys.executable, "-m", "devtools.checks.release", "--suite", "all"),
    )
    try:
        report_bytes = json.dumps(_policy_report(), sort_keys=True).encode("utf-8")
        (run.path / "policy.log").write_bytes(report_bytes)
        record: dict[str, object] = {
            "name": "policy",
            "outcome": "completed",
            "process_outcome": "completed",
            "child_returncode": 0,
            "cleanup_confirmed": True,
            "command": [sys.executable, "-m", "devtools.checks.repository_policy"],
            "git_source_before": source,
            "git_source_after": source,
            "git_state_stable_for_mode": True,
            "proof_generation": "policy-generation",
        }

        policy_report_handoff.bind_report(run, record)

        assert record["cwd"] == str(root.resolve())
        assert "repository_policy_sha256" in record
        run.manifest["steps"] = [record]
        environment = {policy_report_handoff.POLICY_REPORT_ENV: "inherited-forgery"}
        policy_report_handoff.configure(
            run, "unit", True, source, "pytest-generation", environment
        )
        assert policy_report_handoff.POLICY_REPORT_ENV not in environment

        policy_report_handoff.configure(
            run, "all", True, source, "pytest-generation", environment
        )
        token = json.loads(environment[policy_report_handoff.POLICY_REPORT_ENV])
        assert token["run_id"] == run.path.name
        assert token["source_root"] == str(root.resolve())
        assert token["policy_generation"] == "policy-generation"
        assert token["sha256"] == hashlib.sha256(report_bytes).hexdigest()
    finally:
        run.finish("completed")
