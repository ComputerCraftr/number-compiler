"""Share a guarded all-suite policy result with its actual pytest consumer."""

from __future__ import annotations

import hashlib
import json
import os
import sys
from collections.abc import Mapping
from pathlib import Path
from types import MappingProxyType
from typing import TYPE_CHECKING

from devtools.checks.validation_policy import PYTEST_RUNNER_ENV
from devtools.git_source import git_source
from number_compiler.arithmetic.contracts.input_validation import (
    is_object_list,
    string_keyed_mapping,
)

if TYPE_CHECKING:
    from devtools.runs import EvidenceRun

POLICY_REPORT_ENV = "NUMBER_COMPILER_POLICY_REPORT_HANDOFF"
_DIGEST_FIELD = "repository_policy_sha256"
_MAX_BYTES = 8 * 1024**2
_LIMITS = (
    "max_source_lines",
    "clone_minimum_expression_statement_nodes",
    "clone_minimum_statements",
    "clone_minimum_single_statement_operations",
)
_GATES = (
    "source_line_violations",
    "isabelle_session_option_violations",
    "ownership_violations",
    "validation_entrypoint_violations",
    "semantic_name_violations",
    "border_registry_violations",
    "recursion_cycles",
    "duplicate_bodies",
    "package_violations",
)
_TOKEN_FIELDS = {
    "version",
    "run_path",
    "run_id",
    "source_root",
    "source",
    "pytest_generation",
    "policy_generation",
    "sha256",
}


def _unique_json(pairs: list[tuple[str, object]]) -> dict[str, object]:
    obj = dict(pairs)
    if len(obj) != len(pairs):
        raise ValueError("duplicate repository policy evidence key")
    return obj


def _read(path: Path) -> bytes:
    if not path.is_file():
        raise ValueError("repository policy evidence is not a regular file")
    with path.open("rb") as handle:
        raw = handle.read(_MAX_BYTES + 1)
    if len(raw) > _MAX_BYTES:
        raise ValueError("repository policy evidence exceeds its size bound")
    return raw


def _successful_policy(
    record: Mapping[str, object], source: Mapping[str, object], root: Path
) -> bool:
    return (
        source.get("git_dirty") is False
        and record.get("name") == "policy"
        and record.get("outcome") == record.get("process_outcome") == "completed"
        and type(record.get("child_returncode")) is int
        and record.get("child_returncode") == 0
        and record.get("cleanup_confirmed") is True
        and record.get("cwd") == str(root)
        and record.get("command")
        == [sys.executable, "-m", "devtools.checks.repository_policy"]
        and record.get("git_source_before") == record.get("git_source_after") == source
        and record.get("git_state_stable_for_mode") is True
    )


def bind_report(run: EvidenceRun, record: dict[str, object]) -> None:
    """Bind the report bytes at the end of the guarded policy step."""
    if record.get("name") != "policy":
        return
    command = run.manifest.get("command")
    if not is_object_list(command) or not any(
        token == "--suite=all" or command[index : index + 2] == ["--suite", "all"]
        for index, token in enumerate(command)
    ):
        return
    # execute() ran the guarded command from this evidence run's checkout.
    record["cwd"] = str(run.root)
    source = string_keyed_mapping(run.manifest.get("git_source_before"))
    if source is not None and _successful_policy(record, source, run.root):
        try:
            record[_DIGEST_FIELD] = hashlib.sha256(
                _read(run.path / "policy.log")
            ).hexdigest()
        except (OSError, ValueError):
            # The normal independent policy fixture remains available.
            return


def configure(
    run: EvidenceRun,
    name: str,
    pytest_run: bool,
    source: Mapping[str, object],
    generation: str,
    environment: dict[str, str],
) -> None:
    """Pass only this run's recognized report to its serial all-suite child."""
    environment.pop(POLICY_REPORT_ENV, None)
    if (
        name != "all"
        or not pytest_run
        or source != run.manifest.get("git_source_before")
    ):
        return
    steps = run.manifest.get("steps")
    if not is_object_list(steps):
        return
    records = tuple(string_keyed_mapping(step) for step in steps)
    policies = tuple(
        record
        for record in records
        if record is not None and record.get("name") == "policy"
    )
    if len(policies) != 1:
        return
    policy = policies[0]
    digest, issued = policy.get(_DIGEST_FIELD), policy.get("proof_generation")
    if not isinstance(digest, str) or not isinstance(issued, str):
        return
    if not _successful_policy(policy, source, run.root):
        return
    environment[POLICY_REPORT_ENV] = json.dumps(
        {
            "version": 1,
            "run_path": str(run.path),
            "run_id": run.path.name,
            "source_root": str(run.root),
            "source": dict(source),
            "pytest_generation": generation,
            "policy_generation": issued,
            "sha256": digest,
        }
    )


def load_policy_report(root: Path) -> Mapping[str, object] | None:
    """Load a sealed passing report, or leave the fixture to check independently."""
    raw = os.environ.get(POLICY_REPORT_ENV)
    generation = os.environ.get(PYTEST_RUNNER_ENV)
    if raw is None or not generation:
        return None
    root = root.resolve()
    try:
        token = string_keyed_mapping(json.loads(raw, object_pairs_hook=_unique_json))
        if (
            token is None
            or set(token) != _TOKEN_FIELDS
            or type(token["version"]) is not int
            or token["version"] != 1
            or token["source_root"] != str(root)
            or token["pytest_generation"] != generation
        ):
            return None
        path_value = token["run_path"]
        if not isinstance(path_value, str):
            return None
        path = Path(path_value).resolve(strict=True)
        if str(path) != path_value or token["run_id"] != path.name:
            return None
        source = git_source(root).as_dict()
        if source != token["source"]:
            return None
        step = string_keyed_mapping(
            json.loads(_read(path / "policy.json"), object_pairs_hook=_unique_json)
        )
        if (
            step is None
            or not _successful_policy(step, source, root)
            or step.get(_DIGEST_FIELD) != token["sha256"]
            or step.get("proof_generation") != token["policy_generation"]
        ):
            return None
        report_bytes = _read(path / "policy.log")
        if hashlib.sha256(report_bytes).hexdigest() != token["sha256"]:
            return None
        return _freeze_report(report_bytes)
    except (OSError, RuntimeError, ValueError):
        return None


def _freeze_report(raw: bytes) -> Mapping[str, object] | None:
    report = string_keyed_mapping(json.loads(raw, object_pairs_hook=_unique_json))
    if report is None or set(report) != {*_LIMITS, *_GATES}:
        return None
    if any(type(report[key]) is not int for key in _LIMITS):
        return None
    if any(report[key] != [] for key in _GATES):
        return None
    return MappingProxyType(
        {
            **{key: report[key] for key in _LIMITS},
            **{key: () for key in _GATES},
        }
    )
