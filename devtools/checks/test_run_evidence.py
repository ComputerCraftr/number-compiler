"""Validate reusable passing pytest evidence against this exact source tree."""

from __future__ import annotations

import argparse
import json
import os
import xml.etree.ElementTree as ET
from collections.abc import Mapping
from pathlib import Path

from devtools.git_source import git_source
from devtools.paths import repository_root
from devtools.report_values import object_list, string_keyed_mapping

GIT_COMMIT_BEFORE = "number_compiler_git_commit_before"
GIT_COMMIT_AFTER = "number_compiler_git_commit_after"
GIT_TREE_BEFORE = "number_compiler_git_tree_before"
GIT_TREE_AFTER = "number_compiler_git_tree_after"
GIT_OBJECT_FORMAT_BEFORE = "number_compiler_git_object_format_before"
GIT_OBJECT_FORMAT_AFTER = "number_compiler_git_object_format_after"
GIT_DIRTY_BEFORE = "number_compiler_git_dirty_before"
GIT_DIRTY_AFTER = "number_compiler_git_dirty_after"
PROVENANCE_MODE = "number_compiler_provenance_mode"
PROVENANCE_MODE_ENV = "NUMBER_COMPILER_EVIDENCE_MODE"
MANIFEST = "number_compiler_test_manifest"
NODE_ID = "number_compiler_nodeid"
EXECUTION_MODE = "number_compiler_execution_mode"


def _string_list(value: object) -> tuple[str, ...] | None:
    if not object_list(value):
        return None
    result: list[str] = []
    for item in value:
        if type(item) is not str:
            return None
        result.append(item)
    return tuple(result)


def _json_object_list(value: object) -> tuple[Mapping[str, object], ...] | None:
    if not object_list(value):
        return None
    result: list[Mapping[str, object]] = []
    for item in value:
        mapping = string_keyed_mapping(item)
        if mapping is None:
            return None
        result.append(mapping)
    return tuple(result)


def _step_runs_command(value: Mapping[str, object], expected: str) -> bool:
    command = value.get("command")
    commands = _string_list(command)
    return commands is not None and expected in commands


def classify_execution_mode(
    *,
    parallel: bool,
    keyword: str,
    mark_expression: str,
    deselected: bool,
    last_failed: bool,
    collection_args: tuple[str, ...],
) -> str:
    """Classify pytest evidence without treating a selected run as complete.

    The two maintained partitions have deliberately exact marker expressions.
    Any additional selection, alternate marker expression, or narrower path is
    ordinary targeted evidence.  The repository root selector is equivalent to
    pytest's configured default test path; a subdirectory or node ID is not.
    """
    if parallel:
        return "parallel"
    root_selection = collection_args in ((), ("tests",))
    if keyword or deselected or last_failed or not root_selection:
        return "serial-selected"
    normalized_mark = " ".join(mark_expression.split())
    if normalized_mark == "not validation":
        return "serial-unit"
    if normalized_mark == "validation":
        return "serial-validation"
    if not normalized_mark:
        return "serial-unfiltered"
    return "serial-selected"


def pytest_environment() -> dict[str, str]:
    environment = dict(os.environ)
    environment.pop("PYTEST_ADDOPTS", None)
    environment.pop("PYTEST_PLUGINS", None)
    environment["PYTEST_DISABLE_PLUGIN_AUTOLOAD"] = "1"
    return environment


def minimal_selectors(selectors: tuple[str, ...]) -> tuple[str, ...]:
    """A requested file already includes its separately listed test functions."""
    unique = tuple(dict.fromkeys(selectors))
    return tuple(
        selector
        for selector in unique
        if not any(
            selector != other and (selector.startswith((other + "::", other + "[")))
            for other in unique
        )
    )


def validate_evidence(
    path: Path,
    root: Path,
    required: tuple[str, ...] | None = None,
    *,
    require_clean: bool = True,
    require_acceptance: bool = False,
    require_acceptance_verified: bool | None = None,
) -> dict[str, float]:
    """Validate JUnit and return durations; acceptance reuse requires a run manifest.

    ``require_acceptance_verified=False`` is reserved for the release runner's
    in-flight JUnit check, before detached-worktree cleanup has completed.
    """
    tree = ET.parse(path).getroot()
    suites = tuple(tree.iter("testsuite"))
    if len(suites) != 1:
        raise ValueError("evidence requires one complete pytest suite")
    suite = suites[0]
    properties: dict[str, str] = {}
    for prop in suite.findall("./properties/property"):
        key = prop.get("name", "")
        if key in properties:
            raise ValueError("duplicate evidence property")
        properties[key] = prop.get("value", "")
    live = git_source(root)
    before = (
        properties.get(GIT_COMMIT_BEFORE),
        properties.get(GIT_TREE_BEFORE),
        properties.get(GIT_OBJECT_FORMAT_BEFORE),
        properties.get(GIT_DIRTY_BEFORE),
    )
    after = (
        properties.get(GIT_COMMIT_AFTER),
        properties.get(GIT_TREE_AFTER),
        properties.get(GIT_OBJECT_FORMAT_AFTER),
        properties.get(GIT_DIRTY_AFTER),
    )
    live_revision = (live.commit, live.tree, live.object_format)
    before_revision = before[:3]
    after_revision = after[:3]
    mode = properties.get(PROVENANCE_MODE)
    must_be_clean = require_clean or require_acceptance or mode == "acceptance"
    if (
        (must_be_clean and (live.dirty or before[3] != "false" or after[3] != "false"))
        or mode not in {"development", "acceptance"}
        or (require_acceptance and mode != "acceptance")
        or before_revision != live_revision
        or after_revision != live_revision
    ):
        raise ValueError("test evidence is dirty, stale, or changed during execution")
    manifest_value: object = json.loads(properties.get(MANIFEST, "null"))
    manifest = _string_list(manifest_value)
    if manifest is None:
        raise ValueError("test evidence has no complete unique collection manifest")
    if not manifest or len(set(manifest)) != len(manifest):
        raise ValueError("test evidence has no complete unique collection manifest")
    if any(int(suite.get(key, "0")) for key in ("errors", "failures", "skipped")):
        raise ValueError("test evidence contains failed, skipped, or errored tests")
    tests: dict[str, float] = {}
    for case in suite.findall("testcase"):
        if any(case.find(tag) is not None for tag in ("failure", "error", "skipped")):
            raise ValueError("test evidence contains an unsuccessful test case")
        names = [
            prop.get("value", "")
            for prop in case.findall("./properties/property")
            if prop.get("name") == NODE_ID
        ]
        if len(names) != 1 or not names[0] or names[0] in tests:
            raise ValueError("test evidence has a missing or duplicate scoped node ID")
        duration = float(case.get("time", "0"))
        if not 0 <= duration < float("inf"):
            raise ValueError("test evidence has invalid duration")
        tests[names[0]] = duration
    if len(tests) != int(suite.get("tests", "-1")) or set(manifest) != set(tests):
        raise ValueError("test results do not cover their complete collection manifest")
    expected_nodes = tuple(manifest) if required is None else required
    if not expected_nodes or any(node not in tests for node in expected_nodes):
        raise ValueError("test evidence is missing required regression nodes")
    verify_acceptance = (
        (require_acceptance or mode == "acceptance")
        if require_acceptance_verified is None
        else require_acceptance_verified
    )
    if verify_acceptance:
        if mode != "acceptance":
            raise ValueError("reusable evidence requires acceptance provenance")
        _validate_acceptance_manifest(path, live)
    return tests


def _validate_acceptance_manifest(path: Path, source: object) -> None:
    """Bind reusable JUnit to its completed, verified run manifest."""
    from devtools.git_source import GitSource

    if not isinstance(source, GitSource):
        raise TypeError("source must be a GitSource")
    manifest_path = path.parent / "manifest.json"
    try:
        manifest_value: object = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ValueError("reusable evidence has no readable run manifest") from error
    manifest = string_keyed_mapping(manifest_value)
    if manifest is None:
        raise ValueError("run manifest must contain a JSON object")
    if (
        manifest.get("evidence_mode") != "acceptance"
        or manifest.get("outcome") != "completed"
        or manifest.get("acceptance_verified") is not True
        or manifest.get("cacheable") is not True
        or manifest.get("reusable") is not True
    ):
        raise ValueError("run manifest has not verified acceptance completion")
    before = string_keyed_mapping(manifest.get("git_source_before"))
    after = string_keyed_mapping(manifest.get("git_source_after"))
    expected = source.as_dict()
    if (
        before is None
        or after is None
        or before != after
        or before != expected
        or before.get("git_dirty") is not False
    ):
        raise ValueError("run manifest Git source is not clean and current")
    expected_xml = str(path.resolve())
    steps = _json_object_list(manifest.get("steps"))
    if steps is None or not any(
        _step_runs_command(step, f"--junitxml={expected_xml}") for step in steps
    ):
        raise ValueError("run manifest does not bind this JUnit selection")


def validate_serial_release(
    path: Path,
    root: Path,
    required: tuple[str, ...] | None = None,
    *,
    require_clean: bool = True,
    require_acceptance: bool = False,
    require_acceptance_verified: bool | None = None,
) -> dict[str, object]:
    """Assess the unfiltered serial release run, independently of query metrics.

    ``required`` must come from unfiltered collection on the current tree.
    A passing targeted run remains reusable audit evidence, but is not a full
    release run. Missing execution metadata cannot imply serial execution.
    The unverified-acceptance override is only for that in-flight runner path.
    """
    durations = validate_evidence(
        path,
        root,
        required,
        require_clean=require_clean,
        require_acceptance=require_acceptance,
        require_acceptance_verified=require_acceptance_verified,
    )
    if required is not None and set(durations) != set(required):
        raise ValueError("serial release requires the exact unfiltered test manifest")
    suite = next(ET.parse(path).getroot().iter("testsuite"))
    properties = {
        prop.get("name"): prop.get("value")
        for prop in suite.findall("./properties/property")
    }
    if properties.get(EXECUTION_MODE) != "serial-unfiltered":
        raise ValueError("serial release requires recorded unfiltered serial execution")
    raw_time = suite.get("time")
    if raw_time is None:
        raise ValueError("serial release has no complete-suite duration")
    suite_seconds = float(raw_time)
    if not 0 <= suite_seconds < float("inf"):
        raise ValueError("serial release has invalid complete-suite duration")
    slowest = sorted(durations.items(), key=lambda item: (-item[1], item[0]))[:20]
    source = git_source(root)
    properties = {
        prop.get("name"): prop.get("value")
        for prop in suite.findall("./properties/property")
    }
    acceptance = properties.get(PROVENANCE_MODE) == "acceptance"
    acceptance_verified = acceptance and require_acceptance_verified is not False
    return {
        **source.as_dict(),
        "provenance_mode": properties.get(PROVENANCE_MODE),
        "acceptance_verified": acceptance_verified,
        "cacheable": acceptance_verified and not source.dirty,
        "reusable": acceptance_verified and not source.dirty,
        "execution_mode": "serial-unfiltered",
        "test_count": len(durations),
        "complete_suite_seconds": suite_seconds,
        "serial_ceiling_seconds": 300,
        "serial_time_gate_passed": suite_seconds < 300,
        "slowest_testcase": {"nodeid": slowest[0][0], "seconds": slowest[0][1]},
        "slowest_20_seconds": sum(seconds for _, seconds in slowest),
        "slowest_20": [
            {"nodeid": node, "seconds": seconds} for node, seconds in slowest
        ],
    }


def main() -> int:
    """Validate an existing run; never execute or warm its test runtimes."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("junit", type=Path)
    options = parser.parse_args()
    root = repository_root()
    report = validate_serial_release(options.junit, root, require_acceptance=True)
    print(json.dumps(report, indent=2))
    return 0 if report["serial_time_gate_passed"] else 1


if __name__ == "__main__":
    from devtools.runs import run_reported

    raise SystemExit(run_reported(main))
