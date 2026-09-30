"""Validate reusable passing pytest evidence against this exact source tree."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

from devtools.paths import repository_root

FINGERPRINT_BEFORE = "number_compiler_source_before"
FINGERPRINT_AFTER = "number_compiler_source_after"
MANIFEST = "number_compiler_test_manifest"
NODE_ID = "number_compiler_nodeid"
EXECUTION_MODE = "number_compiler_execution_mode"
FINGERPRINT_VERSION = 5


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


def authored_source_paths(
    root: Path, *, include_directories: bool = False
) -> tuple[Path, ...]:
    """Canonical semantic inputs shared by fingerprints and revision guards."""
    paths = {root / "pyproject.toml"}
    if include_directories:
        paths.add(root)
    for folder in ("src", "tests", "devtools", "proofs"):
        if include_directories and (root / folder).is_dir():
            paths.add(root / folder)
        paths.update(
            path
            for path in (root / folder).rglob("*")
            if (path.is_file() or (include_directories and path.is_dir()))
            and path.name != ".DS_Store"
            and not any(
                part in {"__pycache__", ".mypy_cache", ".ruff_cache", ".pytest_cache"}
                for part in path.parts
            )
            and not any(part.endswith(".egg-info") for part in path.parts)
        )
    return tuple(
        path
        for path in sorted(paths)
        if path.is_file() or (include_directories and path.is_dir())
    )


def source_fingerprint(root: Path) -> str:
    digest = hashlib.sha256()
    digest.update(f"number-compiler-authored-source-v{FINGERPRINT_VERSION}\0".encode())
    for path in authored_source_paths(root):
        name, data = path.relative_to(root).as_posix().encode(), path.read_bytes()
        digest.update(len(name).to_bytes(8, "big"))
        digest.update(name)
        digest.update(len(data).to_bytes(8, "big"))
        digest.update(data)
    return digest.hexdigest()


def collect_required(root: Path, selectors: tuple[str, ...]) -> tuple[str, ...]:
    """Collect current exact node IDs without creating or warming an engine."""
    before = source_fingerprint(root)
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "pytest",
            "--collect-only",
            "-q",
            "-o",
            "addopts=",
            *minimal_selectors(selectors),
        ],
        cwd=root,
        capture_output=True,
        text=True,
        check=False,
        env=pytest_environment(),
    )
    if source_fingerprint(root) != before:
        raise ValueError("source tree changed during required test collection")
    if completed.returncode:
        raise ValueError(
            f"cannot collect required tests:\n{completed.stdout}\n{completed.stderr}"
        )
    return parse_collection(completed.stdout)


def parse_collection(output: str) -> tuple[str, ...]:
    """Decode the canonical pytest node list shared by guarded suite runners."""
    nodes = tuple(
        line.strip()
        for line in output.splitlines()
        if line.startswith("tests/") and "::" in line
    )
    if not nodes or len(set(nodes)) != len(nodes):
        raise ValueError("required test collection is empty or contains duplicates")
    return nodes


def validate_evidence(
    path: Path, root: Path, required: tuple[str, ...]
) -> dict[str, float]:
    """Return test durations only after rejecting stale or incomplete evidence."""
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
    fingerprint = source_fingerprint(root)
    if any(
        properties.get(name) != fingerprint
        for name in (FINGERPRINT_BEFORE, FINGERPRINT_AFTER)
    ):
        raise ValueError(
            "test evidence is stale or its source tree changed during execution"
        )
    manifest = json.loads(properties.get(MANIFEST, "null"))
    if (
        type(manifest) is not list
        or not manifest
        or any(type(node) is not str for node in manifest)
        or len(set(manifest)) != len(manifest)
    ):
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
    if not required or any(node not in tests for node in required):
        raise ValueError("test evidence is missing required regression nodes")
    return tests


def validate_serial_release(
    path: Path,
    root: Path,
    required: tuple[str, ...],
) -> dict[str, object]:
    """Assess the unfiltered serial release run, independently of query metrics.

    ``required`` must come from unfiltered collection on the current tree.
    A passing targeted run remains reusable audit evidence, but is not a full
    release run. Missing execution metadata cannot imply serial execution.
    """
    durations = validate_evidence(path, root, required)
    if set(durations) != set(required):
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
    return {
        "source_fingerprint": source_fingerprint(root),
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
    # Callers cannot supply a selected manifest to the release command.
    required = collect_required(root, ("tests",))
    report = validate_serial_release(options.junit, root, required)
    print(json.dumps(report, indent=2))
    return 0 if report["serial_time_gate_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
