"""Audit evidence must prove current complete coverage without another orbit."""

from __future__ import annotations

import json
import xml.etree.ElementTree as ET
from pathlib import Path
from typing import TYPE_CHECKING

import pytest

from devtools.checks.test_run_evidence import (
    EXECUTION_MODE,
    FINGERPRINT_AFTER,
    FINGERPRINT_BEFORE,
    MANIFEST,
    NODE_ID,
    classify_execution_mode,
    source_fingerprint,
    validate_evidence,
    validate_serial_release,
)

if TYPE_CHECKING:
    import pathlib
    import xml.etree.ElementTree


def report(
    tmp_path: Path,
) -> tuple[
    pathlib.Path, pathlib.Path, xml.etree.ElementTree.Element[str], tuple[str, str]
]:
    root = tmp_path / "tree"
    (root / "src").mkdir(parents=True)
    (root / "src" / "a.py").write_text("value = 1\n")
    fingerprint = source_fingerprint(root)
    nodes = ("tests/test_a.py::test_a", "tests/test_a.py::test_b[0]")
    suite = ET.Element("testsuite", tests="2", failures="0", errors="0", skipped="0")
    properties = ET.SubElement(suite, "properties")
    for name, value in (
        (FINGERPRINT_BEFORE, fingerprint),
        (FINGERPRINT_AFTER, fingerprint),
        (MANIFEST, json.dumps(nodes)),
    ):
        ET.SubElement(properties, "property", name=name, value=value)
    for node in nodes:
        case = ET.SubElement(suite, "testcase", time="0.5")
        props = ET.SubElement(case, "properties")
        ET.SubElement(props, "property", name=NODE_ID, value=node)
    path = tmp_path / "run.xml"
    return root, path, suite, nodes


def save(path: pathlib.Path, suite: xml.etree.ElementTree.Element[str]) -> None:
    ET.ElementTree(suite).write(path)


def test_complete_frozen_evidence_is_reusable_without_warming_an_engine(
    tmp_path: Path,
) -> None:
    root, path, suite, nodes = report(tmp_path)
    save(path, suite)
    assert validate_evidence(path, root, nodes) == dict.fromkeys(nodes, 0.5)


@pytest.mark.parametrize(
    "mutation",
    (
        "source",
        "during",
        "missing_manifest",
        "manifest_omission",
        "missing_case",
        "missing_nodeid",
        "duplicate",
        "skip",
        "failure",
        "error",
        "count",
    ),
)
def test_missing_stale_or_unsuccessful_evidence_cannot_pass(
    tmp_path: Path, mutation: str
) -> None:
    root, path, suite, nodes = report(tmp_path)
    if mutation == "source":
        (root / "src" / "a.py").write_text("value = 2\n")
    elif mutation == "during":
        _required(
            suite, './properties/property[@name="' + FINGERPRINT_AFTER + '"]'
        ).set("value", "stale")
    elif mutation == "missing_manifest":
        props = _required(suite, "properties")
        assert props is not None
        props.remove(_required(props, 'property[@name="' + MANIFEST + '"]'))
    elif mutation == "manifest_omission":
        _required(suite, './properties/property[@name="' + MANIFEST + '"]').set(
            "value", json.dumps(nodes[:1])
        )
    elif mutation == "missing_case":
        suite.remove(suite.findall("testcase")[1])
    elif mutation == "missing_nodeid":
        case = _required(suite, "testcase")
        assert case is not None
        case.remove(_required(case, "properties"))
    elif mutation == "duplicate":
        _required(suite.findall("testcase")[1], "./properties/property").set(
            "value", nodes[0]
        )
    elif mutation in ("skip", "failure", "error"):
        ET.SubElement(
            _required(suite, "testcase"), "skipped" if mutation == "skip" else mutation
        )
    else:
        suite.set("tests", "3")
    save(path, suite)
    with pytest.raises(ValueError):
        validate_evidence(path, root, nodes)


def test_passing_subrun_cannot_claim_an_unexecuted_required_case(
    tmp_path: Path,
) -> None:
    root, path, suite, nodes = report(tmp_path)
    save(path, suite)
    with pytest.raises(ValueError, match="missing required"):
        validate_evidence(path, root, nodes + ("tests/test_new.py::test_new",))


@pytest.mark.parametrize(
    "manifest",
    (
        "pyproject.toml",
        "src/number_compiler/__init__.py",
        "devtools/checks/package_contracts.py",
        "devtools/experiments/power_numbers/special_successor_generators.py",
    ),
)
def test_package_contract_changes_invalidate_passing_evidence(
    tmp_path: Path, manifest: str
) -> None:
    root, path, suite, nodes = report(tmp_path)
    save(path, suite)
    target = root / manifest
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text("changed package contract\n")
    with pytest.raises(ValueError, match="stale"):
        validate_evidence(path, root, nodes)


@pytest.mark.parametrize(
    "seconds,passed", [("299.99", True), ("300", False), ("377.85", False)]
)
def test_serial_release_reports_actual_suite_time_and_strict_ceiling(
    tmp_path: Path, seconds: str, passed: bool
) -> None:
    root, path, suite, nodes = report(tmp_path)
    suite.set("time", seconds)
    ET.SubElement(
        _required(suite, "properties"),
        "property",
        name=EXECUTION_MODE,
        value="serial-unfiltered",
    )
    save(path, suite)
    result = validate_serial_release(path, root, nodes)
    assert result["serial_time_gate_passed"] is passed
    assert result["complete_suite_seconds"] == float(seconds)
    assert result["slowest_20_seconds"] == 1.0
    assert result["slowest_testcase"] == {"nodeid": nodes[0], "seconds": 0.5}


@pytest.mark.parametrize(
    "mode", [None, "parallel", "serial-selected", "serial-unit", "serial-validation"]
)
def test_release_cannot_infer_unfiltered_serial_execution(
    tmp_path: Path, mode: None | str
) -> None:
    root, path, suite, nodes = report(tmp_path)
    suite.set("time", "1.0")
    if mode is not None:
        ET.SubElement(
            _required(suite, "properties"), "property", name=EXECUTION_MODE, value=mode
        )
    save(path, suite)
    with pytest.raises(ValueError, match="recorded unfiltered serial"):
        validate_serial_release(path, root, nodes)


@pytest.mark.parametrize(
    ("mark_expression", "collection_args", "mode"),
    (
        ("not validation", (), "serial-unit"),
        ("not validation", ("tests",), "serial-unit"),
        ("validation", (), "serial-validation"),
        ("", ("tests",), "serial-unfiltered"),
        ("validation and proof", (), "serial-selected"),
        ("not validation", ("tests/api",), "serial-selected"),
        ("", ("tests/test_api.py::test_one",), "serial-selected"),
    ),
)
def test_execution_mode_distinguishes_partitions_from_complete_and_targeted_runs(
    mark_expression: str, collection_args: tuple[str, ...], mode: str
) -> None:
    assert (
        classify_execution_mode(
            parallel=False,
            keyword="",
            mark_expression=mark_expression,
            deselected=False,
            last_failed=False,
            collection_args=collection_args,
        )
        == mode
    )


def test_execution_mode_selection_and_parallelism_fail_closed() -> None:
    assert (
        classify_execution_mode(
            parallel=True,
            keyword="",
            mark_expression="",
            deselected=False,
            last_failed=False,
            collection_args=("tests",),
        )
        == "parallel"
    )
    assert (
        classify_execution_mode(
            parallel=False,
            keyword="one",
            mark_expression="",
            deselected=False,
            last_failed=False,
            collection_args=("tests",),
        )
        == "serial-selected"
    )
    assert (
        classify_execution_mode(
            parallel=False,
            keyword="",
            mark_expression="",
            deselected=False,
            last_failed=True,
            collection_args=("tests",),
        )
        == "serial-selected"
    )


@pytest.mark.parametrize("seconds", [None, "nan", "inf", "-1"])
def test_release_rejects_missing_or_invalid_suite_time(
    tmp_path: Path, seconds: None | str
) -> None:
    root, path, suite, nodes = report(tmp_path)
    if seconds is not None:
        suite.set("time", seconds)
    ET.SubElement(
        _required(suite, "properties"),
        "property",
        name=EXECUTION_MODE,
        value="serial-unfiltered",
    )
    save(path, suite)
    with pytest.raises(ValueError, match="duration"):
        validate_serial_release(path, root, nodes)


def test_release_manifest_must_equal_full_collection(tmp_path: Path) -> None:
    root, path, suite, nodes = report(tmp_path)
    save(path, suite)
    with pytest.raises(ValueError, match="exact unfiltered"):
        validate_serial_release(path, root, nodes[:1])


def _required(parent: ET.Element[str], path: str) -> ET.Element[str]:
    child = parent.find(path)
    assert child is not None, path
    return child
