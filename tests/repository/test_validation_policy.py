"""Behavioral checks for the shared Python and Isabelle run policy."""

from __future__ import annotations

import json
import os
import sys
import textwrap
import time
from itertools import pairwise
from pathlib import Path
from types import SimpleNamespace
from typing import cast
from uuid import uuid4

import pytest

from devtools import runs
from devtools.checks import process_guard, pytest_policy, release
from devtools.checks.test_run_evidence import PROVENANCE_MODE_ENV
from devtools.checks.validation_policy import (
    ISABELLE_JOBS,
    ISABELLE_MEMORY_BYTES,
    ISABELLE_OPTIONS,
    ISABELLE_PARALLEL_PROOFS,
    ISABELLE_SESSION_SECONDS,
    ISABELLE_THREADS,
    PYTHON_COMMAND_SECONDS,
    PYTHON_MEMORY_BYTES,
    PYTHON_SUITE_SECONDS,
    PYTHON_TEST_SECONDS,
    isabelle_policy,
)
from devtools.paths import repository_root


def _run_pytest_policy_probe(
    tmp_path: Path,
    source_text: str,
    extra_args: tuple[str, ...] = (),
) -> tuple[process_guard.GuardResult, Path, str]:
    source = tmp_path / "policy_probe.py"
    source.write_text(textwrap.dedent(source_text), encoding="utf-8")
    marker = tmp_path / "active-test.json"
    log = tmp_path / "pytest.log"
    environment = dict(os.environ)
    for name in (
        "PYTEST_ADDOPTS",
        "PYTEST_PLUGINS",
        "PYTEST_TIMEOUT",
        "PYTEST_TIMEOUT_METHOD",
        release.ACCEPTANCE_ROOT_ENV,
    ):
        environment.pop(name, None)
    environment["PYTEST_DISABLE_PLUGIN_AUTOLOAD"] = "1"
    environment["NUMBER_COMPILER_GUARDED_PYTEST"] = uuid4().hex
    environment[PROVENANCE_MODE_ENV] = "development"
    environment[pytest_policy.ACTIVE_TEST_ENV] = str(marker)
    command = (
        sys.executable,
        "-m",
        "pytest",
        "-p",
        "pytest_timeout",
        "-p",
        "devtools.checks.pytest_policy",
        "--timeout",
        str(PYTHON_TEST_SECONDS),
        "--timeout-method",
        "thread",
        "--timeout-disable-debugger-detection",
        *extra_args,
        "-q",
        str(source),
    )
    result = process_guard.run_guarded(
        command,
        output=log,
        cwd=repository_root(),
        timeout=10,
        environment=environment,
        active_test_path=marker,
        active_test_timeout=PYTHON_TEST_SECONDS,
    )
    return result, marker, log.read_text(encoding="utf-8")


def test_shared_execution_budgets_have_one_canonical_owner() -> None:
    assert (PYTHON_TEST_SECONDS, PYTHON_SUITE_SECONDS, PYTHON_COMMAND_SECONDS) == (
        60,
        300,
        60,
    )
    assert PYTHON_MEMORY_BYTES == 4 * 1024**3
    assert ISABELLE_SESSION_SECONDS == 300
    assert ISABELLE_MEMORY_BYTES == 6 * 1024**3
    assert ISABELLE_THREADS == 4
    assert ISABELLE_PARALLEL_PROOFS == ISABELLE_JOBS == 1
    assert f"timeout={ISABELLE_SESSION_SECONDS}" in ISABELLE_OPTIONS
    assert isabelle_policy(0).timeout_seconds == ISABELLE_SESSION_SECONDS
    assert isabelle_policy(2).timeout_seconds == ISABELLE_SESSION_SECONDS * 3
    assert isabelle_policy(1).memory_bytes == ISABELLE_MEMORY_BYTES


def test_explicit_selectors_are_exact_and_default_unit_is_partitioned() -> None:
    selector = "tests/repository/test_git_source.py::test_git_source"
    assert release._pytest_selection("unit", (selector,)) == ((selector,), "")
    assert release._pytest_selection("unit", ()) == (("tests",), "not validation")
    assert release._pytest_selection("p0", (release.P0[0],)) == ((release.P0[0],), "")


def test_selection_command_uses_one_guarded_pytest_process(tmp_path: Path) -> None:
    selector = "tests/repository/test_git_source.py::test_git_source"
    command = release._pytest_command(tmp_path, "unit", (selector,), "")
    assert command.count("pytest") == 1
    assert "--collect-only" not in command
    assert "--timeout" in command
    timeout_position = command.index("--timeout")
    assert command[timeout_position + 1] == str(PYTHON_TEST_SECONDS)
    pytest_module = command.index("pytest")
    assert "-m" not in command[pytest_module + 1 :]
    assert command[-2] == selector
    assert any(argument.startswith("--junitxml=") for argument in command)


def test_default_unit_skips_already_excluded_validation_tree(
    tmp_path: Path,
) -> None:
    selectors, mark = release._pytest_selection("unit", ())
    command = release._pytest_command(tmp_path, "unit", selectors, mark)

    assert mark == "not validation"
    assert command[command.index("--ignore") + 1] == "tests/validation"
    assert command[-2] == "tests"
    assert ("-m", mark) in tuple(pairwise(command))


def test_explicit_and_p0_selections_do_not_skip_requested_files(
    tmp_path: Path,
) -> None:
    validation_selector = "tests/validation/test_example.py::test_requested"
    explicit_selectors, explicit_mark = release._pytest_selection(
        "unit", (validation_selector,)
    )
    explicit_command = release._pytest_command(
        tmp_path, "unit", explicit_selectors, explicit_mark
    )
    assert validation_selector in explicit_command
    assert "--ignore" not in explicit_command

    p0_selectors, p0_mark = release._pytest_selection("p0", ())
    p0_command = release._pytest_command(tmp_path, "p0", p0_selectors, p0_mark)
    assert p0_mark == ""
    assert "--ignore" not in p0_command
    assert all(selector in p0_command for selector in release.P0)

    all_selectors, all_mark = release._pytest_selection("all", ())
    all_command = release._pytest_command(tmp_path, "all", all_selectors, all_mark)
    assert all_mark == ""
    assert "--ignore" not in all_command


def test_timeout_override_parser_handles_both_compact_spellings() -> None:
    assert pytest_policy._timeout_overrides(("-otimeout=2",)) == ("timeout=2",)
    assert pytest_policy._timeout_overrides(
        ("--override-ini=timeout_method=signal",)
    ) == ("timeout_method=signal",)
    assert pytest_policy._timeout_overrides(("-o", "addopts=")) == ()


def test_runner_rejects_inherited_pytest_environment_overrides() -> None:
    assert pytest_policy.forbidden_environment_overrides(
        {"PYTEST_ADDOPTS": "-o timeout=2", "PYTEST_TIMEOUT": "2"}
    ) == ("PYTEST_ADDOPTS", "PYTEST_TIMEOUT")
    assert pytest_policy.forbidden_environment_overrides({}) == ()


def test_native_isabelle_inventory_includes_external_parents() -> None:
    inventory = release._parse_session_inventory(
        "HOL\nHOL-Number_Theory\nHOL-Computational_Algebra\nComma_Check\n",
        ("Comma_Check",),
    )
    assert inventory == (
        "HOL",
        "HOL-Number_Theory",
        "HOL-Computational_Algebra",
        "Comma_Check",
    )


def test_native_inventory_does_not_require_syntactic_but_unbuilt_ancestors() -> None:
    assert release._parse_session_inventory(
        "HOL\nSelected_Check\n", ("Selected_Check",)
    ) == ("HOL", "Selected_Check")
    try:
        release._parse_session_inventory("HOL\n", ("Selected_Check",))
    except ValueError as error:
        assert "omitted requested sessions" in str(error)
    else:
        raise AssertionError("native inventory accepted a missing selected session")


def test_isabelle_environment_command_executes_tool_after_assignments() -> None:
    command = release._isabelle_environment_command(
        "/opt/Isabelle/bin/isabelle",
        ("ML_OPTIONS=--maxheap 4096",),
        ("sessions", "-b", "-d", "proofs/isabelle", "Selected_Check"),
    )
    assert command == (
        "/opt/Isabelle/bin/isabelle",
        "env",
        "ML_OPTIONS=--maxheap 4096",
        "/opt/Isabelle/bin/isabelle",
        "sessions",
        "-b",
        "-d",
        "proofs/isabelle",
        "Selected_Check",
    )


def test_native_build_summary_separates_rebuilds_reuse_and_failure() -> None:
    inventory = ("HOL", "HOL-Library", "Theory_Check")
    success = release._session_build_summary(
        "Building HOL-Library\n"
        "Finished HOL-Library (0:00:12.50 elapsed time, 0:00:08 cpu time)\n"
        "Running Theory_Check\n"
        "Finished Theory_Check (0:00:03.00 elapsed time, 0:00:02 cpu time)\n"
        "Finished at Fri Oct 16 20:05:34 GMT 2026\n",
        inventory,
        succeeded=True,
    )
    assert success["rebuilt_sessions"] == ["HOL-Library", "Theory_Check"]
    assert success["reused_sessions"] == ["HOL"]
    assert success["unmatched_native_session_statuses"] == []
    assert success["finished_session_elapsed_seconds"] == {
        "HOL-Library": 12.5,
        "Theory_Check": 3.0,
    }
    failure = release._session_build_summary(
        "Building Theory_Check ...\n"
        'Theory_Check FAILED (see also "isabelle build_log -H Error Theory_Check")\n'
        "Unfinished session(s): Theory_Check\n",
        inventory,
        succeeded=False,
    )
    assert failure["reused_sessions"] is None
    assert failure["failed_sessions"] == ["Theory_Check"]
    assert failure["unmatched_native_session_statuses"] == []
    assert failure["not_attempted_or_unclassified_sessions"] == [
        "HOL",
        "HOL-Library",
    ]


def test_native_build_footer_preserves_registered_at_session() -> None:
    summary = release._session_build_summary(
        "Finished at (0:00:01 elapsed time, 0:00:01 cpu time)\n"
        "Finished Unexpected_Check (0:00:02 elapsed time, 0:00:01 cpu time)\n",
        ("at",),
        succeeded=True,
    )
    assert summary["finished_sessions"] == ["Unexpected_Check", "at"]
    assert summary["unmatched_native_session_statuses"] == ["Unexpected_Check"]


def test_native_success_keeps_reported_elapsed_budget_failures_visible() -> None:
    summary = release._session_build_summary(
        "Finished At_Limit (0:05:00 elapsed time, 0:04:58 cpu time)\n"
        "Finished Too_Slow (0:05:00.01 elapsed time, 0:04:58 cpu time)\n",
        ("At_Limit", "Too_Slow", "Cached"),
        succeeded=True,
    )
    assert summary["over_budget_finished_sessions"] == ["Too_Slow"]
    assert summary["reused_sessions"] == ["Cached"]
    assert summary["finished_session_elapsed_seconds"] == {
        "At_Limit": 300.0,
        "Too_Slow": 300.01,
    }


def test_acceptance_environment_does_not_inherit_external_python_paths(
    tmp_path: Path,
) -> None:
    (tmp_path / "src").mkdir()
    environment = {"PYTHONPATH": "/poisoned/original/checkout"}
    release._acceptance_environment(tmp_path, environment)
    assert environment["PYTHONPATH"] == str((tmp_path / "src").resolve())
    assert environment[release.ACCEPTANCE_ROOT_ENV] == str(tmp_path.resolve())
    assert set(environment) == {
        "PYTHONPATH",
        release.ACCEPTANCE_ROOT_ENV,
        PROVENANCE_MODE_ENV,
    }


def test_phase_summary_rejects_missing_or_truncated_phase_data(tmp_path: Path) -> None:
    path = tmp_path / "phases.jsonl"
    rows = [
        {"phase": "collection", "seconds": 0.2},
        {"phase": "setup", "seconds": 0.1, "nodeid": "tests/a.py::test_a"},
        {"phase": "call", "seconds": 0.3, "nodeid": "tests/a.py::test_a"},
        {"phase": "teardown", "seconds": 0.05, "nodeid": "tests/a.py::test_a"},
        {"status": "finished", "exitstatus": 0},
    ]
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))
    summary = release._phase_summary(path)
    assert summary["complete"] is True
    assert summary["slowest_test_nodes"] == [
        {"nodeid": "tests/a.py::test_a", "seconds": 0.45}
    ]
    path.write_text(
        json.dumps(rows[0])
        + "\n"
        + json.dumps({"status": "truncated"})
        + "\n"
        + json.dumps(rows[-1])
        + "\n"
    )
    summary = release._phase_summary(path)
    assert summary["complete"] is False
    assert summary["truncated"] is True


def test_phase_summary_retains_failed_test_classification_and_excerpt(
    tmp_path: Path,
) -> None:
    path = tmp_path / "failed-phases.jsonl"
    rows = [
        {"phase": "collection", "seconds": 0.1, "selected_items": 1},
        {
            "phase": "setup",
            "seconds": 0.2,
            "nodeid": "tests/a.py::test_a",
            "outcome": "failed",
            "failure_longrepr": "fixture setup traceback",
            "failure_longrepr_truncated": False,
        },
        {"status": "finished", "exitstatus": 1},
    ]
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))
    summary = release._phase_summary(path)
    assert summary["failure_report_count"] == 1
    assert summary["failure_reports"] == [
        {
            "nodeid": "tests/a.py::test_a",
            "phase": "setup",
            "outcome": "failed",
            "failure_longrepr_excerpt": "fixture setup traceback",
            "failure_longrepr_truncated": False,
        }
    ]
    assert summary["pytest_exitstatus"] == 1


def test_direct_pytest_is_rejected_before_collection(tmp_path: Path) -> None:
    environment = dict(os.environ)
    environment.pop("NUMBER_COMPILER_GUARDED_PYTEST", None)
    environment.pop("PYTEST_ADDOPTS", None)
    environment.pop("PYTEST_PLUGINS", None)
    command = (
        sys.executable,
        "-m",
        "pytest",
        "tests/repository/test_git_source.py",
        "-q",
    )
    log = tmp_path / "direct-pytest-policy-test.log"
    result = process_guard.run_guarded(
        command,
        output=log,
        cwd=repository_root(),
        environment=environment,
    )
    output = log.read_text(encoding="utf-8")
    log.unlink(missing_ok=True)
    assert result.outcome == "child_failed"
    assert result.child_returncode != 0
    assert "must run through the guarded runner" in output
    assert "devtools.checks.release --suite unit --select" in output
    assert "collected" not in output


def test_actual_pytest_hook_covers_fixture_setup_call_and_teardown(
    tmp_path: Path,
) -> None:
    result, marker, output = _run_pytest_policy_probe(
        tmp_path,
        """
        import os
        from pathlib import Path
        import pytest

        marker = Path(os.environ['NUMBER_COMPILER_ACTIVE_TEST_FILE'])

        @pytest.fixture(autouse=True)
        def verify_marker_for_whole_case():
            assert marker.is_file()  # setup
            yield
            assert marker.is_file()  # teardown

        def test_marker_is_present_during_call():
            assert marker.is_file()
        """,
    )
    assert result.outcome == "completed", (result, output)
    assert result.child_returncode == 0
    assert "1 passed" in output
    assert not marker.exists()


def test_active_test_clamps_nested_deadline_and_restores_it_on_failure(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    marker = tmp_path / "active-test.json"
    parent_deadline = str(time.monotonic() + PYTHON_SUITE_SECONDS - 20)
    monkeypatch.setenv(pytest_policy.ACTIVE_TEST_ENV, str(marker))
    monkeypatch.setenv(process_guard.DEADLINE_ENV, parent_deadline)
    monkeypatch.setenv(process_guard.MEMORY_BUDGET_ENV, str(PYTHON_MEMORY_BYTES))
    monkeypatch.setattr(process_guard, "guard_context_is_live", lambda _env: True)
    protocol = pytest_policy.pytest_runtest_protocol(
        cast(
            pytest.Item,
            SimpleNamespace(nodeid="tests/nested.py::test_case"),
        ),
        None,
    )

    next(protocol)
    active_deadline = float(os.environ[process_guard.DEADLINE_ENV])
    marker_data = json.loads(marker.read_text(encoding="utf-8"))
    assert active_deadline <= marker_data["deadline_monotonic"]
    assert active_deadline - time.monotonic() <= PYTHON_TEST_SECONDS
    assert runs._trusted_guard_context()

    with pytest.raises(RuntimeError, match="simulated test failure"):
        protocol.throw(RuntimeError("simulated test failure"))
    assert os.environ[process_guard.DEADLINE_ENV] == parent_deadline
    assert not marker.exists()


def test_active_test_never_extends_shorter_suite_deadline(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    marker = tmp_path / "active-test.json"
    suite_deadline = time.monotonic() + 15
    parent_deadline = str(suite_deadline)
    monkeypatch.setenv(pytest_policy.ACTIVE_TEST_ENV, str(marker))
    monkeypatch.setenv(process_guard.DEADLINE_ENV, parent_deadline)
    protocol = pytest_policy.pytest_runtest_protocol(
        cast(
            pytest.Item,
            SimpleNamespace(nodeid="tests/nested.py::test_case"),
        ),
        None,
    )

    next(protocol)
    assert float(os.environ[process_guard.DEADLINE_ENV]) <= suite_deadline
    protocol.close()
    assert os.environ[process_guard.DEADLINE_ENV] == parent_deadline
    assert not marker.exists()


def test_parent_watchdog_kills_native_gil_stall_before_pytest_thread_timeout(
    tmp_path: Path,
) -> None:
    marker = tmp_path / "active-test.json"
    timeout_seconds = 0.5
    started = time.monotonic()
    marker.write_text(
        json.dumps(
            {
                "nodeid": "tests/native_stall.py::test_native_call_holds_gil",
                "started_monotonic": started,
                "deadline_monotonic": started + timeout_seconds,
            }
        ),
        encoding="utf-8",
    )
    output = tmp_path / "native-stall.log"
    result = process_guard.run_guarded(
        (
            sys.executable,
            "-c",
            "import ctypes; ctypes.PyDLL(None).sleep(3)",
        ),
        output=output,
        cwd=repository_root(),
        timeout=10,
        active_test_path=marker,
        active_test_timeout=timeout_seconds,
    )
    assert result.outcome == "test_timeout"
    assert "test_native_call_holds_gil" in result.detail
    assert "test_native_call_holds_gil" in marker.read_text(encoding="utf-8")


def test_actual_pytest_rejects_timeout_ini_override(tmp_path: Path) -> None:
    result, _, output = _run_pytest_policy_probe(
        tmp_path,
        "def test_never_collected():\n    raise AssertionError()\n",
        extra_args=("-o", "timeout=15"),
    )
    assert result.outcome == "child_failed"
    assert "timeout" in output
    assert "policy" in output


def test_actual_pytest_rejects_per_test_timeout_marker(tmp_path: Path) -> None:
    result, _, output = _run_pytest_policy_probe(
        tmp_path,
        "import pytest\n\n@pytest.mark.timeout(15)\ndef test_never_runs():\n    pass\n",
    )
    assert result.outcome == "child_failed"
    assert "per-test timeout markers are forbidden" in output
    assert "1 passed" not in output
