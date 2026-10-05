"""Enforce release-runner context and pytest timeout policy."""

from __future__ import annotations

import json
import math
import os
import shlex
import sys
import time
import uuid
from collections.abc import Generator, Mapping
from pathlib import Path
from uuid import uuid4

import pytest

from devtools.checks.process_guard import DEADLINE_ENV, guard_context_is_live
from devtools.checks.test_run_evidence import PROVENANCE_MODE_ENV
from devtools.checks.validation_policy import PYTEST_RUNNER_ENV, PYTHON_TEST_SECONDS

ACTIVE_TEST_ENV = "NUMBER_COMPILER_ACTIVE_TEST_FILE"
FORBIDDEN_OVERRIDE_ENV = (
    "PYTEST_ADDOPTS",
    "PYTEST_PLUGINS",
    "PYTEST_TIMEOUT",
    "PYTEST_TIMEOUT_METHOD",
)


def forbidden_environment_overrides(environment: Mapping[str, str]) -> tuple[str, ...]:
    """List pytest environment controls that could bypass the shared policy."""
    return tuple(name for name in FORBIDDEN_OVERRIDE_ENV if name in environment)


def _timeout_overrides(arguments: tuple[str, ...]) -> tuple[str, ...]:
    values: list[str] = []
    for index, argument in enumerate(arguments):
        if argument in {"-o", "--override-ini"} and index + 1 < len(arguments):
            values.append(arguments[index + 1])
        elif argument.startswith("--override-ini="):
            values.append(argument.split("=", 1)[1])
        elif argument.startswith("-o") and argument != "-o":
            values.append(argument[2:])
    return tuple(
        value
        for value in values
        if value.lstrip().split("=", 1)[0].startswith("timeout")
    )


def pytest_configure(config: pytest.Config) -> None:
    """Fail before collection unless the canonical runner configured pytest."""
    token = os.environ.get(PYTEST_RUNNER_ENV, "")
    try:
        if len(token) != 32:
            raise ValueError("runner token must be a 32-character UUID")
        if uuid.UUID(hex=token).hex != token.lower():
            raise ValueError("runner token is not canonical")
        uuid.UUID(hex=token)
        if not guard_context_is_live(os.environ):
            raise ValueError("guarded process parent is not authenticated")
    except (ValueError, AttributeError) as error:
        arguments = tuple(config.invocation_params.args)
        selectors = tuple(
            argument
            for argument in arguments
            if not argument.startswith("-")
            and (
                argument == "tests" or argument.startswith("tests/") or "::" in argument
            )
        )
        command = [
            sys.executable,
            "-m",
            "devtools.checks.release",
            "--suite",
            "unit",
        ]
        for selector in selectors:
            command.extend(("--select", selector))
        raise pytest.UsageError(
            "repository tests must run through the guarded runner: "
            + shlex.join(command)
        ) from error
    if forbidden_environment_overrides(os.environ):
        raise pytest.UsageError("pytest environment overrides are disabled")
    if os.environ.get("PYTEST_DISABLE_PLUGIN_AUTOLOAD") != "1":
        raise pytest.UsageError("the guarded runner must disable plugin autoload")
    if config.getoption("timeout", default=None) != PYTHON_TEST_SECONDS:
        raise pytest.UsageError("all tests require the standard 60-second timeout")
    if config.getoption("timeout_method", default=None) != "thread":
        raise pytest.UsageError("pytest-timeout must use its thread method")
    if not config.getoption("timeout_disable_debugger_detection", default=False):
        raise pytest.UsageError("debugger detection must not suppress test timeouts")
    if config.getini("timeout_func_only"):
        raise pytest.UsageError("test timeout must cover fixtures and teardown")
    if config.getoption("session_timeout", default=None) is not None:
        raise pytest.UsageError("pytest session timeouts are not an execution budget")
    ini_values = config.inicfg
    ini_policy = {
        "timeout": str(PYTHON_TEST_SECONDS),
        "timeout_method": "thread",
        "timeout_func_only": "false",
        "timeout_disable_debugger_detection": "true",
    }
    for key, expected in ini_policy.items():
        configured = ini_values.get(key)
        if configured is not None and str(configured).lower() != expected:
            raise pytest.UsageError(f"pytest ini setting {key} conflicts with policy")
    mode = os.environ.get(PROVENANCE_MODE_ENV, "development")
    acceptance_root = os.environ.get("NUMBER_COMPILER_ACCEPTANCE_ROOT")
    if mode not in {"development", "acceptance"}:
        raise pytest.UsageError("invalid evidence provenance mode")
    if mode == "acceptance":
        if not acceptance_root:
            raise pytest.UsageError("acceptance requires an isolated source worktree")
        _verify_acceptance_imports(Path(acceptance_root).resolve())
    elif acceptance_root:
        raise pytest.UsageError("development run cannot claim an acceptance worktree")
    if _timeout_overrides(tuple(config.invocation_params.args)):
        raise pytest.UsageError("pytest timeout configuration overrides are forbidden")


def _verify_acceptance_imports(root: Path) -> None:
    import number_compiler

    package_file = getattr(number_compiler, "__file__", None)
    if not isinstance(package_file, str):
        raise pytest.UsageError("cannot verify acceptance package import source")
    expected = (root / "src").resolve()
    if not Path(package_file).resolve().is_relative_to(expected):
        raise pytest.UsageError(
            "number_compiler did not import from the acceptance worktree"
        )
    if not Path(__file__).resolve().is_relative_to(root):
        raise pytest.UsageError(
            "pytest policy plugin did not load from the acceptance worktree"
        )
    if Path.cwd().resolve() != root:
        raise pytest.UsageError(
            "acceptance tests must run from the detached worktree root"
        )


def pytest_collection_modifyitems(items: list[pytest.Item]) -> None:
    """Reject test-level timeout markers that weaken or replace the policy."""
    if any(item.get_closest_marker("timeout") is not None for item in items):
        raise pytest.UsageError("per-test timeout markers are forbidden")


@pytest.hookimpl(hookwrapper=True)
def pytest_runtest_protocol(
    item: pytest.Item, nextitem: pytest.Item | None
) -> Generator[None, None, None]:
    """Leave the currently executing node available if the parent kills pytest."""
    marker = os.environ.get(ACTIVE_TEST_ENV)
    path = Path(marker) if marker else None
    temporary: Path | None = None
    inherited_deadline = os.environ.get(DEADLINE_ENV)
    try:
        if path is not None:
            path.parent.mkdir(parents=True, exist_ok=True)
            started = time.monotonic()
            case_deadline = started + PYTHON_TEST_SECONDS
            if inherited_deadline is not None:
                try:
                    suite_deadline = float(inherited_deadline)
                except ValueError as error:
                    raise pytest.UsageError("invalid guarded suite deadline") from error
                if not math.isfinite(suite_deadline):
                    raise pytest.UsageError("guarded suite deadline must be finite")
                case_deadline = min(case_deadline, suite_deadline)
            os.environ[DEADLINE_ENV] = str(case_deadline)
            temporary = path.with_name(f".{path.name}.{uuid4().hex}.tmp")
            temporary.write_text(
                json.dumps(
                    {
                        "nodeid": item.nodeid,
                        "started_monotonic": started,
                        "deadline_monotonic": started + PYTHON_TEST_SECONDS,
                    }
                )
                + "\n",
                encoding="utf-8",
            )
            os.replace(temporary, path)
        yield
    finally:
        if path is not None:
            if inherited_deadline is None:
                os.environ.pop(DEADLINE_ENV, None)
            else:
                os.environ[DEADLINE_ENV] = inherited_deadline
        if path is not None:
            path.unlink(missing_ok=True)
        if temporary is not None:
            temporary.unlink(missing_ok=True)
