"""The strict type-check sweep has complete, deterministic source coverage."""

from __future__ import annotations

import json
import sys
import tomllib
from pathlib import Path

import pytest

from devtools.checks.pyright_policy import (
    MAX_PYRIGHT_BATCH_FILES,
    NODE_EXECUTABLE_ENV,
    NPM_EXECUTABLE_ENV,
    PYRIGHT_OUTPUT_LIMIT_BYTES,
    diagnostics_are_clean,
    node_executable,
    npm_install_command,
    pinned_pyright_version,
    pyright_batches,
    pyright_command,
    pyright_entrypoint,
    pyright_sources,
    validate_pyright_output,
)
from devtools.checks.pyright_runner import capture_batch_diagnostics
from devtools.checks.source_discovery import authored_files
from devtools.checks.toolchain_policy import python_toolchain_violations
from devtools.report_values import string_keyed_mapping
from tests.support.git_repositories import commit_fixture


def test_pyright_source_discovery_includes_untracked_and_excludes_generated(
    tmp_path: Path,
) -> None:
    root = tmp_path
    (root / ".gitignore").write_text("/results/\ndevtools/typing/node_modules/\n")
    for directory in ("src/pkg", "tests", "devtools", "docs"):
        (root / directory).mkdir(parents=True)
    (root / "src/pkg/tracked.py").write_text("VALUE: int = 1\n")
    (root / "tests/contract.pyi").write_text("VALUE: int\n")
    (root / "devtools/checked.py").write_text("VALUE: int = 2\n")
    (root / "devtools/typing/node_modules/generated.py").parent.mkdir(parents=True)
    (root / "devtools/typing/node_modules/generated.py").write_text("VALUE: int = 6\n")
    (root / "docs/ignored.py").write_text("VALUE: int = 3\n")
    (root / "results/generated.py").parent.mkdir(parents=True)
    (root / "results/generated.py").write_text("VALUE: int = 4\n")
    commit_fixture(root)
    (root / "tests/untracked.py").write_text("VALUE: int = 5\n")

    assert [path.relative_to(root).as_posix() for path in pyright_sources(root)] == [
        "devtools/checked.py",
        "src/pkg/tracked.py",
        "tests/contract.pyi",
        "tests/untracked.py",
    ]


def test_pyright_batches_are_sorted_bounded_and_lossless() -> None:
    paths = tuple(Path(f"src/file-{index:03d}.py") for index in range(51))
    batches = pyright_batches((*paths, paths[0]))

    assert tuple(map(len, batches)) == (25, 25, 1)
    assert tuple(path for batch in batches for path in batch) == paths
    with pytest.raises(ValueError, match="batch maximum"):
        pyright_batches(paths, maximum=MAX_PYRIGHT_BATCH_FILES + 1)


def test_filesystem_source_discovery_ignores_private_node_modules(
    tmp_path: Path,
) -> None:
    (tmp_path / "devtools/typing/node_modules/pyright").mkdir(parents=True)
    (tmp_path / "devtools/typing/node_modules/pyright/index.js").write_text("\n")
    authored = authored_files(tmp_path)
    assert not any("node_modules" in path.parts for path in authored)


def test_pyright_command_uses_private_package_and_explicit_node(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    root = tmp_path
    package = root / "devtools/typing/node_modules/pyright"
    package.mkdir(parents=True)
    (package / "index.js").write_text("// private test entrypoint\n")
    (package / "package.json").write_text(
        json.dumps({"name": "pyright", "version": "1.1.414"})
    )
    (root / "devtools/typing/package.json").write_text(
        json.dumps({"private": True, "devDependencies": {"pyright": "1.1.414"}})
    )
    fake_node = root / "node"
    fake_node.write_text("#!/bin/sh\nexit 0\n")
    fake_node.chmod(0o755)
    monkeypatch.setenv(NODE_EXECUTABLE_ENV, str(fake_node))

    command = pyright_command(root, (root / "src/a.py", root / "tests/b.py"))

    assert command == (
        str(fake_node.resolve()),
        "--max-old-space-size=2048",
        str(package / "index.js"),
        "--pythonpath",
        sys.executable,
        "--outputjson",
        "src/a.py",
        "tests/b.py",
    )
    assert node_executable() == fake_node.resolve()
    assert pinned_pyright_version(root) == "1.1.414"
    with pytest.raises(RuntimeError, match="pinned version"):
        (package / "package.json").write_text(
            json.dumps({"name": "pyright", "version": "different"})
        )
        pyright_entrypoint(root)


def test_pyright_diagnostic_policy_rejects_any_reported_finding() -> None:
    assert diagnostics_are_clean({"generalDiagnostics": []})
    assert not diagnostics_are_clean(
        {"generalDiagnostics": [{"severity": "information", "message": "found"}]}
    )
    assert not diagnostics_are_clean({"summary": {"errorCount": 0}})


def test_output_capped_pyright_batch_is_never_complete(
    tmp_path: Path,
) -> None:
    log_path = tmp_path / "batch.log"
    diagnostics_path = tmp_path / "batch.diagnostics.json"
    log_path.write_text('{"generalDiagnostics": []}')

    payload, complete, error = capture_batch_diagnostics(
        log_path=log_path,
        diagnostics_path=diagnostics_path,
        process_outcome="output_limit",
    )

    assert PYRIGHT_OUTPUT_LIMIT_BYTES == 32 * 1024**2
    assert payload is None
    assert not complete
    assert error and "retention limit" in error
    assert not diagnostics_path.exists()


def _pyright_payload(
    *,
    version: str = "1.1.414",
    files_analyzed: int = 2,
    errors: int = 0,
    warnings: int = 0,
    information: int = 0,
    diagnostics: list[dict[str, object]] | None = None,
) -> dict[str, object]:
    rows = diagnostics or []
    return {
        "version": version,
        "generalDiagnostics": rows,
        "summary": {
            "filesAnalyzed": files_analyzed,
            "errorCount": errors,
            "warningCount": warnings,
            "informationCount": information,
            "timeInSec": 0.25,
        },
    }


def test_pyright_output_requires_complete_root_and_summary_counts() -> None:
    valid = _pyright_payload()
    summary, error = validate_pyright_output(
        valid, expected_version="1.1.414", expected_root_count=2
    )
    assert summary is not None
    assert error is None

    for invalid, roots in (
        (_pyright_payload(files_analyzed=0), 1),
        (_pyright_payload(files_analyzed=1), 2),
        (_pyright_payload(version="1.1.413"), 2),
        (_pyright_payload(errors=-1), 2),
        (_pyright_payload(errors=True), 2),
        (_pyright_payload(errors=1), 2),
    ):
        summary, error = validate_pyright_output(
            invalid, expected_version="1.1.414", expected_root_count=roots
        )
        assert summary is None
        assert error is not None

    summary, error = validate_pyright_output(
        valid, expected_version="1.1.414", expected_root_count=0
    )
    assert summary is None
    assert error is not None


def test_pyright_findings_are_complete_but_not_clean() -> None:
    payload = _pyright_payload(
        errors=1,
        diagnostics=[{"severity": "error", "message": "finding"}],
    )
    summary, error = validate_pyright_output(
        payload, expected_version="1.1.414", expected_root_count=2
    )
    assert summary is not None
    assert error is None
    assert not diagnostics_are_clean(payload)


def test_locked_npm_command_uses_node_and_resolved_cli(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    node = tmp_path / "node"
    node.write_text("node executable")
    cli = tmp_path / "npm-cli.js"
    cli.write_text("// npm cli")
    cli.chmod(0o644)
    link = tmp_path / "npm"
    link.symlink_to(cli)
    monkeypatch.setenv(NPM_EXECUTABLE_ENV, str(link))

    command = npm_install_command(tmp_path, node=node)

    assert command == (
        str(node.resolve()),
        str(cli.resolve()),
        "ci",
        "--ignore-scripts",
        "--no-audit",
        "--no-fund",
        "--prefix",
        "devtools/typing",
    )


def test_npm_shell_wrapper_is_rejected(tmp_path: Path) -> None:
    wrapper = tmp_path / "npm"
    wrapper.write_text("#!/bin/sh\nexec node npm-cli.js\n")
    with pytest.raises(ValueError, match="JavaScript CLI entrypoint"):
        npm_install_command(tmp_path, node=tmp_path / "node", npm=wrapper)


def test_python_toolchain_policy_checks_constraints_target_and_installed_versions(
    tmp_path: Path,
) -> None:
    root = tmp_path
    (root / "devtools/typing").mkdir(parents=True)
    (root / "pyproject.toml").write_text(
        """
[project]
dependencies = ["alpha==1.2.3"]

[project.optional-dependencies]
dev = ["beta==4.5.6"]
profile = ["gamma==7.8.9"]

[build-system]
requires = ["setuptools==80.0.0"]
""",
        encoding="utf-8",
    )
    (root / "devtools/typing/constraints-py314-macos.txt").write_text(
        """
# Target: CPython 3.14.8 / macOS arm64
alpha==1.2.3
beta==4.5.6
gamma==7.8.9
setuptools==80.0.0
transitive==2.3.4
""",
        encoding="utf-8",
    )
    installed = {
        "alpha": "1.2.3",
        "beta": "4.5.6",
        "gamma": "7.8.9",
        "setuptools": "80.0.0",
        "transitive": "2.3.4",
    }

    assert (
        python_toolchain_violations(
            root,
            version_reader=installed.__getitem__,
            python_version="3.14.8",
            implementation="CPython",
            system="Darwin",
            machine="arm64",
        )
        == ()
    )

    installed["beta"] = "4.5.7"
    violations = python_toolchain_violations(
        root,
        version_reader=installed.__getitem__,
        python_version="3.14.8",
        implementation="CPython",
        system="Darwin",
        machine="arm64",
    )
    assert any("beta version 4.5.7" in violation for violation in violations)
    assert any(
        "runtime" in violation
        for violation in python_toolchain_violations(
            root,
            version_reader=installed.__getitem__,
            python_version="3.13.0",
            implementation="CPython",
            system="Darwin",
            machine="arm64",
        )
    )


def test_shared_toolchain_settings_are_strict_and_pinned() -> None:
    root = Path(__file__).resolve().parents[2]
    raw_config = tomllib.loads((root / "pyproject.toml").read_text(encoding="utf-8"))
    config = string_keyed_mapping(raw_config)
    assert config is not None
    project = string_keyed_mapping(config.get("project"))
    assert project is not None
    tool = string_keyed_mapping(config.get("tool"))
    assert tool is not None
    pyright = string_keyed_mapping(tool.get("pyright"))
    assert pyright is not None
    assert pyright["typeCheckingMode"] == "strict"
    assert pyright["include"] == ["src", "tests", "devtools"]
    assert pyright["pythonVersion"] == "3.11"
    assert pyright["venvPath"] == "."
    assert pyright["venv"] == ".venv"
    ruff = string_keyed_mapping(tool.get("ruff"))
    assert ruff is not None
    ruff_lint = string_keyed_mapping(ruff.get("lint"))
    assert ruff_lint is not None
    assert ruff_lint.get("select") == [
        "E4",
        "E7",
        "E9",
        "F",
        "I",
        "UP",
        "B",
        "ANN",
        "RUF100",
    ]
    assert ruff_lint.get("preview") is False

    package_path = root / "devtools/typing/package.json"
    raw_package = json.loads(package_path.read_text(encoding="utf-8"))
    package = string_keyed_mapping(raw_package)
    assert package is not None
    package_dependencies = string_keyed_mapping(package.get("devDependencies"))
    assert package_dependencies is not None
    assert package.get("private") is True
    pyright_pin = package_dependencies.get("pyright")
    assert isinstance(pyright_pin, str)
    assert "scripts" not in package
    raw_lock = json.loads(
        (root / "devtools/typing/package-lock.json").read_text(encoding="utf-8")
    )
    lock = string_keyed_mapping(raw_lock)
    assert lock is not None
    packages = string_keyed_mapping(lock.get("packages"))
    assert packages is not None
    pyright_package = string_keyed_mapping(packages.get("node_modules/pyright"))
    assert pyright_package is not None
    assert pyright_package.get("version") == pyright_pin
