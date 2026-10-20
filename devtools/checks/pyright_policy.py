"""Deterministic source discovery and bounded command construction for Pyright."""

from __future__ import annotations

import json
import math
import os
import re
import shutil
import sys
from collections.abc import Iterable, Mapping
from pathlib import Path

from devtools.checks.source_discovery import authored_files
from number_compiler.arithmetic.contracts.input_validation import (
    is_object_list,
    string_keyed_mapping,
)

MAX_PYRIGHT_BATCH_FILES = 25
PYRIGHT_OUTPUT_LIMIT_BYTES = 32 * 1024**2
NODE_EXECUTABLE_ENV = "NUMBER_COMPILER_NODE"
NPM_EXECUTABLE_ENV = "NUMBER_COMPILER_NPM"
_TYPING_PACKAGE = Path("devtools/typing")
_PYRIGHT_INSTALL = Path("devtools/typing/node_modules/pyright")


def pyright_sources(root: Path) -> tuple[Path, ...]:
    """Return every authored Python source selected by the shared config."""
    resolved_root = root.resolve()
    selected_roots = {"src", "tests", "devtools"}
    return tuple(
        sorted(
            path
            for path in authored_files(resolved_root)
            if path.suffix in {".py", ".pyi"}
            and path.relative_to(resolved_root).parts
            and path.relative_to(resolved_root).parts[0] in selected_roots
        )
    )


def pyright_batches(
    files: Iterable[Path], *, maximum: int = MAX_PYRIGHT_BATCH_FILES
) -> tuple[tuple[Path, ...], ...]:
    """Partition a stable file list without dropping or duplicating a path."""
    if type(maximum) is not int or not 1 <= maximum <= MAX_PYRIGHT_BATCH_FILES:
        raise ValueError(f"batch maximum must be in 1..{MAX_PYRIGHT_BATCH_FILES}")
    ordered = tuple(sorted(set(files)))
    return tuple(
        ordered[start : start + maximum] for start in range(0, len(ordered), maximum)
    )


def node_executable() -> Path | None:
    """Resolve Node from an explicit toolchain setting or the process PATH."""
    configured = os.environ.get(NODE_EXECUTABLE_ENV)
    candidate = shutil.which(configured) if configured else shutil.which("node")
    if candidate is None:
        return None
    path = Path(candidate).resolve()
    if not path.is_file() or not os.access(path, os.X_OK):
        return None
    return path


def npm_cli_entrypoint(executable: Path | None = None) -> Path | None:
    """Resolve an npm CLI JavaScript entrypoint without invoking a shell wrapper."""
    if executable is None:
        configured = os.environ.get(NPM_EXECUTABLE_ENV)
        if configured:
            configured_path = Path(configured)
            is_explicit_path = (
                configured_path.is_absolute()
                or os.path.sep in configured
                or (os.path.altsep is not None and os.path.altsep in configured)
            )
            candidate = (
                configured_path if is_explicit_path else shutil.which(configured)
            )
        else:
            candidate = shutil.which("npm")
        if candidate is None:
            return None
        executable = Path(candidate)
    try:
        resolved = executable.resolve(strict=True)
    except OSError:
        return None
    if not resolved.is_file() or resolved.suffix.lower() != ".js":
        raise ValueError(
            "npm must resolve directly to its JavaScript CLI entrypoint; "
            "shell and command wrappers are unsupported"
        )
    return resolved


def npm_install_command(
    root: Path, *, node: Path | None = None, npm: Path | None = None
) -> tuple[str, ...]:
    """Build the locked private npm installation command for guarded execution."""
    source_root = root.resolve()
    if not source_root.is_dir():
        raise FileNotFoundError(f"repository root does not exist: {source_root}")
    selected_node = node or node_executable()
    if selected_node is None:
        raise FileNotFoundError(
            f"Node was not found; set {NODE_EXECUTABLE_ENV} or add Node to PATH"
        )
    cli = npm_cli_entrypoint(npm)
    if cli is None:
        raise FileNotFoundError(
            f"npm was not found; set {NPM_EXECUTABLE_ENV} or add npm to PATH"
        )
    return (
        str(selected_node.resolve()),
        str(cli),
        "ci",
        "--ignore-scripts",
        "--no-audit",
        "--no-fund",
        "--prefix",
        "devtools/typing",
    )


def pyright_entrypoint(root: Path) -> Path:
    """Locate the repository-private npm installation; never use global Pyright."""
    entrypoint = root.resolve() / _PYRIGHT_INSTALL / "index.js"
    if not entrypoint.is_file():
        raise FileNotFoundError(
            "private Pyright is not installed; install devtools/typing with npm ci"
        )
    expected_version = pinned_pyright_version(root)
    installed_version = pyright_version(root)
    if installed_version != expected_version:
        raise RuntimeError(
            f"private Pyright version {installed_version} does not match "
            f"the pinned version {expected_version}"
        )
    return entrypoint


def pinned_pyright_version(root: Path) -> str:
    """Read the exact private npm dependency version from its manifest."""
    manifest = root.resolve() / _TYPING_PACKAGE / "package.json"
    try:
        payload: object = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise FileNotFoundError(
            "private Pyright package manifest is unavailable"
        ) from error
    manifest_data = string_keyed_mapping(payload)
    if manifest_data is None:
        raise ValueError("private npm package manifest must be a JSON object")
    dependencies = string_keyed_mapping(manifest_data.get("devDependencies"))
    if dependencies is None:
        raise ValueError("private npm package must declare devDependencies")
    value = dependencies.get("pyright")
    if (
        not isinstance(value, str)
        or re.fullmatch(r"[0-9]+\.[0-9]+\.[0-9]+", value) is None
    ):
        raise ValueError("private Pyright dependency must pin one exact version")
    return value


def pyright_version(root: Path) -> str:
    """Read the version of the private installed Pyright package, if available."""
    manifest = root.resolve() / _PYRIGHT_INSTALL / "package.json"
    try:
        payload: object = json.loads(manifest.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return "unavailable"
    manifest_data = string_keyed_mapping(payload)
    value = manifest_data.get("version") if manifest_data is not None else None
    return value if isinstance(value, str) else "unavailable"


def pyright_command(
    root: Path, files: Iterable[Path], *, node: Path | None = None
) -> tuple[str, ...]:
    """Build one guarded command with the selected interpreter and exact files."""
    executable = node or node_executable()
    if executable is None:
        raise FileNotFoundError(
            f"Node was not found; set {NODE_EXECUTABLE_ENV} or add Node to PATH"
        )
    source_root = root.resolve()
    relative_files = tuple(
        sorted(path.resolve().relative_to(source_root).as_posix() for path in files)
    )
    if not relative_files:
        raise ValueError("Pyright batch cannot be empty")
    if len(relative_files) > MAX_PYRIGHT_BATCH_FILES:
        raise ValueError("Pyright batch exceeds the 25-file policy")
    return (
        str(executable),
        "--max-old-space-size=2048",
        str(pyright_entrypoint(source_root)),
        "--pythonpath",
        sys.executable,
        "--outputjson",
        *relative_files,
    )


def diagnostics_are_clean(payload: object) -> bool:
    """Treat every emitted Pyright diagnostic severity as a finding."""
    diagnostic_data = string_keyed_mapping(payload)
    if diagnostic_data is None:
        return False
    diagnostics = diagnostic_data.get("generalDiagnostics")
    return isinstance(diagnostics, list) and not diagnostics


def validate_pyright_output(
    payload: object, *, expected_version: str, expected_root_count: int
) -> tuple[Mapping[str, object] | None, str | None]:
    """Validate the exact Pyright output contract and its analyzed-root count."""
    if type(expected_root_count) is not int or expected_root_count < 1:
        return None, "Pyright batch root count must be a positive integer"
    result = string_keyed_mapping(payload)
    if result is None:
        return None, "Pyright output must be a JSON object"
    version_value = result.get("version")
    if type(version_value) is not str or version_value != expected_version:
        return None, "Pyright output version does not match the pinned executable"
    summary = string_keyed_mapping(result.get("summary"))
    if summary is None:
        return None, "Pyright output summary must be a JSON object"
    files_analyzed = summary.get("filesAnalyzed")
    if type(files_analyzed) is not int or files_analyzed < expected_root_count:
        return None, "Pyright analyzed fewer roots than the batch contains"
    count_fields = {
        "error": "errorCount",
        "warning": "warningCount",
        "information": "informationCount",
    }
    counts: dict[str, int] = {}
    for count_severity, field in count_fields.items():
        count = summary.get(field)
        if type(count) is not int or count < 0:
            return None, f"Pyright summary field {field} must be a nonnegative integer"
        counts[count_severity] = count
    elapsed = summary.get("timeInSec")
    if type(elapsed) is int:
        if elapsed < 0:
            return None, "Pyright summary timeInSec must be a nonnegative number"
    elif type(elapsed) is float:
        if not math.isfinite(elapsed) or elapsed < 0:
            return None, "Pyright summary timeInSec must be a nonnegative number"
    else:
        return None, "Pyright summary timeInSec must be a nonnegative number"
    diagnostics = result.get("generalDiagnostics")
    if not is_object_list(diagnostics):
        return None, "Pyright generalDiagnostics must be a JSON array"
    observed = dict.fromkeys(count_fields, 0)
    for diagnostic in diagnostics:
        diagnostic_data = string_keyed_mapping(diagnostic)
        if diagnostic_data is None:
            return None, "Pyright diagnostic entry must be a JSON object"
        diagnostic_severity = diagnostic_data.get("severity")
        if type(diagnostic_severity) is not str or diagnostic_severity not in observed:
            return None, "Pyright diagnostic has an unsupported severity"
        observed[diagnostic_severity] += 1
    if observed != counts:
        return None, "Pyright summary diagnostic counts do not match its rows"
    return summary, None
