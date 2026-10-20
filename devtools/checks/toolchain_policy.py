"""Validate Python tool pins against the generated validation constraints."""

from __future__ import annotations

import importlib.metadata
import platform
import re
import tomllib
from collections.abc import Callable
from pathlib import Path

from packaging.requirements import InvalidRequirement, Requirement
from packaging.utils import canonicalize_name

from number_compiler.arithmetic.contracts.input_validation import (
    is_object_list,
    string_keyed_mapping,
)

_CONSTRAINTS = Path("devtools/typing/constraints-py314-macos.txt")
_TARGET_PATTERN = re.compile(
    r"^# Target: CPython (?P<python>[0-9]+\.[0-9]+\.[0-9]+) / "
    r"(?P<system>[A-Za-z]+) (?P<machine>[A-Za-z0-9_]+)$"
)
_EXACT_PIN_PATTERN = re.compile(r"==(?P<version>[^,*!=<>\s]+)\Z")

VersionReader = Callable[[str], str]


def _exact_requirement(raw: object) -> tuple[str, str] | None:
    if not isinstance(raw, str):
        return None
    try:
        requirement = Requirement(raw)
    except InvalidRequirement:
        return None
    if requirement.marker is not None and not requirement.marker.evaluate():
        return None
    specifiers = tuple(requirement.specifier)
    if len(specifiers) != 1 or specifiers[0].operator != "==":
        return None
    match = _EXACT_PIN_PATTERN.fullmatch(str(specifiers[0]))
    if match is None:
        return None
    return canonicalize_name(requirement.name), match.group("version")


def _declared_tool_pins(root: Path) -> tuple[dict[str, str], list[str]]:
    errors: list[str] = []
    project_path = root / "pyproject.toml"
    try:
        project_data: object = tomllib.loads(project_path.read_text(encoding="utf-8"))
    except (OSError, tomllib.TOMLDecodeError) as error:
        return {}, [f"cannot read pyproject.toml: {error}"]
    top = string_keyed_mapping(project_data)
    if top is None:
        return {}, ["pyproject.toml root must be a table"]
    project = string_keyed_mapping(top.get("project"))
    build_system = string_keyed_mapping(top.get("build-system"))
    if project is None or build_system is None:
        return {}, ["pyproject.toml must declare project and build-system tables"]

    dependencies: list[object] = []
    runtime_dependencies = project.get("dependencies", [])
    if not is_object_list(runtime_dependencies):
        errors.append("project.dependencies must be a list")
    else:
        dependencies.extend(runtime_dependencies)
    optional = string_keyed_mapping(project.get("optional-dependencies"))
    if optional is None:
        errors.append("project.optional-dependencies must be a table")
    else:
        for extra_name, raw_requirements in optional.items():
            if not is_object_list(raw_requirements):
                errors.append(f"optional dependency group {extra_name} must be a list")
                continue
            dependencies.extend(raw_requirements)
    build_requirements = build_system.get("requires")
    if not is_object_list(build_requirements):
        errors.append("build-system.requires must be a list")
    else:
        dependencies.extend(build_requirements)

    pins: dict[str, str] = {}
    for raw in dependencies:
        parsed = _exact_requirement(raw)
        if parsed is None:
            errors.append(f"tool dependency must have one exact version pin: {raw!r}")
            continue
        name, version = parsed
        previous = pins.get(name)
        if previous is not None and previous != version:
            errors.append(
                f"conflicting exact pins for {name}: {previous} and {version}"
            )
        else:
            pins[name] = version
    return pins, errors


def _constraint_pins(path: Path) -> tuple[dict[str, str], str | None, list[str]]:
    errors: list[str] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        return {}, None, [f"cannot read constraints file: {error}"]
    target: str | None = None
    pins: dict[str, str] = {}
    for line_number, line in enumerate(lines, start=1):
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("#"):
            if stripped.startswith("# Target:"):
                if target is not None:
                    errors.append("constraints file declares multiple targets")
                target = stripped
            continue
        parsed = _exact_requirement(stripped)
        if parsed is None:
            errors.append(f"constraints line {line_number} is not an exact pin")
            continue
        name, version = parsed
        if name in pins:
            errors.append(f"constraints file contains duplicate package {name}")
            continue
        pins[name] = version
    if target is None:
        errors.append("constraints file must declare one validation target")
    elif _TARGET_PATTERN.fullmatch(target) is None:
        errors.append("constraints target comment has an unsupported format")
    return pins, target, errors


def _normalized_platform(system: str, machine: str) -> tuple[str, str]:
    normalized_system = "macOS" if system in {"Darwin", "macOS"} else system
    normalized_machine = "arm64" if machine in {"aarch64", "arm64"} else machine
    return normalized_system, normalized_machine


def python_toolchain_violations(
    root: Path,
    *,
    version_reader: VersionReader = importlib.metadata.version,
    python_version: str | None = None,
    implementation: str | None = None,
    system: str | None = None,
    machine: str | None = None,
) -> tuple[str, ...]:
    """Compare declared exact pins, the target lock and installed distributions."""
    resolved_root = root.resolve()
    declared, errors = _declared_tool_pins(resolved_root)
    locked, target, lock_errors = _constraint_pins(resolved_root / _CONSTRAINTS)
    errors.extend(lock_errors)
    for name, version in declared.items():
        if locked.get(name) != version:
            errors.append(
                f"constraints pin for {name} does not match pyproject.toml ({version})"
            )
    target_match = _TARGET_PATTERN.fullmatch(target or "")
    if target_match is not None:
        current_python = python_version or platform.python_version()
        current_implementation = implementation or platform.python_implementation()
        current_system, current_machine = _normalized_platform(
            system or platform.system(), machine or platform.machine()
        )
        expected_system, expected_machine = _normalized_platform(
            target_match.group("system"), target_match.group("machine")
        )
        expected_runtime = (
            target_match.group("python"),
            "CPython",
            expected_system,
            expected_machine,
        )
        actual_runtime = (
            current_python,
            current_implementation,
            current_system,
            current_machine,
        )
        if actual_runtime != expected_runtime:
            errors.append(
                "validation lock target does not match runtime: "
                f"expected {expected_runtime!r}, found {actual_runtime!r}"
            )

    for name, expected in sorted(locked.items()):
        try:
            installed = version_reader(name)
        except importlib.metadata.PackageNotFoundError:
            installed = "unavailable"
        except ValueError as error:
            errors.append(f"cannot read installed version for {name}: {error}")
            continue
        if installed != expected:
            errors.append(
                f"installed {name} version {installed} does not match {expected}"
            )
    return tuple(errors)
