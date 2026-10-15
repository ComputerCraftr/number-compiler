"""Import boundary: exact reverse oracles cannot be production dependencies."""

from __future__ import annotations

import ast
from collections.abc import Mapping
from pathlib import Path

from devtools.checks.package_contracts import DEVELOPER_ROOTS
from devtools.checks.source_discovery import authored_files

LEGACY_MODULES = frozenset(
    {
        "reverse_spacetime",
        "temporal_quotient",
        "reverse_action",
        "forcing_morphism",
    }
)

# Production has no compatibility exemptions. Proof callers live in devtools.
EXPLICIT_PROOF_BOUNDARIES: frozenset[str] = frozenset()


def proof_import_violations(source: str, module: str) -> tuple[str, ...]:
    """Inspect imports, including local imports and literal dynamic imports."""
    return proof_import_tree_violations(ast.parse(source), module)


def proof_import_tree_violations(tree: ast.Module, module: str) -> tuple[str, ...]:
    """Inspect one already-parsed module with the same proof import rules."""
    violations: list[str] = []
    for node in ast.walk(tree):
        targets: list[str] = []
        if isinstance(node, ast.Import):
            targets.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom):
            target = node.module or ""
            if node.level:
                package = module.split(".")[:-1]
                target = ".".join(
                    package[: len(package) - node.level + 1]
                    + ([target] if target else [])
                )
            targets.append(target)
            targets.extend(f"{target}.{alias.name}" for alias in node.names)
        elif isinstance(node, ast.Call):
            name = (
                node.func.attr
                if isinstance(node.func, ast.Attribute)
                else node.func.id
                if isinstance(node.func, ast.Name)
                else ""
            )
            if name in {"__import__", "import_module"} and node.args:
                arg = node.args[0]
                if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
                    target = arg.value
                    if target.startswith("."):
                        target = "number_compiler" + target
                    targets.append(target)
        if not targets:
            continue
        assert isinstance(node, (ast.Import, ast.ImportFrom, ast.Call))
        for target in targets:
            parts = target.split(".")
            if (
                parts[0] in DEVELOPER_ROOTS
                or len(parts) >= 2
                and parts[0] == "number_compiler"
                and ("proof" in parts or parts[1] in LEGACY_MODULES)
            ):
                violations.append(f"{module}:{node.lineno}: {target}")
    return tuple(violations)


def production_proof_import_violations(
    package: Path,
    *,
    parsed_sources: Mapping[Path, ast.Module] | None = None,
) -> tuple[str, ...]:
    """Audit production modules, optionally reusing a caller-owned AST snapshot."""
    package = package.resolve()
    violations: list[str] = []
    for path in authored_files(package):
        if path.suffix != ".py":
            continue
        relative = path.relative_to(package)
        if relative.parts[0] == "proof":
            continue
        module = "number_compiler." + ".".join(relative.with_suffix("").parts)
        if module in EXPLICIT_PROOF_BOUNDARIES:
            continue
        if parsed_sources is None:
            violations.extend(proof_import_violations(path.read_text(), module))
        else:
            violations.extend(
                proof_import_tree_violations(parsed_sources[path], module)
            )
    return tuple(violations)
