"""Executable package ownership rules, derived from the actual source tree."""

from __future__ import annotations

import ast
from collections.abc import Mapping
from pathlib import Path

from devtools.checks.source_discovery import authored_files

PUBLIC_PACKAGES = frozenset(
    {"api", "arithmetic", "hashlife", "sequences", "projection", "resources", "kernels"}
)
DEVELOPER_ROOTS = frozenset({"devtools", "tests", "bench", "research", "proofs"})


def module_inventory(
    root: Path, *, module_paths: tuple[Path, ...] | None = None
) -> dict[str, Path]:
    """Give each retained authored module exactly one qualified name."""
    root = Path(root).resolve()
    modules: dict[str, Path] = {}
    if module_paths is None:
        paths = tuple(
            path
            for path in authored_files(root)
            if path.suffix == ".py"
            and any(
                path.is_relative_to(root / directory)
                for directory in ("src", "devtools", "tests")
            )
        )
    else:
        paths = module_paths
    for path in sorted(paths):
        if path.is_relative_to(root / "src"):
            base = root / "src"
        elif path.is_relative_to(root / "devtools") or path.is_relative_to(
            root / "tests"
        ):
            base = root
        else:
            continue
        parts = path.relative_to(base).with_suffix("").parts
        if parts[-1] == "__init__":
            parts = parts[:-1]
        name = ".".join(parts)
        if name in modules:
            raise ValueError(f"duplicate module identity: {name}")
        modules[name] = path
    return modules


def package_violations(
    root: Path,
    *,
    parsed_sources: Mapping[Path, ast.Module] | None = None,
    module_paths: tuple[Path, ...] | None = None,
) -> tuple[str, ...]:
    """Check ownership without importing or executing the modules being audited."""
    root = Path(root).resolve()
    violations: list[str] = []
    modules = module_inventory(root, module_paths=module_paths)
    for module, path in modules.items():
        for directory in path.parents:
            if directory in (root, root / "src"):
                break
            if not (directory / "__init__.py").is_file():
                violations.append(f"{module}: missing package initializer: {directory}")
        tree = (
            parsed_sources[path]
            if parsed_sources is not None
            else ast.parse(path.read_text(), filename=str(path))
        )
        declarations = [
            node
            for node in tree.body
            if not (
                isinstance(node, ast.Expr)
                and isinstance(node.value, ast.Constant)
                and isinstance(node.value.value, str)
            )
        ]
        if (
            module.startswith("number_compiler.")
            and path.name != "__init__.py"
            and declarations
            and all(
                isinstance(node, (ast.Import, ast.ImportFrom)) for node in declarations
            )
        ):
            violations.append(f"{module}: forwarding module without implementation")
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                targets = [alias.name for alias in node.names]
            elif isinstance(node, ast.ImportFrom):
                targets = [node.module or ""]
            else:
                targets = []
            for target in targets:
                if isinstance(
                    node, (ast.Import, ast.ImportFrom)
                ) and "__init__" in target.split("."):
                    violations.append(
                        f"{module}:{node.lineno}: imports an alternate initializer identity {target}"
                    )
            if module.startswith("number_compiler.") and isinstance(
                node, (ast.Import, ast.ImportFrom)
            ):
                for target in targets:
                    if target.split(".")[0] in DEVELOPER_ROOTS:
                        violations.append(
                            f"{module}:{node.lineno}: developer dependency {target}"
                        )
            if (
                isinstance(node, ast.Call)
                and isinstance(node.func, ast.Attribute)
                and node.func.attr in {"insert", "append", "extend"}
                and isinstance(node.func.value, ast.Attribute)
                and node.func.value.attr == "path"
                and isinstance(node.func.value.value, ast.Name)
                and node.func.value.value.id == "sys"
            ):
                violations.append(
                    f"{module}:{node.lineno}: modifies module search path"
                )
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                assigned = (
                    node.targets if isinstance(node, ast.Assign) else [node.target]
                )
                for target_node in assigned:
                    if isinstance(target_node, ast.Subscript) and (
                        isinstance(target_node.value, ast.Attribute)
                        and target_node.value.attr == "modules"
                        and isinstance(target_node.value.value, ast.Name)
                        and target_node.value.value.id == "sys"
                        or isinstance(target_node.slice, ast.Name)
                        and target_node.slice.id == "__name__"
                    ):
                        violations.append(
                            f"{module}:{node.lineno}: redirects its module identity"
                        )
    package = root / "src" / "number_compiler"
    for path in package.glob("*.py"):
        if path.name not in {"__init__.py", "__main__.py"}:
            violations.append(f"unexpected root implementation: {path.name}")
    for path in package.iterdir() if package.is_dir() else ():
        if (
            path.is_dir()
            and path.name != "__pycache__"
            and any(path.rglob("*.py"))
            and path.name not in PUBLIC_PACKAGES
        ):
            violations.append(f"unowned production package: {path.name}")
    return tuple(violations)
