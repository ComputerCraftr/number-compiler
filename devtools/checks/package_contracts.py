"""Executable package ownership rules, derived from the actual source tree."""

from __future__ import annotations

import ast
from pathlib import Path

PUBLIC_PACKAGES = frozenset(
    {"api", "arithmetic", "hashlife", "sequences", "projection", "resources", "kernels"}
)
DEVELOPER_ROOTS = frozenset({"devtools", "tests", "bench", "research"})


def module_inventory(root: Path) -> dict[str, Path]:
    """Give each retained authored module exactly one qualified name."""
    modules: dict[str, Path] = {}
    for directory in (root / "src", root / "devtools", root / "tests"):
        base = root / "src" if directory.name == "src" else root
        for path in sorted(directory.rglob("*.py")):
            if "__pycache__" in path.parts:
                continue
            parts = path.relative_to(base).with_suffix("").parts
            if parts[-1] == "__init__":
                parts = parts[:-1]
            name = ".".join(parts)
            if name in modules:
                raise ValueError(f"duplicate module identity: {name}")
            modules[name] = path
    return modules


def package_violations(root: Path) -> tuple[str, ...]:
    """Check ownership without importing or executing the modules being audited."""
    violations: list[str] = []
    modules = module_inventory(root)
    for module, path in modules.items():
        for directory in path.parents:
            if directory in (root, root / "src"):
                break
            if not (directory / "__init__.py").is_file():
                violations.append(f"{module}: missing package initializer: {directory}")
        tree = ast.parse(path.read_text(), filename=str(path))
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
            if isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute):
                if ast.unparse(node.func) in {
                    "sys.path.insert",
                    "sys.path.append",
                    "sys.path.extend",
                }:
                    violations.append(
                        f"{module}:{node.lineno}: modifies module search path"
                    )
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                assigned = (
                    node.targets if isinstance(node, ast.Assign) else [node.target]
                )
                for target_node in assigned:
                    if isinstance(target_node, ast.Subscript) and (
                        ast.unparse(target_node.value) == "sys.modules"
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
