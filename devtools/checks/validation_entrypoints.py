"""AST checks that keep validation launchers under shared run policy."""

from __future__ import annotations

import ast
import shlex
from collections.abc import Callable, Mapping
from pathlib import Path
from typing import TypeGuard


def validation_entrypoint_violations(
    root: Path,
    parsed_sources: Mapping[Path, ast.Module],
    module_name_for: Callable[[Path], str],
) -> tuple[str, ...]:
    """Require validation/probe entry points to use the shared run guard.

    This checks executable AST calls, not occurrences of words in strings.
    The release runner is the one intentional pytest launcher; the process
    guard is an orchestration root with synthetic watchdog subprocesses.
    """
    root = Path(root).resolve()
    sources = parsed_sources
    owned_roots = (
        Path("devtools/checks"),
        Path("devtools/benchmarks"),
        Path("devtools/verification"),
        Path("devtools/experiments"),
    )
    orchestration = {
        Path("devtools/checks/release.py"),
        Path("devtools/checks/process_guard.py"),
    }
    violations: list[str] = []

    def main_guard(node: ast.stmt) -> TypeGuard[ast.If]:
        return (
            isinstance(node, ast.If)
            and isinstance(node.test, ast.Compare)
            and len(node.test.ops) == 1
            and isinstance(node.test.ops[0], ast.Eq)
            and len(node.test.comparators) == 1
            and (
                (
                    isinstance(node.test.left, ast.Name)
                    and node.test.left.id == "__name__"
                    and isinstance(node.test.comparators[0], ast.Constant)
                    and node.test.comparators[0].value == "__main__"
                )
                or (
                    isinstance(node.test.left, ast.Constant)
                    and node.test.left.value == "__main__"
                    and isinstance(node.test.comparators[0], ast.Name)
                    and node.test.comparators[0].id == "__name__"
                )
            )
        )

    def aliases_for(
        module: ast.Module, name: str, is_package: bool
    ) -> tuple[dict[str, list[ast.AST]], tuple[ast.AST, ...]]:
        """Resolve aliases and retain one walk for subsequent call inspection."""
        aliases: dict[str, list[ast.AST]] = {}

        def bind(name: str, expression: str) -> None:
            aliases.setdefault(name, []).append(ast.parse(expression, mode="eval").body)

        nodes = tuple(ast.walk(module))
        for item in nodes:
            if isinstance(item, ast.Import):
                for alias in item.names:
                    if alias.asname and alias.asname != alias.name:
                        bind(alias.asname, alias.name)
            elif isinstance(item, ast.ImportFrom) and item.module:
                base = item.module
                if item.level:
                    parts = name.split(".")
                    package = parts if is_package else parts[:-1]
                    parent = package[: max(0, len(package) - item.level + 1)]
                    base = ".".join((*parent, *base.split(".")))
                for alias in item.names:
                    if alias.name != "*":
                        bind(alias.asname or alias.name, f"{base}.{alias.name}")
            elif isinstance(item, ast.Assign):
                for target in item.targets:
                    if isinstance(target, ast.Name):
                        aliases.setdefault(target.id, []).append(item.value)
            elif (
                isinstance(item, ast.AnnAssign)
                and item.value is not None
                and isinstance(item.target, ast.Name)
            ):
                aliases.setdefault(item.target.id, []).append(item.value)
        return aliases, nodes

    def expression_paths(
        expression: ast.AST, aliases: Mapping[str, list[ast.AST]]
    ) -> set[str]:
        paths: set[str] = set()
        pending: list[tuple[ast.AST, tuple[str, ...], frozenset[str]]] = [
            (expression, (), frozenset())
        ]
        while pending:
            node, suffix, seen = pending.pop()
            if isinstance(node, ast.Attribute):
                pending.append((node.value, (node.attr, *suffix), seen))
            elif isinstance(node, ast.Name):
                if node.id in seen:
                    continue
                definitions = aliases.get(node.id, ())
                if definitions:
                    pending.extend(
                        (definition, suffix, seen | {node.id})
                        for definition in definitions
                    )
                else:
                    paths.add(".".join((node.id, *suffix)))
        return paths

    def is_guarded_call(
        expression: ast.AST, aliases: Mapping[str, list[ast.AST]]
    ) -> bool:
        return isinstance(expression, ast.Call) and (
            "devtools.runs.run_reported" in expression_paths(expression.func, aliases)
        )

    def executable_guarded_wrapper(
        node: ast.If, aliases: Mapping[str, list[ast.AST]]
    ) -> bool:
        for statement in node.body:
            if isinstance(statement, ast.Expr) and is_guarded_call(
                statement.value, aliases
            ):
                return True
            if not isinstance(statement, ast.Raise) or not isinstance(
                statement.exc, ast.Call
            ):
                continue
            if "SystemExit" not in expression_paths(statement.exc.func, aliases):
                continue
            if len(statement.exc.args) == 1 and is_guarded_call(
                statement.exc.args[0], aliases
            ):
                return True
        return False

    def command_words(
        node: ast.AST, aliases: Mapping[str, list[ast.AST]]
    ) -> tuple[str | None, ...]:
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return tuple(shlex.split(node.value))
        if not isinstance(node, (ast.List, ast.Tuple)):
            return ()
        words: list[str | None] = []
        for value in node.elts:
            if isinstance(value, ast.Constant) and isinstance(value.value, str):
                words.append(value.value)
            elif isinstance(
                value, ast.Attribute
            ) and "sys.executable" in expression_paths(value, aliases):
                words.append("<python>")
            else:
                words.append(None)
        return tuple(words)

    for path, module in sources.items():
        relative = path.relative_to(root)
        if not any(relative.is_relative_to(directory) for directory in owned_roots):
            continue
        if relative in orchestration:
            continue
        aliases, nodes = aliases_for(
            module, module_name_for(path), path.name == "__init__.py"
        )
        for statement in module.body:
            if main_guard(statement) and not executable_guarded_wrapper(
                statement, aliases
            ):
                violations.append(
                    f"{relative.as_posix()}:{statement.lineno}: standalone validation entry point must call run_reported"
                )
        for node in nodes:
            if not isinstance(node, ast.Call):
                continue
            call_paths = expression_paths(node.func, aliases)
            direct_subprocess = any(
                path.startswith("subprocess.")
                and path.rsplit(".", 1)[-1]
                in {"run", "Popen", "call", "check_call", "check_output"}
                for path in call_paths
            )
            direct_pytest_main = "pytest.main" in call_paths
            if direct_pytest_main:
                violations.append(
                    f"{relative.as_posix()}:{node.lineno}: pytest must be launched by the shared release runner"
                )
            if not direct_subprocess or not node.args:
                continue
            words = command_words(node.args[0], aliases)
            direct = bool(words) and (
                words[0] in {"pytest", "py.test"}
                or (
                    len(words) >= 3
                    and (
                        words[0] == "<python>"
                        or Path(words[0] or "").name.startswith(("python", "pypy"))
                    )
                    and words[1:3] == ("-m", "pytest")
                )
            )
            if direct:
                violations.append(
                    f"{relative.as_posix()}:{node.lineno}: pytest must be launched by the shared release runner"
                )
    return tuple(sorted(violations))
