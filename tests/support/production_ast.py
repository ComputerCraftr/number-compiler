"""One immutable-by-convention AST graph for read-only production checks."""

from __future__ import annotations

import ast
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path
from types import MappingProxyType

import pytest

from devtools.checks.source_discovery import authored_files
from devtools.paths import repository_root


@dataclass(frozen=True, slots=True)
class ProductionASTGraph:
    """Parsed source modules shared by structural checks in one test session."""

    modules: Mapping[Path, ast.Module]

    def under(self, root: Path) -> Mapping[Path, ast.Module]:
        resolved_root = root.resolve()
        return MappingProxyType(
            {
                path: tree
                for path, tree in self.modules.items()
                if path.is_relative_to(resolved_root)
            }
        )


@pytest.fixture(scope="session")
def production_ast_graph() -> ProductionASTGraph:
    """Parse authored production modules used by structural policy checks."""
    root = repository_root()
    source_root = root / "src" / "number_compiler"
    authored = authored_files(source_root)
    paths = sorted(
        {
            path.resolve()
            for path in authored
            if path.suffix == ".py" and path.is_relative_to(source_root)
        }
    )
    modules = {
        path: ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        for path in paths
    }
    return ProductionASTGraph(MappingProxyType(modules))
