"""Read-only values shared by repository-level Isabelle ancestry tests."""

from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path
from typing import NamedTuple

from devtools.checks import isabelle_syntax


class RepositoryProofGraph(NamedTuple):
    sessions: Mapping[str, isabelle_syntax.Session]
    headers: Mapping[Path, tuple[str, tuple[str, ...]]]
    theory_imports: Mapping[str, tuple[str, ...]]
