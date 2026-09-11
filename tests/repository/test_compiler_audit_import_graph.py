"""Architecture audits must traverse canonical packages beyond root facades."""

from pathlib import Path

import pytest

import devtools.checks.dependency_graph as audit


def _write(root: Path, name: str, source: str) -> None:
    path = root / name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source)


def test_audit_follows_relative_absolute_and_package_alias_imports(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(audit, "SRC", tmp_path)
    _write(tmp_path, "entry.py", "from .api import compiler as implementation\n")
    _write(tmp_path, "api/__init__.py", "")
    _write(tmp_path, "api/compiler.py", "from ..runtime.scheduler import execute\n")
    _write(tmp_path, "runtime/__init__.py", "")
    _write(
        tmp_path,
        "runtime/scheduler.py",
        "import number_compiler.arithmetic.tokens as tokens\n",
    )
    _write(tmp_path, "arithmetic/tokens.py", "VALUE = 1\n")
    assert audit._reachable("entry") == {
        "entry",
        "api",
        "api.compiler",
        "runtime.scheduler",
        "arithmetic.tokens",
    }
    assert audit._module_path("api") == tmp_path / "api/__init__.py"


def test_type_checking_edges_do_not_hide_runtime_else_imports(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    monkeypatch.setattr(audit, "SRC", tmp_path)
    _write(
        tmp_path,
        "entry.py",
        """from typing import TYPE_CHECKING
if TYPE_CHECKING:
    from .proof.oracle import Exact
else:
    from .runtime import engine
""",
    )
    _write(tmp_path, "proof/oracle.py", "")
    _write(tmp_path, "runtime/__init__.py", "")
    _write(tmp_path, "runtime/engine.py", "")
    assert audit._reachable("entry") == {"entry", "runtime", "runtime.engine"}
