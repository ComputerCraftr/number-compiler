"""Structural-check reuse is content validated and shares no mutable AST."""

import ast
import os
from dataclasses import FrozenInstanceError
from pathlib import Path
from typing import Never

import pytest

from tests.support.source_imports import Import, ImportAlias, ImportFrom, source_imports


def test_import_facts_cover_nested_relative_and_aliased_imports(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    path = tmp_path / "module.py"
    path.write_text(
        "import os as operating\ndef f():\n    from ..core import kernel as k\n"
    )
    facts = source_imports(path)
    assert facts == (
        Import((ImportAlias("os", "operating"),)),
        ImportFrom("core", 2, (ImportAlias("kernel", "k"),)),
    )

    def forbidden(*args: object, **kwargs: object) -> Never:
        raise AssertionError("unchanged source was parsed again")

    monkeypatch.setattr(ast, "parse", forbidden)
    assert source_imports(path) is facts
    with pytest.raises(FrozenInstanceError):
        facts[0].__setattr__("names", ())


def test_import_facts_revalidate_content_even_when_stat_metadata_matches(
    tmp_path: Path,
) -> None:
    path = tmp_path / "module.py"
    path.write_text("import os\n")
    original = source_imports(path)
    stat = path.stat()
    path.write_text("import re\n")
    os.utime(path, ns=(stat.st_atime_ns, stat.st_mtime_ns))
    assert path.stat().st_size == stat.st_size
    assert source_imports(path) == (Import((ImportAlias("re", None),)),)
    assert source_imports(path) is not original
