"""Exercise the release AST lint rule for eager annotation evaluation."""

import subprocess
import sys

import pytest

from devtools.paths import repository_root


@pytest.mark.parametrize(
    ("source", "postponed", "eager"),
    [
        ("def periodic_word(arena: SLPArena) -> int:\n    return 0\n", False, True),
        ('def periodic_word(arena: "SLPArena") -> int:\n    return 0\n', False, False),
        (
            "def periodic_word(arena: SLPArena) -> int:\n    return 0\n",
            True,
            False,
        ),
        (
            "def periodic_word(arena: SLPArena = SLPArena()) -> int:\n    return 0\n",
            True,
            True,
        ),
    ],
    ids=("eager", "quoted", "postponed", "runtime-default"),
)
def test_type_checking_imports_are_unavailable_at_runtime(
    source: str, postponed: bool, eager: bool
) -> None:
    # Exercise the pinned Ruff parser using the real project configuration.
    code = "from __future__ import annotations\n\n" if postponed else ""
    code += (
        "import typing as t\n\n"
        "if t.TYPE_CHECKING:\n"
        "    from number_compiler.arithmetic.automata.slp import SLPArena\n\n\n"
    )
    result = subprocess.run(
        [
            sys.executable,
            "-m",
            "ruff",
            "check",
            "--output-format",
            "concise",
            "--stdin-filename",
            "src/number_compiler/arithmetic/automata/periodic_slp.py",
            "-",
        ],
        cwd=repository_root(),
        input=code + source,
        text=True,
        capture_output=True,
        check=False,
    )
    assert not result.stderr
    if eager:
        assert result.returncode == 1
        assert "TC004" in result.stdout
        assert "SLPArena" in result.stdout
    else:
        assert result.returncode == 0, result.stdout
