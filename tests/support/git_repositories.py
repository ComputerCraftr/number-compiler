"""Minimal committed Git fixtures shared by provenance tests."""

from __future__ import annotations

import subprocess
from pathlib import Path


def git(root: Path, *arguments: str, check: bool = True) -> str:
    result = subprocess.run(
        ("git", "-C", str(root), *arguments),
        check=False,
        capture_output=True,
        text=True,
    )
    if check and result.returncode:
        raise AssertionError(result.stderr)
    return result.stdout.strip()


def commit_fixture(root: Path, message: str = "fixture") -> None:
    subprocess.run(("git", "init", "-q", str(root)), check=True)
    git(root, "add", ".")
    git(
        root,
        "-c",
        "user.name=Test",
        "-c",
        "user.email=test@example.invalid",
        "commit",
        "-qm",
        message,
    )
