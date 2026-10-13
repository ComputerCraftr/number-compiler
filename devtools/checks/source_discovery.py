"""Discover authored files from Git, with a filesystem fallback for fixtures."""

from __future__ import annotations

import os
import subprocess
from pathlib import Path

IGNORED_PARTS = frozenset(
    {".git", ".venv", ".pytest_cache", "__pycache__", ".mypy_cache", ".ruff_cache"}
)
IGNORED_ROOTS = frozenset({"results", "build", "dist", "venv"})


def _ignored(relative: Path) -> bool:
    return bool(relative.parts) and (
        relative.parts[0] in IGNORED_ROOTS
        or any(part in IGNORED_PARTS for part in relative.parts)
    )


def _filesystem_files(root: Path) -> tuple[Path, ...]:
    files: list[Path] = []
    for directory, dirnames, filenames in os.walk(
        root, topdown=True, followlinks=False
    ):
        parent = Path(directory)
        relative_parent = parent.relative_to(root)
        dirnames[:] = sorted(
            name for name in dirnames if not _ignored(relative_parent / name)
        )
        files.extend(parent / name for name in filenames if (parent / name).is_file())
    return tuple(sorted(files))


def authored_files(root: Path) -> tuple[Path, ...]:
    """Return tracked plus untracked/nonignored files under a Git directory.

    Temporary policy fixtures are not repositories, so they use the same
    generated-directory exclusions through the filesystem fallback.
    """
    root = root.resolve()
    top_level = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "--show-toplevel"],
        capture_output=True,
        check=False,
        text=True,
    )
    if top_level.returncode != 0:
        return _filesystem_files(root)
    git_root = Path(top_level.stdout.strip()).resolve()
    if not root.is_relative_to(git_root):
        return _filesystem_files(root)

    listing = subprocess.run(
        [
            "git",
            "-C",
            str(git_root),
            "ls-files",
            "--full-name",
            "--cached",
            "--others",
            "--exclude-standard",
            "-z",
        ],
        capture_output=True,
        check=False,
    )
    if listing.returncode != 0:
        detail = listing.stderr.decode("utf-8", errors="replace").strip()
        raise RuntimeError(f"cannot discover Git-authored files: {detail}")
    paths = {
        git_root / Path(os.fsdecode(raw)) for raw in listing.stdout.split(b"\0") if raw
    }
    return tuple(
        sorted(
            path
            for path in paths
            if path.is_file()
            and path.is_relative_to(root)
            and not _ignored(path.relative_to(git_root))
        )
    )
