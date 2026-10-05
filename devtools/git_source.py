"""Git-owned source identity and safe acceptance worktree lifecycle."""

from __future__ import annotations

import contextlib
import subprocess
import tempfile
import time
from collections.abc import Iterator
from dataclasses import dataclass
from pathlib import Path


class GitSourceError(RuntimeError):
    """The requested source directory has no usable Git identity."""


class AcceptanceCheckoutError(RuntimeError):
    """An acceptance checkout was dirty, moved, or could not be retired safely."""


@dataclass(frozen=True)
class GitSource:
    commit: str
    tree: str
    object_format: str
    dirty: bool

    def as_dict(self) -> dict[str, str | bool]:
        return {
            "git_commit": self.commit,
            "git_tree": self.tree,
            "git_object_format": self.object_format,
            "git_dirty": self.dirty,
        }


def _git(
    root: Path,
    *arguments: str,
    check: bool = True,
    deadline: float | None = None,
) -> str:
    from devtools.checks.process_guard import remaining_deadline_seconds

    try:
        result = subprocess.run(
            ("git", "-C", str(root), *arguments),
            check=False,
            capture_output=True,
            text=True,
            timeout=remaining_deadline_seconds(deadline=deadline),
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise GitSourceError(f"cannot run git in {root}: {error}") from error
    if check and result.returncode:
        detail = result.stderr.strip() or result.stdout.strip()
        raise GitSourceError(f"git {' '.join(arguments)} failed: {detail}")
    if result.returncode:
        return ""
    return result.stdout.strip()


def git_source(root: Path) -> GitSource:
    """Read commit/tree identity and Git's own tracked/untracked dirty status."""
    from devtools.checks.process_guard import remaining_deadline_seconds

    root = root.resolve(strict=True)
    deadline = time.monotonic() + remaining_deadline_seconds()
    commit = _git(root, "rev-parse", "--verify", "HEAD^{commit}", deadline=deadline)
    tree = _git(root, "rev-parse", "--verify", "HEAD^{tree}", deadline=deadline)
    object_format = _git(root, "rev-parse", "--show-object-format", deadline=deadline)
    status = _git(
        root,
        "status",
        "--porcelain=v1",
        "--untracked-files=all",
        deadline=deadline,
    )
    return GitSource(commit, tree, object_format, bool(status))


def clean_revision_unchanged(before: GitSource, after: GitSource) -> bool:
    """Certify equal clean Git identities; dirty states never certify source."""
    return not before.dirty and not after.dirty and same_git_revision(before, after)


def same_git_revision(before: GitSource, after: GitSource) -> bool:
    """Compare committed revision identities without inferring dirty contents."""
    return (
        before.commit == after.commit
        and before.tree == after.tree
        and before.object_format == after.object_format
    )


def _clean_status(root: Path) -> bool:
    return not _git(root, "status", "--porcelain=v1", "--untracked-files=all")


def _worktree_is_registered(root: Path, checkout: Path) -> bool:
    output = _git(root, "worktree", "list", "--porcelain")
    paths = {
        Path(line.removeprefix("worktree ")).resolve()
        for line in output.splitlines()
        if line.startswith("worktree ")
    }
    return checkout.resolve() in paths


@contextlib.contextmanager
def acceptance_checkout(
    root: Path, worktree_parent: Path | None = None
) -> Iterator[Path]:
    """Yield one clean detached worktree and preserve it if a run changes it.

    The temporary worktree is created outside the source checkout by default,
    so results and generated files cannot become authored input. A dirty or
    moved worktree is deliberately left on disk for inspection.
    """
    root = root.resolve(strict=True)
    baseline = git_source(root)
    if baseline.dirty:
        raise AcceptanceCheckoutError("acceptance requires a clean committed tree")
    if worktree_parent is None:
        parent = Path(tempfile.mkdtemp(prefix="number-compiler-acceptance-"))
        owns_parent = True
    else:
        parent = worktree_parent.resolve()
        if parent == root or root in parent.parents:
            raise AcceptanceCheckoutError(
                "acceptance worktree artifacts must stay outside the source checkout"
            )
        parent.mkdir(parents=True, exist_ok=True)
        owns_parent = False
    checkout = parent / f"worktree-{baseline.commit[:12]}"
    if checkout.exists():
        if owns_parent:
            parent.rmdir()
        raise AcceptanceCheckoutError(f"acceptance path already exists: {checkout}")
    added = False
    try:
        _git(root, "worktree", "add", "--detach", str(checkout), baseline.commit)
        added = True
        source = git_source(checkout)
        detached = not _git(checkout, "symbolic-ref", "-q", "HEAD", check=False)
        if source.dirty or source.commit != baseline.commit or not detached:
            raise AcceptanceCheckoutError(
                "new acceptance worktree is not a clean detached checkout"
            )
        yield checkout
    finally:
        if added:
            after = git_source(checkout)
            detached = not _git(checkout, "symbolic-ref", "-q", "HEAD", check=False)
            safe_to_remove = (
                not after.dirty
                and after.commit == baseline.commit
                and detached
                and _worktree_is_registered(root, checkout)
            )
            if safe_to_remove:
                _git(root, "worktree", "remove", str(checkout))
                if owns_parent:
                    parent.rmdir()
            else:
                raise AcceptanceCheckoutError(
                    "acceptance worktree changed and was preserved at "
                    f"{checkout}; inspect it before cleanup"
                )
        elif owns_parent and parent.exists():
            parent.rmdir()
