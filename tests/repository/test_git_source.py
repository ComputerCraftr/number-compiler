"""Git commit identity replaces filesystem source snapshots."""

from __future__ import annotations

from pathlib import Path

import pytest

from devtools.git_source import (
    AcceptanceCheckoutError,
    acceptance_checkout,
    git_source,
)
from tests.support.git_repositories import commit_fixture, git


def _repository(root: Path) -> Path:
    root.mkdir(parents=True)
    (root / "src").mkdir()
    (root / "src" / "module.py").write_text("value = 1\n")
    (root / ".gitignore").write_text("results/\n")
    commit_fixture(root, "initial")
    return root


def test_git_source_reports_commit_tree_format_and_dirty_status(tmp_path: Path) -> None:
    root = _repository(tmp_path / "repo")
    clean = git_source(root)
    assert len(clean.commit) >= 40
    assert len(clean.tree) >= 40
    assert clean.object_format in {"sha1", "sha256"}
    assert clean.dirty is False
    assert clean.as_dict() == {
        "git_commit": clean.commit,
        "git_tree": clean.tree,
        "git_object_format": clean.object_format,
        "git_dirty": False,
    }

    (root / "src" / "module.py").write_text("value = 2\n")
    dirty = git_source(root)
    assert dirty.commit == clean.commit
    assert dirty.tree == clean.tree
    assert dirty.dirty is True
    git(root, "add", "src/module.py")
    git(
        root,
        "-c",
        "user.name=Test",
        "-c",
        "user.email=test@example.invalid",
        "commit",
        "-qm",
        "updated",
    )
    updated = git_source(root)
    assert not updated.dirty
    assert updated.commit != clean.commit
    assert updated.tree != clean.tree


def test_acceptance_worktree_is_detached_and_removed_when_clean(tmp_path: Path) -> None:
    root = _repository(tmp_path / "repo")
    baseline = git_source(root)
    parent = tmp_path / "acceptance"
    with acceptance_checkout(root, parent) as checkout:
        assert git_source(checkout) == baseline
        assert not git(checkout, "symbolic-ref", "-q", "HEAD", check=False)
        assert checkout.resolve().parent == parent.resolve()
        generated = checkout / "results" / "run.json"
        generated.parent.mkdir()
        generated.write_text("generated output\n")
        assert not git_source(checkout).dirty
    assert not (parent / f"worktree-{baseline.commit[:12]}").exists()
    assert not git(root, "worktree", "list", "--porcelain").count(str(parent.resolve()))
    assert git_source(root) == baseline


def test_acceptance_refuses_dirty_roots_including_untracked_files(
    tmp_path: Path,
) -> None:
    root = _repository(tmp_path / "repo")
    (root / "untracked.py").write_text("value = 2\n")
    with (
        pytest.raises(AcceptanceCheckoutError, match="clean committed"),
        acceptance_checkout(root),
    ):
        pytest.fail("dirty acceptance root must be refused")


@pytest.mark.parametrize("path", ["src/module.py", "untracked.py"])
def test_dirty_acceptance_worktree_is_preserved_for_inspection(
    tmp_path: Path, path: str
) -> None:
    root = _repository(tmp_path / "repo")
    parent = tmp_path / "acceptance"
    checkout: Path | None = None
    with (
        pytest.raises(AcceptanceCheckoutError, match="was preserved"),
        acceptance_checkout(root, parent) as checkout_path,
    ):
        checkout = checkout_path
        target = checkout / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text("edited during run\n")
    assert checkout is not None and checkout.exists()
    assert git_source(checkout).dirty
    assert git(root, "worktree", "list", "--porcelain")
