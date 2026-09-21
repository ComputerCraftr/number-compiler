"""Documentation navigation and evidence cannot conceal missing or stale claims."""

from pathlib import Path

from devtools.checks.docs_index import check_docs


def _fixture(root: Path) -> None:
    docs = root / "docs"
    docs.mkdir()
    (docs / "index.md").write_text("# Index\n\n[Paper](paper.md#proof)\n")
    (docs / "paper.md").write_text("# Paper\n\n## Proof\n\nConditional result.\n")
    (docs / "catalog.toml").write_text(
        '[[document]]\nid="index"\npath="docs/index.md"\n'
        'kind="index"\ntopic="navigation"\nstatus="current"\n'
        '[[document]]\nid="paper"\npath="docs/paper.md"\n'
        'kind="research"\ntopic="arithmetic"\nstatus="current"\n'
    )


def test_complete_index_and_proof_link_pass(tmp_path: Path) -> None:
    _fixture(tmp_path)
    assert check_docs(tmp_path) == ()


def test_missing_heading_and_unindexed_note_are_reported(tmp_path: Path) -> None:
    _fixture(tmp_path)
    (tmp_path / "docs/paper.md").write_text("# A different result\n")
    (tmp_path / "docs/unreviewed.md").write_text("# Unreviewed\n")
    errors = check_docs(tmp_path)
    assert any("missing local heading" in error for error in errors)
    assert any("not catalogued" in error for error in errors)


def test_duplicate_research_and_supersession_cycle_fail(tmp_path: Path) -> None:
    _fixture(tmp_path)
    with (tmp_path / "docs/catalog.toml").open("a") as stream:
        stream.write(
            'supersedes=["second"]\n[[document]]\nid="second"\n'
            'path="docs/second.md"\nkind="research"\ntopic="arithmetic"\n'
            'status="current"\nsupersedes=["paper"]\n'
        )
    (tmp_path / "docs/second.md").write_text("# Second\n")
    errors = check_docs(tmp_path)
    assert any("multiple current" in error for error in errors)
    assert any("supersession cycle" in error for error in errors)


def test_artifact_and_path_escape_rejected_but_code_examples_ignored(
    tmp_path: Path,
) -> None:
    _fixture(tmp_path)
    (tmp_path / "run.log").write_text("local evidence\n")
    (tmp_path / "docs/paper.md").write_text(
        "# Paper\n\n## Proof\n\n[Raw](../run.log)\n"
        "[Outside](../../outside.md)\n```md\n[Example](absent.md)\n```\n"
    )
    errors = check_docs(tmp_path)
    assert any("raw run artifact" in error for error in errors)
    assert any("escapes repository" in error for error in errors)
    assert not any("absent.md" in error for error in errors)


def test_checkpoint_requires_provenance(tmp_path: Path) -> None:
    _fixture(tmp_path)
    catalog = tmp_path / "docs/catalog.toml"
    catalog.write_text(catalog.read_text().replace('kind="research"', 'kind="sprint"'))
    assert any("missing provenance" in error for error in check_docs(tmp_path))


def test_repository_documentation_is_indexed_and_links_resolve() -> None:
    from devtools.paths import repository_root

    assert check_docs(repository_root()) == ()
