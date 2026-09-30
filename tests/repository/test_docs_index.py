"""Documentation navigation and evidence cannot conceal missing or stale claims."""

from pathlib import Path

import pytest

from devtools.checks.docs_index import check_docs
from devtools.checks.sprint_scaffold import refresh_index, scaffold, sunday


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


@pytest.mark.parametrize(
    ("start", "folder", "end", "error"),
    [
        ("2026-09-27", "2026-09-27", "2026-10-03", None),
        ("2026-09-21", "2026-09-21", "2026-09-27", "must be a Sunday"),
        ("2026-09-27", "2026-09-20", "2026-10-03", "folder must match"),
        ("2026-09-27", "2026-09-27", "2026-10-04", "must declare"),
        ("not-a-date", "2026-09-27", "2026-10-03", "invalid sprint"),
    ],
)
def test_sprint_calendar_boundaries(
    tmp_path: Path, start: str, folder: str, end: str, error: str | None
) -> None:
    _fixture(tmp_path)
    relative = f"docs/sprints/week-of-{folder}/README.md"
    sprint = tmp_path / relative
    sprint.parent.mkdir(parents=True)
    sprint.write_text(
        f"# Sprint\n\nPeriod: {start} through {end} (Sunday–Saturday).\n"
        "\n## Provenance\n\nHistorical evidence.\n"
    )
    with (tmp_path / "docs/catalog.toml").open("a") as stream:
        stream.write(
            f'[[document]]\nid="sprint"\npath="{relative}"\n'
            'kind="sprint"\ntopic="repository"\nstatus="current"\n'
            f'week_start="{start}"\n'
        )
    if error is None:
        refresh_index(sprint.parent, sunday(start))
    errors = check_docs(tmp_path)
    if error is None:
        assert errors == ()
    else:
        assert any(error in message for message in errors)


def test_repository_documentation_is_indexed_and_links_resolve() -> None:
    from devtools.paths import repository_root

    assert check_docs(repository_root()) == ()


def test_scaffold_preserves_authored_topic_and_registers_new_category(
    tmp_path: Path,
) -> None:
    _fixture(tmp_path)
    index = tmp_path / "docs/index.md"
    index.write_text(index.read_text() + "\n## Sprint history and provenance\n")
    path = scaffold(tmp_path, "2026-09-27", "new-category", "A new category")
    original = (
        path.read_text() + "\n## Actual experiment\n\nSource abc; two failures.\n"
    )
    path.write_text(original)
    scaffold(tmp_path, "2026-09-27", "new-category", "A changed title")
    assert path.read_text() == original
    assert (
        "[A new category](new-category.md) | 1"
        in (path.parent / "README.md").read_text()
    )
    assert not refresh_index(path.parent, sunday("2026-09-27"), check=True)
    assert check_docs(tmp_path) == ()


def test_stale_topic_count_and_missing_template_section_fail(tmp_path: Path) -> None:
    _fixture(tmp_path)
    path = scaffold(tmp_path, "2026-09-27", "accounting", "Accounting")
    path.write_text(path.read_text().replace("## Changes", "## Extra record"))
    errors = check_docs(tmp_path)
    assert any("missing sprint topic section: Changes" in error for error in errors)
    assert any("topic links/counts are stale" in error for error in errors)


def test_cli_capability_table_and_parser_examples_are_current() -> None:
    from devtools.checks.cli_docs import check_cli_docs
    from devtools.paths import repository_root

    assert check_cli_docs(repository_root()) == []


def test_cli_example_validation_never_executes_arithmetic(tmp_path: Path) -> None:
    from devtools.checks.cli_docs import check_cli_docs

    (tmp_path / "README.md").write_text(
        "```sh\nnumber-compiler collatz --nth 8 --seed 27\n"
        "number-compiler collatz --nth 8 --seed 27 --info mirror\n```\n"
    )
    errors = check_cli_docs(tmp_path)
    assert len(errors) == 1
    assert "invalid CLI example" in errors[0]
