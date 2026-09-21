"""The proof inventory is navigation and validation, never proof certification."""

from pathlib import Path

import pytest

from devtools.checks import isabelle_proof_index as index


def _fixture(root: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    directory = root / "devtools/proofs/isabelle"
    directory.mkdir(parents=True)
    (directory / "ROOT").write_text("session Example = HOL +\n  theories\n    Sample\n")
    (directory / "Sample.thy").write_text(
        "theory Sample imports Main begin\n"
        'lemma bounded [simp]: assumes "n = (0::nat)" shows "n < 1" by simp\n'
        'ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms bounded}) then () else error "oracle";\\<close>\n'
        "end\n"
    )
    monkeypatch.setattr(index, "ROOT", root)
    monkeypatch.setattr(index, "ISABELLE", directory)
    monkeypatch.setattr(index, "COUNTERPARTS", {})
    return directory


def test_index_retains_statement_assumptions_attributes_and_location(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _fixture(tmp_path, monkeypatch)
    result = index.build_index()
    theories = result["theories"]
    assert isinstance(theories, list)
    declaration = theories[0]["declarations"][0]
    assert declaration["name"] == "bounded" and declaration["line"] == 2
    assert '[simp]: assumes "n = (0::nat)"' in declaration["statement_and_assumptions"]
    assert theories[0]["session"] == "Example"
    assert theories[0]["counterparts"] == ()


@pytest.mark.parametrize(
    "fault", ["missing", "duplicate", "orphan", "unaudited", "counterpart"]
)
def test_index_rejects_structural_misrepresentation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fault: str
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    if fault == "missing":
        (directory / "Sample.thy").unlink()
    elif fault == "duplicate":
        with (directory / "ROOT").open("a") as output:
            output.write("session Second = HOL +\n  theories\n    Sample\n")
    elif fault == "orphan":
        (directory / "Orphan.thy").write_text("theory Orphan imports Main begin end\n")
    elif fault == "unaudited":
        path = directory / "Sample.thy"
        path.write_text(
            path.read_text().replace("Thm_Deps.all_oracles", "not_an_audit")
        )
    else:
        monkeypatch.setattr(index, "COUNTERPARTS", {"Sample": ("missing.py",)})
    with pytest.raises(ValueError):
        index.build_index()


def test_registered_proof_inventory_is_consistent() -> None:
    assert index.build_index()["schema_version"] == 1


def test_index_rejects_unregistered_import_cycle(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    (directory / "Cycle_A.thy").write_text("theory Cycle_A imports Cycle_B begin end\n")
    (directory / "Cycle_B.thy").write_text("theory Cycle_B imports Cycle_A begin end\n")
    with pytest.raises(ValueError, match="unregistered and unreachable theories"):
        index.build_index()


def test_index_accepts_unregistered_theory_reached_from_registered_root(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    sample = directory / "Sample.thy"
    sample.write_text(sample.read_text().replace("imports Main", "imports Helper"))
    (directory / "Helper.thy").write_text("theory Helper imports Main begin end\n")
    result = index.build_index()
    theories = result["theories"]
    assert isinstance(theories, list)
    helper = next(row for row in theories if row["theory"] == "Helper")
    assert helper["session"] is None


@pytest.mark.parametrize(
    "wrapper", ["(* {} *)", "(* outer (* {} *) *)", "text \\<open>{}\\<close>"]
)
def test_comment_or_documentation_cannot_forge_audit(wrapper: str) -> None:
    audit = "ML \\<open>Thm_Deps.all_oracles @{thms forged}\\<close>"
    assert index._audited_theorems(wrapper.format(audit)) == ()


def test_string_literal_cannot_forge_audit() -> None:
    assert (
        index._audited_theorems(
            'ML \\<open>val unused = "Thm_Deps.all_oracles @{thms forged}";\\<close>'
        )
        == ()
    )


def test_comments_and_documentation_cannot_forge_declarations_or_uses() -> None:
    text = (
        "theory Sample imports Main begin\n"
        "(* lemma commented: True by simp *)\n"
        "text \\<open>lemma documented: True by simp; bounded\\<close>\n"
        "lemma live: True by simp\n"
        "end\n"
    )
    assert [row["name"] for row in index._declarations(text)] == ["live"]
    clean = index._executable_text(text)
    assert "bounded" not in clean and "commented" not in clean


def test_noncall_marker_cannot_forge_audit() -> None:
    assert (
        index._audited_theorems(
            "ML \\<open>val audit = Thm_Deps.all_oracles; val named = @{thms bounded}\\<close>"
        )
        == ()
    )
