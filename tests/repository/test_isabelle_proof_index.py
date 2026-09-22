"""The proof inventory is navigation and validation, never proof certification."""

from pathlib import Path

import pytest

from devtools.checks import isabelle_proof_index as index
from devtools.checks import isabelle_syntax as syntax


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
    clean = syntax.executable_text(text)
    assert "bounded" not in clean and "commented" not in clean


def test_noncall_marker_cannot_forge_audit() -> None:
    assert (
        index._audited_theorems(
            "ML \\<open>val audit = Thm_Deps.all_oracles; val named = @{thms bounded}\\<close>"
        )
        == ()
    )


def test_nested_documentation_and_escaped_strings_cannot_forge_proof_items() -> None:
    text = (
        "theory Sample imports Main begin\n"
        "text \\<open>outer \\<open>lemma forged: True by simp\\<close> "
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms forged}) "
        'then () else error "oracle";\\<close>\\<close>\n'
        'ML \\<open>val message = "quoted \\"text \\<open>lemma string_forged\\<close>\\"";'
        " val _ = if null (Thm_Deps.all_oracles @{thms live}) "
        'then () else error "oracle";\\<close>\n'
        "lemma live: True by simp\nend\n"
    )
    assert [row["name"] for row in index._declarations(text)] == ["live"]
    assert index._audited_theorems(text) == ("live",)


def test_comment_cannot_forge_theory_header_or_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    root = directory / "ROOT"
    root.write_text(
        "(* session Forged = HOL +\n  theories\n    Forged *)\n" + root.read_text()
    )
    sample = directory / "Sample.thy"
    sample.write_text(
        "(* theory Forged imports Missing begin *)\n" + sample.read_text()
    )
    result = index.build_index()
    sessions = result["sessions"]
    theories = result["theories"]
    assert isinstance(sessions, list) and isinstance(theories, list)
    assert [row["session"] for row in sessions] == ["Example"]
    assert [row["theory"] for row in theories] == ["Sample"]


def test_session_path_and_malformed_declarations_fail_closed() -> None:
    assert syntax.parse_sessions(
        'session Scoped in "local" = HOL +\n  theories\n    Sample\n'
    )[0].directory == Path("local")
    with pytest.raises(ValueError, match="escapes"):
        syntax.parse_sessions('session Escape in "../outside" = HOL +\n')
    with pytest.raises(ValueError, match="unsupported session"):
        syntax.parse_sessions("session Good = HOL +\nsession Bad =\n")


def test_quoted_comment_markers_leave_later_theorems_visible() -> None:
    text = (
        "theory Sample imports Main begin\n"
        'definition quoted where "quoted = (\\"(* literal *)\\" :: string)"\n'
        "lemma live: True by simp\n"
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms live}) "
        'then () else error "oracle";\\<close>\nend\n'
    )
    assert [row["name"] for row in index._declarations(text)] == ["live"]
    assert index._audited_theorems(text) == ("live",)


def test_multiline_strings_and_ml_bodies_cannot_forge_commands() -> None:
    root = (
        'description "note\nsession Forged = HOL +\n  theories\n    Forged"\n'
        "session Real = HOL +\n"
        '  description "note\n  theories\n    Forged\n'
        '  sessions Forged"\n'
        "  theories\n    Actual\n"
    )
    sessions = syntax.parse_sessions(root)
    assert [session.name for session in sessions] == ["Real"]
    assert sessions[0].theories == ("Actual",)
    assert sessions[0].dependencies == ()
    theory = (
        "theory Actual imports Main begin\n"
        'ML \\<open>val message = "line one\n'
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms forged}) "
        'then () else error \\"forged\\";\\<close>\n'
        'lemma string_forged: True by simp";\n'
        "lemma body_forged: True by simp;\\<close>\n"
        "lemma live: True by simp\n"
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms live}) "
        'then () else error "oracle";\\<close>\nend\n'
    )
    assert [row["name"] for row in index._declarations(theory)] == ["live"]
    assert index._audited_theorems(theory) == ("live",)


def test_quoted_proof_words_do_not_truncate_assumptions() -> None:
    declarations = index._declarations(
        "theory Sample imports Main begin\n"
        'lemma live: assumes "marker = \\"proof by\\"" '
        'shows "marker = marker" by simp\nend\n'
    )
    assert len(declarations) == 1
    statement = declarations[0]["statement_and_assumptions"]
    assert isinstance(statement, str)
    assert 'shows "marker = marker"' in statement


def test_repeated_root_sections_are_rejected() -> None:
    with pytest.raises(ValueError, match="repeated ROOT section"):
        syntax.parse_sessions(
            "session Real = HOL +\n  theories\n    First\n  theories\n    Second\n"
        )


def test_documentation_and_string_cannot_forge_theory_header() -> None:
    text = (
        "(* theory Commented imports Missing begin *)\n"
        "text \\<open>theory Documented imports Missing begin\\<close>\n"
        '"quoted header\ntheory String_Forged imports Missing begin"\n'
        'theory Actual imports "Library/Real" Main begin\n'
    )
    assert syntax.parse_theory_header(text, Path("Actual.thy")) == (
        "Actual",
        ("Library/Real", "Main"),
    )
