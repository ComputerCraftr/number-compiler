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


@pytest.mark.parametrize(
    "declaration",
    [
        "declare gcd_nat.simps [simp]",
        "declare gcd_nat.simps\n  [simp, intro]",
        "declare harmless [simp]\n  GCD.gcd_nat.simps [simp]",
        "lemmas recursive_gcd [simp] = gcd_nat.simps",
        "lemmas recursive_gcd = gcd_nat.simps [simp]",
    ],
)
def test_recursive_gcd_cannot_enter_global_simplifier(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, declaration: str
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    path = directory / "Sample.thy"
    path.write_text(path.read_text().replace("\nend\n", f"\n{declaration}\nend\n"))
    with pytest.raises(ValueError, match="recursive gcd rule globally registered"):
        index.build_index()


def test_recursive_gcd_policy_allows_ground_proofs_and_ignores_quoted_text() -> None:
    source = (
        "(* declare gcd_nat.simps [simp] *)\n"
        "text \\<open>declare gcd_nat.simps [simp]\\<close>\n"
        'ML \\<open>val note = "declare gcd_nat.simps [simp]";\\<close>\n'
        'lemma ground: "gcd (2::nat) 10 = 2" by (simp add: gcd_nat.simps)\n'
        "declare gcd_nat.simps [simp del]\n"
    )
    assert syntax.global_simp_registrations(source, "gcd_nat.simps") == ()


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
    (directory / "Helper.thy").write_text(
        'theory Helper imports Main begin lemma helper: "True" by simp\n'
        'ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms helper}) then () else error "oracle";\\<close>\n'
        "end\n"
    )
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


@pytest.mark.parametrize(
    "target",
    [
        "Comma_Cylinder",
        "Comma_Literal_Bridge",
        "Comma_Quotient_Totality",
        "Comma_Round_Totality",
        "Comma_Decade_Totality",
        "Comma_Round_Witness_Check",
        "Comma_Round_Weights",
        "Comma_Short_Phase",
        "Comma_Round_Phase_Slice",
        "Comma_Source_Entry",
        "Comma_Source_Entry_Witness",
        "Comma_Source_Uniqueness",
        "Comma_Decade_Residual_Core",
        "Comma_Decade_Blocks",
        "Comma_Total_Macro",
        "Comma_Decade_Summary_Transport",
        "Comma_Powered_Boundary",
    ],
)
def test_weighted_comma_ancestry_excludes_legacy_execution(target: str) -> None:
    """Heap ancestry and direct imports must both follow the weighted owner."""
    sessions = {
        session.name: session
        for session in syntax.parse_sessions((index.ISABELLE / "ROOT").read_text())
    }
    ancestors: set[str] = set()
    pending = [target]
    while pending:
        name = pending.pop()
        if name in ancestors or name not in sessions:
            continue
        ancestors.add(name)
        session = sessions[name]
        pending.extend((session.parent, *session.dependencies))
    assert "Comma_Forest_Legacy" not in ancestors
    assert "Comma_Scalar_Reference" not in ancestors
    assert "Comma_Trace_Regression" not in ancestors
    rank_free = target in {
        "Comma_Decade_Residual_Core",
        "Comma_Decade_Blocks",
        "Comma_Total_Macro",
        "Comma_Decade_Summary_Transport",
        "Comma_Powered_Boundary",
    }
    if rank_free:
        assert ancestors.isdisjoint({"Comma_Fast_Decade_Rank", "Comma_Fast_Rank_Check"})
    headers = dict(
        syntax.parse_theory_header(path.read_text(), path)
        for path in index.ISABELLE.rglob("*.thy")
    )
    reached: set[str] = set()
    pending_theories = [
        theory for name in ancestors for theory in sessions[name].theories
    ]
    while pending_theories:
        name = pending_theories.pop()
        if name in reached or name not in headers:
            continue
        reached.add(name)
        pending_theories.extend(
            Path(imported.split(".")[-1]).name for imported in headers[name]
        )
    assert "Comma_Finite_Transition" in reached
    assert "Comma_Literal_Path" in reached
    if rank_free:
        assert "Comma_Decade_Residual_Core" in reached
        assert "Comma_Fast_Decade_Rank" not in reached
    assert reached.isdisjoint(
        {
            "Comma_Root_Forest",
            "Comma_Macro_Constructor",
            "Comma_Weighted_Macro",
            "Comma_Trace_Regression",
        }
    )


def test_imported_helper_requires_oracle_audit(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    sample = directory / "Sample.thy"
    sample.write_text(sample.read_text().replace("imports Main", "imports Helper"))
    (directory / "Helper.thy").write_text(
        'theory Helper imports Main begin lemma helper: "True" by simp end\n'
    )
    with pytest.raises(
        ValueError, match="reachable theories without an oracle audit.*Helper"
    ):
        index.build_index()


@pytest.mark.parametrize(
    "source",
    [
        "session A = B +\nsession B = A +\n",
        "session A = HOL +\n  sessions B\nsession B = HOL +\n  sessions A\n",
        "session A = A +\n",
    ],
)
def test_local_session_cycles_are_rejected(source: str) -> None:
    with pytest.raises(ValueError, match="cyclic Isabelle session dependency"):
        syntax.parse_sessions(source)


def test_external_session_parents_remain_allowed() -> None:
    sessions = syntax.parse_sessions('session A = "HOL-Number_Theory" +\n')
    assert sessions[0].parent == "HOL-Number_Theory"


def test_collatz_hensel_owner_has_no_reverse_ancestry() -> None:
    sessions = syntax.parse_sessions((index.ISABELLE / "ROOT").read_text())
    local = {session.name: session for session in sessions}
    reached: set[str] = set()
    pending = ["Collatz_Cylinder_Refinement"]
    while pending:
        name = pending.pop()
        if name in reached or name not in local:
            continue
        reached.add(name)
        session = local[name]
        pending.extend((session.parent, *session.dependencies))
    assert "Shared_S_Arithmetic" in reached
    assert "Reverse_Residuals" not in reached
    assert "Hensel_Cylinders" in local["Shared_S_Arithmetic"].theories
    # Reverse temporal carry proofs retain their genuinely required ancestry.
    assert local["Temporal_Clock_Jumps"].parent == "Reverse_Residuals"
