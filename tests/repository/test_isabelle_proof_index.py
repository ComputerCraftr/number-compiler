"""The proof inventory is navigation and validation, never proof certification."""

from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import TypeGuard, cast

import pytest

from devtools.checks import isabelle_oracle_audit
from devtools.checks import isabelle_proof_index as index
from devtools.checks import isabelle_source_analysis as source_analysis
from devtools.checks import isabelle_syntax as syntax
from devtools.paths import isabelle_root
from tests.support.isabelle_proof_graph import (
    RepositoryProofGraph as _RepositoryProofGraph,
)


def _fixture(root: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    proof_root = isabelle_root(root)
    directory = proof_root / "families" / "example"
    session_directory = directory / "Session"
    session_directory.mkdir(parents=True)
    (proof_root / "ROOTS").write_text("families/example\n")
    (directory / "ROOT").write_text(
        "session Example in Session = HOL +\n  theories\n    Sample\n"
    )
    (session_directory / "Sample.thy").write_text(
        "theory Sample imports Main begin\n"
        'lemma bounded [simp]: assumes "n = (0::nat)" shows "n < 1" by simp\n'
        'ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms bounded}) then () else error "oracle";\\<close>\n'
        "end\n"
    )
    monkeypatch.setattr(index, "ROOT", root)
    monkeypatch.setattr(index, "ISABELLE", proof_root)
    return directory


def _sample(directory: Path) -> Path:
    return directory / "Session" / "Sample.thy"


def _record(value: object) -> TypeGuard[dict[str, object]]:
    return type(value) is dict and all(
        type(key) is str for key in cast(dict[object, object], value)
    )


def _record_sequence(value: object) -> TypeGuard[Sequence[dict[str, object]]]:
    if type(value) is list or type(value) is tuple:
        return all(_record(item) for item in cast(Sequence[object], value))
    return False


def test_index_uses_canonical_isabelle_root() -> None:
    assert index.ISABELLE == isabelle_root(index.ROOT)


def test_index_retains_statement_assumptions_attributes_and_location(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _fixture(tmp_path, monkeypatch)
    result = index.build_index()
    theories = result["theories"]
    assert _record_sequence(theories)
    declaration_rows = theories[0].get("declarations")
    assert _record_sequence(declaration_rows)
    declaration = declaration_rows[0]
    assert declaration["name"] == "bounded" and declaration["line"] == 2
    statement = declaration["statement_and_assumptions"]
    assert isinstance(statement, str)
    assert '[simp]: assumes "n = (0::nat)"' in statement
    assert theories[0]["session"] == "Example"


def test_theory_inventory_uses_one_source_snapshot_per_pass(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    theory = _sample(directory)
    read_text = Path.read_text
    reads: list[Path] = []

    def changing_source(path: Path, encoding: str | None = None) -> str:
        text = read_text(path, encoding=encoding)
        if path == theory:
            reads.append(path)
            # Simulate an editor saving between inventory phases. Metadata and
            # declarations must describe the same read, never a mixed theory.
            path.write_text(text.replace("bounded", "replacement"))
        return text

    monkeypatch.setattr(Path, "read_text", changing_source)
    result = index.build_index()
    theories = result["theories"]
    assert _record_sequence(theories)
    assert reads == [theory]
    assert theories[0]["oracle_audit_theorems"] == ("bounded",)
    declarations = theories[0].get("declarations")
    assert _record_sequence(declarations)
    assert declarations[0]["name"] == "bounded"


def test_index_reuses_theory_analysis_for_tree_and_inventory_views(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _fixture(tmp_path, monkeypatch)
    inventory_calls = 0
    tree_parse_calls = 0
    inventory_analyzer = source_analysis.analyze_isabelle_source
    tree_analyzer = source_analysis.analyze_isabelle_source

    def count_inventory(
        text: str,
        path: Path | str = "<memory>",
        *,
        include_duplicates: bool = True,
    ) -> source_analysis.IsabelleAnalysis:
        nonlocal inventory_calls
        inventory_calls += 1
        return inventory_analyzer(text, path, include_duplicates=include_duplicates)

    def count_tree_parse(
        text: str,
        path: Path | str = "<memory>",
        *,
        include_duplicates: bool = True,
    ) -> source_analysis.IsabelleAnalysis:
        nonlocal tree_parse_calls
        tree_parse_calls += 1
        return tree_analyzer(text, path, include_duplicates=include_duplicates)

    monkeypatch.setattr(index, "analyze_isabelle_source", count_inventory)
    monkeypatch.setattr(source_analysis, "analyze_isabelle_source", count_tree_parse)
    result = index.build_index()

    assert inventory_calls == 1
    assert tree_parse_calls == 0
    theories = result["theories"]
    assert _record_sequence(theories)
    declarations = theories[0].get("declarations")
    assert _record_sequence(declarations)
    assert declarations[0]["name"] == "bounded"
    source_report = result["source_analysis"]
    assert _record(source_report)
    assert source_report["declaration_count"] == 1


@pytest.mark.parametrize("fault", ["missing", "duplicate", "orphan", "unaudited"])
def test_index_rejects_structural_misrepresentation(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, fault: str
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    if fault == "missing":
        _sample(directory).unlink()
    elif fault == "duplicate":
        (directory / "Other").mkdir()
        with (directory / "ROOT").open("a") as output:
            output.write(
                'session Second in Other = HOL +\n  theories\n    "../Session/Sample"\n'
            )
    elif fault == "orphan":
        (directory / "Orphan.thy").write_text("theory Orphan imports Main begin end\n")
    elif fault == "unaudited":
        path = _sample(directory)
        path.write_text(
            path.read_text().replace("Thm_Deps.all_oracles", "not_an_audit")
        )
    with pytest.raises(ValueError):
        index.build_index()


# Release quality builds this complete inventory; keep the exact CLI-level
# mirror in the explicit validation selection and retain fixture adversaries as unit tests.
@pytest.mark.validation
def test_registered_proof_inventory_is_consistent() -> None:
    assert index.build_index()["schema_version"] == 2


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
    path = _sample(directory)
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
    sample = _sample(directory)
    sample.write_text(sample.read_text().replace("imports Main", "imports Helper"))
    (directory / "Session" / "Helper.thy").write_text(
        'theory Helper imports Main begin lemma helper: "True" by simp\n'
        'ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms helper}) then () else error "oracle";\\<close>\n'
        "end\n"
    )
    result = index.build_index()
    theories = result["theories"]
    assert _record_sequence(theories)
    helper = next(row for row in theories if row["theory"] == "Helper")
    assert helper["session"] is None


def test_index_validates_ml_file_targets(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    sample = _sample(directory)
    sample.write_text(
        sample.read_text().replace("\nend\n", '\nML_file "missing.ML"\nend\n')
    )
    with pytest.raises(ValueError, match="missing ML_file target"):
        index.build_index()


def test_index_rejects_ml_file_targets_outside_theory_root(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    sample = _sample(directory)
    sample.write_text(
        sample.read_text().replace(
            "\nend\n", '\nML_file "../../../../outside.ML"\nend\n'
        )
    )
    with pytest.raises(ValueError, match="ML_file target escapes theory root"):
        index.build_index()


def test_ml_file_inventory_resolves_relative_to_theory_source(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    (directory / "child").mkdir()
    (directory / "Session" / "helper.ML").write_text("val helper = ()\n")
    (directory / "child" / "helper.ML").write_text("val other = ()\n")
    sample = _sample(directory)
    sample.write_text(
        sample.read_text().replace("\nend\n", '\nML_file "helper.ML"\nend\n')
    )
    rows = index.build_index()["ml_files"]
    assert _record_sequence(rows)
    by_path: dict[str, dict[str, object]] = {}
    for row in rows:
        path = row.get("path")
        assert isinstance(path, str)
        by_path[path] = row
    assert by_path["proofs/isabelle/families/example/Session/helper.ML"][
        "referenced_by"
    ] == ("Sample",)
    assert (
        by_path["proofs/isabelle/families/example/child/helper.ML"]["referenced_by"]
        == ()
    )


def test_ml_file_lexer_ignores_comments_documentation_and_ml_strings() -> None:
    source = (
        '(* ML_file "missing.ML" *)\n'
        'text \\<open>ML_file "missing.ML"\\<close>\n'
        'ML \\<open>val fake = "ML_file \\"missing.ML\\"";\\<close>\n'
    )
    assert index.ml_file_references(source, Path("Sample.thy")) == ()


def test_ml_file_without_a_target_is_rejected() -> None:
    with pytest.raises(ValueError, match="unsupported ML_file target"):
        index.ml_file_references("ML_file\n", Path("Sample.thy"))


def test_comments_and_documentation_cannot_forge_declarations_or_uses() -> None:
    text = (
        "theory Sample imports Main begin\n"
        "(* lemma commented: True by simp *)\n"
        "text \\<open>lemma documented: True by simp; bounded\\<close>\n"
        "lemma live: True by simp\n"
        "end\n"
    )
    assert [row["name"] for row in index.declarations(text)] == ["live"]
    clean = syntax.executable_text(text)
    assert "bounded" not in clean and "commented" not in clean


def test_noncall_marker_cannot_forge_audit() -> None:
    assert (
        isabelle_oracle_audit.audited_theorems(
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
    assert [row["name"] for row in index.declarations(text)] == ["live"]
    assert isabelle_oracle_audit.audited_theorems(text) == ("live",)


def test_comment_cannot_forge_theory_header_or_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    root = directory / "ROOT"
    root.write_text(
        "(* session Forged = HOL +\n  theories\n    Forged *)\n" + root.read_text()
    )
    sample = _sample(directory)
    sample.write_text(
        "(* theory Forged imports Missing begin *)\n" + sample.read_text()
    )
    result = index.build_index()
    sessions = result["sessions"]
    theories = result["theories"]
    assert _record_sequence(sessions) and _record_sequence(theories)
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


@pytest.mark.parametrize(
    "entry", ("../other/Sample", "Sample ???", '""', "[condition=true] Sample")
)
def test_root_cannot_silently_drop_unparsed_theory_entries(entry: str) -> None:
    with pytest.raises(ValueError, match="unsupported ROOT theory entry"):
        syntax.parse_sessions(f"session Example = HOL +\n  theories\n    {entry}\n")


def test_sessions_cannot_share_the_same_directory() -> None:
    with pytest.raises(ValueError, match="duplicate Isabelle session directory"):
        syntax.parse_sessions(
            "session Check in shared = HOL +\n  theories\n    Check\n"
            "session Instance in shared = Check +\n  theories\n    Instance\n"
        )


def test_quoted_relative_theory_path_resolves_to_its_declared_owner(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    (directory / "child").mkdir()
    (directory / "ROOT").write_text(
        'session Example in child = HOL +\n  theories\n    "../Session/Sample"\n'
    )
    rows = index.build_index()["theories"]
    assert _record_sequence(rows)
    assert rows[0]["theory"] == "Sample" and rows[0]["session"] == "Example"


@pytest.mark.parametrize("entry", ('"../Session/Sample"', '"../../../../outside"'))
def test_aliased_duplicate_and_escaping_theory_paths_are_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, entry: str
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    (directory / "child").mkdir()
    with (directory / "ROOT").open("a") as out:
        out.write(f"session Alias in child = HOL +\n  theories\n    {entry}\n")
    with pytest.raises(ValueError, match="registered in|escapes theory root"):
        index.build_index()


def test_canonical_session_directory_aliases_are_rejected(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    directory = _fixture(tmp_path, monkeypatch)
    (directory / "child").mkdir()
    try:
        (directory / "alias").symlink_to("child", target_is_directory=True)
    except OSError as error:
        pytest.skip(f"cannot create session-directory symlink: {error}")
    (directory / "ROOT").write_text(
        'session Example in child = HOL +\n  theories\n    "../Session/Sample"\n'
        "session Alias in alias = HOL +\n"
    )
    with pytest.raises(
        ValueError, match="duplicate canonical Isabelle session directory"
    ):
        index.build_index()


def test_quoted_comment_markers_leave_later_theorems_visible() -> None:
    text = (
        "theory Sample imports Main begin\n"
        'definition quoted where "quoted = (\\"(* literal *)\\" :: string)"\n'
        "lemma live: True by simp\n"
        "ML \\<open>val _ = if null (Thm_Deps.all_oracles @{thms live}) "
        'then () else error "oracle";\\<close>\nend\n'
    )
    assert [row["name"] for row in index.declarations(text)] == ["live"]
    assert isabelle_oracle_audit.audited_theorems(text) == ("live",)


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
    assert [row["name"] for row in index.declarations(theory)] == ["live"]
    assert isabelle_oracle_audit.audited_theorems(theory) == ("live",)


def test_quoted_proof_words_do_not_truncate_assumptions() -> None:
    declarations = index.declarations(
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


def test_header_rejects_unquoted_hyphens_and_keeps_quoted_symbols() -> None:
    with pytest.raises(ValueError, match="unquoted symbolic token in theory import"):
        syntax.parse_theory_header(
            "theory Actual imports HOL-Library.Product_Lexorder begin end\n",
            Path("Actual.thy"),
        )

    text = (
        'theory Actual imports "HOL-Library.Product_Lexorder" Main begin\n'
        'lemma symbol: "True \\<longrightarrow> True" by simp\n'
        "end\n"
    )
    assert syntax.parse_theory_header(text, Path("Actual.thy")) == (
        "Actual",
        ("HOL-Library.Product_Lexorder", "Main"),
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
@pytest.mark.validation
def test_weighted_comma_ancestry_excludes_legacy_execution(
    target: str, repository_proof_graph: _RepositoryProofGraph
) -> None:
    """Heap ancestry and direct imports must both follow the weighted owner."""
    sessions = repository_proof_graph.sessions
    ancestors = _session_ancestors(sessions, target)
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
    headers = repository_proof_graph.theory_imports
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
    sample = _sample(directory)
    sample.write_text(sample.read_text().replace("imports Main", "imports Helper"))
    (directory / "Session" / "Helper.thy").write_text(
        'theory Helper imports Main begin lemma helper: "True" by simp end\n'
    )
    with pytest.raises(
        ValueError, match="reachable theories without an oracle audit.*Helper"
    ):
        index.build_index()


@pytest.mark.parametrize(
    "source",
    [
        "session A in a = B +\nsession B in b = A +\n",
        "session A in a = HOL +\n  sessions B\nsession B in b = HOL +\n  sessions A\n",
        "session A = A +\n",
    ],
)
def test_local_session_cycles_are_rejected(source: str) -> None:
    with pytest.raises(ValueError, match="cyclic Isabelle session dependency"):
        syntax.parse_sessions(source)


def test_external_session_parents_remain_allowed() -> None:
    sessions = syntax.parse_sessions('session A = "HOL-Number_Theory" +\n')
    assert sessions[0].parent == "HOL-Number_Theory"


def test_session_dependency_closure_counts_project_parent_and_sessions_edges() -> None:
    sessions = syntax.parse_sessions(
        'session Base in base = "HOL-Number_Theory" +\n'
        "session Helper in helper = Base +\n"
        "  theories Helper_Theory\n"
        "session Focus in focus = Base +\n"
        "  sessions Helper\n"
        "session Independent in independent = HOL +\n"
    )
    assert syntax.session_dependency_closure(sessions, ("Focus",)) == (
        "Base",
        "Helper",
        "Focus",
    )
    with pytest.raises(ValueError, match="unknown Isabelle session"):
        syntax.session_dependency_closure(sessions, ("Missing",))


@pytest.mark.validation
def test_collatz_hensel_owner_has_no_reverse_ancestry(
    repository_proof_graph: _RepositoryProofGraph,
) -> None:
    local = repository_proof_graph.sessions
    reached = _session_ancestors(local, "Collatz_Cylinder_Refinement")
    assert "Shared_S_Arithmetic" in reached
    assert "Reverse_Residuals" not in reached
    assert "Hensel_Cylinders" in local["Shared_S_Arithmetic"].theories
    # Reverse temporal carry proofs retain their genuinely required ancestry.
    assert local["Temporal_Clock_Jumps"].parent == "Reverse_Residuals"


@pytest.mark.validation
def test_structural_future_instance_avoids_legacy_checked_instance(
    repository_proof_graph: _RepositoryProofGraph,
) -> None:
    sessions = repository_proof_graph.sessions
    assert "Comma_Fast_Kernel_Smoke" in sessions["Comma_Fast_Control"].theories
    structural = sessions["Comma_Future_Structural_Instance"]
    assert structural.parent == "Comma_Decade_Summary_Checked"
    assert (
        sessions["Comma_Decade_Summary_Checked"].parent == "Comma_Decade_Summary_Kernel"
    )
    assert sessions["Comma_Decade_Summary_Kernel"].parent == "Comma_Decade_Orbit"
    assert sessions["Comma_Future_Source"].parent == "Comma_Future_Structural_Check"
    assert "Comma_Future_Structural_Check" in structural.dependencies
    assert "Comma_Decade_Summary_Checked" not in structural.dependencies
    ancestors = _session_ancestors(sessions, "Comma_Future_Structural_Instance")
    assert {
        "Comma_Future_Structural_Instance",
        "Comma_Future_Structural_Check",
        "Comma_Decade_Summary_Checked",
        "Comma_Decade_Summary_Transport",
        "Comma_Future_Rank_Data",
    } <= ancestors
    assert "Comma_Future_Checked_Instance" not in ancestors


def _session_ancestors(sessions: Mapping[str, syntax.Session], target: str) -> set[str]:
    ancestors: set[str] = set()
    pending = [target]
    while pending:
        name = pending.pop()
        if name in ancestors or name not in sessions:
            continue
        ancestors.add(name)
        session = sessions[name]
        pending.extend((session.parent, *session.dependencies))
    return ancestors


@pytest.mark.parametrize(
    ("target", "required"),
    [
        (
            "Comma_Return_Source",
            {"Comma_Return_Induction", "Comma_Return_Instance", "Comma_Future_Source"},
        ),
        ("Comma_Branch_Induction", {"Comma_Future_Check"}),
        ("Comma_Branch_Instance", {"Comma_Branch_Induction", "Comma_Return_Induction"}),
        ("Comma_Branch_Period", {"Comma_Branch_Induction", "Comma_Return_Induction"}),
        ("Comma_Selected_Return_Blocks", {"Comma_Branch_Period"}),
        (
            "Comma_Branch_Period_Instance",
            {"Comma_Branch_Period", "Comma_Branch_Instance", "Comma_Return_Instance"},
        ),
    ],
)
@pytest.mark.validation
def test_local_induction_does_not_require_global_rank_or_summary_instances(
    target: str,
    required: set[str],
    repository_proof_graph: _RepositoryProofGraph,
) -> None:
    sessions = repository_proof_graph.sessions
    ancestors = _session_ancestors(sessions, target)
    assert required <= ancestors
    assert ancestors.isdisjoint(
        {
            "Comma_Future_Rank_Data",
            "Comma_Decade_Summary_Checked",
            "Comma_Future_Structural_Instance",
            "Comma_Future_Checked_Instance",
            "Comma_Forest_Legacy",
        }
    )


@pytest.mark.validation
def test_period_inherits_checked_return_instead_of_replaying_imported_setup(
    repository_proof_graph: _RepositoryProofGraph,
) -> None:
    sessions = repository_proof_graph.sessions
    # A `sessions` dependency grants theory access but reloads its ML setup;
    # only the parent heap preserves the concrete producer's checked catalog.
    assert sessions["Comma_Branch_Period_Instance"].parent == "Comma_Return_Instance"
    assert sessions["Comma_Return_Instance"].parent == "Comma_Return_Engine"
    for relative in (
        "families/comma/comma_return_instance/Comma_Return_Instance.thy",
        "families/comma/comma_branch_instance/Comma_Branch_Instance.thy",
    ):
        path = index.ISABELLE / relative
        _, imports = repository_proof_graph.headers[path]
        assert "Comma_Return_Engine.Comma_Return_Engine" in imports


@pytest.mark.validation
def test_native_release_inherits_completed_provider_without_legacy_replay(
    repository_proof_graph: _RepositoryProofGraph,
) -> None:
    sessions = repository_proof_graph.sessions
    assert sessions["Comma_Run_Moore"].parent == "Comma_Future_Structural_Check"
    assert (
        sessions["Comma_Run_Moore_Instance"].parent
        == "Comma_Future_Structural_Instance"
    )
    assert (
        sessions["Comma_Global_Future_Safety"].parent == "Comma_Native_Future_Instance"
    )
    ancestors = _session_ancestors(sessions, "Comma_Global_Future_Safety")
    assert {
        "Comma_Native_Future_Instance",
        "Comma_Native_Summary_Instance",
        "Comma_Run_Cycle_Data",
    } <= ancestors
    assert ancestors.isdisjoint(
        {
            "Comma_Decade_Summary_Transport",
            "Comma_Total_Macro",
            "Comma_Future_Structural_Instance",
            "Comma_Run_Moore_Instance",
            "Comma_Future_Checked_Instance",
            "Comma_Return_Instance",
            "Comma_Branch_Period_Instance",
            "Comma_Selected_Return_Blocks",
            "Comma_Branch_Instance",
            "Comma_Return_Source",
        }
    )
    generic = _session_ancestors(sessions, "Comma_Run_Moore")
    assert generic.isdisjoint(
        {
            "Comma_Decade_Summary_Checked",
            "Comma_Future_Structural_Instance",
            "Comma_Future_Rank_Data",
        }
    )


def test_comma_global_release_endpoints_use_strict_native_dependency_audit() -> None:
    audit = (
        index.ISABELLE
        / "families/comma/comma_entry_arithmetic/Proof_Dependency_Audit.ML"
    ).read_text()
    future = (
        index.ISABELLE
        / "families/comma/comma_future_global"
        / "Comma_Global_Future_Safety.thy"
    ).read_text()
    root = (
        index.ISABELLE
        / "families/comma/comma_future_global"
        / "Comma_Global_Root_Safety.thy"
    ).read_text()

    for retired_authority in (
        "Comma_Root_Forest",
        "comma_finite_run",
        "comma_decisive_endpoint_round_refines_fast",
        "comma_fast_round_aux",
        "comma_fast_boundary_run",
        "comma_total_macro",
        "comma_rank_candidate",
        "Comma_Future_Structural_Instance",
        "comma_future_structural_candidate",
        "comma_future_structural_witness",
        "comma_future_descent_check",
        "comma_structural_loser_no_infinite_literal_path",
        "comma_structural_survivor_infinite_literal_path",
    ):
        assert f'"{retired_authority}"' in audit
    assert "fun audit_fuel_free_global" in audit
    assert "fun require_native_clean" in audit
    assert "fun require_fuel_free_global" not in audit

    future_compact = " ".join(future.split())
    assert (
        "require_native_closed_expected_paths @{context} "
        '"Global comma future-safety release endpoints" '
    ) in future_compact
    assert {
        "comma_source20_global_future_safety",
        "comma_source20_global_infinite_paths_agree",
        "comma_source20_global_unique_infinite_literal_path",
    } <= set(isabelle_oracle_audit.audited_theorems(future))
    assert (
        "require_native_closed_expected_paths @{context} "
        '"Global comma root-safety release endpoint" '
    ) in " ".join(root.split())
    assert "comma_global_release_safety" in isabelle_oracle_audit.audited_theorems(root)
    for source in (future, root):
        release_ml = source.rsplit("ML \\<open>", maxsplit=1)[-1]
        assert release_ml.count("require_native_closed_expected_paths") == 1
        assert "Thm_Deps.all_oracles" not in release_ml
        assert "require_native_clean" not in release_ml
    assert "require_fuel_free_global" not in future
    assert "require_fuel_free_global" not in root
    assert "audit_fuel_free_global" not in future
    assert "audit_fuel_free_global" not in root
    future_release_ml = future.rsplit("ML \\<open>", maxsplit=1)[-1]
    assert "val checked" not in future_release_ml
    assert "comma_future_concrete_zero_child_rank" not in future_release_ml
    assert "comma_future_concrete_near_child_unranked" not in future_release_ml


@pytest.mark.validation
def test_direct_summary_semantics_does_not_depend_on_fuel_or_concrete_tables(
    repository_proof_graph: _RepositoryProofGraph,
) -> None:
    sessions = repository_proof_graph.sessions
    ancestors = _session_ancestors(sessions, "Comma_Decade_Summary_Semantic")
    assert "Comma_Decade_Residual_Core" in ancestors
    assert ancestors.isdisjoint(
        {
            "Comma_Total_Macro",
            "Comma_Decade_Summary_Checked",
            "Comma_Decade_Rank_Data",
            "Comma_Future_Rank_Data",
        }
    )
    assert (
        sessions["Comma_Decade_Summary_Transport"].parent
        == "Comma_Decade_Summary_Semantic"
    )
    # Local Schur arithmetic reuses the shared carry monoid, without acquiring
    # comma trajectory, summary-table or future-certificate dependencies.
    assert sessions["Comma_Schur_Carry"].parent == "Shared_Carry_Dynamics"
    assert not any(
        name.startswith("Comma_")
        for name in _session_ancestors(sessions, "Comma_Schur_Carry")
        - {"Comma_Schur_Carry"}
    )


@pytest.mark.parametrize(
    ("name", "parent", "arithmetic_owner"),
    [
        ("Comma_Sparse_Core", "Comma_Decade_Orbit", "Comma_Decade_Orbit"),
        ("Comma_Response_Rows", "Comma_Sparse_Core", "Comma_Decade_Orbit"),
        ("Comma_Sparse_Power_Algebra", "Comma_Sparse_Core", "Comma_Decade_Orbit"),
        (
            "Comma_Sparse_Power_Instance",
            "Comma_Sparse_Base_Instance",
            "Comma_Decade_Orbit",
        ),
        (
            "Comma_Native_Summary",
            "Comma_Decade_Occurrence_Lift",
            "Comma_Decade_Orbit",
        ),
        (
            "Comma_Native_Summary_Occurrence",
            "Comma_Native_Summary",
            "Comma_Decade_Orbit",
        ),
        (
            "Comma_Native_Boundary",
            "Comma_Native_Summary_Occurrence",
            "Comma_Decade_Orbit",
        ),
        (
            "Comma_Native_Summary_Instance",
            "Comma_Sparse_Power_Instance",
            "Comma_Decade_Orbit",
        ),
        ("Comma_Sparse_Base_Instance", "Comma_Compact_B1", "Comma_Decade_Orbit"),
        ("Comma_C1_Carry_Generator", "Comma_Arithmetic", "Comma_Arithmetic"),
        ("Comma_C1_Borrow_Cocycle", "Comma_C1_Phase_Power", "Comma_Arithmetic"),
        ("Comma_C1_Phase_Power", "Comma_C1_Carry_Generator", "Comma_Arithmetic"),
        ("Comma_C1_Occurrence", "Comma_C1_Borrow_Cocycle", "Comma_Arithmetic"),
        (
            "Comma_Decade_Occurrence_Lift",
            "Comma_Decade_Residual_Core",
            "Comma_Decade_Residual_Core",
        ),
        ("Comma_Prefix_Selection", "Comma_Closed_Near", "Comma_Closed_Near"),
        ("Comma_Future_Selector", "Comma_Cylinder", "Comma_Arithmetic"),
        ("Comma_Native19_Carry", "Comma_Schur_Carry", "Shared_Carry_Dynamics"),
        ("Comma_Reset_Germ", "Reverse_Residuals", "Reverse_Residuals"),
        ("Comma_Factored_Port_Carrier", "Comma_Vieta_Root", "Shared_Carry_Dynamics"),
        (
            "Comma_Recursive_Pair_Language",
            "Comma_Entry_Port",
            "Shared_Carry_Dynamics",
        ),
        (
            "Comma_Compact_Decade_Classifier",
            "Comma_Decade_Residual_Core",
            "Comma_Decade_Residual_Core",
        ),
        (
            "Comma_Decade_Occurrence_Semantic",
            "Comma_Terminal_Event",
            "Comma_Terminal_Event",
        ),
    ],
)
@pytest.mark.validation
def test_compact_proof_layers_reuse_owners_without_fuel_tables(
    name: str,
    parent: str,
    arithmetic_owner: str,
    repository_proof_graph: _RepositoryProofGraph,
) -> None:
    sessions = repository_proof_graph.sessions
    ancestors = _session_ancestors(sessions, name)
    assert sessions[name].parent == parent
    assert arithmetic_owner in ancestors
    if name == "Comma_Recursive_Pair_Language":
        assert ancestors == (
            {name}
            | _session_ancestors(sessions, "Comma_Entry_Port")
            | _session_ancestors(sessions, "Comma_Factored_Port_Carrier")
        )
    assert ancestors.isdisjoint(
        {
            "Comma_Total_Macro",
            "Comma_Decade_Summary_Checked",
            "Comma_Decade_Terminal_Data",
            "Comma_Decade_Rank_Data",
            "Comma_Future_Rank_Data",
        }
    )
