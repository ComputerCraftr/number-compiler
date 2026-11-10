"""Source-derived cutover ownership checks for the comma release sessions."""

from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import TypeGuard, cast

import pytest

from devtools.checks import isabelle_proof_index as index
from devtools.paths import isabelle_root
from number_compiler.arithmetic.contracts.input_validation import string_keyed_mapping


def _records(value: object) -> tuple[Mapping[str, object], ...] | None:
    if type(value) not in {list, tuple}:
        return None
    rows: list[Mapping[str, object]] = []
    for item in cast(Sequence[object], value):
        row = string_keyed_mapping(item)
        if row is None:
            return None
        rows.append(row)
    return tuple(rows)


def _strings(value: object) -> TypeGuard[Sequence[str]]:
    if type(value) not in {list, tuple}:
        return False
    return all(type(item) is str for item in cast(Sequence[object], value))


def _release_owner_fixture(
    root: Path,
    monkeypatch: pytest.MonkeyPatch,
    *,
    production_compiler: bool,
    audit_compiler: bool,
    future_imports: str = "B1",
    production_source_override: str | None = None,
) -> None:
    proof_root = isabelle_root(root)
    comma = proof_root / "families" / "comma"
    b1 = comma / "b1"
    future = comma / "future"
    audit = comma / "audit"
    for directory in (b1, future, audit):
        directory.mkdir(parents=True)
    (proof_root / "ROOTS").write_text("families/comma\n")
    (comma / "ROOT").write_text(
        "session Comma_Semantic_B1_Instance in b1 = HOL +\n"
        "  theories\n    B1\n"
        "session Comma_Semantic_Future_Instance in future = Comma_Semantic_B1_Instance +\n"
        "  theories\n    Future\n"
        "session Comma_Audit_Only in audit = HOL +\n"
        "  theories\n    Audit\n"
    )

    def audited_theory(name: str, imports: str, body: str = "") -> str:
        safe = f"{name.lower()}_safe"
        return (
            f"theory {name} imports {imports} begin\n"
            f'lemma {safe}: "True" by simp\n'
            f"ML \\<open>val _ = if null (Thm_Deps.all_oracles @{{thms {safe}}}) "
            f'then () else error "oracle";\\<close>\n'
            f"{body}end\n"
        )

    resource_name = "renamed_action_resource.ML"
    (b1 / "B1.thy").write_text(audited_theory("B1", "Bridge"))
    production_ml_file = f'ML_file "{resource_name}"\n' if production_compiler else ""
    (b1 / "Bridge.thy").write_text(audited_theory("Bridge", "Main", production_ml_file))
    (future / "Future.thy").write_text(audited_theory("Future", future_imports))
    audit_ml_file = 'ML_file "audit_action_resource.ML"\n' if audit_compiler else ""
    (audit / "Audit.thy").write_text(audited_theory("Audit", "Main", audit_ml_file))

    action_source = """
fun compile_program frame memo active env key program source =
  let
    val canonical_env = canonical_environment period env
    val cache_key = (key,canonical_env)
  in
    case Compiler_Table.lookup (!memo) cache_key of
      NONE =>
        let
          val child_states = map (fn child_env =>
            compile_program frame memo active child_env key program source) child_envs
          val theorem = #certify certify_state context child_states
        in theorem end
    | SOME state => state
  end
"""
    safe_source = "val action_metadata = 1\n"
    production_source = production_source_override or action_source
    (b1 / resource_name).write_text(
        production_source if production_compiler else safe_source
    )
    (audit / "audit_action_resource.ML").write_text(
        action_source if audit_compiler else safe_source
    )

    monkeypatch.setattr(index, "ROOT", root)
    monkeypatch.setattr(index, "ISABELLE", proof_root)


def test_release_audit_follows_indirect_imports_and_renamed_ml_resources(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _release_owner_fixture(
        tmp_path,
        monkeypatch,
        production_compiler=True,
        audit_compiler=False,
    )

    gate = index.build_index()["comma_release_owner"]
    gate = string_keyed_mapping(gate)
    assert gate is not None
    assert gate["status"] == "FAIL"
    violations = gate["violations"]
    assert _strings(violations)
    assert any(
        "renamed_action_resource.ML" in item
        and "recursive environment-keyed action states" in item
        for item in violations
    )


def test_future_release_audit_includes_resources_from_parent_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _release_owner_fixture(
        tmp_path,
        monkeypatch,
        production_compiler=True,
        audit_compiler=False,
        future_imports="Main",
    )

    gate = index.build_index()["comma_release_owner"]
    gate = string_keyed_mapping(gate)
    assert gate is not None
    reports = gate["roots"]
    typed_reports = _records(reports)
    assert typed_reports is not None
    future = next(
        report
        for report in typed_reports
        if report["root"] == "Comma_Semantic_Future_Instance"
    )
    assert future["status"] == "FAIL"
    resources = future["ml_resources"]
    assert _strings(resources)
    assert any(item.endswith("renamed_action_resource.ML") for item in resources)


def test_release_audit_allows_the_same_compiler_in_unreached_audit_session(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _release_owner_fixture(
        tmp_path,
        monkeypatch,
        production_compiler=False,
        audit_compiler=True,
    )

    gate = index.build_index()["comma_release_owner"]
    gate = string_keyed_mapping(gate)
    assert gate is not None
    assert gate["status"] == "PASS"
    reports = gate["roots"]
    typed_reports = _records(reports)
    assert typed_reports is not None
    for report in typed_reports:
        resources = report["ml_resources"]
        assert _strings(resources)
        assert not any(item.endswith("audit_action_resource.ML") for item in resources)


def test_release_audit_ignores_full_operation_signature_in_comments_and_strings(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    signature = r"""
fun compile_program frame memo active env key program source =
  let
    val canonical_env = canonical_environment period env
    val cache_key = (key,canonical_env)
  in
    case Compiler_Table.lookup (!memo) cache_key of
      NONE =>
        let
          val child_states = map (fn child_env =>
            compile_program frame memo active child_env key program source) child_envs
          val theorem = #certify certify_state context child_states
        in theorem end
    | SOME state => state
  end
"""
    quoted_signature = signature.replace('"', r"\"").replace("\n", " ")
    hidden_source = f'(*{signature}*)\nval documentation = "{quoted_signature}";\n'
    _release_owner_fixture(
        tmp_path,
        monkeypatch,
        production_compiler=True,
        audit_compiler=False,
        production_source_override=hidden_source,
    )

    gate = index.build_index()["comma_release_owner"]
    gate = string_keyed_mapping(gate)
    assert gate is not None
    assert gate["status"] == "PASS"
