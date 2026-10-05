"""Adversarial contracts for the conservative Isabelle source audit."""

from __future__ import annotations

from dataclasses import asdict
from pathlib import Path

import pytest

from devtools.checks.isabelle_source_analysis import (
    analyze_isabelle_source,
    analyze_isabelle_tree,
)
from devtools.checks.isabelle_syntax import ml_cartouches, navigation_text


def _duplicate_names(source: str) -> set[str]:
    analysis = analyze_isabelle_source(source, Path("Example.thy"))
    return {
        declaration.name
        for group in analysis.duplicates
        for declaration in group.declarations
    }


def test_comments_documentation_and_quoted_fake_commands_are_ignored() -> None:
    source = r"""
(* definition fake where "fake x = x * 2 + 1" *)
text \<open> definition also_fake where "also_fake x = x * 2 + 1" \<close>

 definition real where "real x = x * 2 + 1"
"""
    analysis = analyze_isabelle_source(source)
    assert [item.name for item in analysis.declarations] == ["real"]


def test_alpha_equivalent_definition_bodies_are_reported() -> None:
    source = """
 definition first where "first x = x * 2 + 1"
 definition second where "second y = y * 2 + 1"
"""
    assert _duplicate_names(source) == {"first", "second"}


def test_constants_operators_and_literals_are_not_alpha_normalized() -> None:
    source = """
 definition plus_one where "plus_one x = x * 2 + 1"
 definition plus_two where "plus_two y = y + 2"
 definition minus_one where "minus_one z = z - 1"
"""
    assert _duplicate_names(source) == set()


def test_lambda_binders_are_alpha_equivalent_but_shadowing_is_preserved() -> None:
    equivalent = """
 definition first where "first x = (\\<lambda> y. y * 2 + x)"
 definition second where "second z = (\\<lambda> q. q * 2 + z)"
"""
    assert _duplicate_names(equivalent) == {"first", "second"}
    shadowing = """
 definition first where "first x = (\\<lambda> y. (\\<lambda> y. y * 2 + x))"
 definition second where "second z = (\\<lambda> q. (\\<lambda> r. q * 2 + z))"
"""
    assert _duplicate_names(shadowing) == set()


def test_multiple_equations_are_compared_as_an_ordered_body() -> None:
    same = """
 fun first where "first 0 = 1" | "first (Suc n) = n * 2 + 1"
 fun second where "second 0 = 1" | "second (Suc m) = m * 2 + 1"
"""
    changed = same.replace('"second 0 = 1"', '"second 0 = 2"')
    assert _duplicate_names(same) == {"first", "second"}
    assert _duplicate_names(changed) == set()


def test_ml_prf_is_masked_and_external_ml_functions_are_analyzed(
    tmp_path: Path,
) -> None:
    theory = r"""
ML_prf \<open>
  fun first x = x * 2 + 1
  fun second y = y * 2 + 1
\<close>

 definition actual where "actual x = x * 2 + 1"
"""
    # The embedded ML is dynamic and therefore not a hard unused finding, but
    # it remains available to the duplicate detector.
    analysis = analyze_isabelle_source(theory)
    assert {item.name for item in analysis.declarations} >= {
        "first",
        "second",
        "actual",
    }
    assert any(item.ml for item in analysis.declarations)
    assert ml_cartouches(theory)
    assert "fun first" not in navigation_text(theory)

    ml = tmp_path / "helpers.ML"
    ml.write_text("fun first x = x * 2 + 1\nfun second y = y * 2 + 1\n")
    external = analyze_isabelle_tree(tmp_path)
    assert {item.name for item in external.declarations} == {"first", "second"}
    assert external.duplicates


def test_unused_is_review_only_and_attributes_and_antiquotes_are_roots() -> None:
    source = r"""
 definition private_one where "private_one x = x * 2 + 1"
 definition used_by_other where "used_by_other x = private_one x"
 lemma simp_root: "True" by simp
 lemma antiquote_root: "True" by (insert @{thm simp_root}; simp)
 declare private_one[simp]
"""
    analysis = analyze_isabelle_source(source)
    candidates = {item.declaration.name for item in analysis.unused_candidates}
    assert "private_one" not in candidates
    assert "used_by_other" in candidates
    assert "simp_root" not in candidates
    assert "antiquote_root" in candidates
    assert {item.confidence for item in analysis.unused_candidates} == {
        "review",
        "exported-review",
    }


def test_dynamic_references_are_reported_unknown_not_declared_dead() -> None:
    source = r"""
 definition private_one where "private_one x = x * 2 + 1"
 local_setup \<open> fn ctxt => ctxt \<close>
"""
    analysis = analyze_isabelle_source(source)
    assert analysis.unknown_references
    assert analysis.unused_candidates
    assert analysis.unused_candidates[0].confidence == "dynamic-review"


def test_report_is_json_ready_and_preserves_paths(tmp_path: Path) -> None:
    path = tmp_path / "Example.thy"
    path.write_text('definition one where "one x = x * 2 + 1"\n')
    report = analyze_isabelle_tree(tmp_path).as_dict()
    assert isinstance(asdict(analyze_isabelle_tree(tmp_path)), dict)
    assert report["declarations"][0]["path"] == str(path)
    assert report["declarations"][0]["line"] == 1


def test_exported_unreferenced_theorem_is_review_advisory_not_dead() -> None:
    analysis = analyze_isabelle_source('lemma public_fact: "True" by simp\n')
    assert [item.declaration.name for item in analysis.unused_candidates] == [
        "public_fact"
    ]
    assert analysis.unused_candidates[0].confidence == "exported-review"


def test_unsupported_conditional_body_is_reported() -> None:
    source = 'definition conditional where "conditional x = (if x = 0 then 1 else 2)"\n'
    analysis = analyze_isabelle_source(source)
    assert analysis.unsupported_constructs
    assert not analysis.duplicates


def test_tree_references_cross_file_declarations(tmp_path: Path) -> None:
    (tmp_path / "A.thy").write_text('definition shared where "shared x = x * 2 + 1"\n')
    (tmp_path / "B.thy").write_text('lemma uses_shared: "shared 1 = 3" by simp\n')
    analysis = analyze_isabelle_tree(tmp_path)
    assert "shared" not in {
        item.declaration.name for item in analysis.unused_candidates
    }


def test_argument_order_and_trivial_bodies_are_not_collapsed() -> None:
    source = """
 definition ordered where "ordered x y = x * 2 + y"
 definition swapped where "swapped a b = b * 2 + a"
 definition trivial_one where "trivial_one x = x + 1"
 definition trivial_two where "trivial_two y = y + 1"
"""
    assert _duplicate_names(source) == set()


def test_qualified_cross_file_reference_is_counted(tmp_path: Path) -> None:
    (tmp_path / "A.thy").write_text('definition shared where "shared x = x * 2 + 1"\n')
    (tmp_path / "B.thy").write_text('lemma uses_shared: "A.shared 1 = 3" by simp\n')
    analysis = analyze_isabelle_tree(tmp_path)
    assert "shared" not in {
        item.declaration.name for item in analysis.unused_candidates
    }


def test_ml_comments_strings_and_trailing_bindings_are_not_functions() -> None:
    source = r"""
ML \<open>
  (* fun fake x = x * 9 *)
  fun real x = x * 2 + 1
  val text = "fun fake y = y * 9"
  val finished = 1
\<close>
"""
    analysis = analyze_isabelle_source(source)
    assert [item.name for item in analysis.declarations if item.ml] == ["real"]


def test_compact_report_omits_full_bodies(tmp_path: Path) -> None:
    from devtools.checks.isabelle_source_analysis import analysis_report

    path = tmp_path / "A.thy"
    path.write_text('definition one where "one x = x * 2 + 1"\n')
    report = analysis_report(tmp_path)
    assert report["scope"]["semantic_equivalence"] is False
    assert "body" not in str(report)


def test_formal_locale_name_and_plural_antiquotation_are_conservative() -> None:
    source = r"""
lemma (in arithmetic) public_fact: "True" by simp
ML \<open> val _ = @{thms public_fact other_fact} \<close>
"""
    analysis = analyze_isabelle_source(source)
    assert [item.name for item in analysis.declarations if not item.ml] == [
        "public_fact"
    ]
    assert analysis.unknown_references


def test_recursive_equations_and_explicit_type_signatures() -> None:
    source = """
fun first :: "nat => nat" where
  "first 0 = 1" | "first (Suc n) = first n * 2 + 1"
fun second :: "nat => nat" where
  "second 0 = 1" | "second (Suc m) = second m * 2 + 1"
fun differently_typed :: "nat => int" where
  "differently_typed 0 = 1" |
  "differently_typed (Suc n) = differently_typed n * 2 + 1"
"""
    assert _duplicate_names(source) == {"first", "second"}


def test_multi_binder_scope_is_explicitly_unsupported() -> None:
    analysis = analyze_isabelle_source(
        r'definition first where "first x = (\<lambda> a b. a * 2 + b + x)"'
    )
    assert analysis.unsupported_constructs
    assert not analysis.duplicates


def test_anonymous_facts_and_quoted_extensions_are_not_named_commands() -> None:
    source = """
lemma "True" by simp
lemma real: "P ''
ML_file imaginary.ML
''" by simp
"""
    analysis = analyze_isabelle_source(source)
    assert [item.name for item in analysis.declarations] == ["real"]
    assert not analysis.unknown_references


def test_external_ml_is_not_also_a_hol_declaration(tmp_path: Path) -> None:
    path = tmp_path / "helpers.ML"
    path.write_text("fun first x = x * 2 + 1\n")
    analysis = analyze_isabelle_tree(tmp_path)
    assert len(analysis.declarations) == 1
    assert analysis.declarations[0].ml


def test_external_ml_qualified_call_is_an_incoming_reference(tmp_path: Path) -> None:
    (tmp_path / "helper.ML").write_text(
        "structure Helper = struct\nfun used x = x * 2 + 1\nend\n"
    )
    (tmp_path / "Use.thy").write_text(
        r"ML \<open>val result = Helper.used 5\<close>" + "\n"
    )
    analysis = analyze_isabelle_tree(tmp_path)
    assert "used" not in {
        candidate.declaration.name for candidate in analysis.unused_candidates
    }


def test_snapshot_keys_preserve_same_named_files(tmp_path: Path) -> None:
    first = tmp_path / "a" / "helpers.ML"
    second = tmp_path / "b" / "helpers.ML"
    for path in (first, second):
        path.parent.mkdir()
        path.write_text("fun unrelated x = x\n")
    analysis = analyze_isabelle_tree(
        tmp_path,
        {
            first: "fun first x = x * 2 + 1\n",
            second: "fun second x = x * 2 + 1\n",
        },
    )
    assert {item.name for item in analysis.declarations} == {"first", "second"}
    assert len(analysis.duplicates) == 1


def test_tree_analysis_extracts_each_source_and_groups_only_once(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    from devtools.checks import isabelle_source_analysis as owner

    for name in ("first", "second"):
        (tmp_path / f"{name}.thy").write_text(
            f'definition {name} where "{name} x = x * 2 + 1"\n'
        )
    calls = {"extract": 0, "group": 0}
    extract = owner.extract_isabelle_declarations
    group = owner._duplicate_groups

    def counted_extract(
        text: str, path: Path | str = "<memory>"
    ) -> tuple[owner.IsabelleDeclaration, ...]:
        calls["extract"] += 1
        return extract(text, path)

    def counted_group(
        declarations: tuple[owner.IsabelleDeclaration, ...]
        | list[owner.IsabelleDeclaration],
    ) -> tuple[owner.IsabelleDuplicate, ...]:
        calls["group"] += 1
        return group(declarations)

    monkeypatch.setattr(owner, "extract_isabelle_declarations", counted_extract)
    monkeypatch.setattr(owner, "_duplicate_groups", counted_group)
    assert analyze_isabelle_tree(tmp_path).duplicates
    assert calls == {"extract": 2, "group": 1}


def test_indented_commands_are_inventory_entries_with_unknown_scope() -> None:
    source = '  lemma local_fact: "True" by simp\n'
    analysis = analyze_isabelle_source(source)
    assert [item.name for item in analysis.declarations] == ["local_fact"]
    assert any("scope" in item.reason for item in analysis.unsupported_constructs)


def test_ml_let_functions_are_not_alpha_normalized() -> None:
    source = r"""
ML \<open>
  fun first x = let val y = x * 2 in y + 1 end
  fun second z = let val q = z * 2 in q + 1 end
\<close>
"""
    analysis = analyze_isabelle_source(source)
    assert not analysis.duplicates
    assert analysis.unsupported_constructs


def test_unused_parameter_positions_remain_semantically_distinct() -> None:
    source = """
 definition first where "first x y = x * 2 + 1"
 definition second where "second x y = y * 2 + 1"
"""
    assert _duplicate_names(source) == set()
