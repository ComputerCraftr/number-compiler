"""Positive authority checks must be executable and distinct from their inputs."""

from pathlib import Path

import pytest

from devtools.checks.isabelle_oracle_audit import audited_theorems
from devtools.checks.isabelle_syntax import unquoted_numeric_case_facts

AUDIT_ML = (
    Path(__file__).parents[2]
    / "proofs/isabelle/families/comma/comma_entry_arithmetic/Proof_Dependency_Audit.ML"
)
AUDIT_SMOKE = (
    Path(__file__).parents[2]
    / "proofs/isabelle/families/comma/audit/comma_dependency_audit_smoke/"
    "Comma_Proof_Dependency_Audit_Smoke.thy"
)


def test_numeric_case_fact_requires_quotes_without_scanning_documentation() -> None:
    source = (
        "text \\<open>Example: 0.prems\\<close>\n"
        "(* 1.IH *)\n"
        'ML \\<open>val example = "2.hyps"\\<close>\n'
        'using "0.prems"(2) Suc.prems by simp\n'
        "using 0.prems(2) 1.IH by simp\n"
        'have "0.prems = 0.prems" by simp\n'
    )
    assert unquoted_numeric_case_facts(source) == (5, 5)


@pytest.mark.parametrize(
    "method",
    [
        "require_expected_paths",
        "require_closed_expected_paths",
        "require_native_closed_expected_paths",
        "require_paths",
    ],
)
def test_authority_audit_records_endpoints_not_expected_dependencies(
    method: str,
) -> None:
    text = (
        "ML \\<open>val endpoint = @{thms result}\n"
        f"val _ = Comma_Proof_Dependency_Audit.{method} @{{context}} "
        '"check" ["some_dependency", "another_dependency"] endpoint\\<close>'
    )
    assert audited_theorems(text) == ("result",)


@pytest.mark.parametrize(
    "method", ["require_expected_paths", "require_native_closed_expected_paths"]
)
@pytest.mark.parametrize("authorities", ["[]", "required", '["one"] @ more'])
def test_authority_audit_rejects_unknown_or_empty_authority_lists(
    authorities: str,
    method: str,
) -> None:
    text = (
        f"ML \\<open>val _ = Comma_Proof_Dependency_Audit.{method} "
        f'@{{context}} "check" {authorities} @{{thms result}}\\<close>'
    )
    with pytest.raises(ValueError, match="unsupported"):
        audited_theorems(text)


@pytest.mark.parametrize(
    "method", ["require_expected_paths", "require_native_closed_expected_paths"]
)
def test_captured_authority_failure_is_not_a_release_audit(method: str) -> None:
    text = (
        "ML \\<open>val trial = Exn.capture (fn () => "
        f"Comma_Proof_Dependency_Audit.{method} @{{context}} "
        '"negative test" ["missing"] @{thms result}) ()\\<close>'
    )
    assert audited_theorems(text) == ()


def test_native_dependency_audit_resolves_direct_and_bound_theorem_sets() -> None:
    source = (
        "ML \\<open>"
        "val endpoints = @{thms first_endpoint second_endpoint}\n"
        "val one = @{thm third_endpoint}\n"
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"native endpoint set" endpoints\n'
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"native singleton list" [one]\n'
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"native direct list" [@{thm fourth_endpoint}]\n'
        "val _ = Comma_Proof_Dependency_Audit.audit_fuel_free_global @{context} "
        '"diagnostic list" [@{thm fifth_endpoint}]\\<close>'
    )
    assert audited_theorems(source) == (
        "first_endpoint",
        "second_endpoint",
        "third_endpoint",
        "fourth_endpoint",
        "fifth_endpoint",
    )


def test_required_audits_share_one_local_dependency_and_oracle_walk() -> None:
    audit = AUDIT_ML.read_text()
    checked = audit.split("fun checked_names", maxsplit=1)[1].split(
        "(* Resolve the caller's xstrings", maxsplit=1
    )[0]
    for required_piece in (
        "Thm.proof_body_of transferred",
        "Thm.thm_deps transferred",
        "Future.join (Proofterm.thm_node_body node)",
        "Proofterm.join_thms children",
        "Proofterm.unions_oracles oracle_sets",
        "Inttab.defined seen serial",
        "Thm_Name.print (Proofterm.thm_node_name node)",
    ):
        assert required_piece in checked

    for method in (
        "require_paths",
        "require_expected_paths",
        "require_native_closed_expected_paths",
    ):
        body = audit.split(f"fun {method}", maxsplit=1)[1].split(
            "\n  fun ", maxsplit=1
        )[0]
        assert "checked_names thy label thms" in body
        assert "check_oracles label thms" not in body
        assert "names thy thms" not in body

    assert "fun check_oracles label thms =" not in audit
    assert "Thm_Deps.all_oracles" not in audit
    assert "fun names thy thms =" not in audit
    assert "fun require_native_clean ctxt label thms =\n    require_paths" in audit
    assert (
        "fun require_closed_expected_paths ctxt label expected thms =\n    let\n      val _ = require_expected_paths"
        in audit
    )


def test_combined_walker_has_runtime_name_differential_fixture() -> None:
    smoke = AUDIT_SMOKE.read_text()
    assert "fun legacy_names thy thms =" in smoke
    assert "combined_named = Comma_Proof_Dependency_Audit.checked_names" in smoke
    assert "legacy_named = combined_named" in smoke
    assert "Thm_Deps.all_oracles differential_endpoints" in smoke
