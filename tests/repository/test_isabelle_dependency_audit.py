"""Positive authority checks must be executable and distinct from their inputs."""

import pytest

from devtools.checks.isabelle_proof_index import _audited_theorems
from devtools.checks.isabelle_syntax import unquoted_numeric_case_facts


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
    assert _audited_theorems(text) == ("result",)


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
        _audited_theorems(text)


@pytest.mark.parametrize(
    "method", ["require_expected_paths", "require_native_closed_expected_paths"]
)
def test_captured_authority_failure_is_not_a_release_audit(method: str) -> None:
    text = (
        "ML \\<open>val trial = Exn.capture (fn () => "
        f"Comma_Proof_Dependency_Audit.{method} @{{context}} "
        '"negative test" ["missing"] @{thms result}) ()\\<close>'
    )
    assert _audited_theorems(text) == ()


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
    assert _audited_theorems(source) == (
        "first_endpoint",
        "second_endpoint",
        "third_endpoint",
        "fourth_endpoint",
        "fifth_endpoint",
    )
