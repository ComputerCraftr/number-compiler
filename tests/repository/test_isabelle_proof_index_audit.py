"""Adversarial tests for executable Isabelle dependency-audit parsing."""

import pytest

from devtools.checks import isabelle_proof_index as index


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


def test_native_dependency_audit_rejects_a_binding_declared_after_its_use() -> None:
    source = (
        "ML \\<open>"
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"release" later_endpoint\n'
        "val later_endpoint = @{thms endpoint}\\<close>"
    )
    with pytest.raises(ValueError, match="not a closed thm/thms antiquotation"):
        index._audited_theorems(source)


def test_later_theorem_binding_does_not_rewrite_an_earlier_audit_argument() -> None:
    source = (
        "ML \\<open>"
        "val endpoint = @{thms original_endpoint}\n"
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"release" endpoint\n'
        "val endpoint = @{thms replacement_endpoint}\\<close>"
    )
    assert index._audited_theorems(source) == ("original_endpoint",)


def test_nontheorem_rebinding_invalidates_an_earlier_theorem_list() -> None:
    source = (
        "ML \\<open>"
        "val endpoint = @{thms original_endpoint}\n"
        "val endpoint = computed_endpoint\n"
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"release" endpoint\\<close>'
    )
    with pytest.raises(ValueError, match="not a closed thm/thms antiquotation"):
        index._audited_theorems(source)


def test_native_dependency_audit_cannot_be_forged_by_comments_strings_or_partial_names() -> (
    None
):
    source = (
        "(* ML \\<open>Comma_Proof_Dependency_Audit.require_native_clean "
        '@{context} "comment" @{thms forged_comment}\\<close> *)\n'
        "text \\<open>Comma_Proof_Dependency_Audit.require_native_clean "
        '@{context} "document" @{thms forged_document}\\<close>\n'
        'ML \\<open>val message = "Comma_Proof_Dependency_Audit.require_native_clean '
        '@{context} \\"string\\" @{thms forged_string}"\n'
        "val partial = Comma_Proof_Dependency_Audit.require_native_clean\n"
        "val bare = Comma_Proof_Dependency_Audit.require_native_clean\\<close>"
    )
    assert index._audited_theorems(source) == ()


def test_captured_native_dependency_audit_is_not_release_evidence() -> None:
    source = (
        "ML \\<open>"
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"executed" @{thms executed_endpoint}\n'
        "val hidden = Exn.capture (fn () => "
        "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        r'"captured" @{thms captured_endpoint}) ()\\<close>'
    )
    assert index._audited_theorems(source) == ("executed_endpoint",)


def test_native_dependency_audit_rejects_unknown_executed_authorities() -> None:
    source = (
        "ML \\<open>val _ = Comma_Proof_Dependency_Audit.require_future_clean "
        '@{context} "native endpoint" @{thms endpoint}\\<close>'
    )
    with pytest.raises(
        ValueError, match="unsupported Comma_Proof_Dependency_Audit methods"
    ):
        index._audited_theorems(source)


@pytest.mark.parametrize(
    "call",
    [
        (
            'Comma_Proof_Dependency_Audit.require_native_clean ctxt "endpoint" '
            "@{thms endpoint}"
        ),
        (
            "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
            '"endpoint" @{thms endpoint} unexpected_argument'
        ),
        (
            "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
            '"endpoint" (@{thms endpoint})'
        ),
    ],
)
def test_native_dependency_audit_rejects_unsupported_invocations(call: str) -> None:
    source = f"ML \\<open>val _ = {call}\\<close>"
    with pytest.raises(ValueError, match="unsupported"):
        index._audited_theorems(source)


def test_captured_and_bare_native_audit_references_are_not_release_evidence() -> None:
    source = (
        "ML \\<open>"
        "val captured = Exn.capture (fn () => "
        "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        r'"captured" @{thms hidden}) ()'
        "val partial = Comma_Proof_Dependency_Audit.require_native_clean"
        "\\<close>"
    )
    assert index._audited_theorems(source) == ()


def test_native_dependency_audit_rejects_unresolved_dynamic_theorem_arguments() -> None:
    source = (
        "ML \\<open>val _ = Comma_Proof_Dependency_Audit.require_native_clean "
        '@{context} "native endpoint" dynamically_computed\\<close>'
    )
    with pytest.raises(ValueError, match="not a closed thm/thms antiquotation"):
        index._audited_theorems(source)


def test_native_dependency_audit_rejects_dynamic_antiquotation_expressions() -> None:
    source = (
        "ML \\<open>val _ = Comma_Proof_Dependency_Audit.require_native_clean "
        '@{context} "native endpoint" @{thms endpoint[OF premise]}\\<close>'
    )
    with pytest.raises(ValueError, match="not a closed theorem-name list"):
        index._audited_theorems(source)
