"""Adversarial tests for executable Isabelle dependency-audit parsing."""

import pytest

from devtools.checks import isabelle_oracle_audit


@pytest.mark.parametrize(
    "wrapper", ["(* {} *)", "(* outer (* {} *) *)", "text \\<open>{}\\<close>"]
)
def test_comment_or_documentation_cannot_forge_audit(wrapper: str) -> None:
    audit = "ML \\<open>Thm_Deps.all_oracles @{thms forged}\\<close>"
    assert isabelle_oracle_audit.audited_theorems(wrapper.format(audit)) == ()


def test_string_literal_cannot_forge_audit() -> None:
    assert (
        isabelle_oracle_audit.audited_theorems(
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
        isabelle_oracle_audit.audited_theorems(source)


def test_later_theorem_binding_does_not_rewrite_an_earlier_audit_argument() -> None:
    source = (
        "ML \\<open>"
        "val endpoint = @{thms original_endpoint}\n"
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"release" endpoint\n'
        "val endpoint = @{thms replacement_endpoint}\\<close>"
    )
    assert isabelle_oracle_audit.audited_theorems(source) == ("original_endpoint",)


def test_nontheorem_rebinding_invalidates_an_earlier_theorem_list() -> None:
    source = (
        "ML \\<open>"
        "val endpoint = @{thms original_endpoint}\n"
        "val endpoint = computed_endpoint\n"
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"release" endpoint\\<close>'
    )
    with pytest.raises(ValueError, match="not a closed thm/thms antiquotation"):
        isabelle_oracle_audit.audited_theorems(source)


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
    assert isabelle_oracle_audit.audited_theorems(source) == ()


def test_captured_native_dependency_audit_is_not_release_evidence() -> None:
    source = (
        "ML \\<open>"
        "val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"executed" @{thms executed_endpoint}\n'
        "val hidden = Exn.capture (fn () => "
        "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        r'"captured" @{thms captured_endpoint}) ()\\<close>'
    )
    assert isabelle_oracle_audit.audited_theorems(source) == ("executed_endpoint",)


def test_bare_top_level_audit_calls_after_semicolon_are_release_evidence() -> None:
    source = (
        "ML \\<open>"
        "val checked = @{thms first_endpoint second_endpoint};"
        "Thm.consolidate checked;"
        "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"bare sequence" checked;'
        "Comma_Proof_Dependency_Audit.require_expected_paths @{context} "
        '"closed authority" ["path"] @{thms third_endpoint};'
        "if null (Thm_Deps.all_oracles checked) then () "
        'else error "oracle"\\<close>'
    )
    assert isabelle_oracle_audit.audited_theorems(source) == (
        "first_endpoint",
        "second_endpoint",
        "third_endpoint",
    )


@pytest.mark.parametrize(
    "expression",
    [
        (
            "val delayed = fn () => "
            "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
            '"delayed lambda" @{thms hidden}'
        ),
        (
            "val delayed = let val action = fn () => "
            "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
            '"let-bound lambda" @{thms hidden} in action end'
        ),
        (
            "fun delayed () = let val _ = "
            "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
            '"nested unit binding" @{thms hidden} in () end'
        ),
        (
            "val delayed = fn () => (let val _ = "
            "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
            '"parenthesized block" @{thms hidden} in () end)'
        ),
        (
            "List.app (fn theorem => "
            "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
            '"higher order" @{thms hidden}) []'
        ),
    ],
)
def test_nested_or_delayed_audit_calls_are_rejected_not_counted(
    expression: str,
) -> None:
    source = f"ML \\<open>{expression}\\<close>"
    with pytest.raises(
        ValueError,
        match="unsupported Comma_Proof_Dependency_Audit invocation form",
    ):
        isabelle_oracle_audit.audited_theorems(source)


def test_top_level_audit_function_reference_is_not_release_evidence() -> None:
    source = (
        "ML \\<open>"
        "Comma_Proof_Dependency_Audit.require_native_clean;"
        "Comma_Proof_Dependency_Audit.checked_names"
        "\\<close>"
    )
    assert isabelle_oracle_audit.audited_theorems(source) == ()


def test_nested_theorem_binding_cannot_supply_a_top_level_audit() -> None:
    source = (
        "ML \\<open>"
        "fun delayed () = let val hidden = @{thms forged} in hidden end;"
        "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        '"out of scope" hidden\\<close>'
    )
    with pytest.raises(ValueError, match="not a closed thm/thms antiquotation"):
        isabelle_oracle_audit.audited_theorems(source)


def test_native_dependency_audit_rejects_unknown_executed_authorities() -> None:
    source = (
        "ML \\<open>val _ = Comma_Proof_Dependency_Audit.require_future_clean "
        '@{context} "native endpoint" @{thms endpoint}\\<close>'
    )
    with pytest.raises(
        ValueError, match="unsupported Comma_Proof_Dependency_Audit methods"
    ):
        isabelle_oracle_audit.audited_theorems(source)


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
        isabelle_oracle_audit.audited_theorems(source)


def test_captured_and_bare_native_audit_references_are_not_release_evidence() -> None:
    source = (
        "ML \\<open>"
        "val captured = Exn.capture (fn () => "
        "Comma_Proof_Dependency_Audit.require_native_clean @{context} "
        r'"captured" @{thms hidden}) ()'
        "val partial = Comma_Proof_Dependency_Audit.require_native_clean"
        "\\<close>"
    )
    assert isabelle_oracle_audit.audited_theorems(source) == ()


def test_native_dependency_audit_rejects_unresolved_dynamic_theorem_arguments() -> None:
    source = (
        "ML \\<open>val _ = Comma_Proof_Dependency_Audit.require_native_clean "
        '@{context} "native endpoint" dynamically_computed\\<close>'
    )
    with pytest.raises(ValueError, match="not a closed thm/thms antiquotation"):
        isabelle_oracle_audit.audited_theorems(source)


def test_native_dependency_audit_rejects_dynamic_antiquotation_expressions() -> None:
    source = (
        "ML \\<open>val _ = Comma_Proof_Dependency_Audit.require_native_clean "
        '@{context} "native endpoint" @{thms endpoint[OF premise]}\\<close>'
    )
    with pytest.raises(ValueError, match="not a closed theorem-name list"):
        isabelle_oracle_audit.audited_theorems(source)


def test_local_runtime_dependency_audits_do_not_claim_named_theorems() -> None:
    source = (
        'lemma exported_endpoint: "True" by simp\n'
        "ML \\<open>val _ = let\n"
        "  val ctxt = @{context}\n"
        "  val checked = @{thm exported_endpoint}\n"
        "in Comma_Proof_Dependency_Audit.require_native_clean ctxt "
        '"local runtime audit" ([checked] @ @{thms exported_endpoint}) end\\<close>'
    )
    # The runtime call audits a local theorem value but does not assert an
    # exported theorem-name dependency for the proof index.
    assert isabelle_oracle_audit.audited_theorems(source) == ()


@pytest.mark.parametrize("result", ("lthy", "snd (Local_Theory.note binding lthy)"))
@pytest.mark.parametrize(
    "context", ("Local_Theory.target_of lthy", "Certificate_Store.context store")
)
def test_local_setup_runtime_dependency_audit_has_no_global_theorem_credit(
    result: str,
    context: str,
) -> None:
    source = (
        'lemma exported_endpoint: "True" by simp\n'
        "local_setup \\<open>fn lthy => let\n"
        f"  val ctxt = {context}\n"
        "  val endpoint = @{thm exported_endpoint}\n"
        "  val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt\n"
        '    "local setup runtime audit" (endpoint::@{thms exported_endpoint})\n'
        f"in {result} end\\<close>"
    )
    assert isabelle_oracle_audit.audited_theorems(source) == ()


def test_local_runtime_audit_rejects_shadowed_context_and_delayed_calls() -> None:
    shadowed_context = (
        "ML \\<open>val _ = let\n"
        "  val ctxt = @{context}\n"
        "  val ctxt = dynamically_computed\n"
        'in Comma_Proof_Dependency_Audit.require_native_clean ctxt "local" [endpoint] end\\<close>'
    )
    with pytest.raises(
        ValueError, match="unsupported Comma_Proof_Dependency_Audit invocation form"
    ):
        isabelle_oracle_audit.audited_theorems(shadowed_context)

    delayed_local_setup = (
        "local_setup \\<open>fn lthy => let\n"
        "  val ctxt = Local_Theory.target_of lthy\n"
        "  val delayed = fn () => Comma_Proof_Dependency_Audit.require_native_clean ctxt\n"
        '    "delayed local audit" [endpoint]\n'
        "in lthy end\\<close>"
    )
    with pytest.raises(
        ValueError, match="unsupported Comma_Proof_Dependency_Audit invocation form"
    ):
        isabelle_oracle_audit.audited_theorems(delayed_local_setup)
