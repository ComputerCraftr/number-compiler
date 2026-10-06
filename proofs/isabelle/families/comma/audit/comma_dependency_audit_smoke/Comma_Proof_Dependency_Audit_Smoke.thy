theory Comma_Proof_Dependency_Audit_Smoke
  imports Main
begin

ML_file "../../comma_entry_arithmetic/Proof_Dependency_Audit.ML"

lemma comma_dependency_smoke_atom:
  "(0::nat) = 0"
  by simp

lemma comma_dependency_smoke_wrapper:
  "(0::nat) = 0"
  by (rule comma_dependency_smoke_atom)

lemma comma_dependency_smoke_grandchild:
  "(0::nat) = 0"
  by (rule comma_dependency_smoke_wrapper)

lemma comma_dependency_smoke_atom_suffix:
  "(0::nat) = 0"
  by simp

lemma comma_total_macro_hidden:
  "(0::nat) = 0"
  by (rule comma_dependency_smoke_atom)

lemma comma_dependency_smoke_retired_grandchild:
  "(0::nat) = 0"
  by (rule comma_total_macro_hidden)

lemma comma_dependency_smoke_open:
  assumes premise: "P"
  shows "(0::nat) = 0"
  by (rule comma_dependency_smoke_atom)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "positive exact dependency" ["comma_dependency_smoke_atom"]
    @{thms comma_dependency_smoke_grandchild}

  val _ = Comma_Proof_Dependency_Audit.require_closed_expected_paths @{context}
    "positive closed dependency" ["comma_dependency_smoke_atom"]
    @{thms comma_dependency_smoke_grandchild}

  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "positive combined release dependency" ["comma_dependency_smoke_atom"]
    @{thms comma_dependency_smoke_grandchild}

  val missing = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.require_expected_paths @{context}
      "missing exact dependency" ["comma_dependency_smoke_atom"]
      @{thms comma_dependency_smoke_atom_suffix}) ()
  val _ = (case missing of
      Exn.Exn (ERROR message) =>
        if String.isSubstring "missing exact theorem authorities" message then ()
        else error "positive dependency gate rejected for the wrong reason"
    | _ => error "positive dependency gate accepted a non-dependent theorem")

  val retired = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.require_paths @{context}
      "retired grandchild" ["comma_total_macro"]
      @{thms comma_dependency_smoke_retired_grandchild}) ()
  val _ = (case retired of
      Exn.Exn (ERROR message) =>
        if String.isSubstring "retired production paths" message then ()
        else error "retired-path gate rejected for the wrong reason"
    | _ => error "retired-path gate missed a named grandchild")

  val retired_combined = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
      "combined retired grandchild" ["comma_dependency_smoke_atom"]
      @{thms comma_dependency_smoke_retired_grandchild}) ()
  val _ = (case retired_combined of
      Exn.Exn (ERROR message) =>
        if String.isSubstring "retired production paths" message then ()
        else error "combined retired-path gate rejected for the wrong reason"
    | _ => error "combined retired-path gate missed a named grandchild")

  val open_ok = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.require_expected_paths @{context}
      "premise-bearing dependency" ["comma_dependency_smoke_atom"]
      @{thms comma_dependency_smoke_open}) ()
  val _ = (case open_ok of
      Exn.Res () => ()
    | _ => error "generic dependency gate rejected an explicit theorem premise")

  val open_closed = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.require_closed_expected_paths @{context}
      "closed premise-bearing dependency" ["comma_dependency_smoke_atom"]
      @{thms comma_dependency_smoke_open}) ()
  val _ = (case open_closed of
      Exn.Exn (ERROR message) =>
        if String.isSubstring "endpoint has theorem premises" message then ()
        else error "closed dependency gate rejected for the wrong reason"
    | _ => error "closed dependency gate accepted theorem premises")

  val open_combined = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
      "combined premise-bearing dependency" ["comma_dependency_smoke_atom"]
      @{thms comma_dependency_smoke_open}) ()
  val _ = (case open_combined of
      Exn.Exn (ERROR message) =>
        if String.isSubstring "endpoint has theorem premises" message then ()
        else error "combined closure gate rejected for the wrong reason"
    | _ => error "combined closure gate accepted theorem premises")

  val assumed = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.require_expected_paths @{context}
      "hypothetical endpoint" ["comma_dependency_smoke_atom"]
      [Thm.assume @{cprop True}]) ()
  val _ = (case assumed of
      Exn.Exn (ERROR message) =>
        if String.isSubstring "endpoint has hypotheses" message then ()
        else error "hypothetical endpoint rejected for the wrong reason"
    | _ => error "hypothetical endpoint accepted")

  val assumed_combined = Exn.capture (fn () =>
    Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
      "combined hypothetical endpoint" ["comma_dependency_smoke_atom"]
      [Thm.assume @{cprop True}]) ()
  val _ = (case assumed_combined of
      Exn.Exn (ERROR message) =>
        if String.isSubstring "endpoint has hypotheses" message then ()
        else error "combined hypothesis gate rejected for the wrong reason"
    | _ => error "combined hypothesis gate accepted an open theorem")
\<close>

end
