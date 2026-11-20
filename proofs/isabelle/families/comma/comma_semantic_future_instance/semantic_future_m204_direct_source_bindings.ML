(* Physical source bindings consume checked direct action theorems.  Source,
   program and root values are requests; they do not themselves issue proof. *)
structure Comma_Future_M204_Direct_Source_Bindings =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  type binding = {source:term, program:term, expression:term, root:term,
    evaluation:thm, program_action:thm}

  fun certify ctxt radices nodes (bindings:binding list) =
    let
      val expected_sources = Runtime.physical_initial_sources ()
      val sources = map #source bindings
      val _ = if length bindings = 16 andalso ListPair.allEq (op aconv)
          (sources,expected_sources) then ()
        else error "Direct physical sources differ from the admitted family order"
      val context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps @{thms comma_semantic_port_program_of_source_def
          comma_canonical_position_admitted_def comma_round_admitted.simps
          comma_source_continuation_base.simps comma_sector_entry_bound_def
          comma_entry_control_program_def comma_near_control_program_def
          comma_entry_core_common_rules comma_phase_core_of_modulus_def
          comma_finite_position.simps option.simps prod.case}
      fun publish ({source,program,expression,root,evaluation,program_action}:binding) =
        let
          val _ = Utils.ensure_closed_context ctxt "Direct source MDD evaluation" evaluation
          val _ = Utils.ensure_closed_context ctxt "Direct source program action" program_action
          val phase = Free ("direct_source_phase",@{typ nat})
          val rule = Drule.infer_instantiate ctxt
            [( ("radices",0),Thm.cterm_of ctxt radices),
             ( ("nodes",0),Thm.cterm_of ctxt nodes),
             ( ("root",0),Thm.cterm_of ctxt root),
             ( ("expression",0),Thm.cterm_of ctxt expression),
             ( ("program",0),Thm.cterm_of ctxt program),
             ( ("source",0),Thm.cterm_of ctxt source),
             ( ("phase",0),Thm.cterm_of ctxt phase)]
            @{thm comma_future_m204_direct_physical_round}
          val eval_at = Thm.forall_elim (Thm.cterm_of ctxt phase) evaluation
          val action_at = Thm.forall_elim (Thm.cterm_of ctxt phase) program_action
            |> Thm.forall_elim (Thm.cterm_of ctxt @{term "0::nat"})
          val conclusion = Logic.strip_assums_concl (Thm.prop_of rule)
          val theorem = Goal.prove ctxt [] [] conclusion (fn {context=proof_ctxt,...} =>
            resolve_tac proof_ctxt [rule] 1 THEN
            resolve_tac proof_ctxt [eval_at] 1 THEN
            resolve_tac proof_ctxt [action_at] 1 THEN
            ALLGOALS (asm_full_simp_tac context))
          val _ = if Thm.prop_of theorem aconv conclusion then ()
            else error "Direct physical source proves a different output"
          val universal = Thm.forall_intr (Thm.cterm_of ctxt phase) theorem
        in Utils.ensure_closed_context ctxt "Direct physical source" universal end
      val theorems = map publish bindings
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Direct physical source bindings" theorems
    in theorems end
end
