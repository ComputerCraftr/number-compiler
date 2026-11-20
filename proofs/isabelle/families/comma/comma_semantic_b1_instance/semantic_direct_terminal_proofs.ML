(* Checked terminal-action refinements.  Candidate action/expression pairs are
   demanded binding requests, not semantic IDs or future-action cache keys;
   each theorem is constructed and audited in this theory context. *)
structure Comma_Direct_Terminal_Proofs =
struct
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}

  fun make ctxt =
    let
      val cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val hits = Unsynchronized.ref 0
      val issued = Unsynchronized.ref 0
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps @{thms comma_direct_action_terminal_normalization
          comma_direct_action_exit_normalization comma_direct_action_exit_invalid
          comma_decade_root_admitted_def comma_finite_position.simps
          comma_direct_action_interpret.simps}
      fun certify (action,expression) =
        let
          val _ = if Utils.closed action andalso Utils.closed expression andalso
              fastype_of action = @{typ comma_source_continuation_action} andalso
              fastype_of expression = @{typ comma_direct_action_expression} then ()
            else error "Direct terminal proposal is open or ill-typed"
          val _ = (case Compiler.parse_action action of Compiler.Goto _ =>
              error "Goto action requires an authenticated recursive child"
            | _ => ())
          val key = HOLogic.mk_prod (action,expression)
        in case Termtab.lookup (!cache) key of
          SOME theorem => (hits := !hits+1;
            Utils.ensure_closed_context ctxt "Cached terminal refinement" theorem)
        | NONE =>
            let
              val phase = Free ("direct_terminal_phase",natT)
              val shift = Free ("direct_terminal_shift",natT)
              val left = @{term comma_direct_action_interpret} $ expression $ phase $ shift
              val right = @{term comma_phase_program_full_action_of_source_action} $
                phase $ shift $ action
              val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq (left,right))
              val theorem = Goal.prove ctxt [] [] proposition (fn _ => simp_tac scalar 1)
              val _ = if Thm.prop_of theorem aconv proposition then ()
                else error "Terminal refinement changed the requested action"
              val universal = theorem |> Thm.forall_intr (Thm.cterm_of ctxt shift)
                |> Thm.forall_intr (Thm.cterm_of ctxt phase)
                |> Utils.ensure_closed_context ctxt "Direct terminal refinement"
              val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
                "Direct terminal refinement" [universal]
              val _ = cache := Termtab.update (key,universal) (!cache)
              val _ = issued := !issued+1
            in universal end
        end
      fun statistics () = "direct_terminal_proofs=" ^ Int.toString (!issued) ^
        " direct_terminal_hits=" ^ Int.toString (!hits)
    in {certify=certify,statistics=statistics} end
end
