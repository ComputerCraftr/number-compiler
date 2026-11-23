(* Compose only demanded issued-weight imports, one-step shifts and +10 zips.
   Each result is a closed pointwise theorem for a selected semantic root. *)
structure Comma_Future_M204_Shifted_Weights =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Join = Comma_Future_M204_Join_Proposal
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun prove work_store (join: Join.result) weight weight_period weight_evals
      weight_import_evals mapped_weight_evals =
    let
      val ctxt = Store.context work_store
      val phase = Free ("future_shifted_weight_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val eval = Const (@{const_name comma_crt_mdd_eval_phase},
        @{typ "nat list => nat comma_crt_mdd_node list => nat => nat => nat option"}) $
          Store.radices work_store $ Store.table work_store $ phase
      val some = Const (@{const_name Some},natT --> @{typ "nat option"})
      val lookup = AList.lookup (op =) weight_evals
      val demands = distinct (op =) (map_filter (fn (step: Join.fold_step) =>
        case #stage step of Join.Source => if #label step<=46 then
          SOME (#label step-1,#yes step) else NONE | _ => NONE) (#fold_steps join))
      fun item (cid,output) =
        let
          val weight_eval = (case lookup cid of SOME theorem => theorem
            | NONE => error "Demanded M204 weight lacks its checked evaluation")
          val source = Store.action_index work_store (List.nth (#weights join,cid))
          val candidates = map_filter (fn (i,row: Join.mapped_weight) =>
            if #output row=output andalso #source row=source andalso
                #amount row=1 andalso #add row=10 then SOME i else NONE)
            (map_index I (#mapped_weights join))
          val mapped_index = (case candidates of first::_ => first
            | [] => error "Shifted weight lacks its authenticated mapped +10 phase shift")
          val facts = [List.nth (mapped_weight_evals,mapped_index),
            List.nth (weight_import_evals,cid),weight_eval,weight_period]
          val plus = Const (@{const_name plus},natT --> natT --> natT)
          val modulo = Const (@{const_name modulo},natT --> natT --> natT)
          val next_phase = modulo $ (plus $ phase $ nat 1) $ nat 924
          val expected_value = plus $ (weight $ next_phase $ nat cid) $ nat 10
          val target = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (eval $ nat output,some $ expected_value))
          val context = put_simpset HOL_basic_ss ctxt
            |> Simplifier.add_simps @{thms option.simps}
            |> Simplifier.add_simps facts
          val theorem = Goal.prove ctxt [] [] target (fn _ => simp_tac context 1)
          val _ = if Thm.prop_of theorem aconv target then ()
            else error "Shifted M204 weight proves a different equation"
          val closed = Thm.forall_intr phase_ct theorem
        in ((cid,output),Comma_CRT_MDD_Proof_Utils.ensure_closed_context ctxt
          "Shifted M204 weight evaluation" closed) end
      val facts = map item demands
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Demanded shifted M204 weight evaluations" (map #2 facts)
    in facts end
end
