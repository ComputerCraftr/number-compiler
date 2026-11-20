(* Replays chronological selected steps; no candidate node is a theorem. *)
structure Comma_Future_M204_Select_Steps =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Proposal = Comma_Future_M204_Join_Proposal
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Key = Table(type key = int list val ord = list_ord int_ord)
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun prove store (candidate: Proposal.result) mask_evals selection_evals =
    let
      val ctxt = Store.context store
      val arena = #arena candidate
      val false_id = Store.boolean_index store (Arena.boolean_false arena)
      val true_id = Store.boolean_index store (Arena.boolean_true arena)
      fun insert (key,fact) tab =
        (case Key.lookup tab key of NONE => Key.update (key,fact) tab
        | SOME old => if Thm.prop_of old aconv Thm.prop_of fact then tab
          else error "Conflicting M204 operation transcript")
      val masks = fold insert (map (fn ({source,label,output}: Proposal.mask,fact) =>
        ([source,label,output],fact)) (#masks candidate ~~ mask_evals)) Key.empty
      val selections = fold insert (map (fn ({guard,yes,no,output}: Proposal.selection,fact) =>
        ([guard,yes,no,output],fact)) (#selections candidate ~~ selection_evals)) Key.empty
      val phase = Free ("m204_select_phase",natT)
      val code = Free ("m204_select_code",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val zero = Thm.forall_elim phase_ct (Store.phase_leaf store false_id)
      val one = Thm.forall_elim phase_ct (Store.phase_leaf store true_id)
      val eval = @{term "comma_crt_mdd_eval_phase :: nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option"} $ Store.radices store $
        Store.table store $ phase
      fun at_phase theorem = Drule.infer_instantiate ctxt
        [(("phase",0),phase_ct)] theorem
      fun lookup_mask source label guard =
        (case Key.lookup masks [source,label,guard] of
          SOME fact => at_phase fact
        | NONE => error "M204 select step lacks its checked mask")
      fun lookup_selection guard yes no output =
        (case Key.lookup selections [guard,yes,no,output] of
          SOME fact => at_phase fact
        | NONE => error "M204 select step lacks its checked selection")
      val some = Const (@{const_name Some},natT --> @{typ "nat option"})
      val ifT = @{typ bool} --> @{typ "nat option"} --> @{typ "nat option"} --> @{typ "nat option"}
      fun prove_step ({source,label,guard,yes,no,output,...}: Proposal.fold_step) =
        let
          val mask = lookup_mask source label guard
          val selection = lookup_selection guard yes no output
          val assumption = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval $ nat source,some $ code))
          val rhs = Const (@{const_name If},ifT) $ HOLogic.mk_eq (code,nat label) $
            (eval $ nat yes) $ (eval $ nat no)
          val target = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval $ nat output,rhs))
          val theorem = Goal.prove ctxt ["m204_select_phase","m204_select_code"] [assumption] target
            (fn {context,prems} =>
              resolve_tac context [@{thm comma_future_m204_select_step}] 1 THEN
              resolve_tac context prems 1 THEN
              resolve_tac context [zero] 1 THEN resolve_tac context [one] 1 THEN
              resolve_tac context [mask] 1 THEN resolve_tac context [selection] 1)
        in theorem end
      val facts = map prove_step (#fold_steps candidate)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 chronological select steps" facts
    in facts end
end
