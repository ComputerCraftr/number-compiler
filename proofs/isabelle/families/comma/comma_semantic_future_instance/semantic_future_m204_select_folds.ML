(* Prove each source-root selection as one chronological chain. *)
structure Comma_Future_M204_Select_Folds =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Proposal = Comma_Future_M204_Join_Proposal
  structure Key = Table(type key = int * int val ord = prod_ord int_ord int_ord)
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun stage Proposal.Source = 0 | stage Proposal.Child_N = 1 | stage Proposal.Child_Z = 2

  fun assemble store (candidate: Proposal.result) steps =
    let
      val ctxt = Store.context store
      val arena = #arena candidate
      val initial = Store.action_index store (Arena.action_none arena)
      val phase = Free ("m204_fold_phase",natT)
      val code = Free ("m204_fold_code",natT)
      val eval = @{term "comma_crt_mdd_eval_phase :: nat list \<Rightarrow> nat comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option"} $ Store.radices store $
        Store.table store $ phase
      val some = Const (@{const_name Some},natT --> @{typ "nat option"})
      type state = {last:int, entries: Proposal.fold_step list, facts: thm list}
      fun collect ((item: Proposal.fold_step),fact) tab =
        let
          val key = (stage (#stage item),#source item)
          val (last,entries,facts) = case Key.lookup tab key of
            NONE => (initial,[],[])
          | SOME ({last,entries,facts}: state) => (last,entries,facts)
          val _ = if #no item = last then ()
            else error "M204 select transcript is not chronologically adjacent"
        in Key.update (key,{last= #output item,entries=item::entries,facts=fact::facts}) tab end
      val grouped = fold collect (#fold_steps candidate ~~ steps) Key.empty
      val stepT = @{typ comma_future_m204_select_step}
      fun term_step (entry: Proposal.fold_step) =
        HOLogic.mk_prod (nat (#label entry),HOLogic.mk_prod (nat (#yes entry),
          HOLogic.mk_prod (nat (#no entry),nat (#output entry))))
      fun check ((stage_id,source),({last,entries,facts}: state)) =
        let
          val chronological = rev entries
          val step_list = HOLogic.mk_list stepT (map term_step chronological)
          val chain = @{term "comma_future_m204_select_chain :: (nat \<Rightarrow> nat option) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_future_m204_select_step list \<Rightarrow> bool"} $ eval $ code $ nat initial $ step_list
          val assumption = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval $ nat source,some $ code))
          val theorem = Goal.prove ctxt ["m204_fold_phase","m204_fold_code"] [assumption]
            (HOLogic.mk_Trueprop chain)
            (fn {context,prems} =>
              asm_full_simp_tac (put_simpset HOL_basic_ss context |>
                Simplifier.add_simps
                  (@{thms comma_future_m204_select_chain.simps HOL.simp_thms} @ facts @ prems)) 1)
        in {stage=stage_id,source=source,last=last,entries=chronological,chain=theorem} end
      val checked = map check (Key.dest grouped)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 chronological selection chains" (map #chain checked)
    in checked end
end
