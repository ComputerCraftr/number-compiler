(* Draft: one exact source-output fold theorem per distinct issued root. *)
structure Comma_Future_M204_Source_Transport =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Join = Comma_Future_M204_Join_Proposal
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  type checked_fold = {stage:int,source:int,last:int,entries:Join.fold_step list,chain:thm}

  fun prove store (join: Join.result) (folds:checked_fold list) covers shifted_weights D =
    let
      val ctxt = Store.context store
      val arena = #arena join
      val phase = Free ("future_source_fold_phase",natT)
      val code = Free ("future_source_fold_code",natT)
      val eval = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $ Store.radices store $ Store.table store $ phase
      val some = Const (@{const_name Some},natT --> @{typ "nat option"})
      val zero = Store.action_index store (Arena.action_none arena)
      val zero_eval = Store.phase_leaf store zero
      val expected = @{term "\<lambda>D::nat \<Rightarrow> nat \<Rightarrow> nat.
        \<lambda>phase::nat. \<lambda>code::nat.
        if code=0 then 0 else if code\<le>46 then
          D ((phase+1) mod 924) (code-1)+10 else code-46"} $ D $ phase $ code
      val source_roots = map (Store.action_index store) (#sources join)
      val output_roots = map (Store.action_index store) (#outputs join)
      val _ = if length source_roots=16 andalso length output_roots=16 andalso length covers=16
        then () else error "Source transport requires sixteen authenticated families"
      val requests = distinct (op =) (source_roots ~~ output_roots)
      fun one (source,output) =
        let
          val index = find_index (fn id => id=source) source_roots
          val cover = List.nth (covers,index)
          val groups = filter (fn {stage,source=s,last,...} =>
            stage=0 andalso s=source andalso last=output) folds
          val group = (case groups of [one] => one
            | _ => error "Source transport lacks a unique checked fold")
          val entries = #entries group
          val chain_rule = #chain group RS @{thm comma_future_m204_select_chain_map}
          val selected_weights = map_filter (fn (entry: Join.fold_step) =>
            if #label entry<=46 then
              (case AList.lookup (op =) shifted_weights (#label entry-1,#yes entry) of
                SOME theorem => SOME theorem
              | NONE => error "Source fold lacks a checked shifted weight")
            else NONE) entries
          val terminal_facts = map_filter (fn (entry: Join.fold_step) =>
            if #label entry>46 then SOME (Store.phase_leaf store (#yes entry)) else NONE) entries
          val covered = @{thm comma_future_m204_eval_phase_covered} OF
            [Store.wellformed store,Store.bound store source,cover]
          val assumption = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (eval $ nat source,some $ code))
          val target = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (eval $ nat output,some $ Envir.beta_norm expected))
          val scalar = Comma_Entry_Arithmetic.natural_context ctxt
            |> Simplifier.add_simps @{thms comma_future_m204_select_chain_map
              fold_Cons fold_Nil list.map rev.simps map_of.simps list.set
              prod.case option.simps HOL.simp_thms}
            |> Simplifier.add_simps (chain_rule :: zero_eval :: selected_weights @ terminal_facts)
          val theorem = Goal.prove ctxt ["future_source_fold_phase","future_source_fold_code"]
            [assumption] target (fn {context,prems} =>
              Method.insert_tac context (covered::prems) 1 THEN
              auto_tac (put_simpset (simpset_of scalar) context))
        in ((source,output),theorem) end
      val facts = map one requests
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 semantic source folds" (map #2 facts)
    in facts end
end
