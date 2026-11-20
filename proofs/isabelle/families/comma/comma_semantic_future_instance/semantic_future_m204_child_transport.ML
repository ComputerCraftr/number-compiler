(* One exact ordered-child fold law per distinct encoded-output root and
   direction; all selected values come from checked shifted class roots. *)
structure Comma_Future_M204_Child_Transport =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Join = Comma_Future_M204_Join_Proposal
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  type checked_fold = {stage:int,source:int,last:int,entries:Join.fold_step list,chain:thm}

  fun prove store (join: Join.result) (folds: checked_fold list) covers
      shifted_classes roots =
    let
      val ctxt = Store.context store
      val arena = #arena join
      val phase = Free ("future_child_fold_phase",natT)
      val code = Free ("future_child_fold_code",natT)
      val nodes = Store.table store
      val eval = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $ Store.radices store $ nodes $ phase
      val some = Const (@{const_name Some},natT --> @{typ "nat option"})
      val initial = Store.action_index store (Arena.action_none arena)
      val zero_eval = Store.phase_leaf store initial
      val expected = @{term "\<lambda>nodes::nat comma_crt_mdd_node list. \<lambda>roots::nat list.
        \<lambda>kind::comma_boundary_kind. \<lambda>phase::nat. \<lambda>code::nat.
        if code=0 \<or> (code-1) mod 9=8 then 0 else
          Suc (comma_future_m204_mdd_class nodes roots
            (kind,(code-1) mod 9+2,(phase+(code-1) div 9) mod 924))"}
      val sources = map (Store.action_index store) (#outputs join)
      val children_n = map (Store.action_index store) (#children_n join)
      val children_z = map (Store.action_index store) (#children_z join)
      val _ = if length sources=16 andalso length covers=16 andalso
          length children_n=16 andalso length children_z=16 then ()
        else error "Child transport requires sixteen authenticated families"
      val requests = distinct (op =)
        (map (fn (s,child) => (1,s,child)) (sources ~~ children_n) @
         map (fn (s,child) => (2,s,child)) (sources ~~ children_z))
      fun one (stage,source,output) =
        let
          val index = find_index (fn id => id=source) sources
          val cover = List.nth (covers,index)
          val groups = filter (fn {stage=t,source=s,last,...} =>
            stage=t andalso s=source andalso last=output) folds
          val (entries,chain_facts) = (case groups of
              [] => if output=initial then ([],[zero_eval])
                else error "Empty child fold does not return the checked zero root"
            | [group] => (#entries group,[#chain group RS @{thm comma_future_m204_select_chain_map}])
            | _ => error "Child transport has ambiguous fold transcripts")
          val direction = if stage=1 then Join.Child_N else Join.Child_Z
          val kind = if stage=1 then @{term Comma_N} else @{term Comma_Z}
          val selected = map (fn (entry: Join.fold_step) =>
            (case AList.lookup (op =) shifted_classes (direction,#label entry,#yes entry) of
              SOME theorem => theorem
            | NONE => error "Child fold lacks its checked shifted class")) entries
          val covered = @{thm comma_future_m204_eval_phase_covered} OF
            [Store.wellformed store,Store.bound store source,cover]
          val assumption = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval $ nat source,some $ code))
          val value = Envir.beta_norm (list_comb (expected,[nodes,roots,kind,phase,code]))
          val target = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval $ nat output,some $ value))
          val scalar = Comma_Entry_Arithmetic.natural_context ctxt
            |> Simplifier.add_simps @{thms comma_future_m204_select_chain_map
              fold_Cons fold_Nil list.map rev.simps map_of.simps list.set
              prod.case option.simps HOL.simp_thms}
            |> Simplifier.add_simps (zero_eval :: chain_facts @ selected)
          val theorem = Goal.prove ctxt ["future_child_fold_phase","future_child_fold_code"]
            [assumption] target (fn {context,prems} =>
              Method.insert_tac context (covered::prems) 1 THEN
              auto_tac (put_simpset (simpset_of scalar) context))
        in ((stage,source,output),theorem) end
      val facts = map one requests
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 semantic ordered-child folds" (map #2 facts)
    in facts end
end
