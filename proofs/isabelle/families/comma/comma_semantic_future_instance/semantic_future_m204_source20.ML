(* Prove the two source-20 class/rank facts by following only their two
   authenticated four-axis MDD paths and selected class rows. *)
structure Comma_Future_M204_Source20 =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun prove store roots rows row_selector row_count class_rows =
    let
      val ctxt = Store.context store
      val nodes = Store.table store
      val ids = map (Store.action_index store) roots
      val _ = if length ids=16 then () else error "Source20 needs sixteen class roots"
      val roots_term = HOLogic.mk_list natT (map nat ids)
      fun family (kind,slot) =
        let
          val root = List.nth (ids,slot)
          val {payload=cid,theorem=eval_fact} = Comma_CRT_MDD_Point_Eval.prove store 10 root
          val _ = if 0<=cid andalso cid<length class_rows then ()
            else error "Source20 class ID is outside the authenticated graph"
          val (control,children,rank) = List.nth (class_rows,cid)
          val _ = (control,children)
          val q = HOLogic.mk_prod (kind,HOLogic.mk_prod (nat 2,nat 10))
          val decoder = @{term comma_future_m204_mdd_class} $ nodes $ roots_term $ q
          val goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (decoder,nat cid))
          val context = Comma_Entry_Arithmetic.natural_context ctxt
            |> Simplifier.add_simps [eval_fact]
            |> Simplifier.add_simps @{thms comma_future_m204_mdd_class_def
              comma_future_m204_family_slot_def prod.case comma_boundary_kind.case
              fst_conv snd_conv nth_Cons_0 nth_Cons_Suc option.simps}
          val class_fact = Goal.prove ctxt [] [] goal (fn _ => simp_tac context 1)
          val rank_term = @{term comma_future_m204_rank} $ rows $ decoder
          val result = (case rank of NONE => @{term "None::nat option"}
            | SOME n => Const (@{const_name Some},natT --> @{typ "nat option"}) $ nat n)
          val rank_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq (rank_term,result))
          val scalar = Comma_Entry_Arithmetic.natural_context ctxt
            |> Simplifier.add_proc row_selector
            |> Simplifier.add_simps [class_fact,row_count,@{thm comma_future_m204_rank_def}]
          val rank_fact = Goal.prove ctxt [] [] rank_goal (fn _ => simp_tac scalar 1)
        in (cid,rank,rank_fact) end
      val n = family (@{term Comma_N},0)
      val z = family (@{term Comma_Z},8)
      val _ = (case (#2 n,#2 z) of (NONE,SOME _) => ()
        | _ => error "Source20 class ranks do not have the required N/Z outcomes")
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 source20 checked ranks" [#3 n,#3 z]
    in {north= #3 n,south= #3 z} end
end
