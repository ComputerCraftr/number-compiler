(* Authenticate only the class roots actually demanded by the two ordered
   child folds, including their physical phase shifts. *)
structure Comma_Future_M204_Shifted_Classes =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Join = Comma_Future_M204_Join_Proposal
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun prove store (join: Join.result) shift_evals zip_evals =
    let
      val ctxt = Store.context store
      val phase = Free ("future_shifted_class_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val nodes = Store.table store
      val ids = map (Store.action_index store) (#classes join)
      val _ = if length ids=16 then () else error "Future class decoder requires sixteen roots"
      val roots = HOLogic.mk_list natT (map nat ids)
      val eval = Const (@{const_name comma_crt_mdd_eval_phase},
        @{typ "nat list => nat comma_crt_mdd_node list => nat => nat => nat option"}) $
          Store.radices store $ nodes $ phase
      val some = Const (@{const_name Some},natT --> @{typ "nat option"})
      val small = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps (@{thms list.size list_all_Nil_iff list_all_Cons_iff} @
          map (Store.bound store) ids)
      val count_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (Const (@{const_name size},fastype_of roots --> natT) $ roots,nat 16))
      val count = Goal.prove ctxt [] [] count_goal (fn _ => simp_tac small 1)
      val bounds_prop = @{term "\<lambda>nodes::nat comma_crt_mdd_node list. \<lambda>roots::nat list.
        list_all (\<lambda>root. root < length nodes) roots"} $ nodes $ roots
      val bounds = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (Envir.beta_norm bounds_prop))
        (fn _ => simp_tac small 1)
      val periodic = @{thm comma_crt_mdd_eval_phase_periodic} OF
        [Store.wellformed store,@{thm comma_frontier_radices_divide}]
      val demands = distinct (op =) (map_filter (fn (step: Join.fold_step) =>
        case #stage step of Join.Source => NONE
        | stage => SOME (stage,#label step,#yes step)) (#fold_steps join))
      fun item (stage,label,output) =
        let
          val value = label-1
          val digit = value mod 9
          val delta = value div 9
          val (kind,slot) = (case stage of Join.Child_N => (@{term Comma_N},digit)
            | Join.Child_Z => (@{term Comma_Z},8+digit)
            | _ => error "Source action is not a child-class demand")
          val _ = if label>0 andalso digit<8 andalso delta<=27 then ()
            else error "Invalid child-class demand"
          val raw = List.nth (ids,slot)
          val normalized_candidates = if delta=0 then [(NONE,output)] else
            map_filter (fn (index,row: Join.shift) =>
              if #amount row=delta andalso #output row=output
              then SOME (SOME index,#source row) else NONE) (map_index I (#shifts join))
          val chains = maps (fn (shift_index,normalized) =>
            map_filter (fn (index,row: Join.zip) =>
              if #output row=normalized andalso #left row=raw andalso #add row=1
              then SOME (shift_index,index,row) else NONE) (map_index I (#zips join)))
            normalized_candidates
          val (shift_index,zip_index,zip_row) = (case chains of first::_ => first
            | [] => error "Child class lacks its exact normalized/shifted root chain")
          val _ = (case Store.node store (#right zip_row) of Store.Leaf 0 => ()
            | _ => error "Child class zip does not use the zero leaf")
          val add = Const (@{const_name plus},natT --> natT --> natT)
          val modulo = Const (@{const_name modulo},natT --> natT --> natT)
          val next = modulo $ (add $ phase $ nat delta) $ nat 924
          val q = HOLogic.mk_prod (kind,HOLogic.mk_prod (nat (digit+2),next))
          val valid = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
            (@{term comma_boundary_valid} $ q)) (fn _ =>
              simp_tac (small |> Simplifier.add_simps @{thms comma_boundary_valid_def}) 1)
          val decoder = Drule.infer_instantiate ctxt
            [(("q",0),Thm.cterm_of ctxt q),(("nodes",0),Thm.cterm_of ctxt nodes),
             (("roots",0),Thm.cterm_of ctxt roots)]
            @{thm comma_future_m204_mdd_class_exact} OF
              [valid,Store.wellformed store,count,bounds]
          val class_value = @{term comma_future_m204_mdd_class} $ nodes $ roots $ q
          val target = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (eval $ nat output,some $ (add $ class_value $ nat 1)))
          val shifts = (case shift_index of NONE => [] | SOME i => [List.nth (shift_evals,i)])
          val facts = decoder :: periodic :: List.nth (zip_evals,zip_index) ::
            Store.phase_leaf store (#right zip_row) :: shifts
          val scalar = small |> Simplifier.add_simps facts
            |> Simplifier.add_simps @{thms option.simps comma_future_m204_family_slot_def
              nth_Cons_0 nth_Cons_Suc fst_conv snd_conv}
          val theorem = Goal.prove ctxt [] [] target (fn _ => simp_tac scalar 1)
          val _ = if Thm.prop_of theorem aconv target then ()
            else error "Shifted class theorem proves a different equation"
          val closed = Thm.forall_intr phase_ct theorem
        in ((stage,label,output),Comma_CRT_MDD_Proof_Utils.ensure_closed_context ctxt
          "Shifted class evaluation" closed) end
      val result = map item demands
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Demanded shifted class evaluations" (map #2 result)
    in {roots=roots,count=count,bounds=bounds,evaluations=result} end
end
