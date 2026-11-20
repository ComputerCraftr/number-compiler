(* Convert demanded, authenticated weight roots into pointwise equations for
   the named B1 weight.  No weight or source trajectory is re-executed. *)
structure Comma_Future_M204_Weight_Evals =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Owner = Comma_Frontier_M204_Weight_Owner
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun periodic ctxt (publication: Owner.publication) =
    let
      val store = #store publication
      val rhs = Thm.term_of (Thm.rhs_of (#definition publication))
      val roots = (case strip_comb rhs of
          (Const (name,_),[radices,nodes,root_terms]) =>
            if name = @{const_name comma_frontier_m204_mdd_value} andalso
                radices aconv Store.radices store andalso nodes aconv Store.table store
            then root_terms else error "M204 periodic weight has a foreign decoder"
        | _ => error "Malformed M204 periodic weight definition")
      val phase = Free ("future_weight_period_phase",natT)
      val cid = Free ("future_weight_period_class",natT)
      val generic = Drule.infer_instantiate ctxt
        [(("roots",0),Thm.cterm_of ctxt roots),
         (("phase",0),Thm.cterm_of ctxt phase),(("cid",0),Thm.cterm_of ctxt cid)]
        @{thm comma_future_m204_mdd_value_periodic} OF
          [Store.wellformed store,@{thm comma_frontier_radices_divide}]
      val named = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt)
        [Thm.symmetric (#definition publication)] generic
      val closed = Thm.forall_intr (Thm.cterm_of ctxt phase)
        (Thm.forall_intr (Thm.cterm_of ctxt cid) named)
      val checked = Comma_CRT_MDD_Proof_Utils.ensure_closed_context ctxt
        "M204 named weight periodicity" closed
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 named weight periodicity" [checked]
    in checked end

  fun prove ctxt (publication: Owner.publication) demanded =
    let
      val store = #store publication
      val definition = #definition publication
      val rhs = Thm.term_of (Thm.rhs_of definition)
      val (rs,nodes,root_terms) = (case strip_comb rhs of
          (Const (name,_),[r,n,roots]) =>
            if name = @{const_name comma_frontier_m204_mdd_value} then (r,n,roots)
            else error "M204 weight is not the issued decoder"
        | _ => error "Malformed M204 weight definition")
      val _ = if rs aconv Store.radices store andalso nodes aconv Store.table store then ()
        else error "M204 weight decoder has a foreign Store"
      val ids = map (Store.action_index store) (#roots publication)
      val literals = HOLogic.dest_list root_terms
      val _ = if length ids=46 andalso length literals=46 andalso
          ListPair.allEq (fn (id,t) => t aconv nat id) (ids,literals) then ()
        else error "M204 weight decoder roots differ from the issued handles"
      val phase = Free ("future_weight_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val small = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps @{thms list.size nth_Cons_0 nth_Cons_Suc}
      val eval = Const (@{const_name comma_crt_mdd_eval_phase},
        @{typ "nat list => nat comma_crt_mdd_node list => nat => nat => nat option"}) $
          rs $ nodes $ phase
      val some = Const (@{const_name Some},natT --> @{typ "nat option"})
      fun item cid =
        let
          val _ = if 0<=cid andalso cid<46 then () else error "M204 weight demand is outside 46 classes"
          val id = List.nth (ids,cid)
          val cid_prop = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
            (nat cid,Const (@{const_name size},fastype_of root_terms --> natT) $ root_terms))
          val cid_fact = Goal.prove ctxt [] [] cid_prop (fn _ => simp_tac small 1)
          val root_prop = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
            (Const (@{const_name nth},fastype_of root_terms --> natT --> natT) $
              root_terms $ nat cid,
             Const (@{const_name size},fastype_of nodes --> natT) $ nodes))
          val root_fact = Goal.prove ctxt [] [] root_prop (fn _ =>
            simp_tac (small |> Simplifier.add_simps [Store.bound store id]) 1)
          val generic = Drule.infer_instantiate ctxt [(("phase",0),phase_ct)]
            @{thm comma_frontier_m204_mdd_value_exact} OF
              [Store.wellformed store,cid_fact,root_fact]
          val renamed = Simplifier.rewrite_rule
            (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps @{thms nth_Cons_0 nth_Cons_Suc})
            [Thm.symmetric definition] generic
          val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (eval $ nat id,some $ (#weight publication $ phase $ nat cid)))
          val _ = if Thm.prop_of renamed aconv expected then ()
            else error "M204 demanded weight theorem proves a different equation"
          val closed = Thm.forall_intr phase_ct renamed
        in Comma_CRT_MDD_Proof_Utils.ensure_closed_context ctxt
          "M204 demanded weight evaluation" closed end
      val labels = sort int_ord (distinct (op =) demanded)
      val theorems = map item labels
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 demanded weight evaluations" theorems
    in labels ~~ theorems end
end
