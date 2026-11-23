(* Transport checked symbolic graph-comparison roots to pointwise facts.
   This uses kernel zip and leaf rules; no source phase is enumerated. *)
structure Comma_Future_M204_Graph_Pointwise =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Proposal = Comma_Future_M204_Graph_Proposal
  val natT = @{typ nat}
  val nodesT = @{typ "nat comma_crt_mdd_node list"}
  val radicesT = @{typ "nat list"}
  val optionT = @{typ "nat option"}
  fun nat n = HOLogic.mk_number natT n
  datatype item = Equality of thm | Bound of thm

  fun prove store rows row_count (candidate: Proposal.result) certificates =
    let
      val ctxt = Store.context store
      val phase = Free ("future_graph_point_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val eval = Const (@{const_name comma_crt_mdd_eval_phase},
        radicesT --> nodesT --> natT --> natT --> optionT) $
        Store.radices store $ Store.table store $ phase
      val truth_rule = Drule.infer_instantiate ctxt [(("phase",0),phase_ct)]
        @{thm comma_frontier_m204_import_equal}
      val zip_rule = Drule.infer_instantiate ctxt [(("phase",0),phase_ct)]
        @{thm comma_crt_mdd_zip_certificate_phase}
      val wf = Store.wellformed store
      fun at_leaf id = Thm.forall_elim phase_ct (Store.phase_leaf store id)
      fun true_at id =
        (case Store.node store id of Store.Leaf 1 => at_leaf id
        | _ => error "Future comparison root is not the true leaf")
      fun item (({operation,left,right,output}: Proposal.comparison),certificate) =
        (case operation of
          Proposal.Equal =>
            let val theorem = truth_rule OF [certificate,wf,wf,Store.bound store left,
                  Store.bound store right,true_at output]
            in SOME (Equality (Thm.forall_intr phase_ct theorem)) end
        | Proposal.Class_Bound =>
            let
              val (right_leaf,truth) = (at_leaf right,true_at output)
              val _ = (case Store.node store right of Store.Leaf 0 => ()
                | _ => error "Future class-bound comparison does not use zero")
              val zip_eval = zip_rule OF [certificate,wf,wf,wf]
              val payload = Free ("future_graph_class_payload",natT)
              val some = Const (@{const_name Some},natT --> optionT) $ payload
              val assumption = HOLogic.mk_Trueprop (HOLogic.mk_eq (eval $ nat left,some))
              val count = Const (@{const_name size},fastype_of rows --> natT) $ rows
              val conclusion = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
                (payload,count))
              val goal = Logic.mk_implies (assumption,conclusion)
              val simps = put_simpset HOL_basic_ss ctxt
                |> Simplifier.add_simps [zip_eval,right_leaf,truth,row_count]
              val theorem = Goal.prove ctxt [] [] goal (fn {context,...} =>
                auto_tac (put_simpset (simpset_of simps) context))
            in SOME (Bound (Thm.forall_intr phase_ct
              (Thm.forall_intr (Thm.cterm_of ctxt payload) theorem))) end
        | _ => NONE)
      val _ = if length certificates=length (#comparisons candidate) then ()
        else error "Future graph replay has a mismatched transcript"
      val results = map_filter item (ListPair.zip (#comparisons candidate,certificates))
      val equalities = map_filter (fn Equality theorem => SOME theorem | _ => NONE) results
      val bounds = map_filter (fn Bound theorem => SOME theorem | _ => NONE) results
      val _ = if length equalities=16 andalso length bounds=16 then ()
        else error "Future graph replay lacks the complete 16-family comparisons"
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Future graph pointwise facts" (equalities @ bounds)
    in {equalities=equalities,bounds=bounds} end
end
