(* Builds and kernel-replays the source and symbolic-join components.  This
   deliberately does not issue the global morphism or release certificate. *)
structure Comma_Future_M204_Component_Loader =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Inputs = Comma_Future_M204_Candidate_Data
  structure Join = Comma_Future_M204_Join_Proposal
  structure Graph = Comma_Future_M204_Graph_Proposal

  fun prepare expected_weight lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      val weight = Comma_Frontier_M204_Weight_Owner.retrieve ctxt expected_weight
      val (source,lthy_source) = Comma_Future_M204_Direct_Physical_Issuer.run lthy
      val source_store = #store source
      val source_arena = #arena source
      val source_roots = #roots source
      val source_facts = #exact source
      val (class_publication,lthy3) = Comma_Future_M204_Class_Rank.publish lthy_source
      val class_arena = Arena.create Inputs.radices
      val class_handles = Vector.fromList (Arena.seed_prefix class_arena (Inputs.classes_seeds ()))
      val class_roots = map (fn id => Vector.sub (class_handles,id)) Inputs.classes_roots
      val (compact_store,lthy3a) = Store.make "comma_future_m204_compact_nodes"
        class_arena lthy3
      val join = Join.build source_arena source_roots (#arena weight) (#roots weight)
        class_arena class_roots
      val _ = Comma_Proof_Profile.report
        ("Future M204 join proposal nodes=" ^ Int.toString (Arena.node_count (#arena join)))
      val graph_rows = map (fn (control,children,_) => (control,children))
        Comma_Future_M204_Graph_Data.rows
      val graph = Graph.build join graph_rows
      val _ = Comma_Proof_Profile.report
        ("Future M204 graph proposal nodes=" ^ Int.toString (Arena.node_count (#arena join)))
      val (work_store,lthy4) = Store.make "comma_future_m204_work_nodes" (#arena join) lthy3a
      val compact_equalities = Comma_Future_M204_Compact_Class_Transport.prove
        compact_store class_roots (#class_export join) work_store (#classes join)
        (#class_import_equalities join)
      val source_ids = map (Store.action_index source_store) source_roots
      val weight_ids = map (Store.action_index (#store weight)) (#roots weight)
      val joined = Comma_Future_M204_Join_Replay.replay source_store (#store weight)
        work_store source_ids weight_ids join
      val comparisons = Comma_Future_M204_Graph_Replay.replay work_store
        (#rows class_publication) (#procedure (#selector class_publication))
        (#count_theorem class_publication) graph
      val demanded = distinct (op =) (maps (fn root =>
        map (fn label => label-1) (filter (fn label => 1<=label andalso label<=46)
          (Arena.action_support (#arena join) root))) (#sources join))
      val weight_evals = Comma_Future_M204_Weight_Evals.prove
        (Local_Theory.target_of lthy4) weight demanded
      val weight_period = Comma_Future_M204_Weight_Evals.periodic
        (Local_Theory.target_of lthy4) weight
      val shifted_weights = Comma_Future_M204_Shifted_Weights.prove work_store join
        (#weight weight) weight_period weight_evals (#weight_import_evals joined)
        (#shift_evals joined) (#zip_evals joined)
      val shifted_classes = Comma_Future_M204_Shifted_Classes.prove work_store join
        (#shift_evals joined) (#zip_evals joined)
      val steps = Comma_Future_M204_Select_Steps.prove work_store join
        (#mask_evals joined) (#selection_evals joined)
      val folds = Comma_Future_M204_Select_Folds.assemble work_store join steps
      val source_transports = Comma_Future_M204_Source_Transport.prove work_store join
        folds (#source_covers joined) shifted_weights (#weight weight)
      val child_transports = Comma_Future_M204_Child_Transport.prove work_store join
        folds (#output_covers joined) (#evaluations shifted_classes) (#roots shifted_classes)
      val graph_pointwise = Comma_Future_M204_Graph_Pointwise.prove work_store
        (#rows class_publication) (#count_theorem class_publication) graph
        (#comparisons comparisons)
      val source_pointwise = Comma_Future_M204_Source_Pointwise.prove work_store join
        (#weight weight) source_facts (#source_import_evals joined) source_transports
      val child_pointwise = Comma_Future_M204_Child_Pointwise.prove work_store join
        (#weight weight) (#bellman weight) source_pointwise child_transports
        (#roots shifted_classes)
      val family_pointwise = Comma_Future_M204_Graph_Family_Pointwise.prove work_store
        (#rows class_publication) (#roots shifted_classes) (#count shifted_classes)
        (#bounds shifted_classes) (#weight weight) (#bellman weight) graph
        (#evaluations comparisons) (#equalities graph_pointwise) (#bounds graph_pointwise)
        source_pointwise child_pointwise
      val source20 = Comma_Future_M204_Source20.prove work_store (#classes join)
        (#rows class_publication) (#procedure (#selector class_publication))
        (#count_theorem class_publication) Comma_Future_M204_Graph_Data.rows
      val (final,lthy5) = Comma_Future_M204_Final_Publication.publish lthy4
        (#weight weight) (#bellman weight) (#rows class_publication)
        (#rows_checked class_publication) (Store.table work_store) (#roots shifted_classes)
        family_pointwise (#north source20) (#south source20)
      val (compact,lthy6) = Comma_Future_M204_Compact_Rank_Publication.publish lthy5
        compact_store class_roots compact_equalities (#class_map final) (#definition final)
        (#bellman weight) (#join final) (#rank final)
    in ({source_facts=source_facts,source_store=source_store,
      weight=weight,class_publication=class_publication,compact_store=compact_store,
      compact_roots=class_roots,
      compact_equalities=compact_equalities,compact=compact,
      join=join,graph=graph,work_store=work_store,join_replay=joined,
      graph_replay=comparisons,weight_evals=weight_evals,weight_period=weight_period,
      shifted_weights=shifted_weights,shifted_classes=shifted_classes,steps=steps,folds=folds,
      source_transports=source_transports,child_transports=child_transports,
      source_pointwise=source_pointwise,child_pointwise=child_pointwise,
      family_pointwise=family_pointwise,source20=source20,
      graph_pointwise=graph_pointwise,final=final},lthy6) end
end
