theory Comma_Semantic_Graph_CRT_Local_Node_Compilation
  imports Comma_Semantic_Graph_CRT_Compilation
begin

lemma comma_semantic_b1_graph_completed_node_period_facts:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid bindings nodes"
    and lookup: "comma_semantic_b1_node_of nodes cid=Some node"
  shows "0<comma_semantic_b1_node_period node \<and>
    comma_semantic_b1_node_period node dvd 924 \<and>
    length (comma_semantic_b1_node_actions node)=
      comma_semantic_b1_node_period node"
proof -
  have node_member: "node\<in>set nodes"
    by (rule comma_semantic_b1_node_of_member[OF lookup])
  have node_cid: "comma_semantic_b1_node_cid node=cid"
    by (rule comma_semantic_b1_node_of_key[OF lookup])
  obtain binding where binding:
      "binding\<in>set bindings"
      "comma_semantic_b1_binding_cid binding=cid"
    using graph node_member node_cid
    by (auto simp: comma_semantic_b1_graph_completed_valid_def)
  obtain representative where representative:
      "representative\<in>set bindings"
      "comma_semantic_b1_binding_cid representative=
        comma_semantic_b1_binding_cid binding"
      "comma_semantic_b1_binding_row_valid bindings nodes representative"
      "comma_round_admitted (comma_semantic_b1_binding_source binding)"
      "comma_semantic_b1_binding_source binding=
        comma_source_continuation_base (comma_semantic_b1_binding_source binding)"
      "\<forall>clock. comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source binding)=
        comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source representative)"
    by (rule comma_semantic_b1_graph_completed_binding_row[OF graph binding(1)])
  have representative_cid:
      "comma_semantic_b1_binding_cid representative=cid"
    using representative(2) binding(2) by simp
  let ?source = "comma_semantic_b1_binding_source representative"
  let ?source_period = "comma_decisive_sector_period ?source"
  have source_admitted: "comma_round_admitted ?source"
    using representative(3)
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def)
  have source_period: "0<?source_period" "?source_period dvd 924"
    by (rule comma_decisive_sector_period_admitted[OF source_admitted])+
  have node_facts:
      "0<comma_semantic_b1_node_period node"
      "comma_semantic_b1_node_period node dvd ?source_period"
      "length (comma_semantic_b1_node_actions node)=
        comma_semantic_b1_node_period node"
    using representative(3) representative_cid lookup
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
        split: option.splits)
  show ?thesis using node_facts source_period by (auto intro: dvd_trans)
qed

lemma comma_semantic_b1_crt_compile_node_from_children_refines_graph_eval:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid bindings nodes"
    and lookup: "comma_semantic_b1_node_of nodes cid = Some node"
    and child_exact:
      "\<forall>child. Comma_Semantic_B1_Goto child \<in>
          set (comma_semantic_b1_node_actions node) \<longrightarrow>
        (\<forall>phase. comma_weighted_crt_apply (child_action child) phase =
          map_option comma_semantic_b1_crt_graph_result
            (comma_semantic_b1_graph_eval nodes child phase))"
  shows "\<forall>phase. comma_weighted_crt_apply
      (comma_semantic_b1_crt_compile_node_from_children nodes cid child_action) phase =
    map_option comma_semantic_b1_crt_graph_result
      (comma_semantic_b1_graph_eval nodes cid phase)"
proof (intro allI)
  fix phase
  have period_facts:
      "0<comma_semantic_b1_node_period node"
      "comma_semantic_b1_node_period node dvd 924"
      "length (comma_semantic_b1_node_actions node)=
        comma_semantic_b1_node_period node"
    using comma_semantic_b1_graph_completed_node_period_facts[OF graph lookup]
    by auto
  note positive = period_facts(1)
  note divides = period_facts(2)
  note row_length = period_facts(3)
  have node_member: "node\<in>set nodes"
    by (rule comma_semantic_b1_node_of_member[OF lookup])
  have node_key: "comma_semantic_b1_node_cid node=cid"
    by (rule comma_semantic_b1_node_of_key[OF lookup])
  have node_refs: "comma_semantic_b1_edge_refs_valid nodes node"
    by (rule comma_semantic_b1_graph_completed_node_refs[OF graph node_member])
  let ?period = "comma_semantic_b1_node_period node"
  let ?actions = "comma_semantic_b1_node_actions node"
  let ?selector = "comma_weighted_crt_selector_aux [0,1,2,3] ?period 0 ?actions"
  let ?child_next = "\<lambda>edge. case edge of
      Comma_Semantic_B1_Goto child \<Rightarrow>
        if child<cid then child_action child
        else comma_semantic_b1_crt_invalid_action
    | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
        (0,comma_semantic_b1_crt_leaf (Comma_Semantic_B1_CRT_Continue root))
    | Comma_Semantic_B1_Stop_Edge J \<Rightarrow>
        (0,comma_semantic_b1_crt_leaf (Comma_Semantic_B1_CRT_Stop J))
    | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
        comma_semantic_b1_crt_invalid_action"
  have local_step:
      "comma_semantic_b1_crt_compile_node_from_children nodes cid child_action =
        comma_weighted_crt_bind ?selector ?child_next"
    unfolding comma_semantic_b1_crt_compile_node_from_children_def
    using lookup positive divides row_length by simp
  have selected:
      "comma_weighted_crt_eval ?selector phase =
        Some (?actions!(phase mod ?period),0)"
    by (rule comma_weighted_crt_selector_exact(2)
      [OF positive divides row_length])
  have apply_selected:
      "comma_weighted_crt_apply
          (comma_semantic_b1_crt_compile_node_from_children nodes cid child_action) phase =
        comma_weighted_crt_apply (?child_next (?actions!(phase mod ?period))) phase"
    using local_step selected
    by (simp only: local_step comma_weighted_crt_bind_exact selected
      Option.bind_lunit prod.case case_prod_Pair add_0_left option.map_id)
  have graph_apply:
      "comma_semantic_b1_graph_apply nodes cid phase=
        Some (?actions!(phase mod ?period))"
    using lookup period_facts
    by (simp add: comma_semantic_b1_graph_apply_def Let_def)
  have edge_member:
      "?actions!(phase mod ?period)\<in>set ?actions"
    using positive row_length by (simp add: nth_mem)
  show "comma_weighted_crt_apply
      (comma_semantic_b1_crt_compile_node_from_children nodes cid child_action) phase =
    map_option comma_semantic_b1_crt_graph_result
      (comma_semantic_b1_graph_eval nodes cid phase)"
  proof (cases "?actions!(phase mod ?period)")
    case (Comma_Semantic_B1_Goto child)
    have selected_member:
        "Comma_Semantic_B1_Goto child\<in>set ?actions"
      using edge_member Comma_Semantic_B1_Goto by simp
    have child_less: "child<cid"
      using node_refs node_key selected_member
      by (auto simp: comma_semantic_b1_edge_refs_valid_def)
    have child_refinement:
        "\<forall>phase. comma_weighted_crt_apply (child_action child) phase =
          map_option comma_semantic_b1_crt_graph_result
            (comma_semantic_b1_graph_eval nodes child phase)"
      using child_exact selected_member by blast
    have child_at_phase:
        "comma_weighted_crt_apply (child_action child) phase =
          map_option comma_semantic_b1_crt_graph_result
            (comma_semantic_b1_graph_eval nodes child phase)"
      using child_refinement by blast
    have graph_apply_goto:
        "comma_semantic_b1_graph_apply nodes cid phase=
          Some (Comma_Semantic_B1_Goto child)"
      using graph_apply Comma_Semantic_B1_Goto by simp
    have graph_step:
        "comma_semantic_b1_graph_eval nodes cid phase=
          comma_semantic_b1_graph_eval nodes child phase"
      by (rule comma_semantic_b1_graph_eval_apply_goto
        [OF graph_apply_goto child_less])
    show ?thesis
      using apply_selected child_at_phase graph_step Comma_Semantic_B1_Goto
      by (simp only: apply_selected Comma_Semantic_B1_Goto
        comma_semantic_b1_edge.case child_less if_True child_at_phase graph_step)
  next
    case (Comma_Semantic_B1_Live_Edge root)
    have graph_apply_live:
        "comma_semantic_b1_graph_apply nodes cid phase=
          Some (Comma_Semantic_B1_Live_Edge root)"
      using graph_apply Comma_Semantic_B1_Live_Edge by simp
    have root_bound: "root<46"
      using node_refs edge_member Comma_Semantic_B1_Live_Edge
      by (auto simp: comma_semantic_b1_edge_refs_valid_def)
    have graph_step:
        "comma_semantic_b1_graph_eval nodes cid phase=
          Some (Comma_Semantic_B1_Live root)"
      by (rule comma_semantic_b1_graph_eval_apply_live[OF graph_apply_live root_bound])
    show ?thesis
      using apply_selected graph_step Comma_Semantic_B1_Live_Edge root_bound
      by (simp only: apply_selected Comma_Semantic_B1_Live_Edge
        comma_semantic_b1_edge.case comma_semantic_b1_crt_leaf_apply
        graph_step comma_semantic_b1_crt_graph_result.simps option.map)
  next
    case (Comma_Semantic_B1_Stop_Edge J)
    have graph_apply_stop:
        "comma_semantic_b1_graph_apply nodes cid phase=
          Some (Comma_Semantic_B1_Stop_Edge J)"
      using graph_apply Comma_Semantic_B1_Stop_Edge by simp
    have J_bound: "J\<le>8"
      using node_refs edge_member Comma_Semantic_B1_Stop_Edge
      by (auto simp: comma_semantic_b1_edge_refs_valid_def)
    have graph_step:
        "comma_semantic_b1_graph_eval nodes cid phase=
          Some (Comma_Semantic_B1_Stop J)"
      by (rule comma_semantic_b1_graph_eval_apply_stop[OF graph_apply_stop J_bound])
    show ?thesis
      using apply_selected graph_step Comma_Semantic_B1_Stop_Edge J_bound
      by (simp only: apply_selected Comma_Semantic_B1_Stop_Edge
        comma_semantic_b1_edge.case comma_semantic_b1_crt_leaf_apply
        graph_step comma_semantic_b1_crt_graph_result.simps option.map)
  next
    case Comma_Semantic_B1_Invalid_Edge
    have graph_apply_invalid:
        "comma_semantic_b1_graph_apply nodes cid phase=
          Some Comma_Semantic_B1_Invalid_Edge"
      using graph_apply Comma_Semantic_B1_Invalid_Edge by simp
    have graph_step:
        "comma_semantic_b1_graph_eval nodes cid phase=Some Comma_Semantic_B1_Invalid"
      by (rule comma_semantic_b1_graph_eval_apply_invalid[OF graph_apply_invalid])
    show ?thesis
      using apply_selected graph_step Comma_Semantic_B1_Invalid_Edge
      by (simp only: apply_selected Comma_Semantic_B1_Invalid_Edge
        comma_semantic_b1_edge.case comma_semantic_b1_crt_invalid_action_def
        comma_semantic_b1_crt_leaf_apply graph_step
        comma_semantic_b1_crt_graph_result.simps option.map)
  qed
qed

ML \<open>
  Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Ascending local graph-node actions refine graph evaluation"
    @{thms comma_semantic_b1_graph_completed_node_period_facts
      comma_semantic_b1_crt_compile_node_from_children_refines_graph_eval};
  if null (Thm_Deps.all_oracles @{thms
      comma_semantic_b1_graph_completed_node_period_facts
      comma_semantic_b1_crt_compile_node_from_children_refines_graph_eval}) then ()
  else error "Postorder local graph-node refinement depends on an oracle"
\<close>

end
