theory Comma_Semantic_Graph_Congruence
  imports Comma_Semantic_Graph
begin

ML \<open>Comma_Proof_Profile.report "B1 graph congruence stage=entered"\<close>

definition comma_semantic_b1_binding_from_pair ::
    "(comma_finite_position \<times> nat) \<Rightarrow> comma_semantic_b1_binding" where
  "comma_semantic_b1_binding_from_pair item =
    \<lparr>comma_semantic_b1_binding_source=fst item,
      comma_semantic_b1_binding_cid=snd item\<rparr>"

definition comma_semantic_b1_node_from_data ::
    "((nat \<times> nat) \<times> comma_semantic_b1_edge list) \<Rightarrow>
      comma_semantic_b1_node" where
  "comma_semantic_b1_node_from_data item =
    \<lparr>comma_semantic_b1_node_cid=fst (fst item),
      comma_semantic_b1_node_period=snd (fst item),
      comma_semantic_b1_node_actions=snd item\<rparr>"

text \<open>
Graph node addresses identify nodes in a finite acyclic continuation DAG.
Equality of node addresses preserves the complete typed edge at each receiving
phase, including the ordered successor address, exact live root, or
terminal-position weight.  This is an equal-node control congruence, not a
claim that the generated addresses are minimal for future behavior.  The
source binding carries admission and local-shift conditions; occurrence phase
remains explicit in the rebasing theorem below.  This is not a weighted
right-congruence: physical Near/Entry elapsed weights remain source-bound
occurrence data and are not identified by a node address.
\<close>

lemma comma_semantic_b1_binding_local_action_shape:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding \<in> set bindings"
  shows "comma_semantic_b1_local_action_shape
    (comma_source_continuation_action_at
      (comma_semantic_b1_binding_source binding) clock)"
proof -
  let ?source = "comma_semantic_b1_binding_source binding"
  let ?cid = "comma_semantic_b1_binding_cid binding"
  have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
    by (rule comma_semantic_b1_graph_binding_row[OF graph binding])
  obtain source_period source_actions where source_id:
    "comma_source_continuation_id ?source=(source_period,source_actions)"
    by (cases "comma_source_continuation_id ?source") auto
  have node_lookup: "comma_semantic_b1_node_of nodes ?cid \<noteq> None"
    by (rule comma_semantic_b1_node_lookup_member[OF graph binding refl])
  obtain node where node:
    "comma_semantic_b1_node_of nodes ?cid=Some node"
    using node_lookup by (cases "comma_semantic_b1_node_of nodes ?cid") auto
  have period:
    "source_period=comma_decisive_sector_period ?source"
    and shape_row:
    "list_all (\<lambda>phase.
       comma_semantic_b1_local_action_shape (source_actions!phase) \<and>
       comma_semantic_b1_edge_of_continuation bindings (source_actions!phase) =
         Some (comma_semantic_b1_node_actions node !
           (phase mod comma_semantic_b1_node_period node)))
      [0..<source_period]"
    using row source_id node
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have admitted: "comma_round_admitted ?source"
    using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
  have positive: "0<source_period"
    using period comma_decisive_sector_period_admitted(1)[OF admitted] by simp
  have phase: "clock mod source_period < source_period"
    using positive by simp
  have shape:
    "comma_semantic_b1_local_action_shape (source_actions!(clock mod source_period))"
    using shape_row phase by (auto simp: list_all_iff)
  have selected:
    "comma_source_continuation_action_at ?source clock =
      source_actions!(clock mod source_period)"
    using source_id period
    by (simp add: comma_source_continuation_action_at_def)
  show ?thesis using shape selected by simp
qed

theorem comma_semantic_b1_graph_right_congruence:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and left: "left_binding \<in> set bindings"
    and right: "right_binding \<in> set bindings"
    and left_cid: "comma_semantic_b1_binding_cid left_binding=cid"
    and right_cid: "comma_semantic_b1_binding_cid right_binding=cid"
  shows "(\<forall>clock.
      comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source left_binding) clock) =
      comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source right_binding) clock))
    \<and> (\<forall>clock.
      comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding) =
      comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source right_binding))
    \<and> (\<forall>clock.
      comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source left_binding) clock)
      \<and> comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source right_binding) clock))"
proof (intro conjI)
  show "\<forall>clock.
      comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source left_binding) clock) =
      comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source right_binding) clock)"
  proof (rule allI)
    fix clock
    have left_apply:
      "comma_semantic_b1_graph_apply nodes cid clock =
        comma_semantic_b1_edge_of_continuation bindings
          (comma_source_continuation_action_at
            (comma_semantic_b1_binding_source left_binding) clock)"
      by (rule comma_semantic_b1_graph_apply_exact_local
        [OF graph left left_cid])
    have right_apply:
      "comma_semantic_b1_graph_apply nodes cid clock =
        comma_semantic_b1_edge_of_continuation bindings
          (comma_source_continuation_action_at
            (comma_semantic_b1_binding_source right_binding) clock)"
      by (rule comma_semantic_b1_graph_apply_exact_local
        [OF graph right right_cid])
    show "comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source left_binding) clock) =
      comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source right_binding) clock)"
      using left_apply right_apply by simp
  qed
next
  show "\<forall>clock.
      comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding) =
      comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source right_binding)"
  proof (rule allI)
    fix clock
    have all: "\<forall>cid. comma_semantic_b1_graph_correct_at bindings nodes cid"
      by (rule comma_semantic_b1_graph_eval_refines_endpoint[OF graph])
    have left_exact:
      "comma_semantic_b1_graph_eval nodes cid clock =
        Some (comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source left_binding))"
      using all left left_cid
      by (auto simp: comma_semantic_b1_graph_correct_at_def)
    have right_exact:
      "comma_semantic_b1_graph_eval nodes cid clock =
        Some (comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source right_binding))"
      using all right right_cid
      by (auto simp: comma_semantic_b1_graph_correct_at_def)
    show "comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source left_binding) =
      comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source right_binding)"
      using left_exact right_exact by simp
  qed
next
  show "\<forall>clock.
      comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source left_binding) clock)
      \<and> comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source right_binding) clock)"
  proof (rule allI)
    fix clock
    have left_shape:
      "comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source left_binding) clock)"
      by (rule comma_semantic_b1_binding_local_action_shape[OF graph left])
    have right_shape:
      "comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source right_binding) clock)"
      by (rule comma_semantic_b1_binding_local_action_shape[OF graph right])
    show "comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source left_binding) clock)
      \<and> comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source right_binding) clock)"
      using left_shape right_shape by simp
  qed
qed

lemma comma_semantic_b1_graph_rebased_packet_congruence:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and left: "left_binding \<in> set bindings"
    and right: "right_binding \<in> set bindings"
    and left_base: "comma_semantic_b1_binding_source left_binding =
      comma_source_continuation_base left_source"
    and right_base: "comma_semantic_b1_binding_source right_binding =
      comma_source_continuation_base right_source"
    and left_cid: "comma_semantic_b1_binding_cid left_binding=cid"
    and right_cid: "comma_semantic_b1_binding_cid right_binding=cid"
    and left_admitted: "comma_round_admitted left_source"
    and right_admitted: "comma_round_admitted right_source"
    and receiving_phase:
      "(phase+comma_source_continuation_shift left_source) mod 924 =
       (phase+comma_source_continuation_shift right_source) mod 924"
  shows "comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase left_source)) =
    comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase right_source))"
proof -
  have left_exact:
    "comma_semantic_b1_graph_apply nodes cid
       ((phase+comma_source_continuation_shift left_source) mod 924) =
     comma_semantic_b1_edge_of_continuation bindings
       (comma_source_continuation_action_of_packet
         (comma_decisive_endpoint_packet phase left_source))"
    by (rule comma_semantic_b1_graph_apply_exact_packet
      [OF graph left left_base left_cid left_admitted])
  have right_exact:
    "comma_semantic_b1_graph_apply nodes cid
       ((phase+comma_source_continuation_shift right_source) mod 924) =
     comma_semantic_b1_edge_of_continuation bindings
       (comma_source_continuation_action_of_packet
         (comma_decisive_endpoint_packet phase right_source))"
    by (rule comma_semantic_b1_graph_apply_exact_packet
      [OF graph right right_base right_cid right_admitted])
  show ?thesis using left_exact right_exact receiving_phase by simp
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_binding_local_action_shape
    comma_semantic_b1_graph_right_congruence
    comma_semantic_b1_graph_rebased_packet_congruence};
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Profile.report "B1 graph congruence claims consolidated";
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Control and terminal-position graph congruence" checked;
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Graph right-congruence source action"
    ["comma_semantic_b1_graph_apply_exact_local",
     "comma_semantic_b1_graph_eval_refines_endpoint",
     "comma_semantic_b1_graph_apply_exact_packet"]
    @{thms comma_semantic_b1_graph_right_congruence
      comma_semantic_b1_graph_rebased_packet_congruence};
  val _ = Comma_Proof_Profile.report "B1 graph congruence audit=checked";
\<close>

end
