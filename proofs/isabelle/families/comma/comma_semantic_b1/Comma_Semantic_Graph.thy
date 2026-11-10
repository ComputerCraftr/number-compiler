theory Comma_Semantic_Graph
  imports Comma_Semantic_Graph_Core
begin

ML_file "proof_rewrite_rules.ML"
ML \<open>Comma_Proof_Profile.report "B1 graph stage=entered"\<close>

text \<open>
The completed-action endpoint induction and root-exact laws use the core
source-binding, representative, and local-row contracts.  The core evaluator
continues to preserve terminal labels and evaluates child CIDs at the original
receiving clock.
\<close>

definition comma_semantic_b1_graph_correct_at ::
    "comma_semantic_b1_binding list \<Rightarrow> comma_semantic_b1_node list \<Rightarrow>
      nat \<Rightarrow> bool" where
  "comma_semantic_b1_graph_correct_at bindings nodes cid =
    (\<forall>binding\<in>set bindings.
       comma_semantic_b1_binding_cid binding=cid \<longrightarrow>
       (\<forall>clock. comma_semantic_b1_graph_eval nodes cid clock =
         Some (comma_semantic_b1_round_output clock
           (comma_semantic_b1_binding_source binding))))"

theorem comma_semantic_b1_graph_completed_eval_refines_endpoint:
  assumes graph: "comma_semantic_b1_graph_completed_valid bindings nodes"
  shows "\<forall>cid. comma_semantic_b1_graph_correct_at bindings nodes cid"
proof (rule allI)
  fix cid
  show "comma_semantic_b1_graph_correct_at bindings nodes cid"
  proof (induction cid rule: less_induct)
    case (less cid)
    show ?case
      unfolding comma_semantic_b1_graph_correct_at_def
    proof (intro ballI impI allI)
      fix binding clock
      assume binding_member: "binding\<in>set bindings"
        and source_cid: "comma_semantic_b1_binding_cid binding=cid"
      obtain representative where representative_member:
          "representative\<in>set bindings"
        and representative_cid: "comma_semantic_b1_binding_cid representative=cid"
        and representative_row:
          "comma_semantic_b1_binding_row_valid bindings nodes representative"
        and source_admitted:
          "comma_round_admitted (comma_semantic_b1_binding_source binding)"
        and source_normalized:
          "comma_semantic_b1_binding_source binding =
            comma_source_continuation_base (comma_semantic_b1_binding_source binding)"
        and source_output_transport:
          "\<forall>phase. comma_semantic_b1_round_output phase
              (comma_semantic_b1_binding_source binding) =
            comma_semantic_b1_round_output phase
              (comma_semantic_b1_binding_source representative)"
        using comma_semantic_b1_graph_completed_binding_row
            [OF graph binding_member] source_cid
        by blast
      let ?source = "comma_semantic_b1_binding_source representative"
      have binding_cid: "comma_semantic_b1_binding_cid representative=cid"
        using representative_cid .
      have row: "comma_semantic_b1_binding_row_valid bindings nodes representative"
        by (rule representative_row)
      have admitted: "comma_round_admitted ?source"
        using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
      have source_base: "?source=comma_source_continuation_base ?source"
        using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
      have source_period_positive: "0<comma_decisive_sector_period ?source"
        by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
      have action_slot:
        "comma_source_continuation_action_at ?source clock =
          comma_source_continuation_action_of_packet
            (comma_decisive_endpoint_packet clock ?source)"
        using comma_source_continuation_signature_slot[OF admitted, of clock]
          source_base by simp
      have current_node_exists:
        "comma_semantic_b1_node_of nodes cid\<noteq>None"
        by (rule comma_semantic_b1_graph_completed_node_lookup
          [OF graph representative_member binding_cid])
      obtain current_node where current_node:
        "comma_semantic_b1_node_of nodes cid=Some current_node"
        using current_node_exists
        by (cases "comma_semantic_b1_node_of nodes cid") auto
      have current_period:
        "0<comma_semantic_b1_node_period current_node"
        and current_actions:
        "length (comma_semantic_b1_node_actions current_node)=
          comma_semantic_b1_node_period current_node"
        using row current_node binding_cid
        by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
          split: option.splits)
      have source_shift_zero:
        "comma_source_continuation_shift ?source=0"
        using source_base by (cases ?source) simp_all
      have node_period_divides:
        "comma_semantic_b1_node_period current_node dvd 924"
        using row current_node binding_cid
        by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
          split: option.splits)
      have apply_periodic:
        "comma_semantic_b1_graph_apply nodes cid clock =
          comma_semantic_b1_graph_apply nodes cid (clock mod 924)"
        unfolding comma_semantic_b1_graph_apply_def
        using current_node current_period current_actions node_period_divides
        by (simp add: mod_mod_cancel)
      have packet_action:
        "comma_semantic_b1_graph_apply nodes cid clock =
          comma_semantic_b1_edge_of_continuation bindings
            (comma_source_continuation_action_of_packet
              (comma_decisive_endpoint_packet clock ?source))"
      proof -
        have shifted:
          "comma_semantic_b1_graph_apply nodes cid
              ((clock+comma_source_continuation_shift ?source) mod 924) =
            comma_semantic_b1_edge_of_continuation bindings
              (comma_source_continuation_action_of_packet
                (comma_decisive_endpoint_packet clock ?source))"
          by (rule comma_semantic_b1_graph_completed_apply_exact_packet
            [OF row source_base binding_cid admitted])
        show ?thesis using apply_periodic shifted source_shift_zero
          by simp
      qed
      have apply_present:
        "comma_semantic_b1_graph_apply nodes cid clock\<noteq>None"
        using current_node current_period current_actions
        by (simp add: comma_semantic_b1_graph_apply_def)
      obtain target move where packet:
        "comma_decisive_endpoint_packet clock ?source=(target,move)"
        by (cases "comma_decisive_endpoint_packet clock ?source") auto
      have target_admitted:
        "comma_round_admitted target"
        using comma_decisive_packet_target_admitted[OF admitted, of clock] packet
        by simp
      have packet_target:
        "comma_decisive_sector_target clock ?source=target"
        using packet by (simp add: comma_decisive_endpoint_packet_def Let_def)
      have fast_move:
        "comma_fast_step (clock mod 924) target=move"
        using packet packet_target
        by (simp add: comma_decisive_endpoint_packet_def Let_def)
      have finite_move:
        "comma_finite_step (clock mod 924) target=move"
        using fast_move by (simp only: comma_fast_step_correct)
      have target_shift_zero:
        "comma_source_continuation_shift target=0"
        using comma_semantic_b1_base_packet_target_shift_zero
            [OF source_base, of clock]
          packet by simp
      have packet_shape:
        "comma_semantic_b1_local_action_shape
          (comma_source_continuation_action_of_packet (target,move))"
      proof -
        let ?P = "comma_decisive_sector_period ?source"
        have phase: "clock mod ?P<?P"
          using source_period_positive by simp
        have shape_edge:
          "comma_semantic_b1_local_action_shape
              (comma_source_continuation_action_at ?source (clock mod ?P))
            \<and> comma_semantic_b1_edge_of_continuation bindings
              (comma_source_continuation_action_at ?source (clock mod ?P)) =
                Some (comma_semantic_b1_node_actions current_node !
                  ((clock mod ?P) mod
                    comma_semantic_b1_node_period current_node))"
          by (rule comma_semantic_b1_binding_row_exact_from_valid
            [OF row binding_cid current_node phase])
        have shape:
          "comma_semantic_b1_local_action_shape
            (comma_source_continuation_action_at ?source (clock mod ?P))"
          using shape_edge by simp
        have edge:
          "comma_semantic_b1_edge_of_continuation bindings
            (comma_source_continuation_action_at ?source (clock mod ?P)) =
            Some (comma_semantic_b1_node_actions current_node !
              ((clock mod ?P) mod
                comma_semantic_b1_node_period current_node))"
          using shape_edge by simp
        have periodic:
          "comma_source_continuation_action_at ?source (clock mod ?P) =
            comma_source_continuation_action_at ?source clock"
          using source_base by (simp add: comma_source_continuation_action_at_def
            comma_source_continuation_id_def Let_def)
        show ?thesis using shape periodic action_slot packet by simp
      qed
      have round_equation:
        "comma_decisive_endpoint_round clock ?source =
          (case move of
             Comma_Next successor \<Rightarrow>
               if comma_round_crossing target successor then
                 Comma_Round_Cross successor
               else comma_decisive_endpoint_round clock successor
           | Comma_Fork a delta \<Rightarrow> Comma_Round_Fork a delta
           | Comma_Landmine delta \<Rightarrow> Comma_Round_Landmine delta
           | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
        using comma_decisive_endpoint_round_packet[OF admitted]
          packet by simp
      have representative_exact:
          "comma_semantic_b1_graph_eval nodes cid clock =
            Some (comma_semantic_b1_round_output clock ?source)"
      proof (cases move)
        case (Comma_Next successor)
        show ?thesis
        proof (cases "comma_round_crossing target successor")
          case True
          have finite_next:
            "comma_finite_step (clock mod 924) target=Comma_Next successor"
            using finite_move Comma_Next by simp
          obtain delta headroom offset where target_shape:
            "target=Comma_Near 9 delta headroom"
            and successor_shape:
            "successor=Comma_Entry 1 (Suc delta) offset"
            and offset_bound: "offset\<le>90"
            using comma_round_crossing_offset_bound[OF finite_next True]
            by blast
          have target_delta: "delta=0"
            using target_shape target_shift_zero by simp
          have live_edge:
            "comma_semantic_b1_graph_apply nodes cid clock =
              Some (Comma_Semantic_B1_Live_Edge (comma_offset_orbit offset))"
            using packet_action packet Comma_Next True target_shape
              successor_shape target_delta offset_bound
            by (simp add: comma_source_continuation_action_of_packet.simps
              comma_semantic_b1_edge_of_continuation.simps)
          have eval_live:
            "comma_semantic_b1_graph_eval nodes cid clock =
              Some (Comma_Semantic_B1_Live (comma_offset_orbit offset))"
            by (rule comma_semantic_b1_graph_eval_apply_live[OF live_edge])
              (rule comma_offset_orbit_bound)
          show ?thesis
            using eval_live round_equation Comma_Next True successor_shape
              target_delta offset_bound
            by (simp add: comma_semantic_b1_round_output_def
              comma_semantic_b1_of_word.simps comma_sector_base_project.simps
              comma_decade_root_admitted_def)
        next
          case False
          have successor_shift_zero:
            "comma_source_continuation_shift successor=0"
            using packet_shape packet Comma_Next False
            by (simp add: comma_semantic_b1_local_action_shape.simps
              comma_source_continuation_action_of_packet.simps)
          have successor_base:
            "comma_source_continuation_base successor=successor"
            using successor_shift_zero
            by (cases successor) simp_all
          have edge_lookup:
            "comma_semantic_b1_graph_apply nodes cid clock =
              map_option Comma_Semantic_B1_Goto
                (comma_semantic_b1_binding_cid_of bindings successor)"
            using packet_action packet Comma_Next False successor_base
              successor_shift_zero
            by (simp add: comma_source_continuation_action_of_packet.simps
              comma_semantic_b1_edge_of_continuation.simps)
          obtain child where child_key:
            "comma_semantic_b1_binding_cid_of bindings successor=Some child"
            using edge_lookup apply_present
            by (cases "comma_semantic_b1_binding_cid_of bindings successor") auto
          have child_edge:
            "comma_semantic_b1_graph_apply nodes cid clock =
              Some (Comma_Semantic_B1_Goto child)"
            using edge_lookup child_key by simp
          have child_less: "child<cid"
            by (rule comma_semantic_b1_graph_apply_goto_decreases_from_core
              [OF graph binding_cid row child_edge])
          obtain child_binding where child_member: "child_binding\<in>set bindings"
            and child_source:
              "comma_semantic_b1_binding_source child_binding=successor"
            and child_cid:
              "comma_semantic_b1_binding_cid child_binding=child"
            using comma_semantic_b1_binding_cid_of_sound[OF child_key] by blast
          have child_correct:
            "comma_semantic_b1_graph_correct_at bindings nodes child"
            by (rule less.IH[OF child_less])
          have child_eval:
            "comma_semantic_b1_graph_eval nodes child clock =
              Some (comma_semantic_b1_round_output clock successor)"
            using child_correct child_member child_source child_cid
            by (simp add: comma_semantic_b1_graph_correct_at_def)
          have eval_goto:
            "comma_semantic_b1_graph_eval nodes cid clock =
              comma_semantic_b1_graph_eval nodes child clock"
            by (rule comma_semantic_b1_graph_eval_apply_goto
              [OF child_edge child_less])
          show ?thesis using eval_goto child_eval round_equation False Comma_Next
            by (simp add: comma_semantic_b1_round_output_def)
        qed
      next
        case (Comma_Fork a delta)
        have finite_fork:
          "comma_finite_step (clock mod 924) target=Comma_Fork a delta"
          using finite_move Comma_Fork by simp
        have fork_bounds: "2\<le>a \<and> a\<le>9"
          by (rule comma_finite_fork_digit_bounds[OF finite_fork])
        have delta_zero: "delta=0"
          using packet_shape packet Comma_Fork
          by (simp add: comma_semantic_b1_local_action_shape.simps
            comma_source_continuation_action_of_packet.simps)
        have stop_edge:
          "comma_semantic_b1_graph_apply nodes cid clock =
            Some (Comma_Semantic_B1_Stop_Edge (a-2))"
          using packet_action packet Comma_Fork fork_bounds
          by (simp add: comma_source_continuation_action_of_packet.simps
            comma_semantic_b1_edge_of_continuation.simps)
        have eval_stop:
          "comma_semantic_b1_graph_eval nodes cid clock =
            Some (Comma_Semantic_B1_Stop (a-2))"
          by (rule comma_semantic_b1_graph_eval_apply_stop[OF stop_edge])
            (use fork_bounds in arith)
        show ?thesis using eval_stop round_equation Comma_Fork delta_zero fork_bounds
          by (simp add: comma_semantic_b1_round_output_def
            comma_semantic_b1_of_word.simps comma_sector_base_project.simps
            comma_terminal_weight_encode_def)
      next
        case (Comma_Landmine delta)
        have delta_zero: "delta=0"
          using packet_shape packet Comma_Landmine
          by (simp add: comma_semantic_b1_local_action_shape.simps
            comma_source_continuation_action_of_packet.simps)
        have stop_edge:
          "comma_semantic_b1_graph_apply nodes cid clock =
            Some (Comma_Semantic_B1_Stop_Edge 8)"
          using packet_action packet Comma_Landmine
          by (simp add: comma_source_continuation_action_of_packet.simps
            comma_semantic_b1_edge_of_continuation.simps)
        have eval_stop:
          "comma_semantic_b1_graph_eval nodes cid clock =
            Some (Comma_Semantic_B1_Stop 8)"
          by (rule comma_semantic_b1_graph_eval_apply_stop[OF stop_edge]) simp
        show ?thesis using eval_stop round_equation Comma_Landmine delta_zero
          by (simp add: comma_semantic_b1_round_output_def
            comma_semantic_b1_of_word.simps comma_sector_base_project.simps
            comma_terminal_weight_encode_def)
      next
        case Comma_Invalid
        have invalid_edge:
          "comma_semantic_b1_graph_apply nodes cid clock =
            Some Comma_Semantic_B1_Invalid_Edge"
          using packet_action packet Comma_Invalid
          by (simp add: comma_source_continuation_action_of_packet.simps
            comma_semantic_b1_edge_of_continuation.simps)
        have eval_invalid:
          "comma_semantic_b1_graph_eval nodes cid clock =
            Some Comma_Semantic_B1_Invalid"
          by (rule comma_semantic_b1_graph_eval_apply_invalid[OF invalid_edge])
        show ?thesis using eval_invalid round_equation Comma_Invalid
          by (simp add: comma_semantic_b1_round_output_def
            comma_semantic_b1_of_word.simps comma_sector_base_project.simps)
      qed
      show "comma_semantic_b1_graph_eval nodes cid clock =
          Some (comma_semantic_b1_round_output clock
            (comma_semantic_b1_binding_source binding))"
        using representative_exact source_output_transport by simp
    qed
  qed
qed
theorem comma_semantic_b1_graph_eval_refines_endpoint:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
  shows "\<forall>cid. comma_semantic_b1_graph_correct_at bindings nodes cid"
  using comma_semantic_b1_graph_completed_eval_refines_endpoint
    [OF comma_semantic_b1_graph_valid_implies_completed_valid[OF graph]] .
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_graph_eval_refines_endpoint}]; Comma_Proof_Profile.report "B1 graph claim=eval-refines-endpoint checked"\<close>

theorem comma_semantic_b1_graph_completed_root_exact:
  assumes graph: "comma_semantic_b1_graph_completed_valid bindings nodes"
    and clock: "clock<924"
    and root: "root<46"
  obtains binding where
    "binding\<in>set bindings"
    "comma_semantic_b1_binding_source binding =
      Comma_Entry 1 0 (comma_offset_representatives!root)"
    "comma_semantic_b1_graph_eval nodes
      (comma_semantic_b1_binding_cid binding) clock =
        Some (comma_semantic_b1 clock root)"
proof -
  have roots:
    "\<forall>i<46. \<exists>binding\<in>set bindings.
      comma_semantic_b1_binding_source binding =
        Comma_Entry 1 0 (comma_offset_representatives!i)"
    using graph by (simp add: comma_semantic_b1_graph_completed_valid_def)
  obtain binding where binding:
    "binding\<in>set bindings"
    and source:
    "comma_semantic_b1_binding_source binding =
      Comma_Entry 1 0 (comma_offset_representatives!root)"
    using roots root by blast
  let ?cid = "comma_semantic_b1_binding_cid binding"
  have all: "\<forall>cid. comma_semantic_b1_graph_correct_at bindings nodes cid"
    by (rule comma_semantic_b1_graph_completed_eval_refines_endpoint[OF graph])
  have exact:
    "comma_semantic_b1_graph_eval nodes ?cid clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source binding))"
    using all binding by (simp add: comma_semantic_b1_graph_correct_at_def)
  have output_exact:
    "comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source binding) =
      comma_semantic_b1 clock root"
    using source comma_semantic_b1_round_output_root_exact[OF clock root] by simp
  show thesis using that[OF binding source] exact output_exact by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_graph_completed_root_exact}]; Comma_Proof_Profile.report "B1 graph claim=completed-root-exact checked"\<close>

theorem comma_semantic_b1_graph_root_exact:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and clock: "clock<924"
    and root: "root<46"
  obtains binding where
    "binding\<in>set bindings"
    "comma_semantic_b1_binding_source binding =
      Comma_Entry 1 0 (comma_offset_representatives!root)"
    "comma_semantic_b1_graph_eval nodes
      (comma_semantic_b1_binding_cid binding) clock =
        Some (comma_semantic_b1 clock root)"
  using comma_semantic_b1_graph_completed_root_exact
    [OF comma_semantic_b1_graph_valid_implies_completed_valid[OF graph] clock root] .
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_graph_root_exact}]; Comma_Proof_Profile.report "B1 graph claim=root-exact checked"\<close>


ML \<open>
  val checked = @{thms comma_semantic_b1_node_lookup_member
    comma_semantic_b1_node_of_key
    comma_semantic_b1_binding_row_exact
    comma_semantic_b1_graph_edges_are_well_formed
    comma_semantic_b1_graph_apply_exact_local
    comma_semantic_b1_graph_eval_refines_endpoint
    comma_semantic_b1_graph_completed_eval_refines_endpoint
    comma_semantic_b1_graph_completed_root_exact
    comma_semantic_b1_graph_root_exact
    comma_semantic_b1_edge_transport_invariant
    comma_semantic_b1_edge_apply_exact_packet
    comma_semantic_b1_graph_apply_exact_packet};
  val _ = Thm.consolidate checked;
  val _ = Comma_Proof_Profile.report "B1 graph claims consolidated";
  val _ = Comma_Proof_Profile.report "B1 graph audit=native entered";
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic B1 continuation graph" checked;
  val _ = Comma_Proof_Profile.report "B1 graph audit=native checked";
  val _ = Comma_Proof_Profile.report "B1 graph audit=endpoint entered";
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Semantic graph endpoint application"
    ["comma_source_continuation_apply_exact",
      "comma_decisive_endpoint_round_packet",
      "comma_semantic_b1_graph_apply_exact_from_local_row",
      "comma_semantic_b1_graph_apply_goto_decreases_from_core"]
    @{thms comma_semantic_b1_graph_eval_refines_endpoint
      comma_semantic_b1_graph_completed_eval_refines_endpoint
      comma_semantic_b1_graph_completed_root_exact
      comma_semantic_b1_graph_root_exact};
  val _ = Comma_Proof_Profile.report "B1 graph audit=endpoint checked";
  val _ = Comma_Proof_Profile.report "B1 graph audit=packets entered";
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Semantic graph exact source packets"
    ["comma_source_continuation_apply_exact"]
    @{thms comma_semantic_b1_edge_apply_exact_packet
      comma_semantic_b1_graph_apply_exact_packet};
  val _ = Comma_Proof_Profile.report "B1 graph audit=packets checked";
\<close>

end
