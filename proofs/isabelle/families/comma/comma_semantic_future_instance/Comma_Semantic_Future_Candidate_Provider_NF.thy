theory Comma_Semantic_Future_Candidate_Provider_NF
  imports Comma_Semantic_Future_Action_Compare
begin

text \<open>
The source normal form carries the complete occurrence displacement on its
root and edges.  A receiver must see that displacement while its phase is
selected; only after binding the receiver may the provider-key projection
discard weights.  This file is the action-level boundary for the checked
candidate/source comparison.
\<close>

fun comma_semantic_future_crt_forget_weights ::
    "'a comma_semantic_weighted_crt_dag \<Rightarrow>
      'a comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_crt_forget_weights (Comma_Weighted_CRT_Leaf value) =
    Comma_Weighted_CRT_Leaf value"
| "comma_semantic_future_crt_forget_weights
      (Comma_Weighted_CRT_Branch axis rows) =
    Comma_Weighted_CRT_Branch axis
      (map (\<lambda>(weight,child).
        (0,comma_semantic_future_crt_forget_weights child)) rows)"

lemma comma_semantic_future_crt_forget_weights_shape:
  "comma_weighted_crt_shape lower
      (comma_semantic_future_crt_forget_weights tree) =
    comma_weighted_crt_shape lower tree"
  by (induction tree arbitrary: lower)
    (auto simp: list_all_iff prod_set_defs)

lemma comma_semantic_future_crt_forget_weights_eval:
  "comma_weighted_crt_eval
      (comma_semantic_future_crt_forget_weights tree) phase =
    map_option (\<lambda>(control,weight). (control,0))
      (comma_weighted_crt_eval tree phase)"
  by (induction tree)
    (auto simp: comma_weighted_crt_eval_branch nth_map
      split: option.splits prod.splits)

lemma comma_semantic_future_crt_forget_weights_apply:
  "comma_weighted_crt_apply (0,
      comma_semantic_future_crt_forget_weights (snd action)) phase =
    map_option (\<lambda>(control,weight). (control,0))
      (comma_weighted_crt_apply action phase)"
  by (cases action)
    (simp add: comma_weighted_crt_apply_def
      comma_semantic_future_crt_forget_weights_eval)

definition comma_semantic_future_crt_forget_action_weights ::
    "nat \<times> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      nat \<times> 'a comma_semantic_weighted_crt_dag" where
  "comma_semantic_future_crt_forget_action_weights action =
    (0,comma_semantic_future_crt_forget_weights (snd action))"

lemma comma_semantic_future_crt_forget_action_weights_apply:
  "comma_weighted_crt_apply
      (comma_semantic_future_crt_forget_action_weights action) phase =
    map_option (\<lambda>(value,weight). (value,0))
      (comma_weighted_crt_apply action phase)"
  by (cases action)
    (simp add: comma_semantic_future_crt_forget_action_weights_def
      comma_semantic_future_crt_forget_weights_apply)

lemma comma_semantic_future_crt_forget_action_weights_shape:
  "comma_weighted_crt_shape lower
      (snd (comma_semantic_future_crt_forget_action_weights action)) =
    comma_weighted_crt_shape lower (snd action)"
  by (cases action)
    (simp add: comma_semantic_future_crt_forget_action_weights_def
      comma_semantic_future_crt_forget_weights_shape)

definition comma_semantic_future_initial_nf_source_key_action ::
    "nat \<Rightarrow> comma_semantic_future_projected_key_action" where
  "comma_semantic_future_initial_nf_source_key_action family_slot =
    (if family_slot<16 \<and>
        length comma_semantic_graph_initial_nf_actions=16 then
       (let source=comma_semantic_future_nf_key_action
            (comma_semantic_graph_initial_nf_actions!family_slot)
        in (comma_semantic_future_crt_forget_action_weights
              (comma_semantic_future_control_projection_action source),
            (comma_semantic_future_crt_forget_action_weights
              (comma_semantic_future_child_projection_action source
                comma_semantic_future_candidate_child_receiver_north),
             comma_semantic_future_crt_forget_action_weights
              (comma_semantic_future_child_projection_action source
                comma_semantic_future_candidate_child_receiver_south)))
     else ((0,Comma_Weighted_CRT_Leaf None),
       ((0,Comma_Weighted_CRT_Leaf 0),(0,Comma_Weighted_CRT_Leaf 0)))"

lemma comma_semantic_future_initial_nf_source_key_action_shape:
  assumes family: "family_slot<16"
  shows "comma_weighted_crt_shape 0
      (snd (fst (comma_semantic_future_initial_nf_source_key_action family_slot))) \<and>
    comma_weighted_crt_shape 0
      (snd (fst (snd (comma_semantic_future_initial_nf_source_key_action family_slot)))) \<and>
    comma_weighted_crt_shape 0
      (snd (snd (snd (comma_semantic_future_initial_nf_source_key_action family_slot))))"
proof -
  have actions_length:
    "length comma_semantic_graph_initial_nf_actions=16"
    by (rule comma_semantic_graph_initial_nf_actions_length)
  have all_shapes:
    "list_all (\<lambda>action. comma_weighted_crt_shape 0 (snd action))
      comma_semantic_graph_initial_nf_actions"
    by (rule comma_semantic_graph_initial_nf_actions_shape)
  have family_bound:
    "family_slot < length comma_semantic_graph_initial_nf_actions"
    using family actions_length by simp
  have selected_mem:
    "comma_semantic_graph_initial_nf_actions!family_slot \<in>
      set comma_semantic_graph_initial_nf_actions"
    by (rule nth_mem[OF family_bound])
  have source_shape:
    "comma_weighted_crt_shape 0
      (snd (comma_semantic_graph_initial_nf_actions!family_slot))"
    using all_shapes selected_mem by (simp add: list_all_iff)
  have mapped_shape:
    "comma_weighted_crt_shape 0
      (snd (comma_semantic_future_nf_key_action
        (comma_semantic_graph_initial_nf_actions!family_slot)))"
    using source_shape by (simp add: comma_semantic_future_nf_key_action_shape)
  have control_shape:
    "comma_weighted_crt_shape 0
      (snd (comma_semantic_future_control_projection_action
        (comma_semantic_future_nf_key_action
          (comma_semantic_graph_initial_nf_actions!family_slot))))"
    using mapped_shape
    by (simp add: comma_semantic_future_control_projection_action_def
      comma_semantic_future_crt_map_action_control_def
      comma_semantic_future_crt_map_control_shape)
  have north_shape:
    "comma_weighted_crt_shape 0
      (snd (comma_semantic_future_child_projection_action
        (comma_semantic_future_nf_key_action
          (comma_semantic_graph_initial_nf_actions!family_slot))
        comma_semantic_future_candidate_child_receiver_north))"
    using mapped_shape comma_semantic_future_candidate_child_receiver_north_shape
    by (simp add: comma_semantic_future_child_projection_action_shape)
  have south_shape:
    "comma_weighted_crt_shape 0
      (snd (comma_semantic_future_child_projection_action
        (comma_semantic_future_nf_key_action
          (comma_semantic_graph_initial_nf_actions!family_slot))
        comma_semantic_future_candidate_child_receiver_south))"
    using mapped_shape comma_semantic_future_candidate_child_receiver_south_shape
    by (simp add: comma_semantic_future_child_projection_action_shape)
  show ?thesis
    using family actions_length control_shape north_shape south_shape
    by (simp add: comma_semantic_future_initial_nf_source_key_action_def Let_def
      comma_semantic_future_crt_forget_action_weights_shape)
qed

lemma comma_semantic_future_initial_nf_source_key_action_apply:
  assumes family: "family_slot<16"
    and phase: "phase<924"
    and source:
      "comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!family_slot) phase =
          Some (Comma_Semantic_B1_CRT_Stop J delta)"
    and terminal: "J<9"
  shows "comma_semantic_future_projected_key_apply
      (comma_semantic_future_initial_nf_source_key_action family_slot) phase =
    Some (Some (comma_semantic_future_control_of_terminal_position J),
      (if J<8 then
        [comma_semantic_future_candidate_class_ids!
          (924*J+((phase+delta) mod 924)),
         comma_semantic_future_candidate_class_ids!
          (924*(8+J)+((phase+delta) mod 924))]
       else []))"
proof -
  have actions_length:
    "length comma_semantic_graph_initial_nf_actions=16"
    by (rule comma_semantic_graph_initial_nf_actions_length)
  have mapped:
    "comma_weighted_crt_apply
      (comma_semantic_future_nf_key_action
        (comma_semantic_graph_initial_nf_actions!family_slot)) phase =
      Some ((Some (comma_semantic_future_control_of_terminal_position J),0),delta)"
    using source terminal
    by (simp add: comma_semantic_future_nf_key_action_apply)
  have source_shape:
    "comma_weighted_crt_shape 0
      (snd (comma_semantic_future_nf_key_action
        (comma_semantic_graph_initial_nf_actions!family_slot)))"
  proof -
    have source_shape:
      "comma_weighted_crt_shape 0
        (snd (comma_semantic_graph_initial_nf_actions!family_slot))"
    proof -
      have all_shapes:
        "list_all (\<lambda>action. comma_weighted_crt_shape 0 (snd action))
          comma_semantic_graph_initial_nf_actions"
        by (rule comma_semantic_graph_initial_nf_actions_shape)
      have family_bound:
        "family_slot < length comma_semantic_graph_initial_nf_actions"
        using family actions_length by simp
      have selected_mem:
        "comma_semantic_graph_initial_nf_actions!family_slot \<in>
          set comma_semantic_graph_initial_nf_actions"
        by (rule nth_mem[OF family_bound])
      show ?thesis using all_shapes selected_mem
        by (simp add: list_all_iff)
    qed
    show ?thesis
      using source_shape
      by (simp add: comma_semantic_future_nf_key_action_shape)
  qed
  have selected_phase: "(phase+delta) mod 924<924" by simp
  have control_projection:
    "comma_weighted_crt_apply
      (comma_semantic_future_control_projection_action
        (comma_semantic_future_nf_key_action
          (comma_semantic_graph_initial_nf_actions!family_slot))) phase =
      Some (Some (comma_semantic_future_control_of_terminal_position J),delta)"
    by (rule comma_semantic_future_control_projection_action_apply[OF mapped])
  let ?phase = "(phase+delta) mod 924"
  let ?north = "if J<8 then comma_semantic_future_candidate_class_ids!
      (924*J+?phase) else 0"
  let ?south = "if J<8 then comma_semantic_future_candidate_class_ids!
      (924*(8+J)+?phase) else 0"
  have north_projection:
    "comma_weighted_crt_apply
      (comma_semantic_future_child_projection_action
        (comma_semantic_future_nf_key_action
          (comma_semantic_graph_initial_nf_actions!family_slot))
        comma_semantic_future_candidate_child_receiver_north) phase =
      Some (?north,delta)"
  proof (cases "J=8")
    case True
    have control:
      "comma_semantic_future_control_of_terminal_position J = Comma_Future_Landmine"
      using True by (simp add: comma_semantic_future_control_of_terminal_position_def)
    have target:
      "comma_weighted_crt_eval
        (comma_semantic_future_candidate_child_receiver_north
          (Some (comma_semantic_future_control_of_terminal_position J)))
        ((phase+0+delta) mod 924) = Some (0,0)"
      using control comma_semantic_future_candidate_child_receiver_north_landmine_placeholder[of
        "(phase+delta) mod 924"] selected_phase by simp
    show ?thesis
      using True by (rule comma_semantic_future_child_projection_action_apply
        [OF phase source_shape comma_semantic_future_candidate_child_receiver_north_shape
          mapped target])
  next
    case False
    have j_small: "J<8" using terminal False by arith
    have target_digit: "2\<le>J+2" "J+2\<le>9" using j_small by arith+
    have control:
      "comma_semantic_future_control_of_terminal_position J = Comma_Future_Fork (J+2)"
      using j_small
      by (simp add: comma_semantic_future_control_of_terminal_position_def)
    have target:
      "comma_weighted_crt_eval
        (comma_semantic_future_candidate_child_receiver_north
          (Some (comma_semantic_future_control_of_terminal_position J)))
        ((phase+0+delta) mod 924) =
        Some (comma_semantic_future_candidate_class_ids!
          (924*J+((phase+delta) mod 924)),0)"
      using comma_semantic_future_candidate_child_receiver_north_fork_exact
        [OF target_digit selected_phase] control by simp
    show ?thesis
      by (rule comma_semantic_future_child_projection_action_apply
        [OF phase source_shape comma_semantic_future_candidate_child_receiver_north_shape
          mapped target])
  qed
  have south_projection:
    "comma_weighted_crt_apply
      (comma_semantic_future_child_projection_action
        (comma_semantic_future_nf_key_action
          (comma_semantic_graph_initial_nf_actions!family_slot))
        comma_semantic_future_candidate_child_receiver_south) phase =
      Some (?south,delta)"
  proof (cases "J=8")
    case True
    have control:
      "comma_semantic_future_control_of_terminal_position J = Comma_Future_Landmine"
      using True by (simp add: comma_semantic_future_control_of_terminal_position_def)
    have target:
      "comma_weighted_crt_eval
        (comma_semantic_future_candidate_child_receiver_south
          (Some (comma_semantic_future_control_of_terminal_position J)))
        ((phase+0+delta) mod 924) = Some (0,0)"
      using control comma_semantic_future_candidate_child_receiver_south_landmine_placeholder[of
        "(phase+delta) mod 924"] selected_phase by simp
    show ?thesis
      using True by (rule comma_semantic_future_child_projection_action_apply
        [OF phase source_shape comma_semantic_future_candidate_child_receiver_south_shape
          mapped target])
  next
    case False
    have j_small: "J<8" using terminal False by arith
    have target_digit: "2\<le>J+2" "J+2\<le>9" using j_small by arith+
    have control:
      "comma_semantic_future_control_of_terminal_position J = Comma_Future_Fork (J+2)"
      using j_small
      by (simp add: comma_semantic_future_control_of_terminal_position_def)
    have target:
      "comma_weighted_crt_eval
        (comma_semantic_future_candidate_child_receiver_south
          (Some (comma_semantic_future_control_of_terminal_position J)))
        ((phase+0+delta) mod 924) =
        Some (comma_semantic_future_candidate_class_ids!
          (924*(8+J)+((phase+delta) mod 924)),0)"
      using comma_semantic_future_candidate_child_receiver_south_fork_exact
        [OF target_digit selected_phase] control by simp
    show ?thesis
      by (rule comma_semantic_future_child_projection_action_apply
        [OF phase source_shape comma_semantic_future_candidate_child_receiver_south_shape
          mapped target])
  qed
  have control_erased:
    "comma_weighted_crt_apply
      (comma_semantic_future_projected_control_action
        (comma_semantic_future_initial_nf_source_key_action family_slot)) phase =
      Some (Some (comma_semantic_future_control_of_terminal_position J),0)"
    using control_projection
    by (simp add: comma_semantic_future_initial_nf_source_key_action_def Let_def
      comma_semantic_future_projected_control_action_def
      comma_semantic_future_crt_forget_action_weights_apply)
  have north_erased:
    "comma_weighted_crt_apply
      (comma_semantic_future_projected_north_action
        (comma_semantic_future_initial_nf_source_key_action family_slot)) phase =
      Some (?north,0)"
    using north_projection
    by (simp add: comma_semantic_future_initial_nf_source_key_action_def Let_def
      comma_semantic_future_projected_north_action_def
      comma_semantic_future_crt_forget_action_weights_apply)
  have south_erased:
    "comma_weighted_crt_apply
      (comma_semantic_future_projected_south_action
        (comma_semantic_future_initial_nf_source_key_action family_slot)) phase =
      Some (?south,0)"
    using south_projection
    by (simp add: comma_semantic_future_initial_nf_source_key_action_def Let_def
      comma_semantic_future_projected_south_action_def
      comma_semantic_future_crt_forget_action_weights_apply)
  show ?thesis
  proof (cases "J=8")
    case True
    have control:
      "comma_semantic_future_control_of_terminal_position J = Comma_Future_Landmine"
      using True by (simp add: comma_semantic_future_control_of_terminal_position_def)
    have projected:
      "comma_semantic_future_projected_key_apply
        (comma_semantic_future_initial_nf_source_key_action family_slot) phase =
        Some (Some Comma_Future_Landmine,[])"
      by (rule comma_semantic_future_projected_key_apply_landmine[OF control_erased])
    show ?thesis using projected control True by simp
  next
    case False
    have j_small: "J<8" using terminal False by arith
    have target_low: "2\<le>J+2" using j_small by arith
    have target_high: "J+2\<le>9" using j_small by arith
    have control:
      "comma_semantic_future_control_of_terminal_position J = Comma_Future_Fork (J+2)"
      using j_small
      by (simp add: comma_semantic_future_control_of_terminal_position_def)
    have children_shape:
      "comma_semantic_future_action_children_shape (Comma_Future_Fork (J+2))
        [?north,?south]"
      by simp
    have projected:
      "comma_semantic_future_projected_key_apply
        (comma_semantic_future_initial_nf_source_key_action family_slot) phase =
        Some (Some (Comma_Future_Fork (J+2)),[?north,?south])"
      by (rule comma_semantic_future_projected_key_apply_exact
        [OF control_erased north_erased south_erased target_low target_high
          children_shape])
    show ?thesis using projected control j_small False
      by (simp add: comma_semantic_future_control_of_terminal_position_def)
  qed
qed

lemma comma_semantic_future_initial_nf_source_key_action_result:
  assumes family: "family_slot<16"
    and phase: "phase<924"
  obtains J delta ordered_children where
    "comma_weighted_crt_apply
      (comma_semantic_graph_initial_nf_actions!family_slot) phase =
        Some (Comma_Semantic_B1_CRT_Stop J delta)"
    "J<9"
    "delta\<le>27"
    "comma_semantic_future_candidate_child_ids_at
      (Some (comma_semantic_future_control_of_terminal_position J))
      ((phase+delta) mod 924) = Some ordered_children"
    "comma_semantic_future_projected_key_apply
      (comma_semantic_future_initial_nf_source_key_action family_slot) phase =
        Some (Some (comma_semantic_future_control_of_terminal_position J),
          ordered_children)"
proof -
  have all_stopped:
    "list_all
      (\<lambda>action. \<forall>phase. \<exists>J delta.
        comma_weighted_crt_apply action phase =
          Some (Comma_Semantic_B1_CRT_Stop J delta) \<and>
        J<9 \<and> delta\<le>27)
      comma_semantic_graph_initial_nf_actions"
    by (rule comma_semantic_graph_initial_nf_actions_stopped)
  have actions_length:
    "length comma_semantic_graph_initial_nf_actions=16"
    by (rule comma_semantic_graph_initial_nf_actions_length)
  have family_bound:
    "family_slot < length comma_semantic_graph_initial_nf_actions"
    using family actions_length by simp
  have selected_mem:
    "comma_semantic_graph_initial_nf_actions!family_slot \<in>
      set comma_semantic_graph_initial_nf_actions"
    by (rule nth_mem[OF family_bound])
  have selected_stopped:
    "\<forall>phase. \<exists>J delta.
      comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!family_slot) phase =
          Some (Comma_Semantic_B1_CRT_Stop J delta) \<and>
      J<9 \<and> delta\<le>27"
    using all_stopped selected_mem by (simp add: list_all_iff)
  obtain J delta where stopped:
      "comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!family_slot) phase =
          Some (Comma_Semantic_B1_CRT_Stop J delta)"
    and terminal: "J<9"
    and displacement: "delta\<le>27"
    using selected_stopped by blast
  let ?control = "comma_semantic_future_control_of_terminal_position J"
  let ?phase = "(phase+delta) mod 924"
  have selected_phase: "?phase<924" by simp
  have children:
    "comma_semantic_future_candidate_child_ids_at (Some ?control) ?phase =
      Some (if J<8 then
        [comma_semantic_future_candidate_class_ids!(924*J+?phase),
         comma_semantic_future_candidate_class_ids!(924*(8+J)+?phase)]
        else [])"
  proof (cases "J<8")
    case True
    have target: "2\<le>J+2" "J+2\<le>9" using True by arith+
    have control: "?control=Comma_Future_Fork (J+2)"
      using True by (simp add: comma_semantic_future_control_of_terminal_position_def)
    have exact:
      "comma_semantic_future_candidate_child_ids_at
        (Some (Comma_Future_Fork (J+2))) ?phase =
        Some [comma_semantic_future_candidate_class_ids!(924*J+?phase),
          comma_semantic_future_candidate_class_ids!(924*(8+J)+?phase)]"
      using comma_semantic_future_candidate_child_ids_fork_exact
        [OF target selected_phase] by simp
    show ?thesis using control exact True by simp
  next
    case False
    have J8: "J=8" using terminal False by arith
    have control: "?control=Comma_Future_Landmine"
      using J8 by (simp add: comma_semantic_future_control_of_terminal_position_def)
    show ?thesis using control J8
      by (simp add: comma_semantic_future_candidate_child_ids_landmine)
  qed
  obtain ordered_children where selected_children:
      "comma_semantic_future_candidate_child_ids_at (Some ?control) ?phase =
        Some ordered_children"
    and exact_children:
      "ordered_children = (if J<8 then
        [comma_semantic_future_candidate_class_ids!(924*J+?phase),
         comma_semantic_future_candidate_class_ids!(924*(8+J)+?phase)]
        else [])"
    using children by blast
  have key:
    "comma_semantic_future_projected_key_apply
      (comma_semantic_future_initial_nf_source_key_action family_slot) phase =
        Some (Some ?control, ordered_children)"
    using comma_semantic_future_initial_nf_source_key_action_apply
      [OF family phase stopped terminal] exact_children
    by simp
  show thesis
    by (rule that[OF stopped terminal displacement selected_children key])
qed

ML_file "semantic_future_candidate_provider_nf.ML"

local_setup \<open>Comma_Semantic_Future_Candidate_Provider_NF.publish\<close>

lemma comma_semantic_future_candidate_parent_source_key_nf:
  assumes family: "family_slot<16"
    and phase: "phase<924"
  shows "comma_semantic_future_projected_key_apply
      (comma_semantic_future_candidate_parent_key_action family_slot) phase =
    comma_semantic_future_projected_key_apply
      (comma_semantic_future_initial_nf_source_key_action family_slot) phase"
proof -
  have member: "family_slot\<in>set [0..<16]" using family by simp
  have parent:
    "\<forall>phase. comma_semantic_future_projected_key_apply
        (comma_semantic_future_candidate_provider_nf_candidate_actions!
          family_slot) phase =
      comma_semantic_future_projected_key_apply
        (comma_semantic_future_candidate_parent_key_action family_slot) phase"
    using comma_semantic_future_candidate_parent_key_nf_all_phases member
    by (simp add: list_all_iff)
  have source:
    "phase<924 \<longrightarrow>
      comma_semantic_future_projected_key_apply
        (comma_semantic_future_candidate_provider_nf_candidate_actions!
          family_slot) phase =
      comma_semantic_future_projected_key_apply
        (comma_semantic_future_initial_nf_source_key_action family_slot) phase"
    using comma_semantic_future_candidate_source_key_nf_all_phases member phase
    by (simp add: list_all_iff)
  show ?thesis using parent source phase by blast
qed

ML \<open>
  val published = @{thms
    comma_semantic_future_candidate_provider_nf_candidate_actions_def
    comma_semantic_future_candidate_provider_nf_source_actions_def
    comma_semantic_future_candidate_provider_nf_actions_equal
    comma_semantic_future_candidate_source_key_nf_all_phases
    comma_semantic_future_candidate_parent_key_nf_all_phases
    comma_semantic_future_candidate_provider_nf_candidate_actions_length
    comma_semantic_future_candidate_provider_nf_source_actions_length
    comma_semantic_future_candidate_provider_nf_candidate_actions_shape
    comma_semantic_future_candidate_provider_nf_source_actions_shape
    comma_semantic_future_candidate_parent_source_key_nf}
  val _ = Thm.consolidate published
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Published future candidate and source NF action vectors"
    published
\<close>

end
