theory Comma_Semantic_Future_Rank_B1_Transport
  imports Comma_Semantic_Future_Weighted_Transport
begin

text \<open>
The phase-class instance publishes named action DAGs for its ranked action
roots.  This adapter changes only its leaf alphabet.  The CRT axes, ordered rows,
incoming phase, and edge weights are preserved by the checked weighted bind.
The source apply and shape rows remain the authority for the mapped roots.
\<close>

fun comma_semantic_future_b1_control_of_rank_action ::
    "comma_phase_rank_mask_action \<Rightarrow> comma_semantic_b1_crt_control" where
  "comma_semantic_future_b1_control_of_rank_action
      Comma_Phase_Rank_Mask_Invalid = Comma_Semantic_B1_CRT_Invalid"
| "comma_semantic_future_b1_control_of_rank_action
      (Comma_Phase_Rank_Mask_Fork a d) =
    (if d=0 \<and> 2\<le>a \<and> a\<le>9
     then Comma_Semantic_B1_CRT_Stop (a-2)
     else Comma_Semantic_B1_CRT_Invalid)"
| "comma_semantic_future_b1_control_of_rank_action
      (Comma_Phase_Rank_Mask_Landmine d) =
    (if d=0 then Comma_Semantic_B1_CRT_Stop 8
     else Comma_Semantic_B1_CRT_Invalid)"
| "comma_semantic_future_b1_control_of_rank_action
      (Comma_Phase_Rank_Mask_Continue root) =
    (if root<46 then Comma_Semantic_B1_CRT_Continue root
     else Comma_Semantic_B1_CRT_Invalid)"

fun comma_semantic_future_weighted_of_b1_result ::
    "comma_semantic_b1_result \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_future_weighted_of_b1_result
      (Comma_Semantic_B1_Live root) = Comma_Semantic_B1_Continue root"
| "comma_semantic_future_weighted_of_b1_result
      (Comma_Semantic_B1_Stop digit) = Comma_Semantic_B1_Stop_At digit 0"
| "comma_semantic_future_weighted_of_b1_result
      Comma_Semantic_B1_Invalid = Comma_Semantic_B1_Weighted_Invalid"

definition comma_semantic_future_rank_action_roots ::
    "(nat \<times> comma_semantic_b1_crt_dag) list" where
  "comma_semantic_future_rank_action_roots =
    map (\<lambda>tree. comma_weighted_crt_bind tree
      (\<lambda>move. (0,comma_semantic_b1_crt_leaf
        (comma_semantic_future_b1_control_of_rank_action move))))
      comma_semantic_phase_class_rank_action_roots"

definition comma_semantic_future_rank_round_action ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_future_rank_round_action phase root =
    (if phase<924 \<and> root<46 then
       comma_semantic_future_weighted_of_b1_result
         (comma_semantic_b1_round_output phase
           (Comma_Entry 1 0 (comma_offset_representatives!root)))
     else comma_semantic_future_weighted_of_b1_result
       (comma_semantic_b1 phase root))"

lemma comma_semantic_future_rank_round_action_encode:
  "comma_semantic_b1_weighted_encode
      (comma_semantic_future_rank_round_action phase root) =
    comma_semantic_b1 phase root"
proof (cases "phase<924 \<and> root<46")
  case True
  then have phase: "phase<924" and root: "root<46" by auto
  have source:
    "comma_semantic_b1_round_output phase
      (Comma_Entry 1 0 (comma_offset_representatives!root)) =
      comma_semantic_b1 phase root"
    by (rule comma_semantic_b1_round_output_root_exact[OF phase root])
  show ?thesis using True source
    by (cases "comma_semantic_b1 phase root")
      (simp_all add: comma_semantic_future_rank_round_action_def)
next
  case False
  then show ?thesis
    by (cases "comma_semantic_b1 phase root")
      (simp_all add: comma_semantic_future_rank_round_action_def)
qed

lemma comma_semantic_future_rank_round_action_admitted:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_b1_weighted_result_admitted
      (comma_semantic_future_rank_round_action phase root)"
proof -
  have valid: "comma_semantic_phase_class_valid phase root"
    using phase root by (simp add: comma_semantic_phase_class_valid_def)
  have not_invalid:
    "comma_semantic_phase_class_step phase root \<noteq>
      Comma_Phase_Class_Invalid"
    by (rule comma_semantic_phase_class_step_not_invalid[OF valid])
  have representative_admitted:
    "comma_decade_admitted
      (Comma_Decade phase (comma_offset_representatives!root))"
    by (rule comma_semantic_phase_class_representative(1)[OF valid])
  have offset: "comma_offset_representatives!root\<le>90"
    using representative_admitted by simp
  have exact:
    "comma_phase_rank_mask_lift phase
        (comma_rank_mask_action_of_b1_result
          (comma_semantic_b1_round_output phase
            (Comma_Entry 1 0 (comma_offset_representatives!root)))) =
      comma_semantic_phase_class_step phase root"
    by (rule comma_semantic_b1_round_output_phase_class_exact[OF phase offset])
  have output_admitted:
    "case comma_semantic_b1_round_output phase
      (Comma_Entry 1 0 (comma_offset_representatives!root)) of
      Comma_Semantic_B1_Live next \<Rightarrow> next<46
    | Comma_Semantic_B1_Stop digit \<Rightarrow> digit<9
    | Comma_Semantic_B1_Invalid \<Rightarrow> False"
  proof (cases "comma_semantic_b1_round_output phase
      (Comma_Entry 1 0 (comma_offset_representatives!root))")
    case (Comma_Semantic_B1_Live next)
    have continued:
      "comma_semantic_phase_class_step phase root =
        Comma_Phase_Class_Continue ((phase+1) mod 924) next"
      using exact Comma_Semantic_B1_Live by simp
    have next_valid:
      "comma_semantic_phase_class_valid ((phase+1) mod 924) next"
      by (rule comma_semantic_phase_class_continue_closed(2)[OF valid continued])
    show ?thesis using Comma_Semantic_B1_Live next_valid
      by (simp add: comma_semantic_phase_class_valid_def)
  next
    case (Comma_Semantic_B1_Stop digit)
    have digit_lt: "digit<9"
    proof (rule ccontr)
      assume neg: "\<not>digit<9"
      have no_small: "\<not>digit<8" using neg by arith
      have no_eight: "digit\<noteq>8" using neg by arith
      have rank_invalid:
        "comma_rank_mask_action_of_b1_result (Comma_Semantic_B1_Stop digit) =
          Comma_Phase_Rank_Mask_Invalid"
        using no_small no_eight by simp
      show False using not_invalid exact Comma_Semantic_B1_Stop rank_invalid
        by simp
    qed
    show ?thesis using Comma_Semantic_B1_Stop digit_lt by simp
  next
    case Comma_Semantic_B1_Invalid
    then show ?thesis using not_invalid exact by simp
  qed
  show ?thesis
    using output_admitted phase root
    by (cases "comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root))")
      (simp_all add: comma_semantic_future_rank_round_action_def
        comma_semantic_future_weighted_of_b1_result.simps
        comma_semantic_b1_weighted_result_admitted.simps)
qed

lemma comma_semantic_future_b1_control_of_rank_action_source_exact:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_future_b1_control_of_rank_action
      (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase
          (Comma_Entry 1 0 (comma_offset_representatives!root)))) =
    fst (comma_semantic_b1_crt_graph_result
      (comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root))))"
proof -
  have admitted:
    "case comma_semantic_b1_round_output phase
      (Comma_Entry 1 0 (comma_offset_representatives!root)) of
      Comma_Semantic_B1_Live next \<Rightarrow> next<46
    | Comma_Semantic_B1_Stop digit \<Rightarrow> digit<9
    | Comma_Semantic_B1_Invalid \<Rightarrow> False"
    using comma_semantic_future_rank_round_action_admitted[OF phase root] phase root
    by (cases "comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root))")
      (simp_all add: comma_semantic_future_rank_round_action_def
      comma_semantic_future_weighted_of_b1_result.simps
      comma_semantic_b1_weighted_result_admitted.simps)
  show ?thesis
    using admitted
    by (cases "comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root))")
      (auto simp: comma_semantic_b1_crt_graph_result.simps
        split: if_splits)
qed

lemma comma_semantic_future_rank_action_bind_shape:
  "comma_weighted_crt_shape lower
      (snd (comma_weighted_crt_bind tree
        (\<lambda>move. (0,comma_semantic_b1_crt_leaf (decode move))))) =
    comma_weighted_crt_shape lower tree"
  by (induction tree arbitrary: lower)
    (simp_all add: comma_weighted_crt_shape.simps list_all_iff)

lemma comma_semantic_future_rank_action_roots_length:
  "length comma_semantic_future_rank_action_roots=46"
  by (simp add: comma_semantic_future_rank_action_roots_def
    comma_semantic_phase_class_rank_action_roots_length)

lemma comma_semantic_future_rank_action_root_shape:
  assumes source_rows:
    "list_all (\<lambda>cid. comma_weighted_crt_shape 0
      (comma_semantic_phase_class_rank_action_roots!cid)) [0..<46]"
    and root: "root<46"
  shows "comma_weighted_crt_shape 0
    (snd (comma_semantic_future_rank_action_roots!root))"
proof -
  have source_shape:
    "comma_weighted_crt_shape 0
      (comma_semantic_phase_class_rank_action_roots!root)"
    using source_rows root by (auto simp: list_all_iff)
  have mapped:
    "comma_semantic_future_rank_action_roots!root =
      comma_weighted_crt_bind
        (comma_semantic_phase_class_rank_action_roots!root)
        (\<lambda>move. (0,comma_semantic_b1_crt_leaf
          (comma_semantic_future_b1_control_of_rank_action move)))"
    using root comma_semantic_phase_class_rank_action_roots_length
    by (simp add: comma_semantic_future_rank_action_roots_def)
  show ?thesis
    using comma_semantic_future_rank_action_bind_shape[of 0
      "comma_semantic_phase_class_rank_action_roots!root"
      comma_semantic_future_b1_control_of_rank_action] source_shape mapped
    by simp
qed

lemma comma_semantic_future_rank_action_roots_wellformed:
  "comma_semantic_b1_crt_roots_wellformed
      comma_semantic_future_rank_action_roots"
proof -
  have length:
    "length comma_semantic_future_rank_action_roots=46"
    by (rule comma_semantic_future_rank_action_roots_length)
  have shapes:
    "\<And>root. root<46 \<Longrightarrow>
      comma_weighted_crt_shape 0
        (snd (comma_semantic_future_rank_action_roots!root))"
    by (rule comma_semantic_future_rank_action_root_shape
      [OF comma_semantic_phase_class_rank_source_shape_rows])
  show ?thesis
    unfolding comma_semantic_b1_crt_roots_wellformed_def
    using length shapes comma_weighted_crt_shape_wellformed by blast
qed

lemma comma_semantic_future_rank_action_root_apply_exact:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_weighted_crt_apply
      (comma_semantic_future_rank_action_roots!root) phase =
    Some (fst (comma_semantic_b1_crt_graph_result
      (comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root)))),0)"
proof -
  let ?output = "comma_semantic_b1_round_output phase
    (Comma_Entry 1 0 (comma_offset_representatives!root))"
  have root_length: "root<length comma_semantic_phase_class_rank_action_roots"
    using root comma_semantic_phase_class_rank_action_roots_length by simp
  have root_map:
    "comma_semantic_future_rank_action_roots!root =
      comma_weighted_crt_bind
        (comma_semantic_phase_class_rank_action_roots!root)
        (\<lambda>move. (0,comma_semantic_b1_crt_leaf
          (comma_semantic_future_b1_control_of_rank_action move)))"
    using root_length
    by (simp add: comma_semantic_future_rank_action_roots_def)
  have member: "root\<in>set [0..<46]" using root by simp
  have source_apply:
    "comma_weighted_crt_apply
      (0,comma_semantic_phase_class_rank_action_roots!root) phase =
      Some (comma_rank_mask_action_of_b1_result ?output,0)"
    using comma_semantic_phase_class_rank_source_apply_rows member phase
    by (auto simp: list_all_iff)
  have source_eval:
    "comma_weighted_crt_eval
      (comma_semantic_phase_class_rank_action_roots!root) phase =
      Some (comma_rank_mask_action_of_b1_result ?output,0)"
    using source_apply
    by (auto simp: comma_weighted_crt_apply_def
      split: option.splits prod.splits)
  have decoded:
    "comma_semantic_future_b1_control_of_rank_action
      (comma_rank_mask_action_of_b1_result ?output) =
      fst (comma_semantic_b1_crt_graph_result ?output)"
    by (rule comma_semantic_future_b1_control_of_rank_action_source_exact
      [OF phase root])
  have leaf_apply:
    "comma_weighted_crt_apply
      (0,comma_semantic_b1_crt_leaf
        (comma_semantic_future_b1_control_of_rank_action
          (comma_rank_mask_action_of_b1_result ?output))) phase =
      Some (fst (comma_semantic_b1_crt_graph_result ?output),0)"
    using decoded comma_semantic_b1_crt_leaf_apply by simp
  have bound_apply:
    "comma_weighted_crt_apply
      (comma_weighted_crt_bind
        (comma_semantic_phase_class_rank_action_roots!root)
        (\<lambda>move. (0,comma_semantic_b1_crt_leaf
          (comma_semantic_future_b1_control_of_rank_action move)))) phase =
      Option.bind
        (comma_weighted_crt_eval
          (comma_semantic_phase_class_rank_action_roots!root) phase)
        (\<lambda>(move,elapsed). map_option
          (\<lambda>(control,more). (control,elapsed+more))
          (comma_weighted_crt_apply
            (0,comma_semantic_b1_crt_leaf
              (comma_semantic_future_b1_control_of_rank_action move)) phase))"
    by (rule comma_weighted_crt_bind_exact)
  show ?thesis
    using root_map source_eval leaf_apply bound_apply
    by simp
qed

lemma comma_semantic_future_rank_action_root_eval_exact:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_b1_crt_action_eval
      (comma_semantic_future_rank_action_roots!root) phase =
    comma_semantic_future_rank_round_action phase root"
proof -
  have apply_exact:
    "comma_weighted_crt_apply
      (comma_semantic_future_rank_action_roots!root) phase =
      Some (fst (comma_semantic_b1_crt_graph_result
        (comma_semantic_b1_round_output phase
          (Comma_Entry 1 0 (comma_offset_representatives!root)))),0)"
    by (rule comma_semantic_future_rank_action_root_apply_exact[OF phase root])
  have admitted:
    "case comma_semantic_b1_round_output phase
      (Comma_Entry 1 0 (comma_offset_representatives!root)) of
      Comma_Semantic_B1_Live next \<Rightarrow> next<46
    | Comma_Semantic_B1_Stop digit \<Rightarrow> digit<9
    | Comma_Semantic_B1_Invalid \<Rightarrow> False"
    using comma_semantic_future_rank_round_action_admitted[OF phase root] phase root
    by (cases "comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root))")
      (simp_all add: comma_semantic_future_rank_round_action_def
      comma_semantic_future_weighted_of_b1_result.simps
      comma_semantic_b1_weighted_result_admitted.simps)
  show ?thesis
    using apply_exact admitted
    by (cases "comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root))")
      (auto simp: comma_semantic_b1_crt_action_eval_def
        comma_semantic_b1_crt_decode.simps comma_semantic_b1_crt_graph_result.simps
        comma_semantic_future_rank_round_action_def
        comma_semantic_future_weighted_of_b1_result.simps)
qed

lemma comma_semantic_future_rank_action_base_admitted:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_b1_weighted_result_admitted
      (comma_semantic_future_rank_round_action phase root)"
  by (rule comma_semantic_future_rank_round_action_admitted[OF phase root])

lemma comma_semantic_future_rank_action_root_exact:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_b1_crt_roots_action
      comma_semantic_future_rank_action_roots phase root =
    comma_semantic_future_rank_round_action phase root"
proof -
  have length: "length comma_semantic_future_rank_action_roots=46"
    by (rule comma_semantic_future_rank_action_roots_length)
  show ?thesis using phase root length
    comma_semantic_future_rank_action_root_eval_exact[OF phase root]
    by (simp add: comma_semantic_b1_crt_roots_action_def)
qed

lemma comma_semantic_future_rank_b32_weighted_actions_wellformed:
  "comma_semantic_b1_crt_roots_wellformed
    (comma_semantic_b1_crt_power 5 comma_semantic_future_rank_action_roots)"
  by (rule comma_semantic_b1_crt_power_wellformed
    [OF comma_semantic_future_rank_action_roots_wellformed])

definition comma_semantic_future_rank_b32_weighted_actions ::
    "(nat \<times> comma_semantic_b1_crt_dag) list" where
  "comma_semantic_future_rank_b32_weighted_actions =
    comma_semantic_b1_crt_power 5 comma_semantic_future_rank_action_roots"

lemma comma_semantic_future_rank_b32_weighted_actions_length:
  "length comma_semantic_future_rank_b32_weighted_actions=46"
  using comma_semantic_future_rank_b32_weighted_actions_wellformed
  by (simp add: comma_semantic_future_rank_b32_weighted_actions_def
    comma_semantic_b1_crt_roots_wellformed_def
    comma_semantic_b1_crt_power_length)

lemma comma_semantic_future_rank_b32_action_root_wellformed:
  assumes root: "root<46"
  shows "comma_weighted_crt_wellformed
    (snd (comma_semantic_future_rank_b32_weighted_actions!root))"
proof -
  have roots: "comma_semantic_b1_crt_roots_wellformed
      comma_semantic_future_rank_b32_weighted_actions"
    by (rule comma_semantic_future_rank_b32_weighted_actions_wellformed
      [unfolded comma_semantic_future_rank_b32_weighted_actions_def])
  have length: "length comma_semantic_future_rank_b32_weighted_actions=46"
    by (rule comma_semantic_future_rank_b32_weighted_actions_length)
  show ?thesis
    using roots root length
    by (auto simp: comma_semantic_b1_crt_roots_wellformed_def)
qed

lemma comma_semantic_future_rank_b32_action_eval_exact:
  assumes root: "root<46" and phase: "phase<924"
  shows "comma_semantic_b1_crt_action_eval
      (comma_semantic_future_rank_b32_weighted_actions!root) phase =
    comma_semantic_b1_weighted_action_power 5
      comma_semantic_future_rank_round_action phase root"
proof -
  have roots_wf:
    "comma_semantic_b1_crt_roots_wellformed
      comma_semantic_future_rank_action_roots"
    by (rule comma_semantic_future_rank_action_roots_wellformed)
  have base_exact:
    "\<And>p i. p<924 \<Longrightarrow> i<46 \<Longrightarrow>
      comma_semantic_b1_crt_roots_action
        comma_semantic_future_rank_action_roots p i =
        comma_semantic_future_rank_round_action p i"
    by (rule comma_semantic_future_rank_action_root_exact)
  have base_admitted:
    "\<And>p i. p<924 \<Longrightarrow> i<46 \<Longrightarrow>
      comma_semantic_b1_weighted_result_admitted
        (comma_semantic_future_rank_round_action p i)"
    by (rule comma_semantic_future_rank_action_base_admitted)
  have powered:
    "comma_semantic_b1_crt_roots_action
        (comma_semantic_b1_crt_power 5
          comma_semantic_future_rank_action_roots) phase root =
      comma_semantic_b1_weighted_action_power 5
        comma_semantic_future_rank_round_action phase root"
    by (rule comma_semantic_b1_crt_power_action_eval
      [OF roots_wf base_exact base_admitted phase root])
  have powered_length:
    "length (comma_semantic_b1_crt_power 5
      comma_semantic_future_rank_action_roots)=46"
    using roots_wf by (simp add: comma_semantic_b1_crt_roots_wellformed_def
      comma_semantic_b1_crt_power_length)
  show ?thesis
    using powered powered_length root
    by (simp add: comma_semantic_future_rank_b32_weighted_actions_def
      comma_semantic_b1_crt_roots_action_def)
qed

lemma comma_semantic_future_rank_b32_action_root_nonterminal_zero:
  assumes root: "root<46"
  shows "comma_semantic_b1_crt_action_nonterminal_zero
    (comma_semantic_future_rank_b32_weighted_actions!root)"
proof -
  have wellformed:
    "comma_weighted_crt_wellformed
      (snd (comma_semantic_future_rank_b32_weighted_actions!root))"
    by (rule comma_semantic_future_rank_b32_action_root_wellformed[OF root])
  have admitted:
    "\<forall>phase<924. comma_semantic_b1_weighted_result_admitted
      (comma_semantic_b1_crt_action_eval
        (comma_semantic_future_rank_b32_weighted_actions!root) phase)"
  proof (intro allI impI)
    fix phase :: nat
    assume phase: "phase<924"
    have exact:
      "comma_semantic_b1_crt_action_eval
        (comma_semantic_future_rank_b32_weighted_actions!root) phase =
       comma_semantic_b1_weighted_action_power 5
        comma_semantic_future_rank_round_action phase root"
      by (rule comma_semantic_future_rank_b32_action_eval_exact[OF root phase])
    have power_admitted:
      "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_weighted_action_power 5
          comma_semantic_future_rank_round_action phase root)"
      by (rule comma_semantic_b1_weighted_action_power_admitted
        [OF comma_semantic_future_rank_action_base_admitted phase root])
    show "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_crt_action_eval
          (comma_semantic_future_rank_b32_weighted_actions!root) phase)"
      using exact power_admitted by simp
  qed
  show ?thesis
    by (rule comma_semantic_b1_crt_action_admitted_zero[OF wellformed admitted])
qed

lemma comma_semantic_future_b1_action_power_from_exact:
  "comma_semantic_b1_action_power_from k
      (\<lambda>p i. comma_semantic_b1 p i) phase root =
    comma_semantic_b1_action_power k phase root"
  by (induction k arbitrary: phase root) simp_all

lemma comma_semantic_future_rank_b32_action_stop_exact:
  assumes phase: "phase<924" and root: "root<46"
  obtains height terminal where
    "height\<le>26"
    "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!root)) height terminal"
    "comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    "comma_semantic_b1_crt_action_eval
      (comma_semantic_future_rank_b32_weighted_actions!root) phase =
      Comma_Semantic_B1_Stop_At (comma_terminal_weight_digit terminal) height"
proof -
  obtain height terminal where height: "height\<le>26"
    and summary: "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!root)) height terminal"
    and b1_power:
      "comma_semantic_b1_action_power 5 phase root =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode height terminal)"
    and encoded_bound: "comma_terminal_weight_encode height terminal\<le>242"
    using comma_semantic_phase_class_B32_exact_output_checked phase root by blast
  have encoded_action:
    "comma_semantic_b1_weighted_encode
      (comma_semantic_b1_weighted_action_power 5
        comma_semantic_future_rank_round_action phase root) =
      comma_semantic_b1_action_power 5 phase root"
  proof -
    have base:
      "(\<lambda>p i. comma_semantic_b1_weighted_encode
          (comma_semantic_future_rank_round_action p i)) =
        (\<lambda>p i. comma_semantic_b1 p i)"
    proof (intro ext)+
      fix p i :: nat
      show "comma_semantic_b1_weighted_encode
          (comma_semantic_future_rank_round_action p i) =
          comma_semantic_b1 p i"
        by (rule comma_semantic_future_rank_round_action_encode)
    qed
    have power_from:
      "comma_semantic_b1_action_power_from 5
          (\<lambda>p i. comma_semantic_b1 p i) phase root =
        comma_semantic_b1_action_power 5 phase root"
      by (rule comma_semantic_future_b1_action_power_from_exact)
    show ?thesis
      using comma_semantic_b1_weighted_action_power_encode[of 5
          comma_semantic_future_rank_round_action phase root]
        base power_from by simp
  qed
  have weighted_result:
    "comma_semantic_b1_weighted_action_power 5
        comma_semantic_future_rank_round_action phase root =
      Comma_Semantic_B1_Stop_At (comma_terminal_weight_digit terminal) height"
  proof -
    have admitted:
      "comma_semantic_b1_weighted_result_admitted
        (comma_semantic_b1_weighted_action_power 5
          comma_semantic_future_rank_round_action phase root)"
      by (rule comma_semantic_b1_weighted_action_power_admitted
        [OF comma_semantic_future_rank_action_base_admitted phase root])
    have terminal_admitted: "comma_terminal_weight_admitted terminal"
      by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
    have terminal_digit: "comma_terminal_weight_digit terminal<9"
      by (rule comma_terminal_weight_digit_bound[OF terminal_admitted])
    show ?thesis
      using admitted encoded_action b1_power terminal_digit
      by (cases "comma_semantic_b1_weighted_action_power 5
          comma_semantic_future_rank_round_action phase root")
        (auto simp: comma_semantic_b1_weighted_result_admitted.simps
          comma_semantic_b1_weighted_encode.simps
          comma_terminal_weight_encode_def; arith)
  qed
  show thesis
    using comma_semantic_future_rank_b32_action_eval_exact[OF root phase]
      b1_power weighted_result height summary by (rule that)
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Future B1 rank-root decoder and B32 action transport"
    @{thms comma_semantic_future_rank_round_action_encode
      comma_semantic_future_rank_round_action_admitted
      comma_semantic_future_b1_control_of_rank_action_source_exact
      comma_semantic_future_rank_action_root_apply_exact
      comma_semantic_future_rank_action_root_eval_exact
      comma_semantic_future_rank_action_roots_wellformed
      comma_semantic_future_rank_b32_action_eval_exact
      comma_semantic_future_rank_b32_action_stop_exact};
\<close>

end
