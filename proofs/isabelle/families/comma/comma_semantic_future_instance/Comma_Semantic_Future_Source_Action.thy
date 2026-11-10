theory Comma_Semantic_Future_Source_Action
  imports Comma_Semantic_Future_Prefix_Boundary
    Comma_Semantic_Predecessor_Certificate
begin

ML_file "semantic_future_nf_action_publisher.ML"

text \<open>
The source action is a normalized 16-family boundary action with receiving
phase kept as application data.  Its one-round normal form composes the
admitted source action with the exact B32 action.  This theory owns only that
source-action algebra; candidate child IDs and projected keys are downstream.
\<close>

definition comma_semantic_future_family_action_nf_spec ::
    "(nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result) \<Rightarrow>
      (nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result) \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_future_family_action_nf_spec source_round b32_action phase source_cid =
    comma_semantic_b1_weighted_word_then 1 source_round b32_action
      phase source_cid"

definition comma_semantic_future_family_nf_dags ::
    "(nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow>
      (nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow>
      (nat \<times> comma_semantic_b1_crt_dag) list" where
  "comma_semantic_future_family_nf_dags source_actions b32_actions =
    (if length source_actions=16 \<and> length b32_actions=46 then
       map (\<lambda>source_action.
         comma_semantic_b1_crt_compose 1 source_action b32_actions)
         source_actions
     else [])"

definition comma_semantic_future_family_nf_action_at ::
    "(nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow>
      (nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_future_family_nf_action_at source_actions b32_actions
      phase family_slot =
    (if phase<924 \<and> family_slot<16 \<and>
        length source_actions=16 \<and> length b32_actions=46 then
       comma_semantic_b1_crt_action_eval
         (comma_semantic_future_family_nf_dags source_actions b32_actions !
           family_slot) phase
     else Comma_Semantic_B1_Weighted_Invalid)"

definition comma_semantic_future_family_nf_spec_of_dags ::
    "(nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow>
      (nat \<times> comma_semantic_b1_crt_dag) list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_future_family_nf_spec_of_dags source_actions b32_actions
      phase family_slot =
    comma_semantic_b1_weighted_word_then 1
      (\<lambda>p i. comma_semantic_b1_crt_action_eval (source_actions!i) p)
      (\<lambda>p i. comma_semantic_b1_crt_action_eval (b32_actions!i) p)
      phase family_slot"

lemma comma_semantic_future_family_nf_action_at_exact:
  assumes phase: "phase<924"
    and slot: "family_slot<16"
    and source_length: "length source_actions=16"
    and b32_length: "length b32_actions=46"
    and source_wf: "comma_weighted_crt_wellformed
      (snd (source_actions!family_slot))"
    and source_zero: "comma_semantic_b1_crt_action_nonterminal_zero
      (source_actions!family_slot)"
    and b32_wf: "\<And>root. root<46 \<Longrightarrow>
      comma_weighted_crt_wellformed (snd (b32_actions!root))"
    and b32_zero: "\<And>root. root<46 \<Longrightarrow>
      comma_semantic_b1_crt_action_nonterminal_zero (b32_actions!root)"
  shows "comma_semantic_future_family_nf_action_at source_actions b32_actions
      phase family_slot =
    comma_semantic_future_family_nf_spec_of_dags source_actions b32_actions
      phase family_slot"
proof -
  have roots_wf:
      "\<And>root. root<46 \<Longrightarrow>
        comma_weighted_crt_wellformed (snd (b32_actions!root))"
    by (rule b32_wf)
  have roots_zero:
      "\<And>root. root<46 \<Longrightarrow>
        comma_semantic_b1_crt_action_nonterminal_zero (b32_actions!root)"
    by (rule b32_zero)
  have composed:
      "comma_semantic_b1_crt_action_eval
          (comma_semantic_b1_crt_compose 1
            (source_actions!family_slot) b32_actions) phase =
        comma_semantic_b1_weighted_word_then 1
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (source_actions!i) p)
          (\<lambda>p i. comma_semantic_b1_crt_action_eval
            (b32_actions!i) p)
          phase family_slot"
    by (rule comma_semantic_b1_crt_compose_action_eval
      [OF b32_length source_wf roots_wf source_zero roots_zero])
  show ?thesis
    using composed phase slot source_length b32_length
    by (simp add: comma_semantic_future_family_nf_action_at_def
        comma_semantic_future_family_nf_dags_def
        comma_semantic_future_family_nf_spec_of_dags_def)
qed

local_setup \<open>Comma_Semantic_Future_NF_Action_Publisher.publish\<close>

definition comma_semantic_future_initial_nf_dags ::
    "(nat \<times> comma_semantic_b1_crt_dag) list" where
  "comma_semantic_future_initial_nf_dags =
    comma_semantic_graph_initial_nf_actions"

definition comma_semantic_future_initial_nf_action_at ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_weighted_result" where
  "comma_semantic_future_initial_nf_action_at phase family_slot =
    (if phase<924 \<and> family_slot<16 then
       comma_semantic_b1_crt_action_eval
         (comma_semantic_graph_initial_nf_actions!family_slot) phase
     else Comma_Semantic_B1_Weighted_Invalid)"

lemma comma_semantic_future_initial_nf_action_at_exact:
  assumes phase: "phase<924"
    and slot: "family_slot<16"
    and source_length:
      "length comma_semantic_graph_initial_source_actions=16"
    and b32_length:
      "length comma_semantic_future_rank_b32_weighted_actions=46"
    and source_wf: "comma_weighted_crt_wellformed
      (snd (comma_semantic_graph_initial_source_actions!family_slot))"
    and source_zero: "comma_semantic_b1_crt_action_nonterminal_zero
      (comma_semantic_graph_initial_source_actions!family_slot)"
    and b32_wf: "\<And>root. root<46 \<Longrightarrow>
      comma_weighted_crt_wellformed
        (snd (comma_semantic_future_rank_b32_weighted_actions!root))"
    and b32_zero: "\<And>root. root<46 \<Longrightarrow>
      comma_semantic_b1_crt_action_nonterminal_zero
        (comma_semantic_future_rank_b32_weighted_actions!root)"
  shows "comma_semantic_future_initial_nf_action_at phase family_slot =
    comma_semantic_future_family_nf_spec_of_dags
      comma_semantic_graph_initial_source_actions
      comma_semantic_future_rank_b32_weighted_actions phase family_slot"
proof -
  have generic:
    "comma_semantic_future_family_nf_action_at
      comma_semantic_graph_initial_source_actions
      comma_semantic_future_rank_b32_weighted_actions phase family_slot =
     comma_semantic_future_family_nf_spec_of_dags
      comma_semantic_graph_initial_source_actions
      comma_semantic_future_rank_b32_weighted_actions phase family_slot"
    by (rule comma_semantic_future_family_nf_action_at_exact
      [OF phase slot source_length b32_length source_wf source_zero b32_wf b32_zero])
  have index_member: "family_slot \<in> set [0..<16]"
    using slot by simp
  have apply_refinement:
    "comma_weighted_crt_apply
        (comma_semantic_graph_initial_nf_actions!family_slot) phase =
      comma_weighted_crt_apply
        (comma_semantic_b1_crt_compose 1
          (comma_semantic_graph_initial_source_actions!family_slot)
          comma_semantic_future_rank_b32_weighted_actions) phase"
    using comma_semantic_graph_initial_nf_actions_refine index_member
    by (simp add: list_all_iff)
  have evaluation_refinement:
    "comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_nf_actions!family_slot) phase =
      comma_semantic_b1_crt_action_eval
        (comma_semantic_b1_crt_compose 1
          (comma_semantic_graph_initial_source_actions!family_slot)
          comma_semantic_future_rank_b32_weighted_actions) phase"
    using apply_refinement
    by (simp add: comma_semantic_b1_crt_action_eval_def)
  have compiled_is_family:
    "comma_semantic_future_initial_nf_action_at phase family_slot =
      comma_semantic_future_family_nf_action_at
        comma_semantic_graph_initial_source_actions
        comma_semantic_future_rank_b32_weighted_actions phase family_slot"
    using evaluation_refinement phase slot source_length b32_length
    by (simp add: comma_semantic_future_initial_nf_action_at_def
        comma_semantic_future_family_nf_action_at_def
        comma_semantic_future_family_nf_dags_def
        comma_semantic_future_initial_nf_dags_def)
  show ?thesis using compiled_is_family generic by simp
qed

lemma comma_semantic_future_initial_nf_action_eval_exact:
  fixes slot phase :: nat
  assumes slot: "slot<16" and phase: "phase<924"
  shows "comma_semantic_b1_crt_action_eval
      (comma_semantic_future_initial_nf_dags!slot) phase =
    comma_semantic_b1_weighted_word_then 1
      (\<lambda>p i. comma_semantic_b1_crt_action_eval
        (comma_semantic_graph_initial_source_actions!i) p)
      (\<lambda>p i. comma_semantic_b1_crt_action_eval
        (comma_semantic_future_rank_b32_weighted_actions!i) p)
      phase slot"
proof -
  have source_length:
    "length comma_semantic_graph_initial_source_actions=16"
    by (rule comma_semantic_graph_initial_source_actions_length)
  have b32_length:
    "length comma_semantic_future_rank_b32_weighted_actions=46"
    by (rule comma_semantic_future_rank_b32_weighted_actions_length)
  have source_slot_bound:
    "slot<length comma_semantic_graph_initial_source_actions"
    using slot source_length by simp
  have source_member:
    "comma_semantic_graph_initial_source_actions!slot \<in>
      set comma_semantic_graph_initial_source_actions"
    by (rule nth_mem[OF source_slot_bound])
  have source_wf:
    "comma_weighted_crt_wellformed
      (snd (comma_semantic_graph_initial_source_actions!slot))"
    using comma_semantic_graph_initial_source_actions_wellformed source_member
    by (simp add: list_all_iff)
  have source_zero:
    "comma_semantic_b1_crt_action_nonterminal_zero
      (comma_semantic_graph_initial_source_actions!slot)"
    using comma_semantic_graph_initial_source_actions_nonterminal_zero
      source_member by (simp add: list_all_iff)
  have b32_wf:
    "\<And>root. root<46 \<Longrightarrow>
      comma_weighted_crt_wellformed
        (snd (comma_semantic_future_rank_b32_weighted_actions!root))"
    by (rule comma_semantic_future_rank_b32_action_root_wellformed)
  have b32_zero:
    "\<And>root. root<46 \<Longrightarrow>
      comma_semantic_b1_crt_action_nonterminal_zero
        (comma_semantic_future_rank_b32_weighted_actions!root)"
    by (rule comma_semantic_future_rank_b32_action_root_nonterminal_zero)
  have family_spec:
    "comma_semantic_future_initial_nf_action_at phase slot =
      comma_semantic_future_family_nf_spec_of_dags
        comma_semantic_graph_initial_source_actions
        comma_semantic_future_rank_b32_weighted_actions phase slot"
    by (rule comma_semantic_future_initial_nf_action_at_exact
      [OF phase slot source_length b32_length source_wf source_zero b32_wf b32_zero])
  show ?thesis
    using family_spec slot phase
    by (simp add: comma_semantic_future_initial_nf_dags_def
        comma_semantic_future_initial_nf_action_at_def)
qed

ML \<open>
  val published = @{thms
    comma_semantic_future_family_action_nf_spec_def
    comma_semantic_future_family_nf_dags_def
    comma_semantic_future_family_nf_action_at_def
    comma_semantic_future_family_nf_spec_of_dags_def
    comma_semantic_future_initial_nf_dags_def
    comma_semantic_future_initial_nf_action_at_def
    comma_semantic_future_family_nf_action_at_exact
    comma_semantic_future_initial_nf_action_at_exact
    comma_semantic_future_initial_nf_action_eval_exact};
  val _ = Thm.consolidate published;
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Future source action and exact weighted application" published;
\<close>

end
