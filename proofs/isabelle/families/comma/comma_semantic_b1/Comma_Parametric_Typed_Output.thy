theory Comma_Parametric_Typed_Output
  imports Comma_Parametric_Continue_Closure
begin

lemma comma_frontier24_action_output_linked_goto:
  assumes linked: "comma_frontier24_action_output_linked bundle closure_index closure
      token output_root (Some child_index)"
    and action: "cf24_action_tokens bundle ! token = Comma_Continuation_Goto source delta"
  shows "child_index < closure_index \<and> child_index < length (cf24_closures bundle) \<and>
    output_root = cf24_closure_output_root (cf24_closures bundle ! child_index)"
  using linked action
  by (auto simp: comma_frontier24_action_output_linked_def comma_frontier24_action_output_linked_scalar_def Let_def
    split: option.splits)

lemma comma_frontier24_action_output_linked_exit:
  assumes table:
      "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    and linked: "comma_frontier24_action_output_linked bundle closure_index closure
      token output_root child_ref"
    and action: "cf24_action_tokens bundle ! token = Comma_Continuation_Exit source delta"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase output_root = Some (comma_parametric_exit_continue_code source
        (cf24_closure_full_shift closure + delta))"
proof -
  have bound: "output_root < length (cf24_nodes bundle)"
    using linked unfolding comma_frontier24_action_output_linked_def comma_frontier24_action_output_linked_scalar_def by blast
  have leaf: "cf24_nodes bundle ! output_root = Comma_CRT_MDD_Leaf
      (comma_parametric_exit_continue_code source (cf24_closure_full_shift closure + delta))"
    using linked action by (auto simp: comma_frontier24_action_output_linked_def comma_frontier24_action_output_linked_scalar_def)
  show ?thesis by (rule comma_crt_mdd_eval_phase_leaf[OF table bound leaf])
qed

lemma comma_frontier24_action_output_linked_fork:
  assumes table:
      "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    and linked: "comma_frontier24_action_output_linked bundle closure_index closure
      token output_root child_ref"
    and action: "cf24_action_tokens bundle ! token = Comma_Continuation_Fork digit delta"
    and digit: "2 \<le> digit" "digit \<le> 9"
    and shift: "cf24_closure_full_shift closure + delta = 0"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase output_root = Some (45 + digit)"
proof -
  have bound: "output_root < length (cf24_nodes bundle)"
    using linked unfolding comma_frontier24_action_output_linked_def comma_frontier24_action_output_linked_scalar_def by blast
  have leaf: "cf24_nodes bundle ! output_root = Comma_CRT_MDD_Leaf (45 + digit)"
    using linked action digit shift
    by (auto simp: comma_frontier24_action_output_linked_def comma_frontier24_action_output_linked_scalar_def)
  show ?thesis by (rule comma_crt_mdd_eval_phase_leaf[OF table bound leaf])
qed

lemma comma_frontier24_action_output_linked_landmine:
  assumes table:
      "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    and linked: "comma_frontier24_action_output_linked bundle closure_index closure
      token output_root child_ref"
    and action: "cf24_action_tokens bundle ! token = Comma_Continuation_Landmine delta"
    and shift: "cf24_closure_full_shift closure + delta = 0"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase output_root = Some 55"
proof -
  have bound: "output_root < length (cf24_nodes bundle)"
    using linked unfolding comma_frontier24_action_output_linked_def comma_frontier24_action_output_linked_scalar_def by blast
  have leaf: "cf24_nodes bundle ! output_root = Comma_CRT_MDD_Leaf 55"
    using linked action shift by (simp add: comma_frontier24_action_output_linked_def comma_frontier24_action_output_linked_scalar_def)
  show ?thesis by (rule comma_crt_mdd_eval_phase_leaf[OF table bound leaf])
qed

definition comma_parametric_typed_action_code ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_source_continuation_action \<Rightarrow>
      (comma_semantic_port_program \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "comma_parametric_typed_action_code parent full_shift action child_code =
    (case action of
       Comma_Continuation_Goto source delta \<Rightarrow>
         (case comma_semantic_port_program_of_source source of
            None \<Rightarrow> 0
          | Some child \<Rightarrow>
              if parent < comma_phase_program_sector child \<and>
                 comma_phase_program_sector child \<le> 9
              then child_code child (full_shift + delta) else 0)
     | Comma_Continuation_Exit source delta \<Rightarrow>
         comma_parametric_exit_continue_code source (full_shift + delta)
     | Comma_Continuation_Fork digit delta \<Rightarrow>
         if 2 \<le> digit \<and> digit \<le> 9 \<and> full_shift + delta = 0
         then 45 + digit else 0
     | Comma_Continuation_Landmine delta \<Rightarrow>
         if full_shift + delta = 0 then 55 else 0
     | Comma_Continuation_Invalid \<Rightarrow> 0)"

fun comma_parametric_typed_mask_code :: "comma_phase_rank_mask_action \<Rightarrow> nat" where
  "comma_parametric_typed_mask_code Comma_Phase_Rank_Mask_Invalid = 0"
| "comma_parametric_typed_mask_code (Comma_Phase_Rank_Mask_Continue target) = Suc target"
| "comma_parametric_typed_mask_code (Comma_Phase_Rank_Mask_Fork digit delta) =
    (if 2 \<le> digit \<and> digit \<le> 9 \<and> delta = 0 then 45 + digit else 0)"
| "comma_parametric_typed_mask_code (Comma_Phase_Rank_Mask_Landmine delta) =
    (if delta = 0 then 55 else 0)"

lemma comma_parametric_typed_action_code_full_action:
  assumes goto_bounds:
    "\<And>source delta child. action = Comma_Continuation_Goto source delta \<Longrightarrow>
      comma_semantic_port_program_of_source source = Some child \<Longrightarrow>
      parent < comma_phase_program_sector child \<and> comma_phase_program_sector child \<le> 9"
  shows "comma_parametric_typed_action_code parent shift action
      (\<lambda>child child_shift. comma_parametric_typed_mask_code
        (comma_semantic_phase_program_fold comma_phase_program_full_action_output
          phase child child_shift)) =
    comma_parametric_typed_mask_code
      (comma_phase_program_full_action_of_source_action phase shift action)"
proof -
  have phase_delta:
    "(phase + delta) mod 924 = (phase + 1) mod 924 \<longleftrightarrow> delta mod 924 = 1"
    for delta :: nat
  proof -
    have "[phase+delta=phase+1] (mod 924) \<longleftrightarrow> [delta=1] (mod 924)"
      by (rule cong_add_lcancel_nat)
    then show ?thesis by (simp add: cong_def)
  qed
  have phase_delta_suc:
    "(phase + delta) mod 924 = (Suc phase) mod 924 \<longleftrightarrow>
      delta mod 924 = 1" for delta :: nat
    using phase_delta[of delta] by simp
  show ?thesis
    using goto_bounds phase_delta_suc
    by (cases action)
      (auto simp: comma_parametric_typed_action_code_def
        comma_phase_program_full_action_of_source_action_def
        comma_phase_program_full_action_terminal
        comma_phase_program_full_action_exit_exact
        comma_parametric_exit_continue_code_def phase_delta_suc
        split: option.splits comma_finite_position.splits if_splits)
qed

lemma comma_frontier24_action_output_linked_typed:
  assumes table:
      "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    and linked: "comma_frontier24_action_output_linked bundle closure_index closure
      token output_root child_ref"
    and child_exact:
      "\<And>child_index. child_index < closure_index \<Longrightarrow>
        comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
          (cf24_closure_output_root (cf24_closures bundle ! child_index)) =
        Some (child_code
          (cf24_programs bundle ! cf24_closure_program_ref
            (cf24_closures bundle ! child_index))
          (cf24_closure_full_shift (cf24_closures bundle ! child_index)))"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase output_root = Some (comma_parametric_typed_action_code
        (comma_phase_program_sector
          (cf24_programs bundle ! cf24_closure_program_ref closure))
        (cf24_closure_full_shift closure) (cf24_action_tokens bundle ! token) child_code)"
  using table linked child_exact
  unfolding comma_frontier24_action_output_linked_def comma_frontier24_action_output_linked_scalar_def comma_parametric_typed_action_code_def
  by (cases "cf24_action_tokens bundle ! token")
    (auto simp: Let_def comma_crt_mdd_eval_phase_leaf
      split: option.splits prod.splits)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Source-bound typed continuation output"
    @{thms comma_frontier24_action_output_linked_goto
      comma_frontier24_action_output_linked_exit
      comma_frontier24_action_output_linked_fork
      comma_frontier24_action_output_linked_landmine
      comma_frontier24_action_output_linked_typed
      comma_parametric_typed_action_code_full_action};
\<close>

end
