theory Comma_Semantic_Certificate_Smoke
  imports Comma_Semantic_B1.Comma_Semantic_Phase_Action_Program_Certificate
    Comma_Symbolic_Class_Guards
    Comma_Semantic_B1.Comma_Targeted_Continue_Observer_Refinement
    Comma_Targeted_Continue_Observer_Transport
    Comma_Targeted_Continue_Job_Observer
    Comma_Targeted_Continue_Guarded_Observer
begin

text \<open>
Synthetic checks live in this mandatory certificate-smoke target.  They do
not publish source authority and cannot slow generic theorem imports.
\<close>

lemma comma_continue_guard_rejects_other_target:
  "\<not> comma_crt_eval phase
    (comma_weighted_crt_continue_column (8::nat)
      (Comma_Weighted_CRT_Leaf (Comma_Phase_Class_Continue 1 7)))"
  by (simp add: comma_weighted_crt_continue_column_def)

lemma comma_continue_endpoint_observer_preserves_label_and_clock:
  "\<not>comma_crt_eval 299 (comma_continue_bad_endpoint_observer 33 0) \<and>
    comma_crt_eval 299 (comma_continue_bad_endpoint_observer 12 0) \<and>
    comma_crt_eval 299 (comma_continue_bad_endpoint_observer 34 0) \<and>
    \<not>comma_crt_eval 298 (comma_continue_bad_endpoint_observer 33 1) \<and>
    comma_crt_eval 298 (comma_continue_bad_endpoint_observer 33 0) \<and>
    \<not>comma_crt_eval 292 (comma_continue_bad_endpoint_observer 33 7) \<and>
    comma_crt_eval 292 (comma_continue_bad_endpoint_observer 33 0)"
proof -
  have exact:
      "comma_crt_eval phase (comma_continue_bad_endpoint_observer target clock) =
        (((phase+clock) mod 924,target)\<notin>comma_continue24_endpoints)"
    if "phase<924" "target<46" for phase target clock
    using comma_continue_bad_endpoint_observer_matches that
    by (auto simp only: comma_continue_observer_matches_def
        comma_continue_outside_endpoints_def)
  show ?thesis
    using exact[of 299 33 0] exact[of 299 12 0]
      exact[of 299 34 0] exact[of 298 33 1] exact[of 298 33 0]
      exact[of 292 33 7] exact[of 292 33 0]
    by (simp add: comma_continue24_endpoints_def comma_continue24_endpoint_list_def)
qed

lemma comma_continue_internal_seam_is_not_external_clock:
  defines "job \<equiv> Comma_Continue_Action_Job 9
    (Comma_Continuation_Exit (Comma_Entry 1 0 0) 1)"
  shows "comma_crt_supported (comma_phase_continue_compile_job job 0
      (comma_offset_orbit 0)) \<and>
    comma_crt_eval 0 (comma_phase_continue_compile_job job 0
      (comma_offset_orbit 0)) \<and>
    \<not> comma_crt_eval 0 (comma_phase_continue_compile_job job 1
      (comma_offset_orbit 0)) \<and>
    comma_crt_eval 0 (comma_crt_shift 1
      (comma_phase_continue_compile_job job 0 (comma_offset_orbit 0)))"
proof -
  have zero_shift:
      "comma_phase_continue_compile_job job 0 (comma_offset_orbit 0) =
        Comma_CRT_Bool True"
    by (simp add: job_def comma_phase_continue_compile_job.simps(4)
        comma_phase_continue_exit_target_def comma_shift_position.simps
        comma_decade_root_admitted_def comma_offset_orbit_def
        comma_digit_orbit_sum_def)
  have internal_shift:
      "comma_phase_continue_compile_job job 1 (comma_offset_orbit 0) =
        Comma_CRT_Bool False"
    by (simp add: job_def comma_phase_continue_compile_job.simps(4)
        comma_phase_continue_exit_target_def comma_shift_position.simps
        comma_decade_root_admitted_def comma_offset_orbit_def
        comma_digit_orbit_sum_def)
  show ?thesis using zero_shift internal_shift by simp
qed

lemma comma_continue_exit_target_checks_all_guards:
  "comma_offset_orbit (0::nat)<46 \<and>
    comma_offset_orbit 0=0 \<and>
    comma_phase_continue_exit_target 0 (Comma_Entry 1 0 0) 1 \<and>
    \<not> comma_phase_continue_exit_target 0 (Comma_Entry 2 0 0) 1 \<and>
    \<not> comma_phase_continue_exit_target 0 (Comma_Entry 1 0 91) 1 \<and>
    \<not> comma_phase_continue_exit_target 0 (Comma_Entry 1 0 0) 0 \<and>
    \<not> comma_phase_continue_exit_target 1 (Comma_Entry 1 0 0) 1 \<and>
    \<not> comma_phase_continue_exit_target 0 (Comma_Near 1 0 0) 1"
  by (simp add: comma_phase_continue_exit_target_def
      comma_shift_position.simps comma_decade_root_admitted_def
      comma_offset_orbit_def comma_digit_orbit_sum_def)

lemma comma_crt_root_skip_is_only_a_shape_fact:
  "comma_crt_root_skips_level 2 (Comma_CRT_Bool False) \<and>
    \<not> comma_crt_root_skips_level 2 (Comma_CRT_Node 2 []) \<and>
    \<not> comma_crt_root_skips_level 2 (Comma_CRT_Node 1 []) \<and>
    comma_crt_root_skips_level 2 (Comma_CRT_Node 3 []) \<and>
    \<not> comma_crt_admitted 0 (Comma_CRT_Node 3 [])"
  by (simp add: comma_crt_root_skips_level.simps
      comma_crt_admitted.simps comma_crt_period_def)

lemma comma_continue_guard_malformed_shape_counterexample:
  "\<not> comma_weighted_crt_shape 0
      (Comma_Weighted_CRT_Branch 0
        [(0, Comma_Weighted_CRT_Leaf
          (Comma_Phase_Class_Continue 1 (7::nat)))]) \<and>
    comma_crt_eval 0
      (comma_weighted_crt_continue_column 7
        (Comma_Weighted_CRT_Branch 0
          [(0, Comma_Weighted_CRT_Leaf (Comma_Phase_Class_Continue 1 7))]))"
  by (simp add: comma_weighted_crt_continue_column_def
      comma_crt_node_def comma_crt_axis_radix_def)

lemma comma_fused_continue_retains_terminal_seam_and_observer_clock:
  defines "job \<equiv> Comma_Continue_Action_Job 9
    (Comma_Continuation_Exit (Comma_Entry 1 0 0) 1)"
    and "observer \<equiv> (\<lambda>target clock.
      Comma_CRT_Bool (target=comma_offset_orbit 0 \<and> clock=1))"
  shows "comma_continue_job_observe observer job 0 0 = Comma_CRT_Bool True \<and>
    comma_continue_job_observe observer job 1 0 = Comma_CRT_Bool False \<and>
    comma_continue_job_observe observer job 0 1 = Comma_CRT_Bool False"
  by (simp add: job_def observer_def comma_continue_job_observe.simps(4)
      comma_continue_job_exit_observer_def comma_shift_position.simps
      comma_decade_root_admitted_def)

lemma comma_empty_denotation_does_not_authenticate_malformed_column:
  "comma_crt_set (Comma_CRT_Node 0 []) =
      comma_crt_set (Comma_CRT_Bool False) \<and>
    \<not> comma_crt_equiv_check (Comma_CRT_Node 0 []) (Comma_CRT_Bool False) \<and>
    \<not> comma_crt_equiv_check (Comma_CRT_Node 0 []) (Comma_CRT_Node 0 [])"
  by (simp add: comma_crt_equiv_check_iff comma_crt_set_def comma_crt_period_def)

lemma comma_survival_guard_clock_shift_counterexample:
  defines "even_column \<equiv> Comma_CRT_Node 0
    [Comma_CRT_Bool True, Comma_CRT_Bool False,
     Comma_CRT_Bool True, Comma_CRT_Bool False]"
  shows "comma_crt_eval 0 even_column \<and>
    \<not> comma_crt_eval 0
      (comma_crt_apply_shifted Comma_CRT_And 1
        (Comma_CRT_Bool True) even_column)"
proof -
  have admitted: "comma_crt_admitted 0 even_column"
    by (simp add: even_column_def comma_crt_period_def)
  have shifted:
    "comma_crt_eval 0
        (comma_crt_apply_shifted Comma_CRT_And 1
          (Comma_CRT_Bool True) even_column) =
      comma_crt_eval 1 even_column"
    using comma_phase_guard_survival_edge_eval
      [OF _ admitted, where guard="Comma_CRT_Bool True" and phase=0]
    by simp
  show ?thesis using shifted
    by (simp add: even_column_def comma_crt_period_def)
qed

ML_file "semantic_weighted_crt_view_fixture.ML"
ML_file "semantic_weighted_crt_shallow_fixture.ML"
ML_file "semantic_phase_class_rank_joint_fixture.ML"
ML_file "semantic_phase_class_rank_relation_fixture.ML"
ML_file "semantic_phase_class_rank_shift_fixture.ML"
ML_file "../comma_semantic_b1_instance/semantic_continue_column_proofs.ML"
ML_file "../comma_semantic_b1_instance/semantic_continue_observer_contract.ML"
ML_file "../comma_semantic_b1_instance/semantic_continue_masked_columns.ML"
ML_file "../comma_semantic_b1_instance/semantic_continue_application_transport.ML"
ML_file "semantic_continue_apply_memo_fixture.ML"
ML_file "semantic_continue_application_transport_fixture.ML"
ML \<open>
  Comma_Proof_Profile.report "CRT certificate smoke stage=view-start";
  Comma_Weighted_CRT_View_Fixture.run @{context};
  Comma_Proof_Profile.report "CRT certificate smoke stage=view-done";
  Comma_Weighted_CRT_Shallow_Fixture.run @{context};
  Comma_Semantic_Phase_Class_Rank_Joint_Fixture.run @{context};
  Comma_Semantic_Phase_Class_Rank_Relation_Fixture.run @{context};
  Comma_Semantic_Phase_Class_Rank_Shift_Fixture.run @{context};
  Comma_Semantic_Continue_Apply_Memo_Fixture.run @{context};
  Comma_Semantic_Continue_Application_Transport_Fixture.run @{context};
\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Checked shallow weighted CRT constructor and selector laws"
    @{thms comma_weighted_crt_bind.simps comma_weighted_crt_bind_exact
      comma_weighted_crt_eval_selected comma_weighted_crt_selector_aux_exact
      comma_weighted_crt_selector_exact
      comma_fused_continue_retains_terminal_seam_and_observer_clock
      comma_continue_exit_target_checks_all_guards
      comma_crt_root_skip_is_only_a_shape_fact
      comma_empty_denotation_does_not_authenticate_malformed_column
      comma_continue_internal_seam_is_not_external_clock};
\<close>

end
