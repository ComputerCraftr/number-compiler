theory Comma_Semantic_Phase_Class_Instance
  imports Comma_Semantic_B1.Comma_Semantic_Phase_Action_Program_Certificate
begin

text \<open>
The concrete instance joins exact source-root outputs with the independent
rank sidecar.  The root vector is an ordered list of 46 checked actions; a
constructor cannot claim this theorem from its ML data alone.
The source-root certificate retains the full weighted apply result. Its
zero local weight is proved during the same node induction; the rank consumer
projects only the label. Physical writer weights remain a separate refinement.
\<close>

lemma comma_phase_class_exact_from_root_output:
  assumes phase: "phase<924" and cid: "cid<46"
    and source_output: "comma_crt_payload (actions!cid) phase =
      Some (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase
          (Comma_Entry 1 0 (comma_offset_representatives!cid))))"
  shows "\<exists>move. comma_crt_payload (actions!cid) phase=Some move \<and>
    comma_phase_rank_mask_lift phase move =
      comma_semantic_phase_class_step phase cid"
proof -
  have valid: "comma_semantic_phase_class_valid phase cid"
    using phase cid by (simp add: comma_semantic_phase_class_valid_def)
  have offset: "comma_offset_representatives!cid\<le>90"
    using comma_semantic_phase_class_representative(1)[OF valid] by simp
  have orbit: "comma_offset_orbit (comma_offset_representatives!cid)=cid"
    by (rule comma_semantic_phase_class_representative(2)[OF valid])
  have action: "comma_phase_rank_mask_lift phase
      (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase
          (Comma_Entry 1 0 (comma_offset_representatives!cid)))) =
      comma_semantic_phase_class_step phase cid"
    using comma_semantic_b1_round_output_phase_class_exact
      [OF phase offset] orbit by simp
  show ?thesis using source_output action by blast
qed

lemma comma_phase_class_exact_from_root_apply_rows:
  assumes rows: "list_all (\<lambda>cid. \<forall>phase<924.
      comma_weighted_crt_apply (0,actions!cid) phase =
        Some (comma_rank_mask_action_of_b1_result
          (comma_semantic_b1_round_output phase
            (Comma_Entry 1 0 (comma_offset_representatives!cid))),0))
      [0..<46]"
    and phase: "phase<924" and cid: "cid<46"
  shows "\<exists>move. comma_crt_payload (actions!cid) phase=Some move \<and>
    comma_phase_rank_mask_lift phase move =
      comma_semantic_phase_class_step phase cid"
proof -
  have member: "cid\<in>set [0..<46]" using cid by simp
  have source_apply: "comma_weighted_crt_apply (0,actions!cid) phase =
      Some (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase
          (Comma_Entry 1 0 (comma_offset_representatives!cid))),0)"
    using rows member phase by (auto simp: list_all_iff)
  have projected: "map_option fst
      (comma_weighted_crt_apply (0,actions!cid) phase) =
      map_option fst (Some (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase
          (Comma_Entry 1 0 (comma_offset_representatives!cid))),0::nat))"
    by (simp only: source_apply)
  have source_output: "comma_crt_payload (actions!cid) phase =
      Some (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase
          (Comma_Entry 1 0 (comma_offset_representatives!cid))))"
    using projected
    by (simp only: comma_weighted_crt_apply_payload_projection
      snd_conv option.map fst_conv)
  show ?thesis by (rule comma_phase_class_exact_from_root_output
    [OF phase cid source_output])
qed

lemma comma_phase_class_relation_from_root_rows:
  assumes rows: "list_all (\<lambda>cid. \<forall>phase.
      comma_crt_rank_relation (actions!cid) (ranks!cid)
        (\<lambda>child. if child<46 then
          Some (comma_weighted_crt_shift 1 (ranks!child)) else None) phase)
      [0..<46]"
    and cid: "cid<46"
  shows "comma_crt_rank_relation (actions!cid) (ranks!cid)
    (\<lambda>child. if child<46 then
      Some (comma_weighted_crt_shift 1 (ranks!child)) else None) phase"
  using rows cid by (auto simp: list_all_iff)

lemma comma_phase_class_rank_shape_from_root_rows:
  assumes rows: "list_all (\<lambda>cid.
      comma_weighted_crt_shape 0 (ranks!cid)) [0..<46]"
    and cid: "cid<46"
  shows "comma_weighted_crt_shape 0 (ranks!cid)"
  using rows cid by (auto simp: list_all_iff)

ML_file "../comma_semantic_future_instance/semantic_phase_action_program_compiler.ML"
ML_file "../comma_semantic_future_instance/semantic_phase_action_program_compiler_make.ML"
ML_file "../comma_semantic_future_instance/semantic_phase_action_clock_refinement.ML"
ML_file "../comma_semantic_future_instance/semantic_phase_action_program_certificate.ML"
ML_file "../comma_semantic_future_instance/semantic_phase_action_state_certificate.ML"
ML_file "../comma_semantic_future_instance/semantic_phase_class_compiler_fixture.ML"
ML_file "../comma_semantic_future_instance/semantic_phase_class_rank_publication_fixture.ML"

local_setup \<open>Comma_Semantic_Phase_Class_Rank_Publication_Fixture.run\<close>

ML \<open>Comma_Semantic_Phase_Class_Compiler_Fixture.run @{context}\<close>

ML_file "semantic_phase_class_rank_instance.ML"

local_setup \<open>Comma_Semantic_Phase_Class_Rank_Instance.make\<close>

theorem comma_semantic_phase_class_B32_instance:
  assumes phase: "phase<924" and cid: "cid<46"
  obtains height terminal where
    "height\<le>26"
    "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!cid)) height terminal"
    "comma_semantic_b1_action_power 5 phase cid =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    "comma_terminal_weight_encode height terminal\<le>242"
  using comma_semantic_phase_class_B32_exact_output
    [OF comma_semantic_phase_class_rank_check_instance
        comma_semantic_phase_class_rank_bound_instance[rule_format]
        phase cid]
  by (rule that)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Comma concrete phase-class rank and B32 instance"
    @{thms comma_semantic_phase_class_rank_check_instance
      comma_semantic_phase_class_rank_bound_instance
      comma_semantic_phase_class_rank_action_roots_def
      comma_semantic_phase_class_rank_action_roots_length
      comma_semantic_phase_class_rank_source_apply_rows
      comma_semantic_phase_class_rank_source_shape_rows
      comma_semantic_phase_class_B32_instance};
\<close>

end
