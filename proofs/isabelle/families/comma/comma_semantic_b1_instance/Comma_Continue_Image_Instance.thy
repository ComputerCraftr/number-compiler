theory Comma_Continue_Image_Instance
  imports Comma_Continue_Frontier24_Source_Bridge
begin

text \<open>
The concrete source-authenticated MDD frontier certificate supplies the
existing Continue24 image, no-27 result, exact B32 label and Stop-weight
contracts. This consumer does not construct the legacy masked output columns.
\<close>

theorem comma_semantic_phase_continue24_image_checked:
  "\<And>phase cid terminal. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
    comma_phase_class_continue_power
      comma_semantic_phase_program_class_step 24 (phase,cid) = Some terminal \<Longrightarrow>
    terminal\<in>comma_continue24_endpoints"
proof -
  fix phase cid terminal
  assume phase: "phase<924"
    and cid: "cid<46"
    and continued:
      "comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 24 (phase,cid) = Some terminal"
  have certificate: "comma_continue24_direct_image_certificate"
    by (rule comma_semantic_phase_continue24_image_certificate_native)
  show "terminal\<in>comma_continue24_endpoints"
    by (rule comma_continue24_direct_image_implies_image24[OF certificate phase cid continued])
qed

theorem comma_semantic_phase_class_no27_checked:
  "\<forall>phase<924. \<forall>cid<46.
    \<not>comma_phase_class_survives
      comma_semantic_phase_program_class_step 27 phase cid"
proof (intro allI impI)
  fix phase cid
  assume phase: "phase<924" and cid: "cid<46"
  have valid: "comma_semantic_phase_class_valid phase cid"
    using phase cid by (simp add: comma_semantic_phase_class_valid_def)
  show "\<not>comma_phase_class_survives
      comma_semantic_phase_program_class_step 27 phase cid"
    by (rule comma_no_27_from_continue24_image
      [OF comma_semantic_phase_continue24_image_checked valid])
qed

theorem comma_semantic_phase_class_B32_exact_output_checked:
  "\<forall>phase<924. \<forall>cid<46. \<exists>height terminal.
    height\<le>26 \<and>
    comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!cid)) height terminal \<and>
    comma_semantic_b1_action_power 5 phase cid =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal) \<and>
    comma_terminal_weight_encode height terminal\<le>242"
proof (intro allI impI)
  fix phase cid
  assume phase: "phase<924" and cid: "cid<46"
  obtain height terminal where height: "height\<le>26"
    and summary: "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!cid)) height terminal"
    and action: "comma_semantic_b1_action_power 5 phase cid =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    and weight: "comma_terminal_weight_encode height terminal\<le>242"
    by (rule comma_semantic_phase_class_B32_exact_output_if_continue24_image
      [OF comma_semantic_phase_continue24_image_checked phase cid])
  show "\<exists>height terminal. height\<le>26 \<and>
      comma_decade_exact_summary
        (Comma_Decade phase (comma_offset_representatives!cid)) height terminal \<and>
      comma_semantic_b1_action_power 5 phase cid =
        Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal) \<and>
      comma_terminal_weight_encode height terminal\<le>242"
    using height summary action weight by blast
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "Source-free concrete Continue24 image and exact B32 output"
    ["comma_semantic_phase_continue24_image_certificate_native",
     "comma_continue24_image_implies_direct_certificate",
     "comma_continue_frontier_empty_implies_image",
     "comma_continue24_direct_image_implies_image24",
     "comma_continue24_bad_support_exact"]
    @{thms comma_semantic_phase_continue24_image_checked};
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "Continue image no-27 consumer"
    ["comma_semantic_phase_continue24_image_checked",
     "comma_no_27_from_continue24_image"]
    @{thms comma_semantic_phase_class_no27_checked};
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "Continue image exact B32 action and Stop weight"
    ["comma_semantic_phase_continue24_image_checked",
     "comma_B32_if_continue24_image",
     "comma_semantic_b1_action_stop_from_exact_summary"]
    @{thms comma_semantic_phase_class_B32_exact_output_checked};
\<close>

end
