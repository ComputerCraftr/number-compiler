theory Comma_Semantic_B1_Instance
  imports Comma_Continue_Image_Instance
begin

text \<open>
The concrete B32 stop bound is consumed from the source-free Continue-image
certificate and its exact B1 output refinement. Graph powering and physical
occurrence weights remain owned by their separate consumers.
\<close>

theorem comma_semantic_b1_action_b32_stop242_checked:
  "\<forall>root<46. \<forall>phase<924. \<exists>D.
    comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof (intro allI impI)
  fix root phase :: nat
  assume root: "root<46" and phase: "phase<924"
  have exact_output:
    "\<exists>height terminal. height\<le>26 \<and>
      comma_decade_exact_summary
        (Comma_Decade phase (comma_offset_representatives!root)) height terminal \<and>
      comma_semantic_b1_action_power 5 phase root =
        Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal) \<and>
      comma_terminal_weight_encode height terminal\<le>242"
    using comma_semantic_phase_class_B32_exact_output_checked root phase by blast
  show "\<exists>D. comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
    using exact_output by blast
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "Source-free Continue-image semantic B32 action"
    ["comma_semantic_phase_class_B32_exact_output_checked",
     "comma_semantic_phase_continue24_image_checked",
     "comma_semantic_phase_continue24_image_certificate_native",
     "comma_continue24_direct_image_implies_image24",
     "comma_continue24_bad_support_exact",
     "comma_no_27_from_continue24_image"]
    @{thms comma_semantic_b1_action_b32_stop242_checked};
\<close>

end
