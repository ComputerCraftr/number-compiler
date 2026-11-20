theory Comma_Continue_Image_Instance
  imports Comma_Continue_Frontier24_Source_Bridge
begin

text \<open>
The authenticated M204 Bellman action supplies an exact B32 Stop summary.
It does not assert the stronger legacy Continue24 endpoint-set certificate;
future consumers requiring that separate statement remain gated.
\<close>

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
  show "\<exists>height terminal. height\<le>26 \<and>
      comma_decade_exact_summary
        (Comma_Decade phase (comma_offset_representatives!cid)) height terminal \<and>
      comma_semantic_b1_action_power 5 phase cid =
        Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal) \<and>
      comma_terminal_weight_encode height terminal\<le>242"
    using comma_frontier_m204_exact_stop_from_checked_bellman
      [OF comma_frontier_m204_bellman_native phase cid] by blast
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "Source-bound M204 exact B32 Stop"
    ["comma_frontier_m204_bellman_native",
     "comma_frontier_m204_exact_stop_from_checked_bellman"]
    @{thms comma_semantic_phase_class_B32_exact_output_checked};
\<close>

end
