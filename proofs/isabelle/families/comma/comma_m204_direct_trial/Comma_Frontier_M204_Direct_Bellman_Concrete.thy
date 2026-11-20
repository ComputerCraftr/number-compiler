theory Comma_Frontier_M204_Direct_Bellman_Concrete
  imports Comma_Frontier_M204_D_Candidate
    Comma_Semantic_B1.Comma_Direct_Bellman_Projection
    Comma_Semantic_B1.Comma_Direct_Action_MDD
    Comma_Semantic_B1.Comma_Direct_Action_Simulation
    Comma_Semantic_B1.Comma_Parametric_Continue_Constructors
    Comma_Semantic_B1.Comma_CRT_MDD_Transport
    Comma_Semantic_B1.Comma_Program_Continue_Guard_Exact
begin

text \<open>
The producer projects the shared action expressions directly to Bellman values.
The candidate roots and all projected operations share one checked Store.
There is no separate one-step MDD authenticity premise or Frontier24 closure
bundle. Program relations, guards and symbolic root comparisons remain kernel
obligations. Identical authenticated roots share their evaluation theorem;
candidate agreement alone cannot publish a theorem.
\<close>

ML_file "../comma_semantic_b1_instance/semantic_frontier24_parametric_compiler.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_parametric_runtime.ML"
ML_file "../comma_semantic_b1_instance/semantic_crt_mdd_point_eval.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_entry_arithmetic.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_mdd_import_certificates.ML"
ML_file "../comma_semantic_b1/crt_mdd_multiway_replay.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_entry_row_plan.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_action_proposal.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_mdd_proposal.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_terminal_proofs.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_row_bindings.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_entry_bindings.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_program_bindings.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_mdd_evaluation.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_class_bindings.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_bellman_publication.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_bellman_terminal_proposal.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_bellman_terminal_proofs.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_bellman_issuer.ML"

local_setup \<open>Comma_M204_Direct_Candidate_Publication.publish
  Comma_Direct_Bellman_Issuer.prepare Comma_Direct_Bellman_Issuer.certify\<close>

lemma comma_m204_direct_nodes_wellformed:
  "comma_crt_mdd_table_wellformed [3,4,7,11] comma_m204_direct_nodes"
  by (rule comma_m204_direct_nodes_wellformed_native)

lemma comma_m204_direct_roots_bounded:
  "length comma_m204_direct_roots = 46 \<and>
    list_all (\<lambda>r. r < length comma_m204_direct_nodes)
      comma_m204_direct_roots"
  using comma_m204_direct_root_bounds_native
  by (simp add: comma_m204_direct_roots_def)

text \<open>
This concrete release obligation checks the candidate Bellman potential
against the source-independent class action. The symbolic producer above
certifies the guarded action projection and bounded values; it assumes no
separate MDD-to-class-step equality or per-occurrence proof catalogue.
\<close>

lemma comma_m204_direct_concrete_bellman:
  "comma_frontier_m204_bellman comma_m204_direct_D"
  by (rule comma_m204_direct_concrete_bellman_native)

theorem comma_m204_direct_concrete_exact_B32:
  assumes admitted: "comma_decade_admitted source"
  shows "\<exists>h tau. h \<le> 26 \<and>
    comma_decade_block_power 5 source = Comma_Block_Stop h tau \<and>
    comma_residual_block 32 (h,tau) = Comma_Residual_Stop h tau \<and>
    comma_decade_exact_summary source h tau"
  by (rule comma_frontier_m204_B32_from_checked_bellman
    [OF comma_m204_direct_concrete_bellman admitted])

theorem comma_m204_direct_concrete_exact_class:
  assumes phase: "phase < 924" and cid: "cid < 46"
  shows "\<exists>h tau. h \<le> 26 \<and>
    comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives ! cid)) h tau \<and>
    comma_m204_direct_D phase cid = comma_terminal_weight_encode h tau \<and>
    comma_semantic_b1_action_power 5 phase cid =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h tau) \<and>
    comma_terminal_weight_encode h tau \<le> 242"
  by (rule comma_frontier_m204_exact_stop_from_checked_bellman
    [OF comma_m204_direct_concrete_bellman phase cid])

ML \<open>
 val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
   "Concrete quotient-first Bellman / exact B32 (no Frontier24 publisher)"
   @{thms comma_m204_direct_concrete_bellman
     comma_m204_direct_concrete_exact_B32
     comma_m204_direct_concrete_exact_class};
\<close>

end
