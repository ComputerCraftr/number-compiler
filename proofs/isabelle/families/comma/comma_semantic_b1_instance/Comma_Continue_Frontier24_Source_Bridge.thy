theory Comma_Continue_Frontier24_Source_Bridge
  imports Comma_Semantic_B1.Comma_Direct_Bellman_Projection
    Comma_Semantic_B1.Comma_Direct_Action_MDD
    Comma_Semantic_B1.Comma_Direct_Action_Simulation
    Comma_Semantic_B1.Comma_Parametric_Continue_Constructors
    Comma_Semantic_B1.Comma_Frontier_M204_Checker
    Comma_Semantic_B1.Comma_CRT_MDD_Certificates
    Comma_Semantic_B1.Comma_CRT_MDD_Transport
    Comma_Semantic_B1.Comma_Program_Continue_Guard_Exact
begin

text \<open>The B1 weight is issued by checked direct Bellman projection over
one seeded Store. Physical source roots are separate Future obligations.\<close>

ML_file "semantic_frontier24_parametric_compiler.ML"
ML_file "semantic_frontier24_parametric_runtime.ML"
ML_file "semantic_crt_mdd_point_eval.ML"
ML_file "semantic_direct_entry_arithmetic.ML"
ML_file "semantic_frontier24_mdd_import_certificates.ML"
ML_file "semantic_direct_entry_row_plan.ML"
ML_file "semantic_direct_action_proposal.ML"
ML_file "semantic_phase_selector_proposal.ML"
ML_file "semantic_direct_mdd_proposal.ML"
ML_file "semantic_direct_terminal_proofs.ML"
ML_file "semantic_direct_row_bindings.ML"
ML_file "semantic_direct_entry_bindings.ML"
ML_file "semantic_direct_program_bindings.ML"
ML_file "semantic_phase_selector_replay.ML"
ML_file "semantic_direct_mdd_evaluation.ML"
ML_file "semantic_direct_class_bindings.ML"
ML_file "semantic_direct_bellman_publication.ML"
ML_file "semantic_direct_bellman_terminal_proposal.ML"
ML_file "semantic_direct_bellman_terminal_proofs.ML"
ML_file "semantic_direct_bellman_issuer.ML"
ML_file "semantic_frontier_m204_candidate_data.ML"
ML_file "semantic_direct_candidate_publication.ML"
ML_file "semantic_frontier_m204_weight_owner.ML"
ML_file "semantic_direct_b1_publication.ML"

local_setup \<open>Comma_Direct_B1_Publication.run\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Direct B1 Bellman authority" @{thms comma_frontier_m204_bellman_native}
\<close>

end
