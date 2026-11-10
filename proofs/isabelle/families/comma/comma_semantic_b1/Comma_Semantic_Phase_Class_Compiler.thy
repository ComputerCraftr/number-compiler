theory Comma_Semantic_Phase_Class_Compiler
  imports Comma_Semantic_Port_Program_Congruence
    Comma_Semantic_Phase_Class_Rank_Check
    Comma_Semantic_Phase_Program_Source_Specialization
    Comma_Weighted_CRT_Data
begin

text \<open>
The data constructors below do not issue B1 source authority. Publication
requires both exact source-action refinement and the checked semantic rank
relation. Synthetic construction tests exercise the data boundary only.
\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Candidate source-action and semantic rank contracts"
    @{thms comma_phase_program_action_at_source_round_output
      comma_crt_rank_relations_sound comma_crt_rank_relations_B32};
\<close>

end
