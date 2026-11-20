theory Comma_Frontier_M204_D_Candidate
  imports Comma_Semantic_B1.Comma_Frontier_M204_Checker
    Comma_Semantic_B1.Comma_CRT_MDD_Certificates
begin

text \<open>The candidate is untrusted input. The shared Store checks its node
ordering and publishes balanced named chunks; the Bellman theorem remains a
separate kernel obligation.\<close>

ML_file "../comma_semantic_b1_instance/semantic_frontier_m204_candidate_data.ML"

ML_file "../comma_semantic_b1_instance/semantic_direct_candidate_publication.ML"


end
