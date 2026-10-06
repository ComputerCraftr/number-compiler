theory Comma_Fast_Rank_Check
  imports Comma_Fast_Decade_Rank.Comma_Fast_Decade_Rank
    Comma_Fast_Control.Comma_Fast_Kernel
    Comma_Decade_Rank_Data.Comma_Decade_Rank_Data
begin

text \<open>The rank consumer adds only a one-step predicate and a selected
candidate lookup to the shared fast control evaluator. Candidate definitions
never enter its general simplifier: selecting a leaf precedes normalization.
No repeated termination search or weighted occurrence is evaluated here.\<close>

ML_file "fast_rank_check.ML"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_decade_rank_check_correct}) then ()
    else error "Fast rank dependency audit failed";
\<close>
end
