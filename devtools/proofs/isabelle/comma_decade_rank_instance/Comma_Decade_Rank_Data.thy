theory Comma_Decade_Rank_Data
  imports Comma_Decade_Rank_Check
begin

text \<open>Untrusted rank candidates from the 2026-09-23 arithmetic audit.
Only the 924 by 91 ranks were copied; successor rows, metadata and claimed
verification flags are not inputs to the checker. Padding is outside admission.
Typed term construction avoids re-inferring the numeral type at every table
entry. Shared blocks are definition syntax, not asserted transition facts.
The checked instance, not this definition, establishes rank decrease.\<close>

ML_file "rank_candidates.ML"
ML_file "rank_data_definition.ML"

local_setup \<open>Comma_Decade_Rank_Data.define\<close>

definition comma_decade_rank_candidate :: "comma_decade_state \<Rightarrow> nat" where
  "comma_decade_rank_candidate s = (case s of Comma_Decade r x \<Rightarrow>
    comma_decade_rank_codes ! (r div 256) ! ((r div 16) mod 16) ! (r mod 16) !
      (x div 16) ! (x mod 16))"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_rank_codes_def comma_decade_rank_candidate_def})
    then () else error "Decade rank definitions depend on an oracle";
\<close>
end
