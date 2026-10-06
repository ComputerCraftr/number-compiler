theory Comma_Decade_Rank_Data
  imports Comma_Decade_Totality.Comma_Decade_Control
begin

ML_file "../comma_entry_arithmetic/proof_profile.ML"

text \<open>Untrusted rank candidates from the 2026-09-23 arithmetic audit.
Only the 924 by 91 ranks were copied; successor rows, metadata and claimed
verification flags are not inputs to the checker. The table is ragged at its
exact dimensions and is queried only for admitted states. Typed term
construction and shared blocks are definition syntax, not asserted transition
facts. The checked instance, not this definition, establishes rank decrease.\<close>

ML_file "rank_candidates.ML"
ML_file "candidate_data_definition.ML"
ML_file "rank_data_lookup.ML"

local_setup \<open>fn lthy => Comma_Decade_Candidate_Data.define lthy
  {binding = "comma_decade_rank_codes", max_code = 26,
   rows = comma_decade_candidate_rows, description = "Typed rank data"}\<close>

definition comma_decade_rank_candidate_on_valid :: "comma_decade_state \<Rightarrow> nat" where
  "comma_decade_rank_candidate_on_valid s = (if comma_decade_admitted s then
    (case s of Comma_Decade r x \<Rightarrow>
      comma_decade_rank_codes ! (r div 256) ! ((r div 16) mod 16) ! (r mod 16) !
        (x div 16) ! (x mod 16)) else 0)"


text \<open>The natural-valued adapter above is only an untrusted candidate
for generic rank theorems with an admission premise. Public lookup preserves
invalidity explicitly; an invalid coordinate is not rank zero.\<close>
definition comma_decade_rank_candidate :: "comma_decade_state \<Rightarrow> nat option" where
  "comma_decade_rank_candidate s =
    (if comma_decade_admitted s then Some (comma_decade_rank_candidate_on_valid s)
     else None)"

lemma comma_decade_rank_candidate_valid:
  assumes "comma_decade_admitted s"
  shows "comma_decade_rank_candidate s=Some (comma_decade_rank_candidate_on_valid s)"
  using assms by (simp add: comma_decade_rank_candidate_def)

lemma comma_decade_rank_candidate_invalid:
  assumes "\<not>comma_decade_admitted s"
  shows "comma_decade_rank_candidate s=None"
  using assms by (simp add: comma_decade_rank_candidate_def)

lemma comma_decade_rank_candidate_invalid_boundaries:
  "comma_decade_rank_candidate (Comma_Decade 924 0)=None"
  "comma_decade_rank_candidate (Comma_Decade 0 91)=None"
  by (simp_all add: comma_decade_rank_candidate_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_rank_codes_def comma_decade_rank_candidate_on_valid_def
      comma_decade_rank_candidate_valid comma_decade_rank_candidate_invalid
      comma_decade_rank_candidate_invalid_boundaries})
    then () else error "Decade rank definitions depend on an oracle";
\<close>
end
