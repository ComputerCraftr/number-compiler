theory Comma_Decade_Terminal_Data
  imports Comma_Decade_Rank_Data.Comma_Decade_Rank_Data
    Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
begin

text \<open>Untrusted terminal labels paired with the already independent decade
rank candidate.  The labels carry only the terminal kind/fork coefficient;
the checked one-step summary recurrence below is their sole semantic authority.\<close>

ML \<open>Comma_Proof_Profile.report "Terminal data stage=before-candidate-ML"\<close>
ML_file "terminal_candidates.ML"
ML \<open>Comma_Proof_Profile.report "Terminal data stage=after-candidate-ML"\<close>

local_setup \<open>fn lthy =>
  (Comma_Proof_Profile.report "Terminal data stage=local-setup-enter";
   Comma_Decade_Candidate_Data.define lthy
  {binding = "comma_decade_terminal_codes", max_code = 8,
   rows = comma_decade_terminal_candidate_rows, description = "Typed terminal data"})\<close>

fun comma_terminal_from_code :: "nat \<Rightarrow> comma_decade_terminal" where
  "comma_terminal_from_code 0 = Comma_Terminal_Landmine"
| "comma_terminal_from_code (Suc n) = Comma_Terminal_Fork (Suc (Suc n))"

lemma comma_terminal_from_code_eval:
  "comma_terminal_from_code n =
    (if n = 0 then Comma_Terminal_Landmine else Comma_Terminal_Fork (Suc n))"
  by (cases n) simp_all

definition comma_decade_terminal_code_candidate_on_valid :: "comma_decade_state \<Rightarrow> nat" where
  "comma_decade_terminal_code_candidate_on_valid s = (if comma_decade_admitted s then
    (case s of Comma_Decade r x \<Rightarrow>
      comma_decade_terminal_codes ! (r div 256) ! ((r div 16) mod 16) ! (r mod 16) !
        (x div 16) ! (x mod 16)) else 0)"

definition comma_decade_terminal_candidate_on_valid ::
  "comma_decade_state \<Rightarrow> comma_decade_terminal" where
  "comma_decade_terminal_candidate_on_valid s =
    comma_terminal_from_code (comma_decade_terminal_code_candidate_on_valid s)"


text \<open>The total adapters serve admitted-state rank/summary theorems only.
Public code and terminal lookups retain None for invalid coordinates, rather
than decoding an invalid state as the legitimate Landmine terminal.\<close>
definition comma_decade_terminal_code_candidate :: "comma_decade_state \<Rightarrow> nat option" where
  "comma_decade_terminal_code_candidate s =
    (if comma_decade_admitted s then Some (comma_decade_terminal_code_candidate_on_valid s)
     else None)"

definition comma_decade_terminal_candidate ::
  "comma_decade_state \<Rightarrow> comma_decade_terminal option" where
  "comma_decade_terminal_candidate s =
    map_option comma_terminal_from_code (comma_decade_terminal_code_candidate s)"

lemma comma_decade_terminal_candidate_valid:
  assumes "comma_decade_admitted s"
  shows "comma_decade_terminal_code_candidate s=Some (comma_decade_terminal_code_candidate_on_valid s)"
    "comma_decade_terminal_candidate s=Some (comma_decade_terminal_candidate_on_valid s)"
  using assms by (simp_all only: comma_decade_terminal_code_candidate_def
      comma_decade_terminal_candidate_def comma_decade_terminal_candidate_on_valid_def
      if_True option.map)

lemma comma_decade_terminal_candidate_invalid:
  assumes "\<not>comma_decade_admitted s"
  shows "comma_decade_terminal_code_candidate s=None"
    "comma_decade_terminal_candidate s=None"
  using assms by (simp_all only: comma_decade_terminal_code_candidate_def
      comma_decade_terminal_candidate_def if_False option.map)

lemma comma_decade_terminal_candidate_invalid_boundaries:
  "comma_decade_terminal_candidate (Comma_Decade 924 0)=None"
  "comma_decade_terminal_candidate (Comma_Decade 0 91)=None"
  by (simp_all add: comma_decade_terminal_candidate_def
      comma_decade_terminal_code_candidate_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_terminal_codes_def comma_decade_terminal_code_candidate_on_valid_def
      comma_decade_terminal_candidate_on_valid_def
      comma_decade_terminal_candidate_valid comma_decade_terminal_candidate_invalid
      comma_decade_terminal_candidate_invalid_boundaries})
    then () else error "Decade terminal candidate definitions depend on an oracle";
\<close>

end
