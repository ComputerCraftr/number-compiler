theory Comma_Decade_Terminal_Data
  imports Comma_Decade_Rank_Data.Comma_Decade_Rank_Data
    Comma_Decade_Residual_Core.Comma_Decade_Residual_Core
begin

text \<open>Untrusted terminal labels paired with the already independent decade
rank candidate.  The labels carry only the terminal kind/fork coefficient;
the checked one-step summary recurrence below is their sole semantic authority.\<close>

ML_file "terminal_candidates.ML"
ML_file "terminal_data_definition.ML"

local_setup \<open>Comma_Decade_Terminal_Data.define\<close>

fun comma_terminal_from_code :: "nat \<Rightarrow> comma_decade_terminal" where
  "comma_terminal_from_code 0 = Comma_Terminal_Landmine"
| "comma_terminal_from_code (Suc n) = Comma_Terminal_Fork (Suc (Suc n))"

lemma comma_terminal_from_code_eval:
  "comma_terminal_from_code n =
    (if n = 0 then Comma_Terminal_Landmine else Comma_Terminal_Fork (Suc n))"
  by (cases n) simp_all

definition comma_decade_terminal_code_candidate :: "comma_decade_state \<Rightarrow> nat" where
  "comma_decade_terminal_code_candidate s = (case s of Comma_Decade r x \<Rightarrow>
    comma_decade_terminal_codes ! (r div 256) ! ((r div 16) mod 16) ! (r mod 16) !
      (x div 16) ! (x mod 16))"

definition comma_decade_terminal_candidate ::
  "comma_decade_state \<Rightarrow> comma_decade_terminal" where
  "comma_decade_terminal_candidate s =
    comma_terminal_from_code (comma_decade_terminal_code_candidate s)"

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_decade_terminal_codes_def comma_decade_terminal_code_candidate_def
      comma_decade_terminal_candidate_def})
    then () else error "Decade terminal candidate definitions depend on an oracle";
\<close>

end
