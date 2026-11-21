theory Double_Reverse_Reflected_Physical
  imports Double_Reverse_Four_Port_Numeric_Refinement
    Shared_Carry_Dynamics.Reflected_Physical_Parity
begin

theorem double_reverse_physical_word_one_step:
  assumes "list_all (\<lambda>digit. digit < 10) source"
    "source \<noteq> []" "last source > 0"
  shows "decimal_lsd_value (reflected_physical_word 2 source) =
    double_reverse_T (decimal_lsd_value source)"
  using reflected_physical_word_one_step[OF assms, of 2]
  by (simp only: double_reverse_T_def)

ML \<open>
  val checked = @{thms double_reverse_lsf_value_shared
    reflected_physical_word_one_step double_reverse_physical_word_one_step};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Reflected physical source proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped reflected physical source proof" else ();
\<close>

end
