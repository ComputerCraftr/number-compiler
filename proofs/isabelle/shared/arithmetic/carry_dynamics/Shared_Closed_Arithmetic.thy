theory Shared_Closed_Arithmetic
  imports Main
begin

text \<open>Kernel normalization of closed scalar arithmetic uses a bounded
simpset with no family transitions or occurrence observers.\<close>

ML_file "closed_arithmetic.ML"

ML \<open>
  val checked = @{thms if_weak_cong arith_simps arith_special rel_simps Let_def
    One_nat_def Suc_1 Suc_numeral add_num_simps
    diff_nat_numeral nat_numeral_diff_1 nat_numeral nat_0 nat_1 diff_zero
    diff_self_eq_0 diff_0_eq_0 div_0 mod_0 div_by_0 mod_by_0 div_by_1 mod_by_1
    one_div_numeral one_mod_numeral numeral_div_numeral numeral_mod_numeral
    divmod_trivial divmod_cancel divmod_steps divmod_step_def
    fst_conv snd_conv numeral_One case_prod_beta
    euclidean_size_nat_less_eq_iff euclidean_size_int_less_eq_iff
    mod_self mult_1_left mult_1_right of_nat_0 of_nat_1 of_nat_numeral
    zmod_zminus1_eq_if zmod_zminus2_eq_if zmod_numeral_Bit0 zmod_numeral_Bit1
    more_arith_simps};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Closed arithmetic rules depend on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped closed arithmetic rule" else ();
\<close>

end
