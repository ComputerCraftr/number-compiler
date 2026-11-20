(* Closed scalar conversions shared by concrete proof publishers. *)
structure Shared_Closed_Arithmetic =
struct
  fun numeral n = HOLogic.mk_number @{typ nat} n
  val numeral_rules = @{thms One_nat_def[symmetric] Suc_1 Suc_numeral add_num_simps}

  fun numeral_context ctxt = put_simpset HOL_basic_ss ctxt
    |> Simplifier.add_simps numeral_rules

  val natural_rules = @{thms arith_simps arith_special rel_simps Let_def
      One_nat_def[symmetric] Suc_1 Suc_numeral
      diff_nat_numeral nat_numeral_diff_1 nat_numeral nat_0 nat_1 diff_zero
      diff_self_eq_0 diff_0_eq_0
      div_0 mod_0 div_by_0 mod_by_0 div_by_1 mod_by_1
      one_div_numeral one_mod_numeral numeral_div_numeral numeral_mod_numeral
      divmod_trivial divmod_cancel divmod_steps divmod_step_def
      fst_conv snd_conv numeral_One case_prod_beta
      euclidean_size_nat_less_eq_iff euclidean_size_int_less_eq_iff
      mod_self mult_1_left mult_1_right}

  fun natural_context ctxt = (put_simpset HOL_ss ctxt
    |> Simplifier.add_cong @{thm if_weak_cong})
    |> Simplifier.add_simps natural_rules

  val signed_scalar_rules = @{thms
    of_nat_0 of_nat_1 of_nat_numeral zmod_zminus1_eq_if zmod_zminus2_eq_if
    zmod_numeral_Bit0 zmod_numeral_Bit1 more_arith_simps}
  fun signed_context ctxt = natural_context ctxt
    |> Simplifier.add_simps signed_scalar_rules
end
