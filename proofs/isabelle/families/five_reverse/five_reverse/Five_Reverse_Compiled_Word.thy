theory Five_Reverse_Compiled_Word
  imports Five_Reverse_Padded_H_Consumer Shared_Carry_Dynamics.Reflected_Compiled_Word
begin

lemma five_reverse_orbit_funpow:
  "five_reverse_orbit ticks seed = ((\<lambda>x. 5 * decimal_reverse x) ^^ ticks) seed"
  by (induction ticks) (simp_all add: five_reverse_step_def)

theorem five_reverse_compiled_odd:
  assumes "reflected_decimal seed" "reflected_trim_high seed = seed"
  shows "decimal_lsd_value (reflected_emit 5 (reflected_compiled_levels 5 levels (rev seed))) =
    five_reverse_orbit (2 * reflected_dyadic_spans levels + 1) (decimal_lsd_value seed)"
  using reflected_compiled_odd_value[of 5 seed levels] assms
  by (simp add: five_reverse_orbit_funpow)

theorem five_reverse_compiled_even:
  assumes "reflected_decimal seed" "reflected_trim_high seed = seed"
  shows "decimal_lsd_value
      (reflected_emit 5 (reflected_compiled_levels 5 levels (reflected_padded_E 5 seed))) =
    five_reverse_orbit (2 * reflected_dyadic_spans levels + 2) (decimal_lsd_value seed)"
  using reflected_compiled_even_value[of 5 seed levels] assms
  by (simp add: five_reverse_orbit_funpow)

ML \<open>
  val checked = @{thms five_reverse_compiled_odd five_reverse_compiled_even};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Five reverse compiled consumer depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped five reverse compiled consumer proof" else ();
\<close>

end
