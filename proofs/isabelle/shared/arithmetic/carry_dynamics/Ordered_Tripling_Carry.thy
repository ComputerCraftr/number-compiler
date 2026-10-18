theory Ordered_Tripling_Carry
  imports Main
begin

text \<open>Random-access physical tripling retains its ordered lower-source
carry. A proved full source period is sufficient for repetition; a histogram
of emitted carries is not a source period.\<close>

definition tripling_source :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "tripling_source modulus phase = 3^phase mod modulus"

lemma tripling_source_step:
  "tripling_source modulus (Suc phase) =
    (3 * tripling_source modulus phase) mod modulus"
  by (simp add: tripling_source_def mod_mult_right_eq)

lemma tripling_source_split:
  "tripling_source modulus (phase + left + right) =
    (tripling_source modulus (phase + left) * 3^right) mod modulus"
  by (simp add: tripling_source_def power_add mod_mult_left_eq)

lemma tripling_source_period:
  assumes "3^period mod modulus = 1"
  shows "tripling_source modulus (phase + period) =
    tripling_source modulus phase"
proof -
  have "(3^phase * 3^period) mod modulus =
      (3^phase * (3^period mod modulus)) mod modulus"
    by (rule mod_mult_right_eq[symmetric])
  then show ?thesis using assms
    by (simp add: tripling_source_def power_add)
qed

lemma tripling_source_repeated_period:
  assumes "3^period mod modulus = 1"
  shows "tripling_source modulus (phase + repeats * period) =
    tripling_source modulus phase"
proof (induction repeats)
  case 0
  then show ?case by simp
next
  case (Suc repeats)
  have "tripling_source modulus (phase + Suc repeats * period) =
      tripling_source modulus (phase + repeats * period + period)"
    by (simp add: algebra_simps)
  also have "... = tripling_source modulus (phase + repeats * period)"
    by (rule tripling_source_period[OF assms])
  finally show ?case using Suc.IH by simp
qed

lemma tripling_quotient_carry:
  fixes source boundary :: nat
  assumes "0 < boundary"
  shows "(3 * source) div boundary =
    3 * (source div boundary) + (3 * (source mod boundary)) div boundary"
proof -
  have split: "3 * source =
      (3 * (source div boundary)) * boundary + 3 * (source mod boundary)"
    using div_mult_mod_eq[of source boundary] by arith
  show ?thesis
    unfolding split using assms by simp
qed

lemma tripling_digit_with_ordered_inlet:
  fixes source boundary radix :: nat
  assumes "0 < boundary"
  shows "((3 * source) div boundary) mod radix =
    (3 * ((source div boundary) mod radix) +
      (3 * (source mod boundary)) div boundary) mod radix"
  using tripling_quotient_carry[OF assms, of source]
  by (metis mod_add_left_eq mod_mult_right_eq)

ML \<open>
  val checked = @{thms tripling_source_step tripling_source_split
    tripling_source_period tripling_source_repeated_period
    tripling_quotient_carry tripling_digit_with_ordered_inlet};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Ordered carry theorem depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped ordered carry proof" else ();
\<close>

end
