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

lemma tripling_carry_boolean_borrow:
  fixes r m :: nat
  assumes modulus_positive: "0 < m" and source_remainder: "r < m"
  shows "3 * r div m =
    2 * r div m + (if 3 * r mod m < r then 1 else 0)"
proof -
  let ?q = "2 * r div m"
  let ?s = "2 * r mod m"
  let ?t = "r + ?s"
  have s_bound: "?s < m"
    using modulus_positive by simp
  have double_split: "2 * r = ?q * m + ?s"
    using div_mult_mod_eq[of "2 * r" m] by (simp add: mult.commute)
  have triple_split: "3 * r = ?q * m + ?t"
    using double_split by arith
  have quotient_split: "3 * r div m = ?q + ?t div m"
    unfolding triple_split
    by (rule div_mult_self3) (use modulus_positive in simp)
  have remainder_split: "3 * r mod m = ?t mod m"
    unfolding triple_split by (rule mod_mult_self3)
  have t_bound: "?t < 2 * m"
    using source_remainder s_bound by arith
  have t_quotient_bound: "?t div m < 2"
    using modulus_positive t_bound
    by (simp add: div_less_iff_less_mult mult.commute)
  have t_remainder_bound: "?t mod m < m"
    using modulus_positive by simp
  have t_split: "?t = (?t div m) * m + ?t mod m"
    using div_mult_mod_eq[of ?t m] by (simp add: mult.commute)
  have t_boolean: "?t div m = (if ?t mod m < r then 1 else 0)"
  proof (cases "?t < m")
    case True
    have t_div_zero: "?t div m = 0"
      using True by simp
    have t_mod_self: "?t mod m = ?t"
      using True by simp
    show ?thesis using t_div_zero t_mod_self by (simp; arith)
  next
    case False
    have lower: "m \<le> ?t"
      using False by arith
    have t_div_one: "?t div m = 1"
    proof (cases "?t div m = 0")
      case True
      have "?t = ?t mod m"
        using t_split True by simp
      then show ?thesis
        using lower t_remainder_bound by arith
    next
      case False
      then show ?thesis
        using t_quotient_bound by arith
    qed
    have t_mod_less: "?t mod m < r"
      using t_split s_bound by (simp only: t_div_one mult_1_left; arith)
    show ?thesis using t_div_one t_mod_less by simp
  qed
  show ?thesis
    using quotient_split remainder_split t_boolean by simp
qed

ML \<open>
  val checked = @{thms tripling_source_step tripling_source_split
    tripling_source_period tripling_source_repeated_period
    tripling_quotient_carry tripling_digit_with_ordered_inlet
    tripling_carry_boolean_borrow};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Ordered carry theorem depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped ordered carry proof" else ();
\<close>

end
