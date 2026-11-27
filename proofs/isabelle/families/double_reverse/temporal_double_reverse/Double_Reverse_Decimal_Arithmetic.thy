theory Double_Reverse_Decimal_Arithmetic
  imports Shared_Carry_Dynamics.Shared_Decimal_Cocycle_Core
begin

text \<open>The exact square normalizer may remove any decimal zero suffix before
applying T x = 2 * reverse10 x.  The following arithmetic theorem
proves that contraction normalization preserves both the first endpoint and
T-squared endpoint.  It is a numeric law only; it does not certify an SLP
slice, scheduler publication, or global temporal cone.\<close>

definition double_reverse_T :: "nat \<Rightarrow> nat" where
  "double_reverse_T n = 2 * decimal_reverse n"

definition double_reverse_T_run :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_T_run steps source = (double_reverse_T ^^ steps) source"

theorem double_reverse_T_run_source_root_square:
  "double_reverse_T_run (first + second) source =
    double_reverse_T_run second (double_reverse_T_run first source)"
proof -
  have exponent: "first + second = second + first"
    by (simp add: add.commute)
  show ?thesis
    unfolding double_reverse_T_run_def
    by (simp only: exponent funpow_add comp_apply)
qed

corollary double_reverse_T_run_actual_midpoint_square:
  "double_reverse_T_run (2 * steps) source =
    double_reverse_T_run steps (double_reverse_T_run steps source)"
proof -
  have "2 * steps = steps + steps" by simp
  then show ?thesis by (simp only: double_reverse_T_run_source_root_square)
qed

lemma double_reverse_T_ignores_trailing_zero:
  "double_reverse_T (10*n) = double_reverse_T n"
  by (simp only: double_reverse_T_def decimal_reverse_ignores_trailing_zero)

lemma double_reverse_T_ignores_zero_suffix:
  "double_reverse_T (n * 10^zeros) = double_reverse_T n"
  by (simp only: double_reverse_T_def decimal_reverse_ignores_zero_suffix)

theorem double_reverse_T2_ignores_zero_suffix:
  "double_reverse_T (double_reverse_T (n * 10^zeros)) =
    double_reverse_T (double_reverse_T n)"
  by (simp only: double_reverse_T_ignores_zero_suffix)

text \<open>The source radix projection separates decimal reversal from binary
multiplication. These two residue laws are the 2-adic and 5-adic halves of
the bounded radix-25 observer. They do not replace decimal reversal by bit
reversal or publish temporal branch control.\<close>

lemma double_reverse_T_mod_power_two:
  "double_reverse_T n mod (2^places) =
    (2 * (decimal_reverse n mod (2^places))) mod (2^places)"
  unfolding double_reverse_T_def
  by (rule mod_mult_right_eq[symmetric])

lemma double_reverse_T_mod_power_five:
  "double_reverse_T n mod (5^places) =
    (2 * (decimal_reverse n mod (5^places))) mod (5^places)"
  unfolding double_reverse_T_def
  by (rule mod_mult_right_eq[symmetric])

lemmas double_reverse_decimal_arithmetic_oracle_audit_bundle =
  double_reverse_T_ignores_trailing_zero
  double_reverse_T_ignores_zero_suffix
  double_reverse_T2_ignores_zero_suffix
  double_reverse_T_mod_power_two double_reverse_T_mod_power_five

end
