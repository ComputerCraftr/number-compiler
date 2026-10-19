theory Double_Reverse_Decimal_Arithmetic
  imports Main
begin

text \<open>The exact square normalizer may remove any decimal zero suffix before
applying T x = 2 * reverse10 x.  The following arithmetic theorem
proves that contraction normalization preserves both the first endpoint and
T-squared endpoint.  It is a numeric law only; it does not certify an SLP
slice, scheduler publication, or global temporal cone.\<close>

function double_reverse_decimal_digits :: "nat \<Rightarrow> nat" where
  "double_reverse_decimal_digits n =
    (if n < 10 then 1 else Suc (double_reverse_decimal_digits (n div 10)))"
  by pat_completeness auto
termination
  by (relation "measure id") auto

function double_reverse_reverse10 :: "nat \<Rightarrow> nat" where
  "double_reverse_reverse10 n =
    (if n < 10 then n else
      n mod 10 * 10 ^ (double_reverse_decimal_digits n - 1) +
        double_reverse_reverse10 (n div 10))"
  by pat_completeness auto
termination
  by (relation "measure id") auto

definition double_reverse_T :: "nat \<Rightarrow> nat" where
  "double_reverse_T n = 2 * double_reverse_reverse10 n"

definition double_reverse_T_run :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_T_run steps source = (double_reverse_T ^^ steps) source"

lemma double_reverse_reverse10_ignores_trailing_zero:
  "double_reverse_reverse10 (10*n) = double_reverse_reverse10 n"
proof (cases n)
  case 0
  then show ?thesis by (simp add: double_reverse_reverse10.simps)
next
  case (Suc m)
  then show ?thesis
    by (simp add: double_reverse_reverse10.simps)
qed

lemma double_reverse_T_ignores_trailing_zero:
  "double_reverse_T (10*n) = double_reverse_T n"
  by (simp add: double_reverse_T_def
      double_reverse_reverse10_ignores_trailing_zero)

lemma double_reverse_T_ignores_zero_suffix:
  "double_reverse_T (n * 10^zeros) = double_reverse_T n"
proof (induction zeros)
  case 0
  then show ?case by simp
next
  case (Suc zeros)
  have factor:
    "n * 10 ^ Suc zeros = 10 * (n * 10 ^ zeros)"
    by (simp add: power_Suc algebra_simps)
  have contraction:
    "double_reverse_T (n * 10 ^ Suc zeros) =
      double_reverse_T (n * 10 ^ zeros)"
    unfolding factor
    by (rule double_reverse_T_ignores_trailing_zero)
  show ?case using contraction Suc.IH by simp
qed

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
    (2 * (double_reverse_reverse10 n mod (2^places))) mod (2^places)"
  unfolding double_reverse_T_def
  by (rule mod_mult_right_eq[symmetric])

lemma double_reverse_T_mod_power_five:
  "double_reverse_T n mod (5^places) =
    (2 * (double_reverse_reverse10 n mod (5^places))) mod (5^places)"
  unfolding double_reverse_T_def
  by (rule mod_mult_right_eq[symmetric])

lemmas double_reverse_decimal_arithmetic_oracle_audit_bundle =
  double_reverse_reverse10_ignores_trailing_zero
  double_reverse_T_ignores_trailing_zero
  double_reverse_T_ignores_zero_suffix
  double_reverse_T2_ignores_zero_suffix
  double_reverse_T_mod_power_two double_reverse_T_mod_power_five

end
