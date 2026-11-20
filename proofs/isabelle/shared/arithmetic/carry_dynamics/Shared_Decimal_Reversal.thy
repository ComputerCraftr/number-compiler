theory Shared_Decimal_Reversal
  imports Shared_Decimal_Cocycle_Core Shared_Closed_Arithmetic
begin

text \<open>Bounded decimal reversal transitions are shared arithmetic laws.
The semantic digit equations stay in the core; this theory supplies a
three-digit proof-side evaluator for consumers that can use its grouped
source steps without changing the public recurrence.\<close>

text \<open>A proof-side evaluator groups three adjacent decimal digits into one
base-1000 transition.  The semantic decimal reversal and its existing code
equation remain unchanged until family consumers validate this alternative.
The low block is reduced once before its three bounded digit reads.\<close>

definition decimal_reverse_block3 :: "nat \<Rightarrow> nat" where
  "decimal_reverse_block3 low =
    (low mod 10) * 100 + ((low div 10) mod 10) * 10 +
      ((low div 100) mod 10)"

lemma decimal_reverse_block3_digits:
  "decimal_reverse_block3 (n mod 1000) =
    (n mod 10) * 100 + ((n div 10) mod 10) * 10 +
      ((n div 100) mod 10)"
proof -
  have low_digit: "(n mod 1000) mod 10 = n mod 10"
    by (rule mod_mod_cancel) simp
  have quotient_tens:
    "n div 10 = (n mod 1000) div 10 + n div 1000 * 100"
  proof -
    have split: "n = n mod 1000 + (n div 1000 * 100) * 10"
      using div_mult_mod_eq[of n 1000]
      by (simp add: algebra_simps)
    have divided: "n div 10 =
        (n mod 1000 + (n div 1000 * 100) * 10) div 10"
      by (rule arg_cong[OF split, where f="\<lambda>value. value div 10"])
    have quotient:
      "n div 10 = n div 1000 * 100 + (n mod 1000) div 10"
      by (simp only: divided div_mult_self1)
    show ?thesis using quotient by (simp add: add.commute)
  qed
  have quotient_hundreds:
    "n div 100 = (n mod 1000) div 100 + n div 1000 * 10"
  proof -
    have split: "n = n mod 1000 + (n div 1000 * 10) * 100"
      using div_mult_mod_eq[of n 1000]
      by (simp add: algebra_simps)
    have divided: "n div 100 =
        (n mod 1000 + (n div 1000 * 10) * 100) div 100"
      by (rule arg_cong[OF split, where f="\<lambda>value. value div 100"])
    have quotient:
      "n div 100 = n div 1000 * 10 + (n mod 1000) div 100"
      by (simp only: divided div_mult_self1)
    show ?thesis using quotient by (simp add: add.commute)
  qed
  have tens_multiple: "n div 1000 * 100 = (n div 1000 * 10) * 10"
    by (simp add: mult.assoc)
  have tens_digit: "((n mod 1000) div 10) mod 10 = (n div 10) mod 10"
  proof -
    have "((n mod 1000) div 10) mod 10 =
        (((n mod 1000) div 10) + (n div 1000 * 10) * 10) mod 10"
      by (rule mod_mult_self1[symmetric])
    also have "... = (((n mod 1000) div 10) + n div 1000 * 100) mod 10"
      by (simp only: tens_multiple[symmetric])
    also have "... = (n div 10) mod 10"
      by (simp only: quotient_tens[symmetric])
    finally show ?thesis .
  qed
  have hundreds_digit:
    "((n mod 1000) div 100) mod 10 = (n div 100) mod 10"
  proof -
    have "((n mod 1000) div 100) mod 10 =
        (((n mod 1000) div 100) + n div 1000 * 10) mod 10"
      by (rule mod_mult_self1[symmetric])
    also have "... = (n div 100) mod 10"
      by (simp only: quotient_hundreds[symmetric])
    finally show ?thesis .
  qed
  show ?thesis
    unfolding decimal_reverse_block3_def
    by (simp only: low_digit tens_digit hundreds_digit)
qed

lemma decimal_digit_count_ten_step:
  assumes "10 \<le> n"
  shows "decimal_digit_count n = Suc (decimal_digit_count (n div 10))"
  using assms by (simp add: decimal_digit_count.simps)

lemma decimal_digit_count_thousand_step:
  assumes "1000 \<le> n"
  shows "decimal_digit_count n = decimal_digit_count (n div 1000) + 3"
proof -
  let ?q1 = "n div 10"
  let ?q2 = "n div 100"
  let ?q3 = "n div 1000"
  have b1: "10 \<le> n" using assms by arith
  have b2: "10 \<le> ?q1" using assms by arith
  have b3: "10 \<le> ?q2" using assms by arith
  have d1: "?q1 div 10 = ?q2" by (simp add: div_mult2_eq[symmetric])
  have d2: "?q2 div 10 = ?q3" by (simp add: div_mult2_eq[symmetric])
  have c1: "decimal_digit_count n = Suc (decimal_digit_count ?q1)"
    by (rule decimal_digit_count_ten_step[OF b1])
  have c2: "decimal_digit_count ?q1 = Suc (decimal_digit_count ?q2)"
  proof -
    have "decimal_digit_count ?q1 =
        Suc (decimal_digit_count (?q1 div 10))"
      by (rule decimal_digit_count_ten_step[OF b2])
    then show ?thesis by (simp only: d1)
  qed
  have c3: "decimal_digit_count ?q2 = Suc (decimal_digit_count ?q3)"
  proof -
    have "decimal_digit_count ?q2 =
        Suc (decimal_digit_count (?q2 div 10))"
      by (rule decimal_digit_count_ten_step[OF b3])
    then show ?thesis by (simp only: d2)
  qed
  show ?thesis using c1 c2 c3 by simp
qed

lemma decimal_reverse_ten_step:
  assumes "10 \<le> n"
  shows "decimal_reverse n =
    (n mod 10) * 10^(decimal_digit_count (n div 10)) +
      decimal_reverse (n div 10)"
proof -
  have count: "decimal_digit_count n =
      Suc (decimal_digit_count (n div 10))"
    by (rule decimal_digit_count_ten_step[OF assms])
  show ?thesis using assms count by (simp add: decimal_reverse.simps)
qed

lemma decimal_reverse_thousand_step:
  assumes bound: "1000 \<le> n"
  shows "decimal_reverse n =
    decimal_reverse_block3 (n mod 1000) *
        10^(decimal_digit_count (n div 1000)) +
      decimal_reverse (n div 1000)"
proof -
  let ?q1 = "n div 10"
  let ?q2 = "n div 100"
  let ?q3 = "n div 1000"
  have b1: "10 \<le> n" using bound by arith
  have b2: "10 \<le> ?q1" using bound by arith
  have b3: "10 \<le> ?q2" using bound by arith
  have d1: "?q1 div 10 = ?q2" by (simp add: div_mult2_eq[symmetric])
  have d2: "?q2 div 10 = ?q3" by (simp add: div_mult2_eq[symmetric])
  have c2: "decimal_digit_count ?q1 = Suc (decimal_digit_count ?q2)"
    using decimal_digit_count_ten_step[OF b2] d1 by simp
  have c3: "decimal_digit_count ?q2 = Suc (decimal_digit_count ?q3)"
    using decimal_digit_count_ten_step[OF b3] d2 by simp
  have r0: "decimal_reverse n =
      (n mod 10) * 10^(decimal_digit_count ?q1) + decimal_reverse ?q1"
    by (rule decimal_reverse_ten_step[OF b1])
  have r1: "decimal_reverse ?q1 =
      (?q1 mod 10) * 10^(decimal_digit_count ?q2) + decimal_reverse ?q2"
    using decimal_reverse_ten_step[OF b2] by (simp only: d1)
  have r2: "decimal_reverse ?q2 =
      (?q2 mod 10) * 10^(decimal_digit_count ?q3) + decimal_reverse ?q3"
    using decimal_reverse_ten_step[OF b3] by (simp only: d2)
  have digits: "decimal_reverse_block3 (n mod 1000) =
      (n mod 10) * 100 + (?q1 mod 10) * 10 + (?q2 mod 10)"
    by (rule decimal_reverse_block3_digits)
  have unfolded:
    "decimal_reverse n =
      (n mod 10) * 10^(decimal_digit_count ?q1) +
        ((?q1 mod 10) * 10^(decimal_digit_count ?q2) +
          ((?q2 mod 10) * 10^(decimal_digit_count ?q3) +
            decimal_reverse ?q3))"
    by (simp only: r0 r1 r2)
  have joined:
    "(n mod 10) * 10^(decimal_digit_count ?q1) +
        ((?q1 mod 10) * 10^(decimal_digit_count ?q2) +
          ((?q2 mod 10) * 10^(decimal_digit_count ?q3) +
            decimal_reverse ?q3)) =
      decimal_reverse_block3 (n mod 1000) *
        10^(decimal_digit_count ?q3) + decimal_reverse ?q3"
    using c2 c3 digits
    by (simp add: power_add algebra_simps)
  show ?thesis by (rule trans[OF unfolded joined])
qed

lemma decimal_reverse_acc_thousand_step:
  assumes bound: "1000 \<le> n"
  shows "decimal_reverse_acc n accumulator =
    decimal_reverse_acc (n div 1000)
      (1000 * accumulator + decimal_reverse_block3 (n mod 1000))"
proof -
  let ?q = "n div 1000"
  have count: "decimal_digit_count n = decimal_digit_count ?q + 3"
    by (rule decimal_digit_count_thousand_step[OF bound])
  have reverse: "decimal_reverse n =
      decimal_reverse_block3 (n mod 1000) *
        10^(decimal_digit_count ?q) + decimal_reverse ?q"
    by (rule decimal_reverse_thousand_step[OF bound])
  have left: "decimal_reverse_acc n accumulator =
      accumulator * 10^(decimal_digit_count n) + decimal_reverse n"
    by (rule decimal_reverse_accumulator_correct)
  have right: "decimal_reverse_acc ?q
      (1000 * accumulator + decimal_reverse_block3 (n mod 1000)) =
      (1000 * accumulator + decimal_reverse_block3 (n mod 1000)) *
        10^(decimal_digit_count ?q) + decimal_reverse ?q"
    by (rule decimal_reverse_accumulator_correct)
  show ?thesis using left right count reverse
    by (simp add: power_add algebra_simps)
qed

function decimal_reverse_acc_chunk3 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decimal_reverse_acc_chunk3 n accumulator =
    (if n < 1000 then decimal_reverse_acc n accumulator
     else decimal_reverse_acc_chunk3 (n div 1000)
       (1000 * accumulator + decimal_reverse_block3 (n mod 1000)))"
  by pat_completeness auto
termination
  by (relation "measure fst") auto

lemma decimal_nat_div_mod_pair_from_decomposition:
  fixes n k q r :: nat
  assumes decomposition: "n = k * q + r"
      and remainder: "r < k"
  shows "(n div k, n mod k) = (q, r)"
proof -
  have lower: "k * q \<le> n" using decomposition by simp
  have upper_sum: "k * q + r < k * q + k" using remainder by simp
  have upper_product: "k * q + k = k * Suc q"
    by (simp add: algebra_simps)
  have upper: "n < k * Suc q"
    using decomposition upper_sum upper_product by simp
  have division: "n div k = q"
    by (rule div_nat_eqI[OF lower upper])
  have residue_step: "(k * q + r) mod k = (r + q * k) mod k"
    by (simp add: algebra_simps)
  have residue_multiple: "(r + q * k) mod k = r mod k"
    by (rule mod_mult_self1)
  have residue: "n mod k = r"
    using decomposition remainder residue_step residue_multiple by simp
  show ?thesis using division residue by simp
qed

lemma decimal_nat_div_from_decomposition:
  fixes n k q r :: nat
  assumes "n = k * q + r" "r < k"
  shows "n div k = q"
  using decimal_nat_div_mod_pair_from_decomposition[OF assms] by simp

lemma decimal_nat_mod_from_decomposition:
  fixes n k q r :: nat
  assumes "n = k * q + r" "r < k"
  shows "n mod k = r"
  using decimal_nat_div_mod_pair_from_decomposition[OF assms] by simp

lemma decimal_reverse_acc_chunk3_correct:
  "decimal_reverse_acc_chunk3 n accumulator =
    decimal_reverse_acc n accumulator"
proof (induction n arbitrary: accumulator rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 1000")
    case True
    then show ?thesis by (simp add: decimal_reverse_acc_chunk3.simps)
  next
    case False
    have bound: "1000 \<le> n" using False by simp
    have smaller: "n div 1000 < n" using bound by simp
    have transition: "decimal_reverse_acc n accumulator =
        decimal_reverse_acc (n div 1000)
          (1000 * accumulator + decimal_reverse_block3 (n mod 1000))"
      by (rule decimal_reverse_acc_thousand_step[OF bound])
    have induction:
      "decimal_reverse_acc_chunk3 (n div 1000)
          (1000 * accumulator + decimal_reverse_block3 (n mod 1000)) =
        decimal_reverse_acc (n div 1000)
          (1000 * accumulator + decimal_reverse_block3 (n mod 1000))"
      by (rule less.IH[OF smaller])
    show ?thesis using False transition induction
      by (simp add: decimal_reverse_acc_chunk3.simps)
  qed
qed

lemma decimal_reverse_accumulator_chunk3:
  "decimal_reverse n = decimal_reverse_acc_chunk3 n 0"
  using decimal_reverse_accumulator_correct[of n 0]
    decimal_reverse_acc_chunk3_correct[of n 0]
  by simp

ML \<open>
  val checked = @{thms decimal_reverse_block3_def decimal_reverse_block3_digits
    decimal_digit_count_ten_step decimal_digit_count_thousand_step
    decimal_reverse_ten_step decimal_reverse_thousand_step
    decimal_reverse_acc_thousand_step decimal_reverse_acc_chunk3.simps
    decimal_nat_div_mod_pair_from_decomposition
    decimal_nat_div_from_decomposition decimal_nat_mod_from_decomposition
    decimal_reverse_acc_chunk3_correct decimal_reverse_accumulator_chunk3};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Shared decimal-reversal proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped shared decimal-reversal proof" else ();
\<close>

end
