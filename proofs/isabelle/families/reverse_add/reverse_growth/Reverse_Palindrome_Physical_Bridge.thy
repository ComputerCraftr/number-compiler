theory Reverse_Palindrome_Physical_Bridge
  imports Reverse_Palindrome_Preimage_Seams "Reverse_Residuals.Reverse_Punctured_T2_Coefficients"
begin

definition reverse_palindrome_prefix_carry :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "reverse_palindrome_prefix_carry coefficients i =
    carry_bit (carry_out False (take i coefficients))"

lemma reverse_palindrome_prefix_carry_bit [simp]:
  "reverse_palindrome_prefix_carry coefficients i < 2"
  by (simp add: reverse_palindrome_prefix_carry_def carry_bit_def)

lemma reverse_palindrome_prefix_carry_step:
  assumes "i < length coefficients"
  shows "reverse_palindrome_prefix_carry coefficients (Suc i) =
    decimal_carry (coefficients ! i) (reverse_palindrome_prefix_carry coefficients i)"
  using carry_out_take_successor[OF assms]
  by (cases "carry_out False (take i coefficients)")
     (auto simp: reverse_palindrome_prefix_carry_def carry_bit_def
       decimal_carry_def carry_apply_decimal_threshold)

lemma reverse_palindrome_normalized_digit:
  fixes coefficient incoming :: nat
  assumes "coefficient < 19" "incoming < 2"
  shows "int ((coefficient + incoming) mod 10) =
    int coefficient + int incoming - 10 * int (decimal_carry coefficient incoming)"
proof -
  have coefficient_cases: "coefficient = 0 \<or> coefficient = 1 \<or> coefficient = 2 \<or>
      coefficient = 3 \<or> coefficient = 4 \<or> coefficient = 5 \<or>
      coefficient = 6 \<or> coefficient = 7 \<or> coefficient = 8 \<or>
      coefficient = 9 \<or> coefficient = 10 \<or> coefficient = 11 \<or>
      coefficient = 12 \<or> coefficient = 13 \<or> coefficient = 14 \<or>
      coefficient = 15 \<or> coefficient = 16 \<or> coefficient = 17 \<or> coefficient = 18"
    using assms(1) by (rule nat_less_nineteen_cases)
  have bit: "incoming = 0 \<or> incoming = 1" using assms(2) by arith
  show ?thesis using coefficient_cases bit by (elim disjE; simp add: decimal_carry_def)
qed

theorem reverse_palindrome_physical_digit:
  assumes bound: "i < length coefficients"
    and valid: "\<forall>s \<in> set coefficients. s < 19"
  shows "int (emit False coefficients ! i) =
    normalized_growth_digit (\<lambda>j. coefficients ! j)
      (reverse_palindrome_prefix_carry coefficients) i"
proof -
  have coefficient: "coefficients ! i < 19" using valid bound by auto
  have recurrence: "reverse_palindrome_prefix_carry coefficients (Suc i) =
      decimal_carry (coefficients ! i) (reverse_palindrome_prefix_carry coefficients i)"
    by (rule reverse_palindrome_prefix_carry_step[OF bound])
  show ?thesis
    using emit_nth_carry_prefix[OF bound, of False]
      reverse_palindrome_normalized_digit[OF coefficient
        reverse_palindrome_prefix_carry_bit[of coefficients i]] recurrence
    by (simp add: normalized_growth_digit_def reverse_palindrome_prefix_carry_def carry_bit_def)
qed

end
