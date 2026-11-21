theory Reverse_Palindrome_Physical_Iff
  imports Reverse_Palindrome_Physical_Bridge
begin

theorem reverse_no_growth_palindrome_preimage_exact:
  assumes valid: "valid_pair coefficients"
    and no_growth: "\<not> carry_out False coefficients"
  shows "rev (digits coefficients) = digits coefficients \<longleftrightarrow>
    (\<forall>s \<in> set coefficients. s < 10)"
proof
  assume palindrome: "rev (digits coefficients) = digits coefficients"
  let ?n = "length coefficients"
  let ?C = "reverse_palindrome_prefix_carry coefficients"
  let ?S = "(\<lambda>i. coefficients ! i)"
  have coefficient_bound: "\<forall>s \<in> set coefficients. s < 19"
    using valid by (auto simp: valid_pair_def)
  have symmetric: "rev coefficients = coefficients"
    using valid by (simp add: valid_pair_def)
  have start: "?C 0 = 0"
    by (simp add: reverse_palindrome_prefix_carry_def carry_bit_def carry_out_def)
  have finish: "?C ?n = 0"
    using no_growth by (simp add: reverse_palindrome_prefix_carry_def carry_bit_def)
  have bits: "?C i < 2" for i by simp
  have source_symmetry: "?S i = ?S (?n - Suc i)" if "i < ?n" for i
    using palindrome_nth_reflect[OF symmetric that] by simp
  have carry_step: "?C (Suc i) = decimal_carry (?S i) (?C i)" if "i < ?n" for i
    by (rule reverse_palindrome_prefix_carry_step[OF that])
  have emitted_symmetry:
    "normalized_growth_digit ?S ?C i = normalized_growth_digit ?S ?C (?n - Suc i)"
    if bound: "i < ?n" for i
  proof -
    let ?j = "?n - Suc i"
    have j_bound: "?j < ?n" using bound by arith
    have length: "length (digits coefficients) = ?n"
      using no_growth by (simp add: length_digits_exact)
    have digit_eq: "digits coefficients ! i = digits coefficients ! ?j"
      using palindrome_nth_reflect[OF palindrome, of i] bound length by simp
    have emitted_eq: "emit False coefficients ! i = emit False coefficients ! ?j"
      using digit_eq no_growth by (simp add: digits_def)
    show ?thesis
      using reverse_palindrome_physical_digit[OF bound coefficient_bound]
        reverse_palindrome_physical_digit[OF j_bound coefficient_bound] emitted_eq by simp
  qed
  show "\<forall>s \<in> set coefficients. s < 10"
  proof
    fix s assume "s \<in> set coefficients"
    then obtain i where index: "i < ?n" and s: "s = coefficients ! i"
      by (auto simp: in_set_conv_nth)
    have "?S i < 10"
      by (rule reverse_palindrome_no_growth_pair_bound
          [OF start finish bits source_symmetry emitted_symmetry carry_step index])
    then show "s < 10" using s by simp
  qed
next
  assume bound: "\<forall>s \<in> set coefficients. s < 10"
  have symmetric: "rev coefficients = coefficients" using valid by (simp add: valid_pair_def)
  show "rev (digits coefficients) = digits coefficients"
    by (rule reverse_decimal_palindrome_preimage_no_growth[OF symmetric bound])
qed

definition reverse_q19_no_growth_guard :: "nat list \<Rightarrow> nat option \<Rightarrow> bool" where
  "reverse_q19_no_growth_guard pairs center \<longleftrightarrow>
    (\<forall>p \<in> set pairs. p < 10) \<and>
    (case center of None \<Rightarrow> True | Some d \<Rightarrow> d < 5)"

theorem reverse_q19_no_growth_preimage_exact:
  assumes valid: "valid_pair (reverse_q19_coefficients pairs center)"
    and no_growth: "\<not> carry_out False (reverse_q19_coefficients pairs center)"
  shows "(rev (digits (reverse_q19_coefficients pairs center)) =
      digits (reverse_q19_coefficients pairs center)) = reverse_q19_no_growth_guard pairs center"
proof -
  have guard: "(\<forall>s \<in> set (reverse_q19_coefficients pairs center). s < 10) =
      reverse_q19_no_growth_guard pairs center"
  proof -
    have middle: "2 * d < 10 \<longleftrightarrow> (d::nat) < 5" for d by arith
    show ?thesis by (cases center)
      (simp_all add: reverse_q19_no_growth_guard_def reverse_q19_coefficients_def middle conj_commute)
  qed
  show ?thesis using reverse_no_growth_palindrome_preimage_exact[OF valid no_growth] guard by simp
qed

end
