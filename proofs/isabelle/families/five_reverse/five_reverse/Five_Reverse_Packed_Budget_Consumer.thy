theory Five_Reverse_Packed_Budget_Consumer
  imports Five_Reverse_Packed_Word_Consumer
begin

text \<open>Conservative decimal-width checks for the packed bit budget.
The inequalities decide some widths without opening the digit stream. The
remaining equal-width comparison still requires an exact prefix adapter.\<close>

lemma five_decimal_safe_power:
  "(10::nat)^(3*k) \<le> (2::nat)^(10*k)"
  by (simp only: power_mult; rule power_mono; simp)

lemma five_decimal_impossible_power:
  "(2::nat)^(3*k) \<le> (10::nat)^k"
  by (simp only: power_mult; rule power_mono; simp)

theorem five_decimal_safe_width:
  fixes width bits num :: nat
  assumes "width \<le> 3 * (bits div 10)" "num < 10^width"
  shows "num < 2^bits"
proof -
  have a: "(10::nat)^width \<le> 10^(3 * (bits div 10))"
    by (rule power_increasing[OF assms(1)]) simp
  have b: "(10::nat)^(3 * (bits div 10)) \<le> (2::nat)^(10 * (bits div 10))"
    by (rule five_decimal_safe_power)
  have division: "bits div 10 * 10 + bits mod 10 = bits"
    by (rule div_mult_mod_eq)
  have exponent: "10 * (bits div 10) \<le> bits"
    using division by arith
  have c: "(2::nat)^(10 * (bits div 10)) \<le> 2^bits"
    by (rule power_increasing[OF exponent]) simp
  show ?thesis using assms(2) a b c by arith
qed

theorem five_decimal_impossible_width:
  fixes width bits num :: nat
  assumes "bits div 3 + 2 \<le> width" "10^(width - 1) \<le> num"
  shows "\<not> num < 2^bits"
proof -
  let ?k = "bits div 3 + 1"
  have remainder: "bits mod 3 < 3" by simp
  have decomposition: "bits div 3 * 3 + bits mod 3 = bits"
    by (rule div_mult_mod_eq)
  have exponent: "bits < 3 * ?k" using remainder decomposition by arith
  have width: "?k \<le> width - 1" using assms(1) by arith
  have a: "(2::nat)^bits < 2^(3*?k)"
    by (rule power_strict_increasing[OF exponent]) simp
  have b: "(2::nat)^(3*?k) \<le> 10^?k" by (rule five_decimal_impossible_power)
  have c: "(10::nat)^?k \<le> 10^(width - 1)"
    by (rule power_increasing[OF width]) simp
  show ?thesis using assms(2) a b c by arith
qed

theorem five_bcd_M_valid:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_valid (Suc n) (five_bcd_M n packed)"
  using assms
proof (induction n arbitrary: packed)
  case 0
  then show ?case by (simp add: five_bcd_M_def five_bcd_upper_mask_def)
next
  case (Suc n)
  let ?d = "packed mod 16"
  let ?b = "?d mod 2"
  let ?q = "?d div 2"
  let ?tail = "packed div 16"
  let ?word = "five_bcd_M n ?tail"
  have digit: "?d < 10" using Suc.prems by simp
  have valid: "five_bcd_valid n ?tail" using Suc.prems by simp
  have half: "?q < 5" using digit by (simp add: div_less_iff_less_mult)
  have parity_bound: "?b < 2" by simp
  have output_digit: "5 * ?b < 10" using parity_bound by arith
  have low: "?word mod 16 = 0 \<or> ?word mod 16 = 5"
    by (rule five_bcd_M_low_kind[OF valid])
  have no_spill: "?word mod 16 + ?q < 10" using low half by arith
  have valid_word: "five_bcd_valid (Suc n) ?word" by (rule Suc.IH[OF valid])
  have valid_tail: "five_bcd_valid (Suc n) (?word + ?q)"
    by (rule five_bcd_valid_low_add[OF valid_word no_spill])
  have rec: "five_bcd_M (Suc n) packed = 5 * ?b + 16 * (?word + ?q)"
    by (rule five_bcd_M_word_recursion[OF digit])
  show ?case unfolding rec by (rule five_bcd_valid_cons[OF output_digit valid_tail])
qed


theorem five_bcd_E_reflects_physical_odd:
  assumes "five_bcd_valid n packed"
  shows "five_bcd_decimal (Suc n) (five_bcd_E n packed) =
    five_fixed_reverse (Suc (decimal_digit_count (five_bcd_decimal n packed)))
      (five_reverse_step (five_bcd_decimal n packed))"
proof -
  let ?source = "five_bcd_decimal n packed"
  let ?width = "decimal_digit_count ?source"
  have source_bound: "?source < (10::nat)^?width"
    by (rule decimal_source_below_digit_power)
  have carry: "(0::nat) < 5" by simp
  have reflected:
    "five_fixed_reverse (Suc ?width) (five_reverse_step ?source) =
      five_reflected_E ?source"
    using five_fixed_reverse_reflected_product[OF source_bound carry]
    by (simp only: five_reverse_step_def five_fixed_reverse_decimal
      mult_zero_left Nat.add_0_right)
  show ?thesis using five_bcd_E_decodes_physical[OF assms] reflected by simp
qed


ML \<open>
  val checked = @{thms five_decimal_safe_width five_decimal_impossible_width
    five_bcd_M_valid five_bcd_E_reflects_physical_odd};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Packed five-reverse budget consumer depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Skipped packed five-reverse budget consumer proof" else ();
\<close>

end
