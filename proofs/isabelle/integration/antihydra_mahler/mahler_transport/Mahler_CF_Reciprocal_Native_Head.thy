theory Mahler_CF_Reciprocal_Native_Head
  imports Mahler_CF_Reciprocal_Source Mahler_CF_Low_Period
begin

text \<open>The native continuant consumes one complete high sixteen-digit
word before its bounded remainder. The decimal digit constructor retains
leading zeroes in each word, and the selected value is bound to the original
physical power-of-five row.\<close>

lemma mahler_cf_fixed_width_high_low_words:
  "mahler_cf_decimal_digits (high + low) value =
    mahler_cf_decimal_digits high (value div 10^low) @
      mahler_cf_decimal_digits low (value mod 10^low)"
proof -
  have split: "mahler_cf_decimal_digits (high + low) value =
      mahler_cf_decimal_digits high (value div 10^low) @
        mahler_cf_decimal_digits low value"
  proof (induction high)
    case 0
    then show ?case by (simp add: mahler_cf_decimal_digits_def)
  next
    case (Suc high)
    show ?case
      using Suc.IH
      by (simp add: cf_decimal_digits_split power_add div_mult2_eq[symmetric] mult.commute)
  qed
  have low: "mahler_cf_decimal_digits low value =
      mahler_cf_decimal_digits low (value mod 10^low)"
    by (rule cf_decimal_digits_lower_congruent) simp
  show ?thesis using split low by simp
qed

theorem mahler_cf_reciprocal_native_high16_consumer:
  fixes n t width start count :: nat
  assumes bounded: "16 < count" "count \<le> 32" and clip: "start + count \<le> width"
      and significant: "10^(width-1) \<le> (5::nat)^(n+t)"
        "(5::nat)^(n+t) < 10^width"
  defines "value \<equiv> mahler_cf_reciprocal_selected_digits (5^n) t width start count"
    and "remainder_width \<equiv> count - 16"
  shows "value = ((5^(n+t)) div 10^(width-start-count)) mod 10^count"
    and "value div 10^remainder_width < 10^16"
    and "value mod 10^remainder_width < 10^remainder_width"
    and "length (mahler_cf_decimal_digits 16 (value div 10^remainder_width)) = 16"
    and "length (mahler_cf_decimal_digits remainder_width (value mod 10^remainder_width)) =
      remainder_width"
    and "mahler_cf_word (mahler_cf_decimal_digits count value) =
      ordered_matrix2_multiply
        (mahler_cf_word (mahler_cf_decimal_digits 16 (value div 10^remainder_width)))
        (mahler_cf_word (mahler_cf_decimal_digits remainder_width (value mod 10^remainder_width)))"
proof -
  have count: "count = 16 + remainder_width" using bounded
    by (simp add: remainder_width_def)
  have bound: "value < 10^count"
    by (simp add: value_def mahler_cf_reciprocal_selected_digits_def)
  have head: "value div 10^remainder_width < 10^16"
    using bound by (simp add: count power_add div_less_iff_less_mult mult.commute)
  have words: "mahler_cf_decimal_digits count value =
      mahler_cf_decimal_digits 16 (value div 10^remainder_width) @
        mahler_cf_decimal_digits remainder_width (value mod 10^remainder_width)"
    by (simp only: count mahler_cf_fixed_width_high_low_words)
  show "value = ((5^(n+t)) div 10^(width-start-count)) mod 10^count"
    by (simp only: value_def mahler_cf_reciprocal_selected_physical_source)
  show "value div 10^remainder_width < 10^16" by (rule head)
  show "value mod 10^remainder_width < 10^remainder_width" by simp
  show "length (mahler_cf_decimal_digits 16 (value div 10^remainder_width)) = 16"
    by (simp add: mahler_cf_decimal_digits_def)
  show "length (mahler_cf_decimal_digits remainder_width (value mod 10^remainder_width)) =
      remainder_width" by (simp add: mahler_cf_decimal_digits_def)
  show "mahler_cf_word (mahler_cf_decimal_digits count value) =
      ordered_matrix2_multiply
        (mahler_cf_word (mahler_cf_decimal_digits 16 (value div 10^remainder_width)))
        (mahler_cf_word (mahler_cf_decimal_digits remainder_width (value mod 10^remainder_width)))"
    by (simp only: words mahler_cf_word_append)
qed

ML \<open>
  val checked = @{thms mahler_cf_fixed_width_high_low_words
    mahler_cf_reciprocal_native_high16_consumer};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Native reciprocal head depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native reciprocal head" else ();
\<close>

end
