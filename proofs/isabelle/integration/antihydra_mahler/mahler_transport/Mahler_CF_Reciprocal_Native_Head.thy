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


text \<open>The last tile may retain prefix actions up to the irregular head
of its second row. Removing the left prefix from a longer prefix selects
exactly the requested physical letters, including a cut before a leading zero.\<close>

theorem mahler_cf_reciprocal_indexed_clip:
  fixes n t width start count first len :: nat
  assumes bounds: "start + count \<le> width" "first + len \<le> count"
  defines "digits \<equiv> mahler_cf_decimal_digits count
    (mahler_cf_reciprocal_selected_digits (5^n) t width start count)"
  shows "ordered_matrix2_multiply
      (mahler_cf_integer_adjugate first
        (mahler_cf_matrix_to_integer (mahler_cf_word (take first digits))))
      (mahler_cf_matrix_to_integer (mahler_cf_word (take (first + len) digits))) =
    mahler_cf_matrix_to_integer (mahler_cf_word (take len (drop first
      (mahler_cf_decimal_digits count
        (5^(n+t) div 10^(width-start-count) mod 10^count)))))"
proof -
  have first: "first \<le> count" using bounds by arith
  have length: "length (take first digits) = first"
    using first by (simp add: digits_def mahler_cf_decimal_digits_def)
  note clip = mahler_cf_integer_tail_from_word[OF length,
    of "take len (drop first digits)"]
  show ?thesis using clip
    by (simp only: take_add digits_def mahler_cf_reciprocal_selected_physical_source)
qed

lemma mahler_cf_reciprocal_adjugate_commutes:
  fixes m :: "int ordered_matrix2"
  shows "ordered_matrix2_multiply m (mahler_cf_integer_adjugate k m) =
    ordered_matrix2_multiply (mahler_cf_integer_adjugate k m) m"
  by (cases m) (simp add: mahler_cf_integer_adjugate_def algebra_simps)

text \<open>The retained boundary products cover complete ordered rows. Remove
the earlier boundary on the left, then append the exact clipped physical row.\<close>

theorem mahler_cf_reciprocal_row_boundary_consumer:
  fixes n t width start count :: nat and before selected :: "nat list"
    and widths :: "nat \<Rightarrow> nat"
  defines "issued \<equiv> \<lambda>positions. concat (map (\<lambda>r.
    mahler_cf_decimal_digits (widths r) (mahler_cf_reciprocal_row (5^n) r)) positions)"
  assumes clip: "start + count \<le> width"
  shows "ordered_matrix2_multiply
      (ordered_matrix2_multiply
        (mahler_cf_integer_adjugate (length (issued before))
          (mahler_cf_integer_word (issued before)))
        (mahler_cf_integer_word (issued (before @ selected))))
      (mahler_cf_integer_word (mahler_cf_decimal_digits count
        (mahler_cf_reciprocal_selected_digits (5^n) t width start count))) =
    mahler_cf_integer_word (concat (map (\<lambda>r.
      mahler_cf_decimal_digits (widths r) (5^(n+r))) selected) @
        mahler_cf_decimal_digits count (5^(n+t) div 10^(width-start-count) mod 10^count))"
proof -
  have split: "issued (before @ selected) = issued before @ issued selected"
    by (simp add: issued_def)
  have action: "ordered_matrix2_multiply
      (mahler_cf_integer_adjugate (length (issued before))
        (mahler_cf_integer_word (issued before)))
      (mahler_cf_integer_word (issued (before @ selected))) =
    mahler_cf_integer_word (issued selected)"
    using mahler_cf_integer_tail_from_word[OF refl, of "issued before" "issued selected"]
    by (simp only: split mahler_cf_natural_word_to_integer)
  show ?thesis
    apply (subst action)
    by (simp only: mahler_cf_integer_word_append[symmetric]
        issued_def mahler_cf_reciprocal_physical_source mahler_cf_reciprocal_selected_physical_source)
qed

theorem mahler_cf_reciprocal_indexed_head_settled_clip:
  fixes n t width start count split limit :: nat
  assumes bounds: "start + count \<le> width" "split \<le> limit" "limit \<le> count"
  defines "digits \<equiv> mahler_cf_decimal_digits count
    (mahler_cf_reciprocal_selected_digits (5^n) t width start count)"
  shows "ordered_matrix2_multiply (mahler_cf_integer_word (take split digits))
      (ordered_matrix2_multiply
        (mahler_cf_integer_word (drop split digits))
        (mahler_cf_integer_adjugate (count-limit)
          (mahler_cf_integer_word (drop limit digits)))) =
    mahler_cf_integer_word (take limit (mahler_cf_decimal_digits count
      (5^(n+t) div 10^(width-start-count) mod 10^count)))"
proof -
  have tail: "length (drop limit digits) = count-limit"
    by (simp add: digits_def mahler_cf_decimal_digits_def)
  have cancel: "ordered_matrix2_multiply
      (mahler_cf_integer_word (drop limit digits))
      (mahler_cf_integer_adjugate (count-limit)
        (mahler_cf_integer_word (drop limit digits))) = ordered_matrix2_identity"
    by (subst mahler_cf_reciprocal_adjugate_commutes)
      (rule mahler_cf_integer_adjugate_inverse_left[OF tail])
  have take_cut: "split + (limit-split) = limit"
    by (rule le_add_diff_inverse[OF bounds(2)])
  have drop_cut: "(limit-split) + split = limit" using take_cut by (simp only: add.commute)
  have rest: "drop split digits =
      take (limit-split) (drop split digits) @ drop limit digits"
    using append_take_drop_id[of "limit-split" "drop split digits", symmetric]
    by (simp only: drop_drop drop_cut)
  have head: "take split digits @ take (limit-split) (drop split digits) =
      take limit digits"
    using take_add[of split "limit-split" digits, symmetric] by (simp only: take_cut)
  have narrowed: "ordered_matrix2_multiply
        (mahler_cf_integer_word (drop split digits))
        (mahler_cf_integer_adjugate (count-limit)
          (mahler_cf_integer_word (drop limit digits))) =
      mahler_cf_integer_word (take (limit-split) (drop split digits))"
    by (subst (1) rest)
      (simp only: mahler_cf_integer_word_append ordered_matrix2_multiply_associative
        cancel ordered_matrix2_identity_right)
  have joined: "ordered_matrix2_multiply (mahler_cf_integer_word (take split digits))
      (mahler_cf_integer_word (take (limit-split) (drop split digits))) =
      mahler_cf_integer_word (take limit digits)"
    by (simp only: mahler_cf_integer_word_append[symmetric] head)
  have "ordered_matrix2_multiply (mahler_cf_integer_word (take split digits))
      (ordered_matrix2_multiply (mahler_cf_integer_word (drop split digits))
        (mahler_cf_integer_adjugate (count-limit)
          (mahler_cf_integer_word (drop limit digits)))) =
      mahler_cf_integer_word (take limit digits)"
    by (simp only: narrowed joined)
  also have "... = mahler_cf_integer_word (take limit (mahler_cf_decimal_digits count
      (5^(n+t) div 10^(width-start-count) mod 10^count)))"
    by (simp only: digits_def mahler_cf_reciprocal_selected_physical_source)
  finally show ?thesis .
qed

text \<open>Multiplying the low field at a cut issues exactly the carry into
the successor head. The same equation applies at each base-100 boundary
and at the split used to index the successor's prefixes.\<close>

lemma mahler_cf_head_carry_step:
  fixes x radix :: nat
  assumes "0 < radix"
  shows "(5 * x) div radix =
    5 * (x div radix) + (5 * (x mod radix)) div radix"
proof -
  have scaled: "5 * x = (5 * (x div radix)) * radix + 5 * (x mod radix)"
    using arg_cong[OF div_mult_mod_eq[of x radix], of "(*) 5"]
    by (simp only: algebra_simps)
  show ?thesis by (subst scaled) (simp add: assms)
qed

theorem mahler_cf_paired_head_consumer:
  fixes n h k low :: nat
  shows "mahler_cf_word (mahler_cf_decimal_digits (h+low) (5^n) @
        mahler_cf_decimal_digits (k+low) (5^Suc n)) =
    ordered_matrix2_multiply
      (mahler_cf_word (mahler_cf_decimal_digits h (5^n div 10^low) @
        mahler_cf_decimal_digits low (5^n mod 10^low)))
      (mahler_cf_word (mahler_cf_decimal_digits k
        (5 * (5^n div 10^low) + (5 * (5^n mod 10^low)) div 10^low) @
        mahler_cf_decimal_digits low ((5 * 5^n) mod 10^low)))"
proof -
  have succ: "(5::nat)^Suc n = 5 * 5^n" by (simp add: power_Suc mult.commute)
  have step: "(5 * (5::nat)^n) div 10^low =
      5 * (5^n div 10^low) + (5 * (5^n mod 10^low)) div 10^low"
    by (rule mahler_cf_head_carry_step) simp
  show ?thesis
    by (simp only: mahler_cf_fixed_width_high_low_words mahler_cf_word_append succ step)
qed

ML \<open>
  val checked = @{thms mahler_cf_head_carry_step mahler_cf_paired_head_consumer mahler_cf_reciprocal_indexed_clip mahler_cf_fixed_width_high_low_words
    mahler_cf_reciprocal_native_high16_consumer mahler_cf_reciprocal_indexed_head_settled_clip
    mahler_cf_reciprocal_row_boundary_consumer};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Native reciprocal head depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then error "Skipped native reciprocal head" else ();
\<close>

end
