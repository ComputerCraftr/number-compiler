theory Five_Reverse_Packed_Consumer
  imports Five_Reverse_Reflected_H
begin

unbundle bit_operations_syntax

text \<open>Local packed BCD lanes and physical two-step admission.  The word-level
mask compiler and its correspondence to these lanes remain a separate
obligation: these statements do not assume that a supplied packed word has
been decoded correctly.\<close>

fun five_bcd_low_mask :: "nat \<Rightarrow> nat" where
  "five_bcd_low_mask 0 = 0"
| "five_bcd_low_mask (Suc n) = 1 + 16 * five_bcd_low_mask n"

lemma five_bcd_low_mask_geometric:
  "15 * five_bcd_low_mask n + 1 = 16^n"
  by (induction n) (simp_all add: power_Suc algebra_simps)

lemma five_bcd_low_mask_closed:
  "five_bcd_low_mask n = (16^n - 1) div 15"
proof -
  have "16^n - 1 = 15 * five_bcd_low_mask n"
    using five_bcd_low_mask_geometric[of n] by arith
  then show ?thesis by simp
qed

lemma five_bcd_mask_lane:
  assumes "i < n"
  shows "(five_bcd_low_mask n div 16^i) mod 16 = 1"
  using assms
proof (induction n arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc n)
  note smaller_lane = Suc.IH
  note index_bound = Suc.prems
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    have "j < n" using index_bound Suc by simp
    then have digit: "(five_bcd_low_mask n div 16^j) mod 16 = 1"
      by (rule smaller_lane)
    have quotient:
      "(1 + 16 * five_bcd_low_mask n) div 16 = five_bcd_low_mask n"
      by (subst div_mult_self2) simp_all
    have exponent: "(16::nat)^Suc j = 16 * 16^j"
      by (simp only: power_Suc)
    have shift: "five_bcd_low_mask (Suc n) div 16^(Suc j) =
        five_bcd_low_mask n div 16^j"
      by (simp only: five_bcd_low_mask.simps exponent div_mult2_eq quotient)
    show ?thesis using Suc shift digit by simp
  qed
qed

lemma five_bcd_word_extensionality:
  fixes left right n :: nat
  assumes "left < 16^n" "right < 16^n"
      "\<forall>i<n. (left div 16^i) mod 16 = (right div 16^i) mod 16"
  shows "left = right"
  using assms
proof (induction n arbitrary: left right)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have left_bound: "left div 16 < 16^n"
    using Suc.prems(1) by (simp add: power_Suc div_less_iff_less_mult mult.commute)
  have right_bound: "right div 16 < 16^n"
    using Suc.prems(2) by (simp add: power_Suc div_less_iff_less_mult mult.commute)
  have low: "left mod 16 = right mod 16"
  proof -
    have at_zero: "0 < Suc n \<longrightarrow>
        (left div 16^0) mod 16 = (right div 16^0) mod 16"
      using Suc.prems(3) by (rule spec)
    have "(left div 16^0) mod 16 = (right div 16^0) mod 16"
      using at_zero by simp
    then show ?thesis by simp
  qed
  have lanes: "\<forall>i<n. (left div 16 div 16^i) mod 16 =
      (right div 16 div 16^i) mod 16"
  proof (intro allI impI)
    fix i
    assume "i < n"
    then have "(left div 16^(Suc i)) mod 16 =
        (right div 16^(Suc i)) mod 16"
      using Suc.prems(3) by auto
    then show "(left div 16 div 16^i) mod 16 =
        (right div 16 div 16^i) mod 16"
      by (simp add: power_Suc div_mult2_eq mult.commute)
  qed
  have high: "left div 16 = right div 16"
    by (rule Suc.IH[OF left_bound right_bound lanes])
  have left_decomposition: "left = 16 * (left div 16) + left mod 16"
    using div_mult_mod_eq[of left 16] by (simp add: mult.commute)
  have right_decomposition: "right = 16 * (right div 16) + right mod 16"
    using div_mult_mod_eq[of right 16] by (simp add: mult.commute)
  show ?case using left_decomposition right_decomposition low high by simp
qed

lemma five_bcd_masked_lane:
  fixes packed mask :: nat
  shows "take_bit 4 (drop_bit (4 * i) (packed AND mask)) =
    take_bit 4 (drop_bit (4 * i) packed) AND
      take_bit 4 (drop_bit (4 * i) mask)"
  by simp

lemma five_bcd_low_mask_bit_lane:
  assumes "i < n"
  shows "take_bit 4 (drop_bit (4 * i) (five_bcd_low_mask n)) = 1"
  using five_bcd_mask_lane[OF assms]
  by (simp add: take_bit_eq_mod drop_bit_eq_div power_mult)

lemma five_bcd_parity_lane_from_word:
  assumes "i < n"
  shows "take_bit 4 (drop_bit (4 * i) (packed AND five_bcd_low_mask n)) =
    take_bit 4 (drop_bit (4 * i) packed) AND 1"
  using five_bcd_masked_lane[of i packed "five_bcd_low_mask n"]
    five_bcd_low_mask_bit_lane[OF assms] by simp

lemma five_bcd_digit_masks:
  fixes d :: nat
  assumes "d < 10"
  shows "d AND 1 = d mod 2"
    and "d AND 14 = 2 * (d div 2)"
proof -
  have cases: "d=0 \<or> d=1 \<or> d=2 \<or> d=3 \<or> d=4 \<or>
      d=5 \<or> d=6 \<or> d=7 \<or> d=8 \<or> d=9"
    using assms by arith
  show "d AND 1 = d mod 2" using cases by (elim disjE; simp)
  show "d AND 14 = 2 * (d div 2)" using cases by (elim disjE; simp)
qed

lemma five_bcd_multiply_lane:
  fixes d :: nat
  assumes "d < 10"
  shows "5 * (d AND 1) + 8 * (d AND 14) =
    5 * (d mod 2) + 16 * (d div 2)"
  using five_bcd_digit_masks[OF assms] by simp

lemma five_bcd_reflected_lane:
  fixes d :: nat
  assumes "d < 10"
  shows "(d AND 14) div 2 + 80 * (d AND 1) =
    d div 2 + 16 * (5 * (d mod 2))"
  using five_bcd_digit_masks[OF assms] by simp

lemma five_bcd_low_lane_no_spill:
  fixes digit carry :: nat
  assumes "digit < 10" "carry < 5"
  shows "5 * (digit mod 2) + carry < 10"
proof -
  have parity: "digit mod 2 < 2" by simp
  show ?thesis using assms parity by arith
qed

lemma five_bcd_lane_carries:
  fixes digit carry :: nat
  assumes "digit < 10" "carry < 5"
  shows "(5 * digit + carry) div 10 = digit div 2"
    and "(5 * digit + carry) mod 10 = 5 * (digit mod 2) + carry"
  using five_reflected_high_digit_split[OF assms] by auto

definition five_physical_bounded_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "five_physical_bounded_pair bits source =
    (let odd = five_reverse_step source;
         even = five_reverse_step odd
     in if odd < 2^bits \<and> even < 2^bits then Some even else None)"

theorem five_physical_bounded_pair_exact:
  "five_physical_bounded_pair bits source =
    (if five_reverse_step source < 2^bits \<and>
        5 * five_reflected_normalize (five_reflected_E source) < 2^bits
     then Some (5 * five_reflected_normalize (five_reflected_E source))
     else None)"
  unfolding five_physical_bounded_pair_def Let_def
  by (simp only: five_reflected_physical_two_step)

lemma five_physical_bounded_pair_first_refusal:
  assumes "2^bits \<le> five_reverse_step source"
  shows "five_physical_bounded_pair bits source = None"
  using assms by (simp add: five_physical_bounded_pair_def Let_def)

lemma five_physical_bounded_pair_six_rejects_middle:
  "five_physical_bounded_pair 4 6 = None"
  by (simp add: five_physical_bounded_pair_def Let_def five_reverse_step_def
      decimal_reverse.simps decimal_digit_count.simps)

lemma five_decimal_prefix_accept:
  fixes prefix remaining num bits :: nat
  assumes "num < (prefix + 1) * 10^remaining"
      "(prefix + 1) * 10^remaining \<le> 2^bits"
  shows "num < 2^bits"
  using assms by arith

lemma five_decimal_prefix_refuse:
  fixes prefix remaining num bits :: nat
  assumes "prefix * 10^remaining \<le> num"
      "2^bits \<le> prefix * 10^remaining"
  shows "\<not> num < 2^bits"
  using assms by arith

ML \<open>
  val checked = @{thms five_bcd_low_mask_geometric five_bcd_low_mask_closed
    five_bcd_mask_lane five_bcd_word_extensionality five_bcd_masked_lane
    five_bcd_low_mask_bit_lane
    five_bcd_parity_lane_from_word
    five_bcd_digit_masks five_bcd_multiply_lane
    five_bcd_reflected_lane five_bcd_low_lane_no_spill five_bcd_lane_carries
    five_physical_bounded_pair_exact five_physical_bounded_pair_first_refusal
    five_physical_bounded_pair_six_rejects_middle
    five_decimal_prefix_accept five_decimal_prefix_refuse};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Packed five-reverse consumer depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Skipped packed five-reverse consumer proof" else ();
\<close>

end
