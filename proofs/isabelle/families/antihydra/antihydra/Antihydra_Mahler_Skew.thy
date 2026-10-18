theory Antihydra_Mahler_Skew
  imports Antihydra_Literal_TM "Shared_S_Arithmetic.S_Arithmetic_Skew"
begin

text \<open>The return-section scalar map and its centered Mahler coordinate
are defined independently of any claimed all-time barrier.\<close>

definition antihydra_h_step :: "nat \<Rightarrow> nat" where
  "antihydra_h_step h = (3*h - h mod 2) div 2"

definition mahler_D_step :: "nat \<Rightarrow> nat" where
  "mahler_D_step D = (3*D + 1) div 2"

lemma nat_mod_two_cases:
  fixes D :: nat
  obtains k where "D = 2*k" | k where "D = 2*k+1"
proof (cases "D mod 2")
  case 0
  have "2 dvd D" using 0 by (simp add: dvd_eq_mod_eq_0)
  then obtain k where "D = 2*k" by (auto simp: dvd_def mult.commute)
  then show thesis by (rule that(1))
next
  case (Suc r)
  have bound: "D mod 2 < 2" by simp
  with Suc have rem: "D mod 2 = 1" by arith
  have decomposition: "D mod 2 + D div 2 * 2 = D"
    by (rule mod_div_mult_eq)
  have "D = 2*(D div 2)+1" using rem decomposition by arith
  then show thesis by (rule that(2))
qed

lemma mahler_D_step_parity:
  "mahler_D_step D = (3*D + D mod 2) div 2"
  by (cases D rule: nat_mod_two_cases;
      simp add: mahler_D_step_def algebra_simps mod_Suc)

definition mahler_center_next :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_center_next C c U =
    (3*C+c) mod 100 div 2 + 50*((U + (3*C+c) div 100) mod 2)"

lemma mahler_pair_block_quotient:
  fixes B A r :: nat
  assumes positive: "0 < B" and remainder: "r < B"
  shows "(B*A+r) div (2*B) = A div 2"
proof -
  have nested: "(B*A+r) div (B*2) = ((B*A+r) div B) div 2"
    by (simp only: div_mult2_eq[symmetric])
  have quotient: "(B*A+r) div B = A"
    using positive remainder by (simp add: div_add_self2 add.commute)
  show ?thesis using nested quotient by (simp add: mult.commute)
qed

lemma mahler_center_half_residue:
  fixes m x :: nat
  assumes bound: "m < 100"
  shows "(m div 2 + 50*x) mod 100 = m div 2 + 50*(x mod 2)"
proof -
  have x_split: "x = 2*(x div 2) + x mod 2"
    using div_mult_mod_eq[of x 2] by (simp add: mult.commute)
  have x_remainder: "x mod 2 < 2" by simp
  have half_bound: "m div 2 < 50" using bound by arith
  have result_bound: "m div 2 + 50*(x mod 2) < 100"
    using half_bound x_remainder by arith
  have expansion:
    "m div 2 + 50*x =
      (m div 2 + 50*(x mod 2)) + 100*(x div 2)"
    using x_split by arith
  have reduced:
    "(m div 2 + 50*x) mod 100 = (m div 2 + 50*(x mod 2)) mod 100"
    using expansion by (simp only: expansion; simp add: mod_add_eq)
  show ?thesis using reduced result_bound by simp
qed

lemma mahler_decimal_even_add_quotient:
  fixes h m :: nat
  shows "(100*h + m) div 2 = 50*h + m div 2"
proof -
  have regroup: "(100*h + m) div 2 = (m + (50*h)*2) div 2"
    by (simp add: algebra_simps)
  have quotient: "(m + (50*h)*2) div 2 = m div 2 + 50*h"
    by (simp add: div_add_self2)
  show ?thesis using regroup quotient by (simp add: add.commute)
qed

theorem mahler_decimal_center_transfer:
  fixes D L C U V s c :: nat
  assumes low_bound: "L < 10^s"
      and center_bound: "C < 100"
      and upper_parity_bound: "U < 2"
      and decomposition: "D = L + 10^s*C + 10^(s+2)*V"
      and upper_parity: "U = V mod 2"
      and authenticated_low_carry:
        "c = (3*L + D mod 2) div (10^s)"
      and carry_bound: "c \<le> 2"
  shows "(((3*D + D mod 2) div 2) div (10^s)) mod 100 =
    mahler_center_next C c U"
proof -
  let ?B = "(10::nat)^s"
  let ?e = "D mod 2"
  let ?r = "(3*L + ?e) mod ?B"
  let ?center = "3*C+c"
  have positive: "0 < (10::nat)^s" by simp
  have remainder: "?r < ?B"
    by (rule mod_less_divisor) simp
  have low_split: "3*L + ?e = ?B*c + ?r"
    using authenticated_low_carry
    by (metis div_mult_mod_eq mult.commute)
  have upper_power: "(10::nat)^(s+2) = ?B*100"
    by (simp add: power_add algebra_simps)
  have numerator:
      "3*D + ?e = ?B*(?center + 300*V) + ?r"
  proof -
    have triple_decomposition:
        "3*D = 3*(L + ?B*C + 10^(s+2)*V)"
      using arg_cong[OF decomposition, of "\<lambda>n. 3*n"] .
    have expanded:
        "3*D + ?e = (3*L + ?e) + ?B*(3*C + 300*V)"
      using triple_decomposition upper_power
      by (simp only: triple_decomposition upper_power; simp add: algebra_simps)
    have replace_low:
        "(3*L + ?e) + ?B*(3*C + 300*V) =
          (?B*c + ?r) + ?B*(3*C + 300*V)"
      using arg_cong[OF low_split, of "\<lambda>x. x + ?B*(3*C + 300*V)"] .
    show ?thesis
      using expanded replace_low
      by (simp only: expanded replace_low; simp add: algebra_simps)
  qed
  have block_quotient:
      "(3*D + ?e) div (2*?B) = (?center + 300*V) div 2"
    using numerator mahler_pair_block_quotient[OF positive remainder] by simp
  have extraction:
      "(((3*D + ?e) div 2) div ?B) = (?center + 300*V) div 2"
    using block_quotient by (simp only: div_mult2_eq)
  let ?h = "?center div 100 + 3*V"
  let ?m = "?center mod 100"
  have center_split:
      "?center + 300*V = 100*?h + ?m"
    using div_mult_mod_eq[of ?center 100] by (simp add: mult.commute algebra_simps)
  have centered_quotient:
      "(?center + 300*V) div 2 = (100*?h + ?m) div 2"
    using arg_cong[OF center_split, of "\<lambda>n. n div 2"] .
  have quotient_split:
      "(100*?h + ?m) div 2 = 50*?h + ?m div 2"
    by (rule mahler_decimal_even_add_quotient)
  have halved:
      "(?center + 300*V) div 2 =
        ?center mod 100 div 2 + 50*(?center div 100 + 3*V)"
    using centered_quotient quotient_split by (simp add: add.commute)
  have triple_parity: "(3*V) mod 2 = U"
  proof -
    have "(3*V) mod 2 = ((3 mod 2)*(V mod 2)) mod 2"
      by (rule mod_mult_eq[symmetric])
    also have "... = V mod 2" by simp
    also have "... = U" by (rule upper_parity[symmetric])
    finally show ?thesis .
  qed
  have parity:
      "?h mod 2 = (U + ?center div 100) mod 2"
  proof -
    have "(?center div 100 + 3*V) mod 2 =
        (?center div 100 mod 2 + (3*V) mod 2) mod 2"
      by (rule mod_add_eq[symmetric])
    also have "... = (?center div 100 mod 2 + U) mod 2"
      by (simp only: triple_parity)
    also have "... = (?center div 100 mod 2 + V mod 2) mod 2"
      by (simp only: upper_parity)
    also have "... = (V mod 2 + ?center div 100 mod 2) mod 2"
      by (simp add: add.commute)
    also have "... = (U + ?center div 100) mod 2"
      by (simp only: upper_parity mod_add_right_eq)
    finally show ?thesis .
  qed
  have center_remainder_bound: "?m < 100" by simp
  have residue_base:
      "(?m div 2 + 50*?h) mod 100 = ?m div 2 + 50*(?h mod 2)"
    by (rule mahler_center_half_residue[OF center_remainder_bound])
  have residue:
      "(?m div 2 + 50*?h) mod 100 =
        ?m div 2 + 50*((U + ?center div 100) mod 2)"
    using residue_base parity by simp
  show ?thesis
    using extraction halved residue
    by (simp add: mahler_center_next_def)
qed

corollary mahler_decimal_source_center_projection:
  fixes D s :: nat
  shows "mahler_center_next
      ((D div (10::nat)^s) mod 100)
      ((3*(D mod (10::nat)^s) + D mod 2) div (10::nat)^s)
      ((D div (10::nat)^(s+2)) mod 2) =
    (((3*D + D mod 2) div 2) div (10::nat)^s) mod 100"
proof -
  let ?B = "(10::nat)^s"
  let ?L = "D mod ?B"
  let ?C = "(D div ?B) mod 100"
  let ?V = "D div (10::nat)^(s+2)"
  let ?U = "?V mod 2"
  let ?c = "(3*?L + D mod 2) div ?B"
  have positive: "0 < ?B" by simp
  have low_bound: "?L < ?B" by (rule mod_less_divisor) simp
  have center_bound: "?C < 100" by simp
  have upper_bound: "?U < 2" by simp
  have upper_power: "(10::nat)^(s+2) = ?B*100"
    by (simp add: power_add algebra_simps)
  have source_split: "D = ?L + ?B*(D div ?B)"
    using div_mult_mod_eq[of D ?B] by (simp add: add.commute mult.commute)
  have quotient_low:
      "D div ?B = ?C + 100*((D div ?B) div 100)"
    using div_mult_mod_eq[of "D div ?B" 100]
    by (simp add: add.commute mult.commute)
  have quotient_high: "(D div ?B) div 100 = ?V"
    by (simp only: div_mult2_eq upper_power)
  have quotient_split:
      "D div ?B = ?C + 100*?V"
  proof -
    have "D div ?B = ?C + 100*((D div ?B) div 100)"
      by (rule quotient_low)
    also have "... = ?C + 100*?V"
      by (simp only: quotient_high)
    finally show ?thesis .
  qed
  have quotient_replacement:
      "?L + ?B*(D div ?B) = ?L + ?B*(?C + 100*?V)"
    using arg_cong[OF quotient_split, of "\<lambda>q. ?L + ?B*q"] .
  have power_replacement:
      "?L + ?B*(?C + 100*?V) = ?L + ?B*?C + (10::nat)^(s+2)*?V"
    using upper_power by (simp add: algebra_simps)
  have decomposition:
      "D = ?L + ?B*?C + (10::nat)^(s+2)*?V"
  proof -
    have "D = ?L + ?B*(D div ?B)" by (rule source_split)
    also have "... = ?L + ?B*(?C + 100*?V)"
      by (rule quotient_replacement)
    also have "... = ?L + ?B*?C + (10::nat)^(s+2)*?V"
      by (rule power_replacement)
    finally show ?thesis .
  qed
  have numerator_bound: "3*?L + D mod 2 < 3*?B"
  proof -
    have source_parity_bound: "D mod 2 < 2" by simp
    show ?thesis using low_bound source_parity_bound by arith
  qed
  have carry_lt: "?c < 3"
    using numerator_bound positive
    by (simp only: div_less_iff_less_mult[OF positive]; simp add: mult.commute)
  have carry_bound: "?c \<le> 2" using carry_lt by arith
  have upper_parity: "?U = ?V mod 2" by simp
  have carry_equation: "?c = (3*?L + D mod 2) div ?B" by simp
  have transfer:
      "(((3*D + D mod 2) div 2) div ?B) mod 100 =
        mahler_center_next ?C ?c ?U"
    by (rule mahler_decimal_center_transfer[OF low_bound center_bound
        upper_bound decomposition upper_parity carry_equation carry_bound])
  show ?thesis using transfer by (rule sym)
qed

lemma mahler_decimal_source_blocks:
  fixes D s :: nat
  shows "D = D mod (10::nat)^s
    + (10::nat)^s * ((D div (10::nat)^s) mod 100)
    + (10::nat)^(s+2) * (D div (10::nat)^(s+2))"
proof -
  let ?B = "(10::nat)^s"
  let ?L = "D mod ?B"
  let ?C = "(D div ?B) mod 100"
  let ?U = "D div (10::nat)^(s+2)"
  have upper_power: "(10::nat)^(s+2) = ?B*100"
    by (simp add: power_add algebra_simps)
  have source_split: "D = ?L + ?B*(D div ?B)"
    using div_mult_mod_eq[of D ?B] by (simp add: add.commute mult.commute)
  have quotient_low:
      "D div ?B = ?C + 100*((D div ?B) div 100)"
    using div_mult_mod_eq[of "D div ?B" 100]
    by (simp add: add.commute mult.commute)
  have quotient_high: "(D div ?B) div 100 = ?U"
    by (simp only: div_mult2_eq upper_power)
  have quotient_split: "D div ?B = ?C + 100*?U"
  proof -
    have "D div ?B = ?C + 100*((D div ?B) div 100)"
      by (rule quotient_low)
    also have "... = ?C + 100*?U"
      by (simp only: quotient_high)
    finally show ?thesis .
  qed
  have quotient_replacement:
      "?L + ?B*(D div ?B) = ?L + ?B*(?C + 100*?U)"
    using arg_cong[OF quotient_split, of "\<lambda>q. ?L + ?B*q"] .
  have power_replacement:
      "?L + ?B*(?C + 100*?U) = ?L + ?B*?C + (10::nat)^(s+2)*?U"
    using upper_power by (simp add: algebra_simps)
  have "D = ?L + ?B*(D div ?B)" by (rule source_split)
  also have "... = ?L + ?B*(?C + 100*?U)"
    by (rule quotient_replacement)
  also have "... = ?L + ?B*?C + (10::nat)^(s+2)*?U"
    by (rule power_replacement)
  finally show ?thesis .
qed

lemma mahler_decimal_low_carry_block_decomposition:
  fixes D L C U B c :: nat
  assumes positive: "0 < B"
      and low_bound: "L < B"
      and decomposition: "D = L + B*C + 100*B*U"
      and authenticated_carry: "c = (3*L + D mod 2) div B"
  shows "3*D + D mod 2 =
    B*(3*C + c + 300*U) + (3*L + D mod 2) mod B"
proof -
  let ?r = "(3*L + D mod 2) mod B"
  have low_split: "3*L + D mod 2 = B*c + ?r"
    using authenticated_carry
    by (metis div_mult_mod_eq mult.commute)
  have triple_decomposition:
      "3*D + D mod 2 = 3*L + D mod 2 + B*(3*C + 300*U)"
    using decomposition by (simp add: algebra_simps)
  have low_replacement:
      "(3*L + D mod 2) + B*(3*C + 300*U) =
        (B*c + ?r) + B*(3*C + 300*U)"
    using arg_cong[OF low_split,
      of "\<lambda>x. x + B*(3*C + 300*U)"] .
  have "3*D + D mod 2 = (3*L + D mod 2) + B*(3*C + 300*U)"
    by (rule triple_decomposition)
  also have "... = (B*c + ?r) + B*(3*C + 300*U)"
    by (rule low_replacement)
  also have "... = B*(3*C + c + 300*U) + ?r"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma mahler_decimal_upper_block_projection:
  fixes D L C U B c :: nat
  assumes positive: "0 < B"
      and low_bound: "L < B"
      and decomposition: "D = L + B*C + 100*B*U"
      and authenticated_carry: "c = (3*L + D mod 2) div B"
  shows "(((3*D + D mod 2) div 2) div (100*B)) =
    (3*U + (3*C+c) div 100) div 2"
proof -
  let ?N = "3*D + D mod 2"
  let ?X = "3*C + c + 300*U"
  let ?r = "(3*L + D mod 2) mod B"
  let ?m = "(3*C+c) mod 100"
  let ?K = "3*U + (3*C+c) div 100"
  have numerator:
      "?N = B*?X + ?r"
    using mahler_decimal_low_carry_block_decomposition
      [OF positive low_bound decomposition authenticated_carry]
    by (simp add: algebra_simps)
  have remainder: "?r < B"
    by (rule mod_less_divisor[OF positive])
  have block_quotient: "?N div (2*B) = ?X div 2"
    using numerator mahler_pair_block_quotient[OF positive remainder] by simp
  have extraction: "(?N div 2) div B = ?X div 2"
    using block_quotient by (simp only: div_mult2_eq)
  have center_split: "?X = 100*?K + ?m"
    using div_mult_mod_eq[of "3*C+c" 100]
    by (simp add: mult.commute algebra_simps)
  have centered_quotient: "?X div 2 = (100*?K + ?m) div 2"
    using arg_cong[OF center_split, of "\<lambda>n. n div 2"] .
  have half_quotient: "(100*?K + ?m) div 2 = 50*?K + ?m div 2"
    by (rule mahler_decimal_even_add_quotient)
  have residue_bound: "?m div 2 < 50"
    using mod_less_divisor[of "3*C+c" 100] by arith
  have positive50: "0 < (50::nat)" by simp
  have upper_quotient: "(50*?K + ?m div 2) div 100 = ?K div 2"
    using mahler_pair_block_quotient[OF positive50 residue_bound] by simp
  have nested_quotient:
      "(?N div 2) div (100*B) = ((?N div 2) div B) div 100"
    by (simp only: div_mult2_eq[symmetric]; simp add: mult.commute)
  show ?thesis
    using nested_quotient extraction centered_quotient half_quotient
      upper_quotient
    by (simp only: nested_quotient extraction centered_quotient
        half_quotient upper_quotient)
qed

corollary mahler_decimal_source_bilateral_port_projection:
  fixes D s :: nat
  shows "((3*(D mod (10::nat)^s) + D mod 2) div (10::nat)^s) \<le> 2"
    "mahler_D_step D =
      (mahler_D_step D mod (10::nat)^s)
      + (10::nat)^s * mahler_center_next
          ((D div (10::nat)^s) mod 100)
          ((3*(D mod (10::nat)^s) + D mod 2) div (10::nat)^s)
          ((D div (10::nat)^(s+2)) mod 2)
      + (100*(10::nat)^s) *
          ((3*(D div (10::nat)^(s+2))
            + (3*((D div (10::nat)^s) mod 100)
              + (3*(D mod (10::nat)^s) + D mod 2)
                div (10::nat)^s) div 100) div 2)"
proof -
  let ?B = "(10::nat)^s"
  let ?L = "D mod ?B"
  let ?C = "(D div ?B) mod 100"
  let ?U = "D div (10::nat)^(s+2)"
  let ?c = "(3*?L + D mod 2) div ?B"
  let ?N = "3*D + D mod 2"
  let ?Q = "?N div 2"
  let ?next_center = "mahler_center_next ?C ?c (?U mod 2)"
  let ?next_upper = "(3*?U + (3*?C+?c) div 100) div 2"
  have positive: "0 < ?B" by simp
  have low_bound: "?L < ?B" by (rule mod_less_divisor) simp
  have center_bound: "?C < 100" by simp
  have decomposition:
      "D = ?L + ?B*?C + 100*?B*?U"
    using mahler_decimal_source_blocks[of D s]
    by (simp add: power_add algebra_simps)
  have carry_equation: "?c = (3*?L + D mod 2) div ?B" by simp
  have numerator_bound: "3*?L + D mod 2 < 3*?B"
  proof -
    have parity_bound: "D mod 2 < 2" by simp
    show ?thesis using low_bound parity_bound by arith
  qed
  have carry_lt: "?c < 3"
    using numerator_bound positive
    by (simp only: div_less_iff_less_mult[OF positive]; simp add: mult.commute)
  have carry_bound: "?c \<le> 2" using carry_lt by arith
  have center_projection:
      "?next_center = (?Q div ?B) mod 100"
    by (rule mahler_decimal_source_center_projection)
  have upper_projection:
      "?Q div (100*?B) = ?next_upper"
    by (rule mahler_decimal_upper_block_projection
        [OF positive low_bound decomposition carry_equation])
  have q_split: "?Q = ?Q mod ?B + ?B*(?Q div ?B)"
    using div_mult_mod_eq[of ?Q ?B]
    by (simp add: add.commute mult.commute)
  have middle_split:
      "?Q div ?B = (?Q div ?B) mod 100 + 100*((?Q div ?B) div 100)"
    using div_mult_mod_eq[of "?Q div ?B" 100]
    by (simp add: add.commute mult.commute)
  have nested_order:
      "(?Q div ?B) div 100 = (?Q div 100) div ?B"
  proof -
    have left_product: "(?Q div ?B) div 100 = ?Q div (?B*100)"
      by (rule div_mult2_eq[symmetric])
    have right_product: "(?Q div 100) div ?B = ?Q div (100*?B)"
      by (rule div_mult2_eq[symmetric])
    show ?thesis using left_product right_product by (simp add: mult.commute)
  qed
  have nested_upper:
      "(?Q div ?B) div 100 = ?Q div (100*?B)"
  proof -
    have upper_product: "(?Q div 100) div ?B = ?Q div (100*?B)"
      by (rule div_mult2_eq[symmetric])
    show ?thesis using nested_order upper_product by simp
  qed
  have middle_projection:
      "?Q div ?B = ?next_center + 100*?next_upper"
    using middle_split center_projection nested_upper upper_projection by arith
  have source_split:
      "?Q = (?Q mod ?B) + ?B*?next_center + 100*?B*?next_upper"
  proof -
    have middle_product:
        "?B*(?Q div ?B) = ?B*?next_center + 100*?B*?next_upper"
      using arg_cong[OF middle_projection, of "\<lambda>x. ?B*x"]
      by (simp only: algebra_simps)
    have "?Q = ?Q mod ?B + ?B*(?Q div ?B)"
      by (rule q_split)
    also have "... = ?Q mod ?B + (?B*?next_center + 100*?B*?next_upper)"
      using arg_cong[OF middle_product, of "\<lambda>x. ?Q mod ?B + x"] .
    also have "... = ?Q mod ?B + ?B*?next_center + 100*?B*?next_upper"
      by (simp only: algebra_simps)
    finally show ?thesis .
  qed
  have source_step: "mahler_D_step D = ?Q"
    by (rule mahler_D_step_parity)
  have source_mod:
      "?Q mod ?B = (mahler_D_step D mod ?B)"
    using arg_cong[OF source_step, of "\<lambda>x. x mod ?B"] by (rule sym)
  have output_replacement:
      "?Q mod ?B + ?B*?next_center + 100*?B*?next_upper =
        (mahler_D_step D mod ?B) + ?B*?next_center + 100*?B*?next_upper"
    using arg_cong[OF source_mod,
      of "\<lambda>x. x + ?B*?next_center + 100*?B*?next_upper"] .
  show "?c \<le> 2" by (rule carry_bound)
  show "mahler_D_step D =
      (mahler_D_step D mod ?B) + ?B*?next_center + (100*?B)*?next_upper"
  proof -
    have "mahler_D_step D = ?Q" by (rule source_step)
    also have "... = ?Q mod ?B + ?B*?next_center + 100*?B*?next_upper"
      by (rule source_split)
    also have "... =
        (mahler_D_step D mod ?B) + ?B*?next_center + (100*?B)*?next_upper"
      by (rule output_replacement)
    finally show
        "mahler_D_step D =
          (mahler_D_step D mod ?B) + ?B*?next_center + (100*?B)*?next_upper" .
  qed
qed

theorem centered_return_commutes:
  "antihydra_h_step (D+1) = mahler_D_step D + 1"
  by (cases D rule: nat_mod_two_cases;
      simp add: antihydra_h_step_def mahler_D_step_def algebra_simps mod_Suc)

definition mahler_X :: "nat \<Rightarrow> int" where
  "mahler_X D = 2*int D + 1"

definition mahler_sigma :: "nat \<Rightarrow> int" where
  "mahler_sigma D = 1 - 2*int (D mod 2)"

theorem mahler_balanced_action:
  "2 * mahler_X (mahler_D_step D) = 3 * mahler_X D - mahler_sigma D"
  by (cases D rule: nat_mod_two_cases;
      simp add: mahler_X_def mahler_sigma_def mahler_D_step_def
        algebra_simps mod_Suc)

theorem mahler_D_step_even_lift:
  "mahler_D_step (D + 2*k) = mahler_D_step D + 3*k"
  by (cases D rule: nat_mod_two_cases;
      simp add: mahler_D_step_def algebra_simps)

definition mahler_radix4_low_translation :: "nat \<Rightarrow> nat" where
  "mahler_radix4_low_translation d = mahler_D_step (mahler_D_step d)"

theorem mahler_radix4_two_tick_reentry:
  "mahler_D_step (mahler_D_step (d + 4*M)) =
    mahler_radix4_low_translation d + 9*M"
proof -
  have lower: "mahler_D_step (d + 4*M) = mahler_D_step d + 6*M"
    using mahler_D_step_even_lift[of d "2*M"]
    by (simp add: algebra_simps)
  have upper: "mahler_D_step (mahler_D_step d + 6*M) =
      mahler_D_step (mahler_D_step d) + 9*M"
    using mahler_D_step_even_lift[of "mahler_D_step d" "3*M"]
    by (simp add: algebra_simps)
  have lifted:
      "mahler_D_step (mahler_D_step (d + 4*M)) =
        mahler_D_step (mahler_D_step d + 6*M)"
    by (simp only: lower)
  show ?thesis
    using lifted upper by (simp add: mahler_radix4_low_translation_def)
qed

lemma mahler_radix4_low_translation_table:
  "mahler_radix4_low_translation 0 = 0"
  "mahler_radix4_low_translation 1 = 3"
  "mahler_radix4_low_translation 2 = 5"
  "mahler_radix4_low_translation 3 = 8"
  by (simp_all add: mahler_radix4_low_translation_def mahler_D_step_def)

theorem mahler_radix4_two_tick_finite_block_projection:
  assumes "d < 4"
  shows "mahler_D_step (mahler_D_step (d + 4*M)) div (4::nat)^k =
      9*(M div (4::nat)^k) +
        (mahler_radix4_low_translation d
          + 9*(M mod (4::nat)^k)) div (4::nat)^k"
proof -
  let ?B = "(4::nat)^k"
  have source_split: "M = M mod ?B + ?B*(M div ?B)"
    using div_mult_mod_eq[of M ?B] by (simp add: add.commute mult.commute)
  have scaled_source:
      "9*M = 9*(M mod ?B) + ?B*(9*(M div ?B))"
  proof -
    have "9*M = 9*(M mod ?B + ?B*(M div ?B))"
      using arg_cong[OF source_split, of "\<lambda>x. 9*x"] .
    also have "... = 9*(M mod ?B) + ?B*(9*(M div ?B))"
      by (simp only: algebra_simps)
    finally show ?thesis .
  qed
  have numerator_split:
      "mahler_radix4_low_translation d + 9*M =
        ?B*(9*(M div ?B)) +
          (mahler_radix4_low_translation d + 9*(M mod ?B))"
    using scaled_source by (simp only: algebra_simps)
  have reentry: "mahler_D_step (mahler_D_step (d + 4*M)) =
      mahler_radix4_low_translation d + 9*M"
    by (rule mahler_radix4_two_tick_reentry)
  show ?thesis
    using reentry numerator_split
    by (simp only: reentry numerator_split; simp add: div_add_self2)
qed

record antihydra_skew =
  sk_width :: nat
  sk_A :: int
  sk_D :: int
  sk_J :: int
  sk_delta :: int
  sk_minprefix :: int

definition skew_identity :: antihydra_skew where
  "skew_identity = \<lparr>sk_width=0, sk_A=1, sk_D=1, sk_J=0,
    sk_delta=0, sk_minprefix=0\<rparr>"

definition skew_valid :: "antihydra_skew \<Rightarrow> bool" where
  "skew_valid g \<longleftrightarrow>
    sk_minprefix g \<le> 0 \<and> sk_minprefix g \<le> sk_delta g"

definition skew_then :: "antihydra_skew \<Rightarrow> antihydra_skew \<Rightarrow> antihydra_skew" where
  "skew_then a b = \<lparr>
    sk_width = sk_width a + sk_width b,
    sk_A = sk_A b * sk_A a,
    sk_D = sk_D b * sk_D a,
    sk_J = sk_A b * sk_J a + sk_J b * sk_D a,
    sk_delta = sk_delta a + sk_delta b,
    sk_minprefix = min (sk_minprefix a) (sk_delta a + sk_minprefix b)\<rparr>"

lemma skew_then_identity [simp]:
  assumes "skew_valid a"
  shows "skew_then skew_identity a = a" "skew_then a skew_identity = a"
  using assms by (simp_all add: skew_valid_def skew_then_def
      skew_identity_def antihydra_skew.equality min_def)

lemma skew_then_valid:
  assumes "skew_valid a" "skew_valid b"
  shows "skew_valid (skew_then a b)"
  using assms by (auto simp: skew_valid_def skew_then_def min_def)

theorem skew_then_assoc:
  "skew_then (skew_then a b) c = skew_then a (skew_then b c)"
  by (simp add: skew_then_def antihydra_skew.equality min.assoc
      min_def algebra_simps)

definition skew_numerator :: "antihydra_skew \<Rightarrow> int \<Rightarrow> int" where
  "skew_numerator g x = sk_A g*x + sk_J g"

theorem skew_numerator_composition:
  "skew_numerator (skew_then a b) x =
    sk_A b * skew_numerator a x + sk_J b * sk_D a"
  by (simp add: skew_numerator_def skew_then_def algebra_simps)

text \<open>This projection forgets width and ledger geometry only for linear
arithmetic observations; it does not authorize guarded action substitution.\<close>

definition antihydra_linear_projection ::
    "antihydra_skew \<Rightarrow> int skew_transfer" where
  "antihydra_linear_projection g =
    \<lparr>upper = sk_A g, offset = sk_J g, lower = sk_D g\<rparr>"

lemma antihydra_linear_projection_identity:
  "antihydra_linear_projection skew_identity = shared_skew_identity"
  by (simp add: antihydra_linear_projection_def
      skew_identity_def shared_skew_identity_def)

lemma antihydra_linear_projection_then:
  "antihydra_linear_projection (skew_then a b) = shared_skew_then
    (antihydra_linear_projection a) (antihydra_linear_projection b)"
  by (cases a; cases b)
    (simp add: antihydra_linear_projection_def skew_then_def
      shared_skew_then_def algebra_simps)

lemma antihydra_linear_projection_numerator:
  "skew_numerator g x = upper (antihydra_linear_projection g) * x +
    offset (antihydra_linear_projection g)"
  by (simp add: skew_numerator_def antihydra_linear_projection_def)

theorem skew_minprefix_composition:
  "sk_minprefix (skew_then a b) =
    min (sk_minprefix a) (sk_delta a + sk_minprefix b)"
  by (simp add: skew_then_def)

text \<open>The atom is indexed by the physical return branch bit b=h mod 2.
Thus J=-b, while the ledger change is +2 on b=0 and -1 on b=1.  The Mahler
epsilon used in the source-barrier theory is D mod 2=1-b.\<close>

definition skew_atom :: "nat \<Rightarrow> antihydra_skew" where
  "skew_atom b = \<lparr>sk_width=1, sk_A=3, sk_D=2, sk_J= - int b,
    sk_delta=2-3*int b, sk_minprefix=min 0 (2-3*int b)\<rparr>"

fun skew_word :: "nat list \<Rightarrow> antihydra_skew" where
  "skew_word [] = skew_identity"
| "skew_word (e#es) = skew_then (skew_atom e) (skew_word es)"

fun ledger_word_delta :: "nat list \<Rightarrow> int" where
  "ledger_word_delta [] = 0"
| "ledger_word_delta (b#bs) = 2-3*int b + ledger_word_delta bs"

fun ledger_word_minprefix :: "nat list \<Rightarrow> int" where
  "ledger_word_minprefix [] = 0"
| "ledger_word_minprefix (b#bs) =
    min (min 0 (2-3*int b)) (2-3*int b + ledger_word_minprefix bs)"

lemma skew_atom_valid [simp]: "skew_valid (skew_atom e)"
  by (simp add: skew_valid_def skew_atom_def min_def)

lemma skew_word_valid [simp]: "skew_valid (skew_word es)"
proof (induct es)
  case Nil
  then show ?case by (simp add: skew_identity_def skew_valid_def)
next
  case (Cons e es)
  show ?case
    by (simp only: skew_word.simps; rule skew_then_valid[OF skew_atom_valid Cons])
qed

theorem skew_word_append:
  "skew_word (xs @ ys) = skew_then (skew_word xs) (skew_word ys)"
  by (induct xs) (simp_all add: skew_then_assoc)

theorem skew_word_induces_ledger_geometry:
  "sk_delta (skew_word es) = ledger_word_delta es"
  "sk_minprefix (skew_word es) = ledger_word_minprefix es"
  by (induct es) (simp_all add: skew_identity_def skew_atom_def skew_then_def)

definition one_return_h :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "one_return_h b x = 3*x+b"

definition one_return_ledger :: "nat \<Rightarrow> int \<Rightarrow> int" where
  "one_return_ledger b a = a + (if b=0 then 2 else -1)"

definition one_return_physical_roof4 :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int" where
  "one_return_physical_roof4 b x a =
    (if b=0 then 12*int x^2 + 8*a - 4 else 12*int x^2 - 28)"

theorem one_return_skew_equation:
  assumes "b < 2"
  shows "2 * int (one_return_h b x) = 3 * int (2*x+b) - int b"
  using assms by (simp add: one_return_h_def algebra_simps)

theorem one_return_kernel_coefficients:
  "one_return_physical_roof4 0 x a = 12*int x^2 + 8*a - 4"
  "one_return_physical_roof4 1 x a = 12*int x^2 - 28"
  "one_return_ledger 0 a = a+2"
  "one_return_ledger 1 a = a-1"
  by (simp_all add: one_return_physical_roof4_def one_return_ledger_def)

text \<open>The roof equations above match the production width-one kernel on
its safe nonhalting domain.  In particular, the odd branch requires incoming
ledger at least one; ledger zero follows the separate terminal F/0 roof and is
not described by the odd polynomial above.  These equations do not prove that
the compressed section grammar realizes the counts from every literal tape
A(a,b).  That parametric literal-to-macro simulation lemma remains required
before a nonhalting result may cross the TM boundary.\<close>

lemma source_seven_is_blank_return_center:
  "7 + 1 = (8::nat)"
  by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms antihydra_linear_projection_identity antihydra_linear_projection_then
      antihydra_linear_projection_numerator nat_mod_two_cases mahler_D_step_parity centered_return_commutes
      mahler_balanced_action mahler_D_step_even_lift
      mahler_pair_block_quotient mahler_center_half_residue
      mahler_decimal_even_add_quotient
      mahler_decimal_center_transfer mahler_decimal_source_center_projection
      mahler_decimal_source_blocks mahler_decimal_low_carry_block_decomposition
      mahler_decimal_upper_block_projection
      mahler_decimal_source_bilateral_port_projection
      mahler_radix4_two_tick_reentry mahler_radix4_low_translation_table
      mahler_radix4_two_tick_finite_block_projection
      skew_then_identity skew_then_valid skew_then_assoc
      skew_numerator_composition skew_minprefix_composition
      skew_atom_valid skew_word_valid skew_word_append
      skew_word_induces_ledger_geometry
      one_return_skew_equation one_return_kernel_coefficients
      source_seven_is_blank_return_center}) then ()
    else error "Antihydra Mahler/skew proof depends on an oracle";
\<close>

end
