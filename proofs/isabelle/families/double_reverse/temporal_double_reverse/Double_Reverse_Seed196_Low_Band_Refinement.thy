theory Double_Reverse_Seed196_Low_Band_Refinement
  imports Double_Reverse_Decimal_Source_Carry_Mask
begin

text \<open>The seed-196 low-band action follows from the exact source carry
mask, its two-step affine recurrence, and finite Boolean guard closures.
It proves only the admitted low four digits.\<close>

definition double_reverse_seed196_first_pair_low6 :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "double_reverse_seed196_first_pair_low6 u upper_high =
    nat ((40 * int u - 198 * int
      (double_reverse_decimal_threshold_mask u +
        (if upper_high then 100000 else 0))) mod (1000000::int))"

definition double_reverse_seed196_phi5 :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "double_reverse_seed196_phi5 u upper_high =
    nat ((4 * int (double_reverse_seed196_first_pair_low6 u upper_high) -
      198 * int (double_reverse_decimal_threshold_mask
        (double_reverse_seed196_first_pair_low6 u upper_high) div 10))
        mod (100000::int))"

definition double_reverse_seed196_j4 :: "nat \<Rightarrow> bool \<Rightarrow> nat" where
  "double_reverse_seed196_j4 u upper_high =
    (4 * double_reverse_decimal_threshold_mask u +
      double_reverse_decimal_threshold_mask
        (double_reverse_seed196_first_pair_low6 u upper_high) div 10)
      mod 10000"

definition double_reverse_seed196_entry_guards :: "nat set" where
  "double_reverse_seed196_entry_guards = {73488}"

definition double_reverse_seed196_first_guards :: "nat set" where
  "double_reverse_seed196_first_guards = {11568, 21568, 31568, 41568}"

definition double_reverse_seed196_second_guards :: "nat set" where
  "double_reverse_seed196_second_guards = {60988, 80988}"

definition double_reverse_seed196_third_guards :: "nat set" where
  "double_reverse_seed196_third_guards = {28388, 48388}"

definition double_reverse_seed196_phase_index :: "nat \<Rightarrow> nat" where
  "double_reverse_seed196_phase_index blocks =
    (if blocks = 0 then 0 else 1 + (blocks - 1) mod 3)"

definition double_reverse_seed196_phase_guards :: "nat \<Rightarrow> nat set" where
  "double_reverse_seed196_phase_guards blocks =
    (if double_reverse_seed196_phase_index blocks = 0 then
       double_reverse_seed196_entry_guards
     else if double_reverse_seed196_phase_index blocks = 1 then
       double_reverse_seed196_first_guards
     else if double_reverse_seed196_phase_index blocks = 2 then
       double_reverse_seed196_second_guards
     else double_reverse_seed196_third_guards)"

lemma double_reverse_seed196_phase_index_bound:
  "double_reverse_seed196_phase_index blocks \<le> 3"
  unfolding double_reverse_seed196_phase_index_def by auto

lemma double_reverse_seed196_phase_index_successor:
  "double_reverse_seed196_phase_index (Suc blocks) =
    (if double_reverse_seed196_phase_index blocks = 3 then 1
     else Suc (double_reverse_seed196_phase_index blocks))"
proof (cases blocks)
  case 0
  then show ?thesis
    by (simp add: double_reverse_seed196_phase_index_def)
next
  case (Suc n)
  have next_remainder:
    "(Suc n) mod 3 = Suc (n mod 3) mod 3"
    by (rule mod_Suc_eq[symmetric])
  have remainder_bound: "n mod 3 < 3"
    by (rule mod_less_divisor) simp
  have remainder_cases:
    "n mod 3 = 0 \<or> n mod 3 = 1 \<or> n mod 3 = 2"
    using remainder_bound by arith
  from remainder_cases show ?thesis
  proof (elim disjE)
    assume zero: "n mod 3 = 0"
    show ?thesis using Suc next_remainder zero
      unfolding double_reverse_seed196_phase_index_def by simp
  next
    assume one: "n mod 3 = 1"
    show ?thesis using Suc next_remainder one
      unfolding double_reverse_seed196_phase_index_def by simp
  next
    assume two: "n mod 3 = 2"
    show ?thesis using Suc next_remainder two
      unfolding double_reverse_seed196_phase_index_def by simp
  qed
qed

lemma double_reverse_seed196_phase_guards_successor:
  "double_reverse_seed196_phase_guards (Suc blocks) =
    (if double_reverse_seed196_phase_index blocks = 0 then
       double_reverse_seed196_first_guards
     else if double_reverse_seed196_phase_index blocks = 1 then
       double_reverse_seed196_second_guards
     else if double_reverse_seed196_phase_index blocks = 2 then
       double_reverse_seed196_third_guards
     else double_reverse_seed196_first_guards)"
proof -
  have bound: "double_reverse_seed196_phase_index blocks \<le> 3"
    by (rule double_reverse_seed196_phase_index_bound)
  have cases:
    "double_reverse_seed196_phase_index blocks = 0 \<or>
      double_reverse_seed196_phase_index blocks = 1 \<or>
      double_reverse_seed196_phase_index blocks = 2 \<or>
      double_reverse_seed196_phase_index blocks = 3"
    using bound by arith
  from cases show ?thesis
    by (elim disjE; simp_all add: double_reverse_seed196_phase_guards_def
      double_reverse_seed196_phase_index_successor)
qed

lemmas double_reverse_seed196_guard_step_simp =
  double_reverse_seed196_phi5_def double_reverse_seed196_j4_def
  double_reverse_seed196_first_pair_low6_def
  double_reverse_decimal_threshold_mask.simps
  double_reverse_decimal_threshold_mask_step double_reverse_decimal_threshold_mask_div
  double_reverse_decimal_threshold_mask_mod threshold5_digit_def

lemma double_reverse_seed196_entry_guard_step:
  assumes "u \<in> double_reverse_seed196_entry_guards"
  shows "double_reverse_seed196_phi5 u upper_high \<in>
      double_reverse_seed196_first_guards"
    and "double_reverse_seed196_j4 u upper_high = 1144"
    and "double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42"
    and "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 7342"
proof -
  have outcomes:
    "double_reverse_seed196_phi5 u upper_high \<in>
        double_reverse_seed196_first_guards
      \<and> double_reverse_seed196_j4 u upper_high = 1144
      \<and> double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42
      \<and> double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 7342"
    using assms
    by (simp only: double_reverse_seed196_entry_guards_def insert_iff empty_iff;
        cases upper_high; simp_all add: double_reverse_seed196_first_guards_def
          double_reverse_seed196_guard_step_simp)
  show "double_reverse_seed196_phi5 u upper_high \<in>
      double_reverse_seed196_first_guards" and
    "double_reverse_seed196_j4 u upper_high = 1144" and
    "double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42" and
    "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 7342"
    using outcomes by simp_all
qed

lemma double_reverse_seed196_guard_unit_digit:
  assumes "u \<in> double_reverse_seed196_entry_guards \<union>
      double_reverse_seed196_first_guards \<union>
      double_reverse_seed196_second_guards \<union>
      double_reverse_seed196_third_guards"
  shows "u mod 10 = 8"
  using assms
  by (auto simp: double_reverse_seed196_entry_guards_def
      double_reverse_seed196_first_guards_def
      double_reverse_seed196_second_guards_def
      double_reverse_seed196_third_guards_def)

lemma double_reverse_seed196_first_pair_source_exact:
  assumes low: "n mod 100000 = u"
      and unit: "u mod 10 = 8"
  shows "double_reverse_T_run 2 n mod 1000000 =
    double_reverse_seed196_first_pair_low6 u
      (threshold5_digit ((n div 100000) mod 10) = 1)"
proof -
  let ?source = "double_reverse_decimal_source n"
  let ?upper = "(n div 100000) mod 10"
  let ?mask = "double_reverse_decimal_threshold_mask"
  have ten_dvd_100000: "10 dvd (100000::nat)"
    by simp
  have low_unit_mod:
    "(n mod 100000) mod 10 = n mod 10"
    by (rule mod_mod_cancel[OF ten_dvd_100000])
  have unit_source: "n mod 10 = 8"
    using low unit low_unit_mod by simp
  have positive: "n > 0"
    using unit_source by (cases n) auto
  have canonical: "double_reverse_canonical_source ?source"
    using double_reverse_decimal_source_canonical[OF positive]
      unit_source by simp
  have source_value: "double_reverse_msf_value ?source = n"
    by (rule double_reverse_decimal_source_value)
  have source_mask: "double_reverse_source_carry_mask ?source = ?mask n"
    by (rule double_reverse_decimal_threshold_mask_source)
  have source_last: "last ?source = n mod 10"
    by (rule double_reverse_decimal_source_last)
  have growth: "threshold5_digit (last ?source) = 1"
    using source_last unit_source by (simp add: threshold5_digit_def)
  have affine:
    "int (double_reverse_T_run 2 n) = 40 * int n - 198 * int (?mask n)"
    using double_reverse_four_port_source_affine_carry[OF canonical]
      source_value source_mask growth by simp
  have upper_bound: "?upper < 10"
    by (rule mod_less_divisor) simp
  have source_low_bound: "n mod 100000 < 100000"
    by (rule mod_less_divisor) simp
  have u_bound: "u < 100000"
    using low source_low_bound by arith
  have low_six:
    "n mod 1000000 = u + 100000 * ?upper"
    using mod_mult2_eq[of n 100000 10] low by simp
  have low_six_parts:
    "(n mod 1000000) mod 100000 = u"
    "(n mod 1000000) div 100000 = ?upper"
  proof -
    have low_residue: "(u + 100000 * ?upper) mod 100000 = u"
      using u_bound by (simp add: mod_add_left_eq)
    have high_quotient: "(u + 100000 * ?upper) div 100000 = ?upper"
      using u_bound upper_bound by (simp add: div_add1_eq)
    show "(n mod 1000000) mod 100000 = u"
      using low_six low_residue by simp
    show "(n mod 1000000) div 100000 = ?upper"
      using low_six high_quotient by simp
  qed
  have source_mask_low:
    "?mask n mod 1000000 = ?mask (n mod 1000000)"
    using double_reverse_decimal_threshold_mask_mod_power[of n 6]
    by simp
  have split_low:
    "?mask (n mod 1000000) = ?mask u +
      100000 * ?mask ?upper"
    using double_reverse_decimal_threshold_mask_split_power[of
        "n mod 1000000" 5]
      low_six_parts by simp
  have upper_mask: "?mask ?upper = threshold5_digit ?upper"
    using upper_bound double_reverse_decimal_threshold_mask_step[of ?upper]
    by (simp add: threshold5_digit_def)
  have mask_congruence:
    "int (?mask n) mod 1000000 =
      int (?mask u + 100000 * threshold5_digit ?upper) mod 1000000"
  proof -
    have mask_nat_exact:
      "?mask n mod 1000000 =
        ?mask u + 100000 * threshold5_digit ?upper"
      using source_mask_low split_low upper_mask by simp
    have mask_nat_residue:
      "?mask n mod 1000000 =
        (?mask u + 100000 * threshold5_digit ?upper) mod 1000000"
    proof -
      have "(?mask n mod 1000000) mod 1000000 =
          (?mask u + 100000 * threshold5_digit ?upper) mod 1000000"
        by (rule arg_cong[where f="\<lambda>r::nat. r mod 1000000",
          OF mask_nat_exact])
      then show ?thesis by simp
    qed
    have mask_int_residue:
      "int (?mask n mod 1000000) =
        int ((?mask u + 100000 * threshold5_digit ?upper) mod 1000000)"
      by (rule arg_cong[where f="\<lambda>r::nat. int r", OF mask_nat_residue])
    show ?thesis using mask_int_residue
      by (simp only: of_nat_mod of_nat_numeral)
  qed
  have source_int_residue:
    "int (n mod 1000000) = int (u + 100000 * ?upper)"
    by (rule arg_cong[where f="\<lambda>r::nat. int r", OF low_six])
  have source_int_mod_exact:
    "int n mod (1000000::int) = int (u + 100000 * ?upper)"
    using source_int_residue by (simp add: of_nat_mod of_nat_numeral)
  have source_int_mod_residue:
    "(int n mod (1000000::int)) mod (1000000::int) =
      int (u + 100000 * ?upper) mod (1000000::int)"
    by (rule arg_cong[where f="\<lambda>r::int. r mod (1000000::int)",
      OF source_int_mod_exact])
  have source_mod_congruence:
    "int n mod (1000000::int) =
      int (u + 100000 * ?upper) mod (1000000::int)"
    using source_int_mod_residue by simp
  have n_congruence:
    "(40 * int n) mod (1000000::int) =
      (40 * int (u + 100000 * ?upper)) mod (1000000::int)"
    by (rule mod_mult_cong[OF refl source_mod_congruence])
  have mask_product_congruence:
    "(198 * int (?mask n)) mod (1000000::int) =
      (198 * int (?mask u + 100000 * threshold5_digit ?upper))
        mod (1000000::int)"
    by (rule mod_mult_cong[OF refl mask_congruence])
  have signed_congruence:
    "(40 * int n - 198 * int (?mask n)) mod (1000000::int) =
      (40 * int (u + 100000 * ?upper) -
        198 * int (?mask u + 100000 * threshold5_digit ?upper))
        mod (1000000::int)"
    by (rule mod_diff_cong[OF n_congruence mask_product_congruence])
  have upper_flag:
    "(if threshold5_digit ?upper = 1 then 100000 else 0) =
      100000 * threshold5_digit ?upper"
    using upper_bound by (auto simp: threshold5_digit_def)
  have target_integer:
    "int (double_reverse_seed196_first_pair_low6 u
        (threshold5_digit ?upper = 1)) =
      (40 * int u - 198 * int (?mask u +
        (if threshold5_digit ?upper = 1 then 100000 else 0))) mod 1000000"
    using upper_flag
    unfolding double_reverse_seed196_first_pair_low6_def
    by (simp add: algebra_simps)
  have source_sum_expansion:
    "40 * int (u + 100000 * ?upper) =
      40 * int u + 4000000 * int ?upper"
    by (simp add: algebra_simps)
  have upper_contribution_multiple:
    "(1000000::int) dvd 4000000 * int ?upper"
    unfolding dvd_def
    by (rule exI[of _ "4 * int ?upper"]) (simp add: algebra_simps)
  have upper_contribution_residue:
    "(4000000 * int ?upper) mod (1000000::int) =
      0 mod (1000000::int)"
    using upper_contribution_multiple by (simp add: dvd_eq_mod_eq_0)
  have source_growth_residue:
    "(40 * int (u + 100000 * ?upper)) mod (1000000::int) =
      (40 * int u) mod (1000000::int)"
  proof -
    have scaled_sum_residue:
      "(40 * int u + 4000000 * int ?upper) mod (1000000::int) =
        (40 * int u + 0) mod (1000000::int)"
      by (rule mod_add_cong[OF refl upper_contribution_residue])
    show ?thesis using source_sum_expansion scaled_sum_residue by simp
  qed
  have upper_flag_reverse:
    "100000 * threshold5_digit ?upper =
      (if threshold5_digit ?upper = 1 then 100000 else 0)"
    by (rule sym[OF upper_flag])
  have mask_argument_nat_equal:
    "?mask u + 100000 * threshold5_digit ?upper =
      ?mask u + (if threshold5_digit ?upper = 1 then 100000 else 0)"
    by (rule arg_cong[where f="\<lambda>r::nat. ?mask u + r",
      OF upper_flag_reverse])
  have mask_argument_int_equal:
    "int (?mask u + 100000 * threshold5_digit ?upper) =
      int (?mask u + (if threshold5_digit ?upper = 1 then 100000 else 0))"
    by (rule arg_cong[where f="\<lambda>r::nat. int r",
      OF mask_argument_nat_equal])
  have target_expression_equal:
    "40 * int u - 198 * int (?mask u + 100000 * threshold5_digit ?upper) =
      40 * int u - 198 * int (?mask u +
        (if threshold5_digit ?upper = 1 then 100000 else 0))"
    by (rule arg_cong[where f="\<lambda>r::int. 40 * int u - 198 * r",
      OF mask_argument_int_equal])
  have target_expression_residue:
    "(40 * int u -
        198 * int (?mask u + 100000 * threshold5_digit ?upper))
        mod (1000000::int) =
      (40 * int u - 198 * int (?mask u +
        (if threshold5_digit ?upper = 1 then 100000 else 0)))
        mod (1000000::int)"
    by (rule arg_cong[where f="\<lambda>r::int. r mod (1000000::int)",
      OF target_expression_equal])
  have output_mod:
    "int (double_reverse_T_run 2 n mod 1000000) =
      (40 * int n - 198 * int (?mask n)) mod 1000000"
    using affine by (simp only: of_nat_mod of_nat_numeral)
  have result_int:
    "int (double_reverse_T_run 2 n mod 1000000) =
      int (double_reverse_seed196_first_pair_low6 u
        (threshold5_digit ?upper = 1))"
  proof -
    have output_signed:
      "int (double_reverse_T_run 2 n mod 1000000) =
        (40 * int (u + 100000 * ?upper) -
          198 * int (?mask u + 100000 * threshold5_digit ?upper))
          mod (1000000::int)"
      by (rule trans[OF output_mod signed_congruence])
    have source_growth_removed:
      "(40 * int (u + 100000 * ?upper) -
          198 * int (?mask u + 100000 * threshold5_digit ?upper))
          mod (1000000::int) =
        (40 * int u -
          198 * int (?mask u + 100000 * threshold5_digit ?upper))
          mod (1000000::int)"
      by (rule mod_diff_cong[OF source_growth_residue refl])
    have output_low_signed:
      "int (double_reverse_T_run 2 n mod 1000000) =
        (40 * int u -
          198 * int (?mask u + 100000 * threshold5_digit ?upper))
          mod (1000000::int)"
      by (rule trans[OF output_signed source_growth_removed])
    have output_flag_signed:
      "int (double_reverse_T_run 2 n mod 1000000) =
        (40 * int u - 198 * int (?mask u +
          (if threshold5_digit ?upper = 1 then 100000 else 0)))
          mod (1000000::int)"
      by (rule trans[OF output_low_signed target_expression_residue])
    show ?thesis
      by (rule trans[OF output_flag_signed target_integer[symmetric]])
  qed
  show ?thesis using result_int by (simp only: of_nat_eq_iff)
qed

lemma double_reverse_seed196_first_guard_step:
  assumes "u \<in> double_reverse_seed196_first_guards"
  shows "double_reverse_seed196_phi5 u upper_high \<in>
      double_reverse_seed196_second_guards"
    and "double_reverse_seed196_j4 u upper_high = 454"
    and "double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42"
    and "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 742"
proof -
  have outcomes:
    "double_reverse_seed196_phi5 u upper_high \<in>
        double_reverse_seed196_second_guards
      \<and> double_reverse_seed196_j4 u upper_high = 454
      \<and> double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42
      \<and> double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 742"
    using assms
    by (simp only: double_reverse_seed196_first_guards_def insert_iff empty_iff;
        elim disjE; cases upper_high; simp_all add:
          double_reverse_seed196_second_guards_def
          double_reverse_seed196_guard_step_simp)
  show "double_reverse_seed196_phi5 u upper_high \<in>
      double_reverse_seed196_second_guards" and
    "double_reverse_seed196_j4 u upper_high = 454" and
    "double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42" and
    "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 742"
    using outcomes by simp_all
qed

lemma double_reverse_seed196_second_guard_step:
  assumes "u \<in> double_reverse_seed196_second_guards"
  shows "double_reverse_seed196_phi5 u upper_high \<in>
      double_reverse_seed196_third_guards"
    and "double_reverse_seed196_j4 u upper_high = 554"
    and "double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42"
    and "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 7542"
proof -
  have outcomes:
    "double_reverse_seed196_phi5 u upper_high \<in>
        double_reverse_seed196_third_guards
      \<and> double_reverse_seed196_j4 u upper_high = 554
      \<and> double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42
      \<and> double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 7542"
    using assms
    by (simp only: double_reverse_seed196_second_guards_def insert_iff empty_iff;
        elim disjE; cases upper_high; simp_all add:
          double_reverse_seed196_third_guards_def
          double_reverse_seed196_guard_step_simp)
  show "double_reverse_seed196_phi5 u upper_high \<in>
      double_reverse_seed196_third_guards" and
    "double_reverse_seed196_j4 u upper_high = 554" and
    "double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42" and
    "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 7542"
    using outcomes by simp_all
qed

lemma double_reverse_seed196_third_guard_step:
  assumes "u \<in> double_reverse_seed196_third_guards"
  shows "double_reverse_seed196_phi5 u upper_high \<in>
      double_reverse_seed196_first_guards"
    and "double_reverse_seed196_j4 u upper_high = 4144"
    and "double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42"
    and "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 5342"
proof -
  have outcomes:
    "double_reverse_seed196_phi5 u upper_high \<in>
        double_reverse_seed196_first_guards
      \<and> double_reverse_seed196_j4 u upper_high = 4144
      \<and> double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42
      \<and> double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 5342"
    using assms
    by (simp only: double_reverse_seed196_third_guards_def insert_iff empty_iff;
        elim disjE; cases upper_high; simp_all add:
          double_reverse_seed196_first_guards_def
          double_reverse_seed196_guard_step_simp)
  show "double_reverse_seed196_phi5 u upper_high \<in>
      double_reverse_seed196_first_guards" and
    "double_reverse_seed196_j4 u upper_high = 4144" and
    "double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42" and
    "double_reverse_seed196_first_pair_low6 u upper_high mod 10000 = 5342"
    using outcomes by simp_all
qed

lemma double_reverse_seed196_guard_successor:
  assumes guard: "u \<in> double_reverse_seed196_phase_guards blocks"
  shows "double_reverse_seed196_phi5 u upper_high \<in>
    double_reverse_seed196_phase_guards (Suc blocks)"
proof -
  have bound: "double_reverse_seed196_phase_index blocks \<le> 3"
    by (rule double_reverse_seed196_phase_index_bound)
  have cases:
    "double_reverse_seed196_phase_index blocks = 0 \<or>
      double_reverse_seed196_phase_index blocks = 1 \<or>
      double_reverse_seed196_phase_index blocks = 2 \<or>
      double_reverse_seed196_phase_index blocks = 3"
    using bound by arith
  from cases show ?thesis
  proof (elim disjE)
    assume zero: "double_reverse_seed196_phase_index blocks = 0"
    have entry: "u \<in> double_reverse_seed196_entry_guards"
      using guard zero by (simp add: double_reverse_seed196_phase_guards_def)
    have next_guard: "double_reverse_seed196_phi5 u upper_high \<in>
        double_reverse_seed196_first_guards"
      by (rule double_reverse_seed196_entry_guard_step(1)[OF entry])
    show ?thesis using next_guard zero
      by (simp add: double_reverse_seed196_phase_guards_successor)
  next
    assume one: "double_reverse_seed196_phase_index blocks = 1"
    have first: "u \<in> double_reverse_seed196_first_guards"
      using guard one by (simp add: double_reverse_seed196_phase_guards_def)
    have next_guard: "double_reverse_seed196_phi5 u upper_high \<in>
        double_reverse_seed196_second_guards"
      by (rule double_reverse_seed196_first_guard_step(1)[OF first])
    show ?thesis using next_guard one
      by (simp add: double_reverse_seed196_phase_guards_successor)
  next
    assume two: "double_reverse_seed196_phase_index blocks = 2"
    have second: "u \<in> double_reverse_seed196_second_guards"
      using guard two by (simp add: double_reverse_seed196_phase_guards_def)
    have next_guard: "double_reverse_seed196_phi5 u upper_high \<in>
        double_reverse_seed196_third_guards"
      by (rule double_reverse_seed196_second_guard_step(1)[OF second])
    show ?thesis using next_guard two
      by (simp add: double_reverse_seed196_phase_guards_successor)
  next
    assume three: "double_reverse_seed196_phase_index blocks = 3"
    have third: "u \<in> double_reverse_seed196_third_guards"
      using guard three by (simp add: double_reverse_seed196_phase_guards_def)
    have next_guard: "double_reverse_seed196_phi5 u upper_high \<in>
        double_reverse_seed196_first_guards"
      by (rule double_reverse_seed196_third_guard_step(1)[OF third])
    show ?thesis using next_guard three
      by (simp add: double_reverse_seed196_phase_guards_successor)
  qed
qed

lemma double_reverse_seed196_guard_first_pair_low6_mod100:
  assumes guard: "u \<in> double_reverse_seed196_entry_guards \<union>
      double_reverse_seed196_first_guards \<union>
      double_reverse_seed196_second_guards \<union>
      double_reverse_seed196_third_guards"
  shows "double_reverse_seed196_first_pair_low6 u upper_high mod 100 = 42"
  using guard
    double_reverse_seed196_entry_guard_step
    double_reverse_seed196_first_guard_step
    double_reverse_seed196_second_guard_step
    double_reverse_seed196_third_guard_step
  by (auto simp: double_reverse_seed196_entry_guards_def
      double_reverse_seed196_first_guards_def
      double_reverse_seed196_second_guards_def
      double_reverse_seed196_third_guards_def
      dest: double_reverse_seed196_entry_guard_step
        double_reverse_seed196_first_guard_step
        double_reverse_seed196_second_guard_step
        double_reverse_seed196_third_guard_step)

lemma double_reverse_seed196_four_step_source_exact:
  assumes low: "n mod 100000 = u"
      and guard: "u \<in> double_reverse_seed196_entry_guards \<union>
        double_reverse_seed196_first_guards \<union>
        double_reverse_seed196_second_guards \<union>
        double_reverse_seed196_third_guards"
  shows "double_reverse_T_run 4 n mod 100000 =
    double_reverse_seed196_phi5 u
      (threshold5_digit ((n div 100000) mod 10) = 1)"
proof -
  let ?upper = "(n div 100000) mod 10"
  let ?high = "threshold5_digit ?upper = 1"
  let ?middle = "double_reverse_T_run 2 n"
  let ?low6 = "double_reverse_seed196_first_pair_low6 u ?high"
  have unit: "u mod 10 = 8"
    by (rule double_reverse_seed196_guard_unit_digit[OF guard])
  have first_pair:
    "?middle mod 1000000 = ?low6"
    using double_reverse_seed196_first_pair_source_exact[OF low unit]
    by simp
  have first_pair_mod100: "?low6 mod 100 = 42"
    by (rule double_reverse_seed196_guard_first_pair_low6_mod100[OF guard])
  have hundred_dvd_million: "100 dvd (1000000::nat)"
    by simp
  have ten_dvd_hundred: "10 dvd (100::nat)"
    by simp
  have middle_low100: "?middle mod 100 = ?low6 mod 100"
    using first_pair hundred_dvd_million by (metis mod_mod_cancel)
  have middle_low_unit:
    "(?middle mod 100) mod 10 = ?middle mod 10"
    by (rule mod_mod_cancel[OF ten_dvd_hundred])
  have middle_unit: "?middle mod 10 = 2"
    using middle_low100 first_pair_mod100 middle_low_unit by simp
  have middle_positive: "?middle > 0"
    using first_pair_mod100 first_pair by (cases ?middle) auto
  let ?source = "double_reverse_decimal_source ?middle"
  let ?mask = "double_reverse_decimal_threshold_mask"
  have middle_canonical: "double_reverse_canonical_source ?source"
    using double_reverse_decimal_source_canonical[OF middle_positive]
      middle_unit by simp
  have middle_value: "double_reverse_msf_value ?source = ?middle"
    by (rule double_reverse_decimal_source_value)
  have middle_mask:
    "double_reverse_source_carry_mask ?source = ?mask ?middle"
    by (rule double_reverse_decimal_threshold_mask_source)
  have middle_last: "last ?source = ?middle mod 10"
    by (rule double_reverse_decimal_source_last)
  have no_growth: "threshold5_digit (last ?source) = 0"
    using middle_last middle_unit by (simp add: threshold5_digit_def)
  have middle_affine:
    "int (double_reverse_T_run 2 ?middle) =
      4 * int ?middle - 198 * int (?mask ?middle div 10)"
    using double_reverse_four_port_source_affine_carry[OF middle_canonical]
      middle_value middle_mask no_growth by simp
  have mask_middle_low6:
    "?mask ?middle mod 1000000 = ?mask ?low6"
    using double_reverse_decimal_threshold_mask_mod_power[of ?middle 6]
      first_pair by simp
  have mask_div_low:
    "?mask ?middle div 10 mod 100000 = ?mask ?low6 div 10"
    using mod_mult2_eq[of "?mask ?middle" 10 100000]
      mask_middle_low6 by simp
  have hundred_thousand_dvd_million: "100000 dvd (1000000::nat)"
    by simp
  have middle_low5: "?middle mod 100000 = ?low6 mod 100000"
    using first_pair hundred_thousand_dvd_million by (metis mod_mod_cancel)
  have middle_div_congruence:
    "int (?mask ?middle div 10) mod 100000 =
      int (?mask ?low6 div 10) mod 100000"
  proof -
    have mask_div_nat_residue:
      "(?mask ?middle div 10) mod 100000 =
        (?mask ?low6 div 10) mod 100000"
    proof -
      have "((?mask ?middle div 10) mod 100000) mod 100000 =
          (?mask ?low6 div 10) mod 100000"
        by (rule arg_cong[where f="\<lambda>r::nat. r mod 100000",
          OF mask_div_low])
      then show ?thesis by simp
    qed
    have mask_div_int_residue:
      "int ((?mask ?middle div 10) mod 100000) =
        int ((?mask ?low6 div 10) mod 100000)"
      by (rule arg_cong[where f="\<lambda>r::nat. int r",
        OF mask_div_nat_residue])
    show ?thesis using mask_div_int_residue
      by (simp only: of_nat_mod of_nat_numeral)
  qed
  have second_signed_congruence:
    "(4 * int ?middle - 198 * int (?mask ?middle div 10)) mod 100000 =
      (4 * int ?low6 - 198 * int (?mask ?low6 div 10)) mod 100000"
  proof -
    have middle_nat_residue:
      "int (?middle mod 100000) = int (?low6 mod 100000)"
      by (rule arg_cong[where f="\<lambda>r::nat. int r", OF middle_low5])
    have middle_mod_congruence:
      "int ?middle mod (100000::int) = int ?low6 mod (100000::int)"
      using middle_nat_residue by (simp only: of_nat_mod of_nat_numeral)
    have middle_product_congruence:
      "(4 * int ?middle) mod (100000::int) =
        (4 * int ?low6) mod (100000::int)"
      by (rule mod_mult_cong[OF refl middle_mod_congruence])
    have mask_product_congruence:
      "(198 * int (?mask ?middle div 10)) mod (100000::int) =
        (198 * int (?mask ?low6 div 10)) mod (100000::int)"
      by (rule mod_mult_cong[OF refl middle_div_congruence])
    show ?thesis
      by (rule mod_diff_cong[OF middle_product_congruence
        mask_product_congruence])
  qed
  have endpoint:
    "double_reverse_T_run 4 n = double_reverse_T_run 2 ?middle"
    using double_reverse_T_run_source_root_square[of 2 2 n] by simp
  have output_mod:
    "int (double_reverse_T_run 4 n mod 100000) =
      (4 * int ?middle - 198 * int (?mask ?middle div 10)) mod 100000"
    using endpoint middle_affine
    by (simp only: of_nat_mod of_nat_numeral)
  have target_int:
    "int (double_reverse_seed196_phi5 u ?high) =
      (4 * int ?low6 - 198 * int (?mask ?low6 div 10)) mod 100000"
    unfolding double_reverse_seed196_phi5_def
      double_reverse_seed196_first_pair_low6_def
    by simp
  have result_int:
    "int (double_reverse_T_run 4 n mod 100000) =
      int (double_reverse_seed196_phi5 u ?high)"
    using output_mod second_signed_congruence target_int by simp
  show ?thesis using result_int by (simp only: of_nat_eq_iff)
qed

lemmas double_reverse_seed196_low_band_base_audit_bundle =
  double_reverse_seed196_phase_index_bound
  double_reverse_seed196_phase_index_successor
  double_reverse_seed196_phase_guards_successor
  double_reverse_seed196_entry_guard_step
  double_reverse_seed196_first_guard_step
  double_reverse_seed196_second_guard_step
  double_reverse_seed196_third_guard_step
  double_reverse_seed196_guard_unit_digit
  double_reverse_seed196_first_pair_source_exact
  double_reverse_seed196_guard_successor
  double_reverse_seed196_guard_first_pair_low6_mod100
  double_reverse_seed196_four_step_source_exact

ML \<open>
  val checked = @{thms double_reverse_seed196_low_band_base_audit_bundle};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Seed-196 low-band base refinement has oracle dependencies, including skip_proof";
\<close>

end
