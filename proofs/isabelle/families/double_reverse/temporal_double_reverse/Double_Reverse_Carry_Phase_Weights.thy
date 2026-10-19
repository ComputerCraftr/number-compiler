theory Double_Reverse_Carry_Phase_Weights
  imports Double_Reverse_Digit_Carry_Affine
begin

definition double_reverse_f5_weighted_phase_sum ::
    "double_reverse_f5_action \<Rightarrow> nat" where
  "double_reverse_f5_weighted_phase_sum action =
    (2 ^ ((double_reverse_f5_ticks action + 3) mod 4) *
        double_reverse_f5_phase_count action 0 +
     2 ^ ((double_reverse_f5_ticks action + 2) mod 4) *
        double_reverse_f5_phase_count action 1 +
     2 ^ ((double_reverse_f5_ticks action + 1) mod 4) *
        double_reverse_f5_phase_count action 2 +
     2 ^ (double_reverse_f5_ticks action mod 4) *
        double_reverse_f5_phase_count action 3) mod 5"

definition double_reverse_f5_phase_weight :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "double_reverse_f5_phase_weight ticks phase =
    2 ^ ((ticks + 3 - phase) mod 4)"

definition double_reverse_f5_weighted_counts ::
    "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "double_reverse_f5_weighted_counts ticks counts =
    (double_reverse_f5_phase_weight ticks 0 * counts 0 +
     double_reverse_f5_phase_weight ticks 1 * counts 1 +
     double_reverse_f5_phase_weight ticks 2 * counts 2 +
     double_reverse_f5_phase_weight ticks 3 * counts 3) mod 5"

lemma double_reverse_f5_phase_weight_earlier:
  fixes a b phase :: nat
  assumes a_bound: "a < 4" and b_bound: "b < 4" and phase_bound: "phase < 4"
  shows "double_reverse_f5_phase_weight (a+b) phase mod 5 =
    (2^b * double_reverse_f5_phase_weight a phase) mod 5"
proof -
  have a_values: "a = 0 \<or> a = 1 \<or> a = 2 \<or> a = 3"
    using a_bound by arith
  have b_values: "b = 0 \<or> b = 1 \<or> b = 2 \<or> b = 3"
    using b_bound by arith
  have phase_values: "phase = 0 \<or> phase = 1 \<or> phase = 2 \<or> phase = 3"
    using phase_bound by arith
  show ?thesis
    using a_values b_values phase_values
    unfolding double_reverse_f5_phase_weight_def
    by (elim disjE; simp_all)
qed

lemma double_reverse_f5_phase_weight_later:
  fixes a b phase :: nat
  assumes a_bound: "a < 4" and b_bound: "b < 4" and phase_bound: "phase < 4"
  shows "double_reverse_f5_phase_weight (a+b) phase mod 5 =
    double_reverse_f5_phase_weight b ((phase+4-a) mod 4) mod 5"
proof -
  have a_values: "a = 0 \<or> a = 1 \<or> a = 2 \<or> a = 3"
    using a_bound by arith
  have b_values: "b = 0 \<or> b = 1 \<or> b = 2 \<or> b = 3"
    using b_bound by arith
  have phase_values: "phase = 0 \<or> phase = 1 \<or> phase = 2 \<or> phase = 3"
    using phase_bound by arith
  show ?thesis
    using a_values b_values phase_values
    unfolding double_reverse_f5_phase_weight_def
    by (elim disjE; simp_all)
qed

lemma double_reverse_f5_weighted_counts_join:
  fixes earlier later :: "nat \<Rightarrow> nat" and a b :: nat
  assumes a_bound: "a < 4" and b_bound: "b < 4"
  shows
    "double_reverse_f5_weighted_counts (a + b)
        (\<lambda>phase. earlier phase + later ((phase + 4 - a) mod 4)) =
      (2 ^ b * double_reverse_f5_weighted_counts a earlier +
        double_reverse_f5_weighted_counts b later) mod 5"
proof -
  let ?weight = double_reverse_f5_phase_weight
  let ?e0 = "earlier 0"
  let ?e1 = "earlier 1"
  let ?e2 = "earlier 2"
  let ?e3 = "earlier 3"
  let ?q0 = "(0+4-a) mod 4"
  let ?q1 = "(1+4-a) mod 4"
  let ?q2 = "(2+4-a) mod 4"
  let ?q3 = "(3+4-a) mod 4"
  let ?l0 = "later ?q0"
  let ?l1 = "later ?q1"
  let ?l2 = "later ?q2"
  let ?l3 = "later ?q3"
  have phase0: "(0::nat) < 4" by simp
  have phase1: "(1::nat) < 4" by simp
  have phase2: "(2::nat) < 4" by simp
  have phase3: "(3::nat) < 4" by simp
  have e_coeff0: "?weight (a+b) 0 mod 5 = (2^b * ?weight a 0) mod 5"
    by (rule double_reverse_f5_phase_weight_earlier[OF a_bound b_bound phase0])
  have e_coeff1: "?weight (a+b) 1 mod 5 = (2^b * ?weight a 1) mod 5"
    by (rule double_reverse_f5_phase_weight_earlier[OF a_bound b_bound phase1])
  have e_coeff2: "?weight (a+b) 2 mod 5 = (2^b * ?weight a 2) mod 5"
    by (rule double_reverse_f5_phase_weight_earlier[OF a_bound b_bound phase2])
  have e_coeff3: "?weight (a+b) 3 mod 5 = (2^b * ?weight a 3) mod 5"
    by (rule double_reverse_f5_phase_weight_earlier[OF a_bound b_bound phase3])
  have l_coeff0: "?weight (a+b) 0 mod 5 = ?weight b ?q0 mod 5"
    by (rule double_reverse_f5_phase_weight_later[OF a_bound b_bound phase0])
  have l_coeff1: "?weight (a+b) 1 mod 5 = ?weight b ?q1 mod 5"
    by (rule double_reverse_f5_phase_weight_later[OF a_bound b_bound phase1])
  have l_coeff2: "?weight (a+b) 2 mod 5 = ?weight b ?q2 mod 5"
    by (rule double_reverse_f5_phase_weight_later[OF a_bound b_bound phase2])
  have l_coeff3: "?weight (a+b) 3 mod 5 = ?weight b ?q3 mod 5"
    by (rule double_reverse_f5_phase_weight_later[OF a_bound b_bound phase3])
  have e_term0:
    "(?weight (a+b) 0 * ?e0) mod 5 = ((2^b * ?weight a 0) * ?e0) mod 5"
    by (rule mod_mult_cong[OF e_coeff0 refl])
  have e_term1:
    "(?weight (a+b) 1 * ?e1) mod 5 = ((2^b * ?weight a 1) * ?e1) mod 5"
    by (rule mod_mult_cong[OF e_coeff1 refl])
  have e_term2:
    "(?weight (a+b) 2 * ?e2) mod 5 = ((2^b * ?weight a 2) * ?e2) mod 5"
    by (rule mod_mult_cong[OF e_coeff2 refl])
  have e_term3:
    "(?weight (a+b) 3 * ?e3) mod 5 = ((2^b * ?weight a 3) * ?e3) mod 5"
    by (rule mod_mult_cong[OF e_coeff3 refl])
  have early01:
    "(?weight (a+b) 0 * ?e0 + ?weight (a+b) 1 * ?e1) mod 5 =
      ((2^b * ?weight a 0) * ?e0 + (2^b * ?weight a 1) * ?e1) mod 5"
    by (rule mod_add_cong[OF e_term0 e_term1])
  have early012:
    "(?weight (a+b) 0 * ?e0 + ?weight (a+b) 1 * ?e1 +
       ?weight (a+b) 2 * ?e2) mod 5 =
      ((2^b * ?weight a 0) * ?e0 + (2^b * ?weight a 1) * ?e1 +
       (2^b * ?weight a 2) * ?e2) mod 5"
    by (rule mod_add_cong[OF early01 e_term2])
  have early_terms:
    "(?weight (a+b) 0 * ?e0 + ?weight (a+b) 1 * ?e1 +
       ?weight (a+b) 2 * ?e2 + ?weight (a+b) 3 * ?e3) mod 5 =
      ((2^b * ?weight a 0) * ?e0 + (2^b * ?weight a 1) * ?e1 +
       (2^b * ?weight a 2) * ?e2 + (2^b * ?weight a 3) * ?e3) mod 5"
    by (rule mod_add_cong[OF early012 e_term3])
  have l_term0:
    "(?weight (a+b) 0 * ?l0) mod 5 = (?weight b ?q0 * ?l0) mod 5"
    by (rule mod_mult_cong[OF l_coeff0 refl])
  have l_term1:
    "(?weight (a+b) 1 * ?l1) mod 5 = (?weight b ?q1 * ?l1) mod 5"
    by (rule mod_mult_cong[OF l_coeff1 refl])
  have l_term2:
    "(?weight (a+b) 2 * ?l2) mod 5 = (?weight b ?q2 * ?l2) mod 5"
    by (rule mod_mult_cong[OF l_coeff2 refl])
  have l_term3:
    "(?weight (a+b) 3 * ?l3) mod 5 = (?weight b ?q3 * ?l3) mod 5"
    by (rule mod_mult_cong[OF l_coeff3 refl])
  have late01:
    "(?weight (a+b) 0 * ?l0 + ?weight (a+b) 1 * ?l1) mod 5 =
      (?weight b ?q0 * ?l0 + ?weight b ?q1 * ?l1) mod 5"
    by (rule mod_add_cong[OF l_term0 l_term1])
  have late012:
    "(?weight (a+b) 0 * ?l0 + ?weight (a+b) 1 * ?l1 +
       ?weight (a+b) 2 * ?l2) mod 5 =
      (?weight b ?q0 * ?l0 + ?weight b ?q1 * ?l1 +
       ?weight b ?q2 * ?l2) mod 5"
    by (rule mod_add_cong[OF late01 l_term2])
  have late_terms:
    "(?weight (a+b) 0 * ?l0 + ?weight (a+b) 1 * ?l1 +
       ?weight (a+b) 2 * ?l2 + ?weight (a+b) 3 * ?l3) mod 5 =
      (?weight b ?q0 * ?l0 + ?weight b ?q1 * ?l1 +
       ?weight b ?q2 * ?l2 + ?weight b ?q3 * ?l3) mod 5"
    by (rule mod_add_cong[OF late012 l_term3])
  have a_cases: "a=0 \<or> a=1 \<or> a=2 \<or> a=3"
    using a_bound by arith
  have late_reindex:
    "(?weight b ?q0 * ?l0 + ?weight b ?q1 * ?l1 +
       ?weight b ?q2 * ?l2 + ?weight b ?q3 * ?l3) mod 5 =
     (?weight b 0 * later 0 + ?weight b 1 * later 1 +
       ?weight b 2 * later 2 + ?weight b 3 * later 3) mod 5"
    using a_cases
    unfolding double_reverse_f5_phase_weight_def
    by (elim disjE; simp_all; simp_all add: ac_simps)
  have early_scaled:
    "(2^b * double_reverse_f5_weighted_counts a earlier) mod 5 =
     (2^b * (?weight a 0 * ?e0 + ?weight a 1 * ?e1 +
       ?weight a 2 * ?e2 + ?weight a 3 * ?e3)) mod 5"
  proof -
    have weighted:
      "double_reverse_f5_weighted_counts a earlier =
        (?weight a 0 * ?e0 + ?weight a 1 * ?e1 +
          ?weight a 2 * ?e2 + ?weight a 3 * ?e3) mod 5"
      by (simp add: double_reverse_f5_weighted_counts_def)
    have weighted_mod:
      "double_reverse_f5_weighted_counts a earlier mod 5 =
        (?weight a 0 * ?e0 + ?weight a 1 * ?e1 +
          ?weight a 2 * ?e2 + ?weight a 3 * ?e3) mod 5"
      using weighted by simp
    show ?thesis
      by (rule mod_mult_cong[OF refl weighted_mod])
  qed
  have early_distributed:
    "2^b * (?weight a 0 * ?e0 + ?weight a 1 * ?e1 +
       ?weight a 2 * ?e2 + ?weight a 3 * ?e3) =
     (2^b * ?weight a 0) * ?e0 + (2^b * ?weight a 1) * ?e1 +
       (2^b * ?weight a 2) * ?e2 + (2^b * ?weight a 3) * ?e3"
    by (simp add: algebra_simps)
  have early_contribution:
    "(?weight (a+b) 0 * ?e0 + ?weight (a+b) 1 * ?e1 +
       ?weight (a+b) 2 * ?e2 + ?weight (a+b) 3 * ?e3) mod 5 =
     (2^b * double_reverse_f5_weighted_counts a earlier) mod 5"
    using early_terms early_scaled early_distributed by simp
  have later_contribution:
    "(?weight (a+b) 0 * ?l0 + ?weight (a+b) 1 * ?l1 +
       ?weight (a+b) 2 * ?l2 + ?weight (a+b) 3 * ?l3) mod 5 =
     double_reverse_f5_weighted_counts b later mod 5"
    using late_terms late_reindex
    unfolding double_reverse_f5_weighted_counts_def by simp
  have joined_raw:
    "double_reverse_f5_weighted_counts (a+b)
        (\<lambda>phase. earlier phase + later ((phase+4-a) mod 4)) =
      ((?weight (a+b) 0 * ?e0 + ?weight (a+b) 1 * ?e1 +
        ?weight (a+b) 2 * ?e2 + ?weight (a+b) 3 * ?e3) +
       (?weight (a+b) 0 * ?l0 + ?weight (a+b) 1 * ?l1 +
        ?weight (a+b) 2 * ?l2 + ?weight (a+b) 3 * ?l3)) mod 5"
    unfolding double_reverse_f5_weighted_counts_def
    by (simp add: algebra_simps)
  have sum_contribution:
    "((?weight (a+b) 0 * ?e0 + ?weight (a+b) 1 * ?e1 +
        ?weight (a+b) 2 * ?e2 + ?weight (a+b) 3 * ?e3) +
       (?weight (a+b) 0 * ?l0 + ?weight (a+b) 1 * ?l1 +
        ?weight (a+b) 2 * ?l2 + ?weight (a+b) 3 * ?l3)) mod 5 =
      (2^b * double_reverse_f5_weighted_counts a earlier +
        double_reverse_f5_weighted_counts b later) mod 5"
    by (rule mod_add_cong[OF early_contribution later_contribution])
  show ?thesis using joined_raw sum_contribution by simp
qed

lemma double_reverse_f5_power_phase:
  "(2::nat) ^ n mod 5 = 2 ^ (n mod 4) mod 5"
proof -
  have cycle: "(2::nat) ^ (4*k) mod 5 = 1" for k
  proof (induction k)
    case 0
    then show ?case by simp
  next
    case (Suc k)
    have exponent: "4 * Suc k = 4*k + 4" by simp
    have sixteen: "(2::nat)^4 mod 5 = 1" by simp
    have x_mod: "(2::nat)^(4*k) mod 5 =
        ((2::nat)^(4*k) mod 5) mod 5" by simp
    have sixteen_mod: "(16::nat) mod 5 = (16 mod 5) mod 5" by simp
    have product_mod:
      "(2::nat)^(4*k) * 16 mod 5 =
        ((2::nat)^(4*k) mod 5) * (16 mod 5) mod 5"
      by (rule mod_mult_cong[OF x_mod sixteen_mod])
    show ?case
      using Suc.IH sixteen product_mod
      by (simp only: exponent power_add; simp add: product_mod)
  qed
  have division: "4 * (n div 4) + n mod 4 = n"
    by (metis div_mult_mod_eq mult.commute)
  have split: "n = n mod 4 + 4 * (n div 4)"
    using division by (simp add: add.commute)
  have power_split:
    "(2::nat) ^ n = 2 ^ (n mod 4 + 4 * (n div 4))"
    by (rule arg_cong[OF split])
  have power_factor:
    "(2::nat) ^ (n mod 4 + 4 * (n div 4)) =
      2 ^ (n mod 4) * 2 ^ (4 * (n div 4))"
    by (rule power_add)
  have expanded:
    "(2::nat) ^ n =
      2 ^ (n mod 4) * 2 ^ (4 * (n div 4))"
    by (rule trans[OF power_split power_factor])
  have product_residues:
    "((2::nat) ^ (n mod 4) * 2 ^ (4 * (n div 4))) mod 5 =
      (((2::nat) ^ (n mod 4) mod 5) *
        (2 ^ (4 * (n div 4)) mod 5)) mod 5"
    by (rule mod_mult_eq[symmetric])
  show ?thesis
    using expanded product_residues cycle[of "n div 4"]
    by simp
qed

lemma double_reverse_f5_weighted_phase_sum_then:
  "double_reverse_f5_weighted_phase_sum
      (double_reverse_f5_then earlier later) =
    (double_reverse_f5_multiplier later *
        double_reverse_f5_weighted_phase_sum earlier +
      double_reverse_f5_weighted_phase_sum later) mod 5"
proof -
  let ?a = "double_reverse_f5_ticks earlier mod 4"
  let ?b = "double_reverse_f5_ticks later mod 4"
  have a_bound: "?a < 4" by simp
  have b_bound: "?b < 4" by simp
  have clock_a: "double_reverse_f5_ticks earlier mod 4 = ?a" by simp
  have clock_a_cong:
    "double_reverse_f5_ticks earlier mod 4 = ?a mod 4"
    using a_bound clock_a by simp
  have clock_b_cong:
    "double_reverse_f5_ticks later mod 4 = ?b mod 4"
    by simp
  have shifted: "(phase + 4 - double_reverse_f5_ticks earlier mod 4) mod 4 =
      (phase + 4 - ?a) mod 4" for phase
    using clock_a by simp
  have earlier_coeff:
    "(double_reverse_f5_ticks earlier + k) mod 4 = (?a + k) mod 4" for k
    using mod_add_cong[OF clock_a_cong refl] .
  have earlier_succ:
    "Suc (double_reverse_f5_ticks earlier) mod 4 = Suc ?a mod 4"
    using earlier_coeff[of 1] by simp
  have earlier_succ_succ:
    "Suc (Suc (double_reverse_f5_ticks earlier)) mod 4 =
      Suc (Suc ?a) mod 4"
    using earlier_coeff[of 2] by simp
  have earlier_succ_succ_succ:
    "Suc (Suc (Suc (double_reverse_f5_ticks earlier))) mod 4 =
      Suc (Suc (Suc ?a)) mod 4"
    using earlier_coeff[of 3] by (simp add: add.commute)
  have later_coeff:
    "(double_reverse_f5_ticks later + k) mod 4 = (?b + k) mod 4" for k
    using mod_add_cong[OF clock_b_cong refl] .
  have later_succ:
    "Suc (double_reverse_f5_ticks later) mod 4 = Suc ?b mod 4"
    using later_coeff[of 1] by simp
  have later_succ_succ:
    "Suc (Suc (double_reverse_f5_ticks later)) mod 4 =
      Suc (Suc ?b) mod 4"
    using later_coeff[of 2] by simp
  have later_succ_succ_succ:
    "Suc (Suc (Suc (double_reverse_f5_ticks later))) mod 4 =
      Suc (Suc (Suc ?b)) mod 4"
    using later_coeff[of 3] by (simp add: add.commute)
  have total_coeff:
    "(double_reverse_f5_ticks earlier + double_reverse_f5_ticks later + k)
        mod 4 = (?a + ?b + k) mod 4" for k
  proof -
    have sum_clock:
      "(double_reverse_f5_ticks earlier + double_reverse_f5_ticks later) mod 4 =
        (?a + ?b) mod 4"
      by (rule mod_add_cong[OF clock_a_cong clock_b_cong])
    show ?thesis using mod_add_cong[OF sum_clock refl] .
  qed
  have total_zero:
    "(double_reverse_f5_ticks earlier + double_reverse_f5_ticks later) mod 4 =
      (?a + ?b) mod 4"
    by (rule mod_add_cong[OF clock_a_cong clock_b_cong])
  have total_succ:
    "Suc (double_reverse_f5_ticks earlier + double_reverse_f5_ticks later) mod 4 =
      Suc (?a + ?b) mod 4"
    using total_coeff[of 1] by simp
  have total_succ_succ:
    "Suc (Suc (double_reverse_f5_ticks earlier + double_reverse_f5_ticks later)) mod 4 =
      Suc (Suc (?a + ?b)) mod 4"
    using total_coeff[of 2] by simp
  have total_succ_succ_succ:
    "Suc (Suc (Suc (double_reverse_f5_ticks earlier + double_reverse_f5_ticks later))) mod 4 =
      Suc (Suc (Suc (?a + ?b))) mod 4"
    using total_coeff[of 3] by (simp add: add.commute)
  have multiplier_reduced:
    "double_reverse_f5_multiplier later =
      (2 ^ ?b) mod 5"
    unfolding double_reverse_f5_multiplier_def
    by (rule double_reverse_f5_power_phase)
  have earlier_weight:
    "double_reverse_f5_weighted_counts ?a
        (double_reverse_f5_phase_count earlier) =
      double_reverse_f5_weighted_phase_sum earlier"
    unfolding double_reverse_f5_weighted_counts_def
      double_reverse_f5_weighted_phase_sum_def
      double_reverse_f5_phase_weight_def
    by (simp add: earlier_coeff earlier_succ earlier_succ_succ
        earlier_succ_succ_succ)
  have later_weight:
    "double_reverse_f5_weighted_counts ?b
        (double_reverse_f5_phase_count later) =
      double_reverse_f5_weighted_phase_sum later"
    unfolding double_reverse_f5_weighted_counts_def
      double_reverse_f5_weighted_phase_sum_def
      double_reverse_f5_phase_weight_def
    by (simp add: later_coeff later_succ later_succ_succ
        later_succ_succ_succ)
  have joined_counts:
    "double_reverse_f5_weighted_counts (?a + ?b)
       (\<lambda>phase. double_reverse_f5_phase_count earlier phase +
         double_reverse_f5_phase_count later ((phase + 4 - ?a) mod 4)) =
     (2 ^ ?b * double_reverse_f5_weighted_counts ?a
         (double_reverse_f5_phase_count earlier) +
       double_reverse_f5_weighted_counts ?b
         (double_reverse_f5_phase_count later)) mod 5"
    by (rule double_reverse_f5_weighted_counts_join[OF a_bound b_bound])
  have composed_weight:
    "double_reverse_f5_weighted_phase_sum
        (double_reverse_f5_then earlier later) =
      double_reverse_f5_weighted_counts (?a + ?b)
        (\<lambda>phase. double_reverse_f5_phase_count earlier phase +
          double_reverse_f5_phase_count later ((phase + 4 - ?a) mod 4))"
  proof -
    have joined_ticks:
      "double_reverse_f5_ticks (double_reverse_f5_then earlier later) =
        double_reverse_f5_ticks earlier + double_reverse_f5_ticks later"
      by (simp add: double_reverse_f5_then_def)
    have joined_count0:
      "double_reverse_f5_phase_count (double_reverse_f5_then earlier later) 0 =
        double_reverse_f5_phase_count earlier 0 +
          double_reverse_f5_phase_count later ((0 + 4 - ?a) mod 4)"
      using shifted[of 0]
      by (simp add: double_reverse_f5_phase_count_then
          double_reverse_f5_phase_before_def)
    have joined_count1:
      "double_reverse_f5_phase_count (double_reverse_f5_then earlier later) 1 =
        double_reverse_f5_phase_count earlier 1 +
          double_reverse_f5_phase_count later ((1 + 4 - ?a) mod 4)"
      using shifted[of 1]
      by (simp add: double_reverse_f5_phase_count_then
          double_reverse_f5_phase_before_def)
    have joined_count2:
      "double_reverse_f5_phase_count (double_reverse_f5_then earlier later) 2 =
        double_reverse_f5_phase_count earlier 2 +
          double_reverse_f5_phase_count later ((2 + 4 - ?a) mod 4)"
      using shifted[of 2]
      by (simp add: double_reverse_f5_phase_count_then
          double_reverse_f5_phase_before_def)
    have joined_count3:
      "double_reverse_f5_phase_count (double_reverse_f5_then earlier later) 3 =
        double_reverse_f5_phase_count earlier 3 +
          double_reverse_f5_phase_count later ((3 + 4 - ?a) mod 4)"
      using shifted[of 3]
      by (simp add: double_reverse_f5_phase_count_then
          double_reverse_f5_phase_before_def)
    show ?thesis
      unfolding double_reverse_f5_weighted_phase_sum_def
        double_reverse_f5_weighted_counts_def
        double_reverse_f5_phase_weight_def
      using joined_ticks joined_count0 joined_count1 joined_count2 joined_count3
      by (simp add: total_zero total_coeff total_succ total_succ_succ
          total_succ_succ_succ)
  qed
  have multiplier_cong:
    "double_reverse_f5_multiplier later mod 5 = (2 ^ ?b) mod 5"
    using multiplier_reduced by simp
  have earlier_cong:
    "double_reverse_f5_weighted_phase_sum earlier mod 5 =
      double_reverse_f5_weighted_counts ?a
        (double_reverse_f5_phase_count earlier) mod 5"
    using earlier_weight by simp
  have later_cong:
    "double_reverse_f5_weighted_phase_sum later mod 5 =
      double_reverse_f5_weighted_counts ?b
        (double_reverse_f5_phase_count later) mod 5"
    using later_weight by simp
  have product_cong:
    "(double_reverse_f5_multiplier later *
        double_reverse_f5_weighted_phase_sum earlier) mod 5 =
      (2 ^ ?b * double_reverse_f5_weighted_counts ?a
        (double_reverse_f5_phase_count earlier)) mod 5"
    by (rule mod_mult_cong[OF multiplier_cong earlier_cong])
  have result_cong:
    "(double_reverse_f5_multiplier later *
        double_reverse_f5_weighted_phase_sum earlier +
        double_reverse_f5_weighted_phase_sum later) mod 5 =
      (2 ^ ?b * double_reverse_f5_weighted_counts ?a
        (double_reverse_f5_phase_count earlier) +
        double_reverse_f5_weighted_counts ?b
          (double_reverse_f5_phase_count later)) mod 5"
    by (rule mod_add_cong[OF product_cong later_cong])
  have composed_to_counts:
    "double_reverse_f5_weighted_phase_sum
        (double_reverse_f5_then earlier later) =
      (2 ^ ?b * double_reverse_f5_weighted_counts ?a
          (double_reverse_f5_phase_count earlier) +
        double_reverse_f5_weighted_counts ?b
          (double_reverse_f5_phase_count later)) mod 5"
    by (rule trans[OF composed_weight joined_counts])
  show ?thesis
    by (rule trans[OF composed_to_counts result_cong[symmetric]])
qed

lemma double_reverse_f5_two_step_weighted_phase_sum:
  "double_reverse_f5_weighted_phase_sum
      (double_reverse_f5_two_step first second) =
    double_reverse_f5_offset (double_reverse_f5_two_step first second) mod 5"
  by (cases first; cases second;
      simp add: double_reverse_f5_weighted_phase_sum_def
        double_reverse_f5_phase_count_def double_reverse_f5_two_step_def
        double_reverse_f5_bool_value_def)

theorem double_reverse_f5_open_trace_offset_weighted:
  "double_reverse_f5_offset
      (double_reverse_f5_open_trace_action center ports) mod 5 =
    double_reverse_f5_weighted_phase_sum
      (double_reverse_f5_open_trace_action center ports)"
proof (induction ports arbitrary: center)
  case Nil
  then show ?case
    by (simp add: double_reverse_f5_open_trace_action.simps
        double_reverse_f5_identity_def
        double_reverse_f5_weighted_phase_sum_def
        double_reverse_f5_phase_count_def)
next
  case (Cons port ports)
  obtain left right where port: "port=(left,right)"
    by (cases port) auto
  let ?early = "double_reverse_f5_stencil_step left center right"
  let ?late = "double_reverse_f5_open_trace_action
      (double_reverse_t2_digit left center right) ports"
  have early:
    "double_reverse_f5_offset ?early mod 5 =
      double_reverse_f5_weighted_phase_sum ?early"
    by (simp only: double_reverse_f5_stencil_step_def;
        rule double_reverse_f5_two_step_weighted_phase_sum[symmetric])
  have late:
    "double_reverse_f5_offset ?late mod 5 =
      double_reverse_f5_weighted_phase_sum ?late"
    by (rule Cons.IH)
  have early_mod:
    "double_reverse_f5_offset ?early mod 5 =
      double_reverse_f5_weighted_phase_sum ?early mod 5"
    using early by simp
  have late_mod:
    "double_reverse_f5_offset ?late mod 5 =
      double_reverse_f5_weighted_phase_sum ?late mod 5"
    using late by simp
  have product:
    "(double_reverse_f5_multiplier ?late *
        double_reverse_f5_offset ?early) mod 5 =
      (double_reverse_f5_multiplier ?late *
        double_reverse_f5_weighted_phase_sum ?early) mod 5"
    by (rule mod_mult_cong[OF refl early_mod])
  have total:
    "(double_reverse_f5_multiplier ?late *
        double_reverse_f5_offset ?early +
        double_reverse_f5_offset ?late) mod 5 =
     (double_reverse_f5_multiplier ?late *
        double_reverse_f5_weighted_phase_sum ?early +
        double_reverse_f5_weighted_phase_sum ?late) mod 5"
    by (rule mod_add_cong[OF product late_mod])
  show ?case
    using total double_reverse_f5_weighted_phase_sum_then[of ?early ?late]
    by (simp add: port double_reverse_f5_open_trace_action.simps
        double_reverse_f5_then_def)
qed

theorem double_reverse_f5_open_trace_offset_four_phase:
  assumes center: "center < 10"
      and ports: "double_reverse_open_inputs_valid ports"
      and four_phase:
        "double_reverse_f5_ticks
          (double_reverse_f5_open_trace_action center ports) mod 4 = 0"
  shows "double_reverse_f5_offset
      (double_reverse_f5_open_trace_action center ports) mod 5 =
    (3 * double_reverse_f5_phase_count
          (double_reverse_f5_open_trace_action center ports) 0 +
     4 * double_reverse_f5_phase_count
          (double_reverse_f5_open_trace_action center ports) 1 +
     2 * double_reverse_f5_phase_count
          (double_reverse_f5_open_trace_action center ports) 2 +
     double_reverse_f5_phase_count
          (double_reverse_f5_open_trace_action center ports) 3) mod 5"
proof -
  let ?action = "double_reverse_f5_open_trace_action center ports"
  let ?c0 = "double_reverse_f5_phase_count ?action 0"
  let ?c1 = "double_reverse_f5_phase_count ?action 1"
  let ?c2 = "double_reverse_f5_phase_count ?action 2"
  let ?c3 = "double_reverse_f5_phase_count ?action 3"
  have weighted: "double_reverse_f5_offset ?action mod 5 =
      double_reverse_f5_weighted_phase_sum ?action"
    by (rule double_reverse_f5_open_trace_offset_weighted)
  have phase0: "(double_reverse_f5_ticks ?action + 3) mod 4 = 3"
  proof -
    have add:
      "(double_reverse_f5_ticks ?action + 3) mod 4 =
        ((double_reverse_f5_ticks ?action mod 4) + (3 mod 4)) mod 4"
      by (rule mod_add_eq[symmetric])
    show ?thesis using add four_phase by simp
  qed
  have phase1: "(double_reverse_f5_ticks ?action + 2) mod 4 = 2"
  proof -
    have add:
      "(double_reverse_f5_ticks ?action + 2) mod 4 =
        ((double_reverse_f5_ticks ?action mod 4) + (2 mod 4)) mod 4"
      by (rule mod_add_eq[symmetric])
    show ?thesis using add four_phase by simp
  qed
  have phase2: "(double_reverse_f5_ticks ?action + 1) mod 4 = 1"
  proof -
    have add:
      "(double_reverse_f5_ticks ?action + 1) mod 4 =
        ((double_reverse_f5_ticks ?action mod 4) + (1 mod 4)) mod 4"
      by (rule mod_add_eq[symmetric])
    show ?thesis using add four_phase by simp
  qed
  have phase3: "double_reverse_f5_ticks ?action mod 4 = 0"
    using four_phase .
  have weighted_value:
    "double_reverse_f5_weighted_phase_sum ?action =
      (8 * ?c0 + 4 * ?c1 + 2 * ?c2 + ?c3) mod 5"
    using phase0 phase1 phase2 phase3
    by (simp add: double_reverse_f5_weighted_phase_sum_def)
  have eight_mod: "(8::nat) mod 5 = 3 mod 5" by simp
  have first_coefficient: "(8 * ?c0) mod 5 = (3 * ?c0) mod 5"
    by (rule mod_mult_cong[OF eight_mod refl])
  have coefficient_sum:
    "(8 * ?c0 + (4 * ?c1 + 2 * ?c2 + ?c3)) mod 5 =
      (3 * ?c0 + (4 * ?c1 + 2 * ?c2 + ?c3)) mod 5"
    by (rule mod_add_cong[OF first_coefficient refl])
  show ?thesis
    using weighted weighted_value coefficient_sum
    by (simp add: add.assoc)
qed

theorem double_reverse_f5_packed_window_offset_four_phase:
  assumes positive: "0 < count"
      and source_window:
        "length row = 2*(steps + count div 2) + 1"
      and index: "i < count"
      and decimal: "double_reverse_decimal_row row"
      and four_phase:
        "double_reverse_f5_ticks
          (double_reverse_f5_open_trace_action
            (row ! (i + (if even count then 1 else 0) + steps))
            (double_reverse_packed_row_ports steps row
              (i + (if even count then 1 else 0)))) mod 4 = 0"
  shows "double_reverse_f5_offset
      (double_reverse_f5_open_trace_action
        (row ! (i + (if even count then 1 else 0) + steps))
        (double_reverse_packed_row_ports steps row
          (i + (if even count then 1 else 0)))) mod 5 =
    (3 * double_reverse_f5_phase_count
          (double_reverse_f5_open_trace_action
            (row ! (i + (if even count then 1 else 0) + steps))
            (double_reverse_packed_row_ports steps row
              (i + (if even count then 1 else 0)))) 0 +
     4 * double_reverse_f5_phase_count
          (double_reverse_f5_open_trace_action
            (row ! (i + (if even count then 1 else 0) + steps))
            (double_reverse_packed_row_ports steps row
              (i + (if even count then 1 else 0)))) 1 +
     2 * double_reverse_f5_phase_count
          (double_reverse_f5_open_trace_action
            (row ! (i + (if even count then 1 else 0) + steps))
            (double_reverse_packed_row_ports steps row
              (i + (if even count then 1 else 0)))) 2 +
     double_reverse_f5_phase_count
          (double_reverse_f5_open_trace_action
            (row ! (i + (if even count then 1 else 0) + steps))
            (double_reverse_packed_row_ports steps row
              (i + (if even count then 1 else 0)))) 3) mod 5"
proof -
  let ?start = "i + (if even count then 1 else 0)"
  let ?center = "row ! (?start + steps)"
  let ?ports = "double_reverse_packed_row_ports steps row ?start"
  let ?action = "double_reverse_f5_open_trace_action ?center ?ports"
  have count_halves:
    "2*(count div 2) = (if even count then count else count - 1)"
  proof -
    have divmod: "count = 2*(count div 2) + count mod 2"
      by (metis div_mult_mod_eq mult.commute)
    have remainder: "count mod 2 = 0 \<or> count mod 2 = 1"
      using mod_less_divisor[of count 2] by arith
    show ?thesis using divmod remainder
      by (auto simp: even_iff_mod_2_eq_zero; arith)
  qed
  have start_bound: "?start \<le> 2*(count div 2)"
    using index count_halves by (cases "even count"; simp_all; arith)
  have halo: "?start + 2*steps < length row"
    using source_window start_bound by arith
  have center_index: "?start + steps < length row"
    using halo by arith
  have center_decimal: "?center < 10"
    using decimal center_index unfolding double_reverse_decimal_row_def by blast
  have ports_valid: "double_reverse_open_inputs_valid ?ports"
    by (rule double_reverse_f5_packed_row_ports_valid[OF halo decimal])
  have result:
    "double_reverse_f5_offset ?action mod 5 =
      (3 * double_reverse_f5_phase_count ?action 0 +
       4 * double_reverse_f5_phase_count ?action 1 +
       2 * double_reverse_f5_phase_count ?action 2 +
       double_reverse_f5_phase_count ?action 3) mod 5"
    by (rule double_reverse_f5_open_trace_offset_four_phase
      [OF center_decimal ports_valid four_phase])
  show ?thesis using result by simp
qed


ML \<open>
  val checked = @{thms double_reverse_f5_weighted_counts_join
    double_reverse_f5_power_phase
    double_reverse_f5_weighted_phase_sum_then
    double_reverse_f5_two_step_weighted_phase_sum
    double_reverse_f5_open_trace_offset_weighted
    double_reverse_f5_open_trace_offset_four_phase
    double_reverse_f5_packed_window_offset_four_phase};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse phase-weight proof depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse phase-weight proof" else ();
\<close>

end
