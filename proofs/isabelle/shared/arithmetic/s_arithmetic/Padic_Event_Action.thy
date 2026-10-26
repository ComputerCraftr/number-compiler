theory Padic_Event_Action
  imports "HOL-Number_Theory.Prime_Powers"
begin

text \<open>Prime-adic gain and loss are derived observers of an already
authenticated positive additive step n -> n + delta.  They do not reconstruct
the valuation magnitude or refine a semantic transition alphabet.  The
period result is conditional on every compared step satisfying an explicit
interval guard.\<close>

datatype padic_event = Padic_Gain | Padic_Neutral | Padic_Loss

definition padic_modulus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "padic_modulus p s = p ^ Suc s"

definition padic_negative_residue :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "padic_negative_residue p s delta =
    (padic_modulus p s - delta mod padic_modulus p s) mod
      padic_modulus p s"

definition padic_value_event :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> padic_event" where
  "padic_value_event p n delta =
    (if multiplicity p (n + delta) > multiplicity p n then Padic_Gain
     else if multiplicity p (n + delta) < multiplicity p n then Padic_Loss
     else Padic_Neutral)"

definition padic_residue_event :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> padic_event" where
  "padic_residue_event p n delta =
    (let s = multiplicity p delta in
      if n mod padic_modulus p s = padic_negative_residue p s delta
      then Padic_Gain
      else if n mod padic_modulus p s = 0 then Padic_Loss
      else Padic_Neutral)"

lemma padic_power_dvd_iff_valuation:
  fixes p x k :: nat
  assumes prime_p: "prime p" and positive: "0 < x"
  shows "p^k dvd x \<longleftrightarrow> k \<le> multiplicity p x"
proof -
  have prime_elem: "prime_elem p" using prime_p by simp
  have p_not_unit: "\<not> is_unit p"
  proof
    assume unit: "is_unit p"
    have "p dvd 1" by (rule unit_imp_dvd[OF unit])
    with prime_elem_not_unit[OF prime_elem] show False by contradiction
  qed
  have x_nonzero: "x \<noteq> 0" using positive by simp
  show ?thesis
    using power_dvd_iff_le_multiplicity[OF x_nonzero p_not_unit, of k] .
qed

lemma padic_negative_residue_add:
  fixes n delta modulus :: nat
  assumes modulus_pos: "0 < modulus"
  shows "n mod modulus = (modulus - delta mod modulus) mod modulus
    \<longleftrightarrow> (n + delta) mod modulus = 0"
proof -
  let ?n = "n mod modulus"
  let ?d = "delta mod modulus"
  have n_bound: "?n < modulus" using modulus_pos by simp
  have d_bound: "?d < modulus" using modulus_pos by simp
  have reduced: "(n + delta) mod modulus = (?n + ?d) mod modulus"
    by (simp add: mod_add_eq)
  show ?thesis
  proof
    assume residue: "?n = (modulus - ?d) mod modulus"
    show "(n + delta) mod modulus = 0"
    proof (cases "?d = 0")
      case True
      with residue have "?n = 0" using modulus_pos by simp
      then show ?thesis using reduced True by simp
    next
      case False
      have d_positive: "0 < ?d" using False by simp
      have complement_bound: "modulus - ?d < modulus"
        using modulus_pos d_positive by arith
      have complement: "(modulus - ?d) mod modulus = modulus - ?d"
        using complement_bound
        by simp
      have "?n + ?d = modulus" using residue complement d_bound by arith
      then show ?thesis using reduced by simp
    qed
  next
    assume zero: "(n + delta) mod modulus = 0"
    have divisible: "modulus dvd ?n + ?d"
      using zero reduced by (simp add: dvd_eq_mod_eq_0)
    then obtain q where q: "?n + ?d = modulus * q"
      unfolding dvd_def by blast
    have bound: "?n + ?d < 2 * modulus"
      using n_bound d_bound by arith
    have q_lt: "q < 2"
    proof (rule ccontr)
      assume "\<not>q < 2"
      then have q_lower: "2 \<le> q" by arith
      have "modulus*2 \<le> modulus*q"
        by (rule mult_left_mono[OF q_lower]) simp
      then show False using q bound by arith
    qed
    consider (zero) "q=0" | (one) "q=1" using q_lt by arith
    then show "?n = (modulus - ?d) mod modulus"
    proof cases
      case zero
      then have "?n = 0" and "?d = 0" using q by simp_all
      then show ?thesis using modulus_pos by simp
    next
      case one
      have sum: "?n + ?d = modulus" using q one by simp
      have d_positive: "0 < ?d"
        using sum n_bound by arith
      have complement_bound: "modulus - ?d < modulus"
        using modulus_pos d_positive by arith
      have complement: "(modulus - ?d) mod modulus = modulus - ?d"
        using complement_bound by simp
      have "?n = modulus - ?d" using sum by arith
      then show ?thesis using complement by simp
    qed
  qed
qed

lemma padic_gain_residue_iff:
  fixes p n delta :: nat
  assumes prime_p: "prime p" and n_positive: "0 < n" and delta_positive: "0 < delta"
  shows "multiplicity p (n + delta) > multiplicity p n \<longleftrightarrow>
    n mod padic_modulus p (multiplicity p delta) =
      padic_negative_residue p (multiplicity p delta) delta"
proof -
  let ?s = "multiplicity p delta"
  let ?m = "padic_modulus p ?s"
  let ?vn = "multiplicity p n"
  let ?vs = "multiplicity p (n + delta)"
  have sum_positive: "0 < n + delta" using n_positive by simp
  have residue_divides: "n mod ?m = padic_negative_residue p ?s delta
      \<longleftrightarrow> ?m dvd n + delta"
    unfolding padic_negative_residue_def padic_modulus_def
    by (simp only: dvd_eq_mod_eq_0;
        rule padic_negative_residue_add)
      (simp add: prime_gt_0_nat[OF prime_p])
  have sum_power: "p ^ Suc ?s dvd n + delta \<longleftrightarrow> Suc ?s \<le> ?vs"
    by (rule padic_power_dvd_iff_valuation[OF prime_p sum_positive])
  consider (below) "?vn < ?s" | (equal) "?vn = ?s" | (above) "?s < ?vn"
    by arith
  then show ?thesis
  proof cases
    case below
    have min_law: "?vs = min ?vn ?s"
      by (rule multiplicity_sum_min) (use below n_positive delta_positive in auto)
    have no_power: "\<not> p ^ Suc ?s dvd n + delta"
      using sum_power min_law below by simp
    show ?thesis using residue_divides no_power min_law below
      by (auto simp: padic_modulus_def)
  next
    case equal
    have n_power: "p ^ ?s dvd n"
      by (rule multiplicity_dvd') (simp add: equal)
    have delta_power: "p ^ ?s dvd delta"
      by (rule multiplicity_dvd') simp
    have sum_power_low: "p ^ ?s dvd n + delta"
      by (rule dvd_add[OF n_power delta_power])
    have sum_lower: "?s \<le> ?vs"
      using padic_power_dvd_iff_valuation[OF prime_p sum_positive, of ?s]
        sum_power_low by simp
    have high_iff: "?vs > ?vn \<longleftrightarrow> Suc ?s \<le> ?vs"
      using equal by arith
    show ?thesis using residue_divides sum_power high_iff
      by (auto simp: padic_modulus_def)
  next
    case above
    have min_law: "?vs = min ?vn ?s"
      by (rule multiplicity_sum_min) (use above n_positive delta_positive in auto)
    have no_power: "\<not> p ^ Suc ?s dvd n + delta"
      using sum_power min_law above by simp
    show ?thesis using residue_divides no_power min_law above
      by (auto simp: padic_modulus_def)
  qed
qed

lemma padic_loss_residue_iff:
  fixes p n delta :: nat
  assumes prime_p: "prime p" and n_positive: "0 < n" and delta_positive: "0 < delta"
  shows "multiplicity p (n + delta) < multiplicity p n \<longleftrightarrow>
    n mod padic_modulus p (multiplicity p delta) = 0"
proof -
  let ?s = "multiplicity p delta"
  let ?m = "padic_modulus p ?s"
  let ?vn = "multiplicity p n"
  let ?vs = "multiplicity p (n + delta)"
  have sum_positive: "0 < n + delta" using n_positive by simp
  have residue_divides: "n mod ?m = 0 \<longleftrightarrow> p ^ Suc ?s dvd n"
    by (simp add: padic_modulus_def dvd_eq_mod_eq_0)
  have n_power: "p ^ Suc ?s dvd n \<longleftrightarrow> Suc ?s \<le> ?vn"
    by (rule padic_power_dvd_iff_valuation[OF prime_p n_positive])
  consider (below) "?vn < ?s" | (equal) "?vn = ?s" | (above) "?s < ?vn"
    by arith
  then show ?thesis
  proof cases
    case below
    have min_law: "?vs = min ?vn ?s"
      by (rule multiplicity_sum_min) (use below n_positive delta_positive in auto)
    have no_power: "\<not> p ^ Suc ?s dvd n"
      using n_power below by simp
    show ?thesis using residue_divides no_power min_law below by auto
  next
    case equal
    have n_power_low: "p ^ ?s dvd n"
      by (rule multiplicity_dvd') (simp add: equal)
    have delta_power_low: "p ^ ?s dvd delta"
      by (rule multiplicity_dvd') simp
    have sum_power_low: "p ^ ?s dvd n + delta"
      by (rule dvd_add[OF n_power_low delta_power_low])
    have sum_lower: "?s \<le> ?vs"
      using padic_power_dvd_iff_valuation[OF prime_p sum_positive, of ?s]
        sum_power_low by simp
    have no_source_power: "\<not> p ^ Suc ?s dvd n"
      using n_power equal by simp
    show ?thesis using residue_divides no_source_power equal sum_lower
      by (auto simp: padic_modulus_def)
  next
    case above
    have min_law: "?vs = min ?vn ?s"
      by (rule multiplicity_sum_min) (use above n_positive delta_positive in auto)
    show ?thesis using residue_divides n_power min_law above by auto
  qed
qed

lemma padic_event_residue_exact:
  assumes "prime p" "0 < n" "0 < delta"
  shows "padic_value_event p n delta = padic_residue_event p n delta"
  using padic_gain_residue_iff[OF assms]
    padic_loss_residue_iff[OF assms]
  by (auto simp: padic_value_event_def padic_residue_event_def Let_def)

definition padic_cycle_period :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "padic_cycle_period p s t = p ^ max 0 (Suc s - t)"

lemma padic_cycle_period_divisibility:
  fixes p delta displacement :: nat
  assumes prime_p: "prime p" and delta_positive: "0 < delta"
    and displacement_positive: "0 < displacement"
  shows "p ^ Suc (multiplicity p delta) dvd
    padic_cycle_period p (multiplicity p delta) (multiplicity p displacement) * displacement"
proof -
  let ?s = "multiplicity p delta"
  let ?t = "multiplicity p displacement"
  let ?e = "max 0 (Suc ?s - ?t)"
  let ?q = "padic_cycle_period p ?s ?t"
  have prime_elem: "prime_elem p" using prime_p by simp
  have q_positive: "0 < ?q"
    using prime_gt_0_nat[OF prime_p]
    by (simp add: padic_cycle_period_def)
  have q_nonzero: "?q \<noteq> 0" using q_positive by simp
  have displacement_nonzero: "displacement \<noteq> 0"
    using displacement_positive by simp
  have product_positive: "0 < ?q * displacement"
    using q_positive displacement_positive by simp
  have qvaluation: "multiplicity p ?q = ?e"
    using prime_elem by (simp add: padic_cycle_period_def)
  have product_valuation: "multiplicity p (?q * displacement) = ?e + ?t"
    using prime_elem_multiplicity_mult_distrib[OF prime_elem q_nonzero displacement_nonzero]
    by (simp add: qvaluation)
  have enough: "Suc ?s \<le> ?e + ?t"
    by (simp add: max_def; arith)
  have valuation_bound:
    "Suc ?s \<le> multiplicity p (?q * displacement)"
    using product_valuation enough by arith
  show ?thesis by (rule multiplicity_dvd'[OF valuation_bound])
qed

definition padic_interval_step_guard :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "padic_interval_step_guard lower upper n delta \<longleftrightarrow>
    lower \<le> n \<and> n + delta < upper"


lemma padic_event_periodic_on_guarded_additive_cycle:
  fixes p lower upper base displacement k delta :: nat
  assumes prime_p: "prime p" and lower_positive: "0 < lower"
    and delta_positive: "0 < delta" and displacement_positive: "0 < displacement"
    and guarded: "\<And>i. i \<le> padic_cycle_period p (multiplicity p delta)
        (multiplicity p displacement) \<Longrightarrow>
      padic_interval_step_guard lower upper
        (base + (k+i)*displacement) delta"
  shows "padic_value_event p (base + k*displacement) delta =
    padic_value_event p
      (base + (k + padic_cycle_period p (multiplicity p delta)
        (multiplicity p displacement))*displacement) delta"
proof -
  let ?q = "padic_cycle_period p (multiplicity p delta) (multiplicity p displacement)"
  let ?m = "padic_modulus p (multiplicity p delta)"
  let ?now = "base + k*displacement"
  let ?later = "base + (k+?q)*displacement"
  have current_guard: "padic_interval_step_guard lower upper ?now delta"
    using guarded[of 0] by simp
  have later_guard: "padic_interval_step_guard lower upper ?later delta"
    using guarded[of ?q] by simp
  have now_positive: "0 < ?now"
    using current_guard lower_positive unfolding padic_interval_step_guard_def by arith
  have later_positive: "0 < ?later"
    using later_guard lower_positive unfolding padic_interval_step_guard_def by arith
  have shift_divides: "?m dvd ?q * displacement"
    unfolding padic_modulus_def
    by (rule padic_cycle_period_divisibility[OF prime_p delta_positive displacement_positive])
  have state_shift: "?later = ?now + ?q*displacement"
    by (simp add: algebra_simps)
  have shift_zero: "(?q*displacement) mod ?m = 0"
    using shift_divides by (simp only: dvd_eq_mod_eq_0)
  have same_residue: "?later mod ?m = ?now mod ?m"
  proof -
    have "?later mod ?m = (?now + ?q*displacement) mod ?m"
      by (simp only: state_shift)
    also have "... = (?now + (?q*displacement) mod ?m) mod ?m"
      by (rule mod_add_right_eq[symmetric])
    also have "... = ?now mod ?m" by (simp only: shift_zero add_0_right)
    finally show ?thesis .
  qed
  have now_exact: "padic_value_event p ?now delta = padic_residue_event p ?now delta"
    by (rule padic_event_residue_exact[OF prime_p now_positive delta_positive])
  have later_exact: "padic_value_event p ?later delta = padic_residue_event p ?later delta"
    by (rule padic_event_residue_exact[OF prime_p later_positive delta_positive])
  show ?thesis
    using now_exact later_exact same_residue
    by (simp add: padic_residue_event_def Let_def)
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms padic_power_dvd_iff_valuation padic_negative_residue_add
      padic_gain_residue_iff padic_loss_residue_iff padic_event_residue_exact
      padic_cycle_period_divisibility padic_event_periodic_on_guarded_additive_cycle})
    then () else error "Prime-adic event action proof depends on an oracle";
\<close>
end
