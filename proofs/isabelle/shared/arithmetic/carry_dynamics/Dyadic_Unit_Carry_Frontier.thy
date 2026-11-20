theory Dyadic_Unit_Carry_Frontier
  imports Main
begin

text \<open>
An exponent phase may be reduced only after an exact unit return has been
proved at the precision used by the observation.  The results below are
generic arithmetic; they do not establish a source period or admit a family
transition.  Families supply those guards and source refinements separately.
\<close>

definition dyadic_affine_carry_at ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dyadic_affine_carry_at a n u b cut bits =
    ((a^n * (u mod 2^cut) + (b mod 2^cut)) mod 2^(cut+bits)) div 2^cut"

lemma dyadic_unit_power_phase_reduction:
  fixes a :: nat
  assumes unit_return: "a^period mod 2^precision = 1"
      and exponent: "n = phase + repetitions * period"
  shows "a^n mod 2^precision = a^phase mod 2^precision"
proof -
  have precision_positive: "0 < precision"
  proof (cases precision)
    case 0
    then show ?thesis using unit_return by simp
  next
    case (Suc p)
    then show ?thesis by simp
  qed
  have repeated_return: "(a^period)^repetitions mod 2^precision = 1"
    using unit_return
  proof (induction repetitions)
    case 0
    then show ?case using precision_positive by simp
  next
    case (Suc repetitions)
    have step:
      "((a^period)^Suc repetitions) mod 2^precision =
        (((a^period)^repetitions mod 2^precision) *
          (a^period mod 2^precision)) mod 2^precision"
    proof -
      have "((a^period)^Suc repetitions) mod 2^precision =
          ((a^period)^repetitions * a^period) mod 2^precision"
          by (simp only: power_Suc mult.commute)
      also have "... = (((a^period)^repetitions mod 2^precision) *
          (a^period mod 2^precision)) mod 2^precision"
          by (rule mod_mult_eq[symmetric])
      finally show ?thesis .
    qed
    show ?case using step Suc.IH unit_return precision_positive by simp
  qed
  have exponent_order: "n = phase + period * repetitions"
    using exponent by (simp only: mult.commute)
  have factorization: "a^n = a^phase * (a^period)^repetitions"
    by (simp only: exponent_order power_add power_mult)
  have "a^n mod 2^precision =
      ((a^phase mod 2^precision) *
       ((a^period)^repetitions mod 2^precision)) mod 2^precision"
    unfolding factorization by (rule mod_mult_eq[symmetric])
  also have "... = a^phase mod 2^precision"
    using repeated_return by simp
  finally show ?thesis .
qed

text \<open>A return modulo one dyadic bit lifts after doubling the exponent.
This uses only the binomial square of a returned unit residue; it makes no
claim that the displayed exponent is minimal.\<close>

lemma dyadic_unit_return_doubles:
  fixes a period precision :: nat
  assumes precision_positive: "0 < precision"
      and unit_return: "a^period mod 2^precision = 1"
  shows "a^(2*period) mod 2^(precision+1) = 1"
proof -
  let ?x = "a^period"
  let ?m = "2^precision"
  let ?q = "?x div ?m"
  have x_decomposition: "?x = ?m * ?q + 1"
    using div_mult_mod_eq[of ?x ?m] unit_return
    by (simp add: mult.commute)
  have square_expansion:
    "(?m * ?q + 1)^2 = (?m * ?q)^2 + 2*(?m*?q) + 1"
    by (simp add: power2_eq_square algebra_simps)
  have exponent_doubling: "a^(2*period) = (a^period)^2"
    by (simp add: power_mult mult.commute)
  have power_bound: "precision + 1 \<le> 2*precision"
    using precision_positive by arith
  have power_divisor:
    "(2::nat)^(precision+1) dvd (2::nat)^(2*precision)"
    using power_bound by (rule le_imp_power_dvd)
  have square_term_form:
    "(?m * ?q)^2 = 2^(2*precision) * ?q^2"
    by (simp add: power2_eq_square power_mult mult.commute algebra_simps)
  have square_term_divisor: "2^(precision+1) dvd (?m*?q)^2"
  proof -
    have "2^(precision+1) dvd 2^(2*precision) * ?q^2"
      by (rule dvd_mult2[OF power_divisor])
    then show ?thesis by (simp only: square_term_form)
  qed
  have cross_term_form: "2*(?m*?q) = 2^(precision+1) * ?q"
    by (simp add: power_Suc mult.assoc)
  have cross_term_divisor: "2^(precision+1) dvd 2*(?m*?q)"
    by (rule dvdI[where k="?q"]) (simp only: cross_term_form)
  have sum_divisor:
    "2^(precision+1) dvd (?m*?q)^2 + 2*(?m*?q)"
    by (rule dvd_add[OF square_term_divisor cross_term_divisor])
  have sum_zero:
    "((?m*?q)^2 + 2*(?m*?q)) mod 2^(precision+1) = 0"
    using sum_divisor by (simp add: mod_eq_0_iff_dvd)
  have return_equation:
    "a^(2*period) = 1 + ((?m*?q)^2 + 2*(?m*?q))"
    using x_decomposition square_expansion exponent_doubling by simp
  have modulus_gt_one: "1 < (2::nat)^(precision+1)"
    by (rule one_less_power) simp_all
  have one_mod: "1 mod (2::nat)^(precision+1) = 1"
    using modulus_gt_one by simp
  have add_mod_left:
    "(1 + ((?m*?q)^2 + 2*(?m*?q))) mod 2^(precision+1) =
      (1 mod 2^(precision+1) + ((?m*?q)^2 + 2*(?m*?q))) mod
        2^(precision+1)"
    by (rule mod_add_left_eq[symmetric])
  have add_mod_right:
    "(1 mod 2^(precision+1) + ((?m*?q)^2 + 2*(?m*?q))) mod
        2^(precision+1) =
      (1 mod 2^(precision+1) +
        (((?m*?q)^2 + 2*(?m*?q)) mod 2^(precision+1))) mod
        2^(precision+1)"
    by (rule mod_add_right_eq[symmetric])
  have final_residue:
    "(1 + ((?m*?q)^2 + 2*(?m*?q))) mod 2^(precision+1) = 1"
    using add_mod_left add_mod_right one_mod sum_zero by simp
  show ?thesis using return_equation final_residue by simp
qed

definition dyadic_unit_phase_period :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "dyadic_unit_phase_period base precision =
    (if base = 3 then
       (if precision = 1 then 1 else if precision = 2 then 2
        else 2^(precision-2))
     else if base = 5 then
       (if precision \<le> 2 then 1 else 2^(precision-2))
     else if base = 15 then
       (if precision = 1 then 1 else if precision \<le> 5 then 2
        else 2^(precision-4))
     else 0)"

lemma dyadic_three_return_large:
  assumes precision: "3 \<le> precision"
  shows "(3::nat)^(2^(precision-2)) mod 2^precision = 1"
  using precision
proof (induction precision)
  case 0
  then show ?case by simp
next
  case (Suc precision)
  show ?case
  proof (cases "precision = 2")
    case True
    then show ?thesis by simp
  next
    case False
    have previous_precision: "3 \<le> precision"
      using Suc.prems False by arith
    have previous:
      "(3::nat)^(2^(precision-2)) mod 2^precision = 1"
      using Suc.IH previous_precision by blast
    have lifted:
      "(3::nat)^(2 * 2^(precision-2)) mod 2^(precision+1) = 1"
      by (rule dyadic_unit_return_doubles[OF _ previous])
        (use previous_precision in arith)
    have index: "Suc precision - 2 = Suc (precision - 2)"
      using previous_precision by arith
    have exponent: "(2::nat)^(Suc precision-2) = 2 * 2^(precision-2)"
      by (simp only: index power_Suc)
    show ?thesis using lifted exponent by simp
  qed
qed

lemma dyadic_five_return_large:
  assumes precision: "3 \<le> precision"
  shows "(5::nat)^(2^(precision-2)) mod 2^precision = 1"
  using precision
proof (induction precision)
  case 0
  then show ?case by simp
next
  case (Suc precision)
  show ?case
  proof (cases "precision = 2")
    case True
    then show ?thesis by simp
  next
    case False
    have previous_precision: "3 \<le> precision"
      using Suc.prems False by arith
    have previous:
      "(5::nat)^(2^(precision-2)) mod 2^precision = 1"
      using Suc.IH previous_precision by blast
    have lifted:
      "(5::nat)^(2 * 2^(precision-2)) mod 2^(precision+1) = 1"
      by (rule dyadic_unit_return_doubles[OF _ previous])
        (use previous_precision in arith)
    have index: "Suc precision - 2 = Suc (precision - 2)"
      using previous_precision by arith
    have exponent: "(2::nat)^(Suc precision-2) = 2 * 2^(precision-2)"
      by (simp only: index power_Suc)
    show ?thesis using lifted exponent by simp
  qed
qed

lemma dyadic_fifteen_return_large:
  assumes precision: "5 \<le> precision"
  shows "(15::nat)^(2^(precision-4)) mod 2^precision = 1"
  using precision
proof (induction precision)
  case 0
  then show ?case by simp
next
  case (Suc precision)
  show ?case
  proof (cases "precision = 4")
    case True
    then show ?thesis by simp
  next
    case False
    have previous_precision: "5 \<le> precision"
      using Suc.prems False by arith
    have previous:
      "(15::nat)^(2^(precision-4)) mod 2^precision = 1"
      using Suc.IH previous_precision by blast
    have lifted:
      "(15::nat)^(2 * 2^(precision-4)) mod 2^(precision+1) = 1"
      by (rule dyadic_unit_return_doubles[OF _ previous])
        (use previous_precision in arith)
    have index: "Suc precision - 4 = Suc (precision - 4)"
      using previous_precision by arith
    have exponent: "(2::nat)^(Suc precision-4) = 2 * 2^(precision-4)"
      by (simp only: index power_Suc)
    show ?thesis using lifted exponent by simp
  qed
qed

lemma dyadic_fifteen_return_small:
  assumes precision_positive: "0 < precision"
      and precision_bound: "precision \<le> 5"
  shows "(15::nat)^2 mod 2^precision = 1"
proof -
  have precision_cases:
    "precision = 1 \<or> precision = 2 \<or> precision = 3 \<or>
      precision = 4 \<or> precision = 5"
    using precision_positive precision_bound by arith
  from precision_cases show ?thesis by auto
qed

lemma dyadic_three_unit_phase_period_returns:
  assumes precision: "0 < precision"
  shows "(3::nat)^dyadic_unit_phase_period 3 precision mod 2^precision = 1"
proof (cases "precision = 1")
  case True
  then show ?thesis by (simp add: dyadic_unit_phase_period_def)
next
  case False
  show ?thesis
  proof (cases "precision = 2")
    case True
    then show ?thesis by (simp add: dyadic_unit_phase_period_def)
  next
    case False
    have bound: "3 \<le> precision" using precision False \<open>precision \<noteq> 1\<close> by arith
    have returned:
      "(3::nat)^(2^(precision-2)) mod 2^precision = 1"
      by (rule dyadic_three_return_large[OF bound])
    show ?thesis
      using returned \<open>precision \<noteq> 1\<close> False
      by (simp add: dyadic_unit_phase_period_def)
  qed
qed

lemma dyadic_five_unit_phase_period_returns:
  assumes precision: "0 < precision"
  shows "(5::nat)^dyadic_unit_phase_period 5 precision mod 2^precision = 1"
proof (cases "precision \<le> 2")
  case True
  have precision_cases: "precision = 1 \<or> precision = 2"
    using precision True by arith
  from precision_cases show ?thesis
    by (auto simp: dyadic_unit_phase_period_def)
next
  case False
  have bound: "3 \<le> precision" using False by arith
  have returned:
    "(5::nat)^(2^(precision-2)) mod 2^precision = 1"
    by (rule dyadic_five_return_large[OF bound])
  show ?thesis using returned False
    by (simp add: dyadic_unit_phase_period_def)
qed

lemma dyadic_fifteen_unit_phase_period_returns:
  assumes precision: "0 < precision"
  shows "(15::nat)^dyadic_unit_phase_period 15 precision mod 2^precision = 1"
proof (cases "precision = 1")
  case True
  then show ?thesis by (simp add: dyadic_unit_phase_period_def)
next
  case False
  show ?thesis
  proof (cases "precision \<le> 5")
    case True
    have returned: "(15::nat)^2 mod 2^precision = 1"
      by (rule dyadic_fifteen_return_small[OF precision True])
    show ?thesis using returned False True
      by (simp add: dyadic_unit_phase_period_def)
  next
    case False
    have bound: "5 \<le> precision" using False by arith
    have returned:
      "(15::nat)^(2^(precision-4)) mod 2^precision = 1"
      by (rule dyadic_fifteen_return_large[OF bound])
    show ?thesis using returned False \<open>precision \<noteq> 1\<close>
      by (simp add: dyadic_unit_phase_period_def)
  qed
qed

theorem dyadic_unit_phase_period_returns:
  assumes base: "base = 3 \<or> base = 5 \<or> base = 15"
      and precision: "0 < precision"
  shows "base^dyadic_unit_phase_period base precision mod 2^precision = 1"
proof (cases "base = 3")
  case True
  have returned:
    "(3::nat)^dyadic_unit_phase_period 3 precision mod 2^precision = 1"
    by (rule dyadic_three_unit_phase_period_returns[OF precision])
  show ?thesis using True returned by simp
next
  case False
  show ?thesis
  proof (cases "base = 5")
    case True
    have returned:
      "(5::nat)^dyadic_unit_phase_period 5 precision mod 2^precision = 1"
      by (rule dyadic_five_unit_phase_period_returns[OF precision])
    show ?thesis using True returned by simp
  next
    case False
    have base_fifteen: "base = 15" using base False \<open>base \<noteq> 3\<close> by blast
    have returned:
      "(15::nat)^dyadic_unit_phase_period 15 precision mod 2^precision = 1"
      by (rule dyadic_fifteen_unit_phase_period_returns[OF precision])
    show ?thesis using base_fifteen returned by simp
  qed
qed

lemma dyadic_affine_carry_at_bound:
  assumes "bits > 0"
  shows "dyadic_affine_carry_at a n u b cut bits < 2^bits"
proof -
  have modulus_positive: "0 < (2::nat)^(cut+bits)" by simp
  have residue_bound:
    "((a^n * (u mod 2^cut) + (b mod 2^cut)) mod 2^(cut+bits)) <
      2^(cut+bits)"
    by (rule mod_less_divisor[OF modulus_positive])
  have modulus_factor: "(2::nat)^(cut+bits) = 2^cut * 2^bits"
    by (simp only: power_add)
  show ?thesis
    unfolding dyadic_affine_carry_at_def
    using residue_bound assms modulus_factor
    by (simp add: div_less_iff_less_mult ac_simps)
qed

lemma dyadic_affine_carry_at_phase_reduction:
  assumes unit_return: "a^period mod 2^(cut+bits) = 1"
      and exponent: "n = phase + repetitions * period"
  shows "dyadic_affine_carry_at a n u b cut bits =
    dyadic_affine_carry_at a phase u b cut bits"
proof -
  have power:
    "a^n mod 2^(cut+bits) = a^phase mod 2^(cut+bits)"
    by (rule dyadic_unit_power_phase_reduction[OF unit_return exponent])
  have numerator:
    "(a^n * (u mod 2^cut) + (b mod 2^cut)) mod 2^(cut+bits) =
      (a^phase * (u mod 2^cut) + (b mod 2^cut)) mod 2^(cut+bits)"
  proof -
    let ?M = "2^(cut+bits)"
    let ?x = "u mod 2^cut"
    let ?y = "b mod 2^cut"
    have left:
      "(a^n * ?x) mod ?M = ((a^n mod ?M) * ?x) mod ?M"
      by (rule mod_mult_left_eq[symmetric])
    have right:
      "(a^phase * ?x) mod ?M = ((a^phase mod ?M) * ?x) mod ?M"
      by (rule mod_mult_left_eq[symmetric])
    have product: "(a^n * ?x) mod ?M = (a^phase * ?x) mod ?M"
      using left right power by simp
    have add_left:
      "(a^n * ?x + ?y) mod ?M = ((a^n * ?x) mod ?M + ?y) mod ?M"
      by (rule mod_add_left_eq[symmetric])
    have add_right:
      "((a^phase * ?x) mod ?M + ?y) mod ?M =
        (a^phase * ?x + ?y) mod ?M"
      by (rule mod_add_left_eq)
    have "(a^n * ?x + ?y) mod ?M =
        ((a^n * ?x) mod ?M + ?y) mod ?M"
      by (rule add_left)
    also have "... = ((a^phase * ?x) mod ?M + ?y) mod ?M"
      using product by simp
    also have "... = (a^phase * ?x + ?y) mod ?M"
      by (rule add_right)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding dyadic_affine_carry_at_def
    using numerator by simp
qed

ML \<open>
  val checked = @{thms dyadic_affine_carry_at_def
    dyadic_unit_power_phase_reduction dyadic_unit_return_doubles
    dyadic_unit_phase_period_def dyadic_three_return_large
    dyadic_five_return_large dyadic_fifteen_return_large
    dyadic_fifteen_return_small dyadic_three_unit_phase_period_returns
    dyadic_five_unit_phase_period_returns
    dyadic_fifteen_unit_phase_period_returns
    dyadic_unit_phase_period_returns dyadic_affine_carry_at_bound
    dyadic_affine_carry_at_phase_reduction};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Dyadic unit carry frontier depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped dyadic unit carry frontier proof" else ();
\<close>

end
