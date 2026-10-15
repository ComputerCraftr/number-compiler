theory Fermat_Dyadic_Unit_Pivot
  imports Fermat_Binomial_Negacyclic_Source
begin

text \<open>The normalized dyadic unit is a source-local coordinate for
\<open>3^(2^t)\<close>.  Its recurrence locates the first changed bit in two aligned
unit windows.  This does not identify those windows with a direct XOR edit of
the full Fermat source, nor does it provide a global temporal fold or prime
predicate.\<close>

fun fermat_dyadic_unit :: "nat \<Rightarrow> nat" where
  "fermat_dyadic_unit 0 = 0"
| "fermat_dyadic_unit (Suc 0) = 1"
| "fermat_dyadic_unit (Suc (Suc t)) =
    fermat_dyadic_unit (Suc t) +
      2^(Suc (Suc t)) * fermat_dyadic_unit (Suc t)^2"

lemma fermat_dyadic_unit_successor_exact:
  assumes "1 \<le> t"
  shows "fermat_dyadic_unit (Suc t) = fermat_dyadic_unit t +
      2^(Suc t) * fermat_dyadic_unit t^2"
  using assms by (cases t) simp_all

lemma fermat_dyadic_unit_initial_values:
  "fermat_dyadic_unit 1 = 1"
  "fermat_dyadic_unit 2 = 5"
  "fermat_dyadic_unit 3 = 205"
proof -
  have two_index: "(2::nat) = Suc (Suc 0)" by simp
  have three_index: "(3::nat) = Suc (Suc (Suc 0))" by simp
  have unit_two: "fermat_dyadic_unit (Suc (Suc 0)) = 5"
    by (simp add: fermat_dyadic_unit.simps)
  have unit_three: "fermat_dyadic_unit (Suc (Suc (Suc 0))) = 205"
    by (simp add: fermat_dyadic_unit.simps)
  show "fermat_dyadic_unit 1 = 1" by simp
  show "fermat_dyadic_unit 2 = 5"
    using two_index unit_two by metis
  show "fermat_dyadic_unit 3 = 205"
    using three_index unit_three by metis
qed

lemma fermat_dyadic_unit_source_equation:
  "t = 0 \<or>
    (3::nat)^(2^t) = 1 + 2^(t+2) * fermat_dyadic_unit t"
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  show ?case
  proof (cases t)
    case 0
    then show ?thesis by simp
  next
    case (Suc r)
    then have old:
      "(3::nat)^(2^t) = 1 + 2^(t+2) * fermat_dyadic_unit t"
      using Suc.IH by auto
    have t_positive: "1 \<le> t" using Suc by simp
    have next_unit:
      "fermat_dyadic_unit (Suc t) =
        fermat_dyadic_unit t +
          2^(Suc t) * fermat_dyadic_unit t^2"
      by (rule fermat_dyadic_unit_successor_exact[OF t_positive])
    have exponent: "(2::nat)^(Suc t) = 2^t * 2"
      by (simp only: power_Suc)
    have square:
      "(1 + 2^(t+2) * fermat_dyadic_unit t)^2 =
        1 + 2^(Suc t+2) *
          (fermat_dyadic_unit t +
            2^(Suc t) * fermat_dyadic_unit t^2)"
    proof -
      have p1: "(2::nat)^(t+2) = 2 * 2^(Suc t)"
        by (simp add: power_Suc algebra_simps)
      have p2: "(2::nat)^(Suc t+2) = 4 * 2^(Suc t)"
        by (simp add: power_Suc algebra_simps)
      show ?thesis
        using p1 p2 by (simp add: power2_eq_square algebra_simps)
    qed
    have source_square:
      "(3::nat)^(2^(Suc t)) = ((3::nat)^(2^t))^2"
    proof -
      have power_split:
        "(3::nat)^(2^(Suc t)) = (3::nat)^(2^t * 2)"
        by (simp only: exponent)
      show ?thesis using power_split by (simp only: power_mult)
    qed
    show ?thesis
      using old next_unit square source_square by simp
  qed
qed

lemma fermat_dyadic_unit_positive:
  assumes "1 \<le> t"
  shows "0 < fermat_dyadic_unit t"
  using assms
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  note positive_ih = Suc.IH
  show ?case
  proof (cases t)
    case 0
    then show ?thesis by simp
  next
    case (Suc r)
    have level: "1 \<le> t" using Suc by simp
    have positive: "0 < fermat_dyadic_unit t"
      using positive_ih level by simp
    have successor:
      "fermat_dyadic_unit (Suc t) = fermat_dyadic_unit t +
        2^(Suc t) * fermat_dyadic_unit t^2"
      by (rule fermat_dyadic_unit_successor_exact[OF level])
    show ?thesis using positive successor by simp
  qed
qed

lemma fermat_dyadic_unit_odd:
  assumes "1 \<le> t"
  shows "odd (fermat_dyadic_unit t)"
  using assms
proof (induction t)
  case 0
  then show ?case by simp
next
  case (Suc t)
  note odd_ih = Suc.IH
  show ?case
  proof (cases t)
    case 0
    then show ?thesis by simp
  next
    case (Suc r)
    have level: "1 \<le> t" using Suc by simp
    have old_odd: "odd (fermat_dyadic_unit t)"
      using odd_ih level by simp
    have successor:
      "fermat_dyadic_unit (Suc t) = fermat_dyadic_unit t +
        2^(Suc t) * fermat_dyadic_unit t^2"
      by (rule fermat_dyadic_unit_successor_exact[OF level])
    show ?thesis using old_odd successor by simp
  qed
qed

theorem fermat_dyadic_unit_pivot_factorization:
  assumes level: "1 \<le> t"
  shows "fermat_dyadic_unit (Suc t) - fermat_dyadic_unit t =
      2^(Suc t) * fermat_dyadic_unit t^2"
    and "odd (fermat_dyadic_unit t^2)"
  using fermat_dyadic_unit_successor_exact[OF level]
    fermat_dyadic_unit_odd[OF level]
  by simp_all

theorem fermat_dyadic_unit_pivot_exact_valuation:
  assumes level: "1 \<le> t"
  shows "2^(Suc t) dvd
      fermat_dyadic_unit (Suc t) - fermat_dyadic_unit t"
    and "\<not> 2^(Suc (Suc t)) dvd
      fermat_dyadic_unit (Suc t) - fermat_dyadic_unit t"
proof -
  have factor:
    "fermat_dyadic_unit (Suc t) - fermat_dyadic_unit t =
      2^(Suc t) * fermat_dyadic_unit t^2"
    using fermat_dyadic_unit_pivot_factorization(1)[OF level] .
  have odd: "odd (fermat_dyadic_unit t^2)"
    using fermat_dyadic_unit_pivot_factorization(2)[OF level] .
  show "2^(Suc t) dvd
      fermat_dyadic_unit (Suc t) - fermat_dyadic_unit t"
    using factor by (auto simp: dvd_def)
  show "\<not> 2^(Suc (Suc t)) dvd
      fermat_dyadic_unit (Suc t) - fermat_dyadic_unit t"
  proof
    assume divides:
      "2^(Suc (Suc t)) dvd
        fermat_dyadic_unit (Suc t) - fermat_dyadic_unit t"
    then obtain q where equation:
      "fermat_dyadic_unit (Suc t) - fermat_dyadic_unit t =
        2^(Suc (Suc t))*q"
      by (elim dvdE)
    have factor_equality:
      "2^(Suc t) * fermat_dyadic_unit t^2 = 2^(Suc t) * (2*q)"
      using factor equation by (simp add: power_Suc algebra_simps)
    have power_nonzero: "(2::nat)^(Suc t) \<noteq> 0" by simp
    have cofactor: "fermat_dyadic_unit t^2 = 2*q"
      using factor_equality mult_left_cancel[OF power_nonzero] by blast
    have even: "even (fermat_dyadic_unit t^2)"
      using cofactor by simp
    show False using odd even by simp
  qed
qed

theorem fermat_dyadic_unit_fixed_prefix:
  assumes level: "1 \<le> t" and precision: "p \<le> Suc t"
  shows "fermat_dyadic_unit (Suc t) mod (2::nat)^p =
    fermat_dyadic_unit t mod (2::nat)^p"
proof -
  have power_divides: "(2::nat)^p dvd (2::nat)^(Suc t)"
    using precision by (rule le_imp_power_dvd)
  have multiple:
    "(2::nat)^p dvd (2::nat)^(Suc t) * fermat_dyadic_unit t^2"
    using power_divides by (rule dvd_mult2)
  have next_unit:
    "fermat_dyadic_unit (Suc t) = fermat_dyadic_unit t +
      2^(Suc t) * fermat_dyadic_unit t^2"
    by (rule fermat_dyadic_unit_successor_exact[OF level])
  have increment_zero:
    "((2::nat)^(Suc t) * fermat_dyadic_unit t^2) mod (2::nat)^p = 0"
    using multiple by (simp add: mod_eq_0_iff_dvd)
  show ?thesis
    using next_unit increment_zero
    by (simp add: mod_add_eq[symmetric])
qed

text \<open>A guarded run edit belongs to the normalized unit window.  The
following finite-slice equation is the signed arithmetic contribution of
toggling a constant guarded run; it is independent of a full source SLP and
does not claim that the unit-relative coordinates are full-word positions.\<close>

definition fermat_run_weight :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "fermat_run_weight start width = (2::int)^(start+width) - 2^start"

definition fermat_run_slice_value ::
    "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> int" where
  "fermat_run_slice_value start width bits =
    (\<Sum>j\<in>{..<width}. if bits (start+j) then (2::int)^(start+j) else 0)"

lemma fermat_run_weight_sum:
  "(\<Sum>j\<in>{..<width}. (2::int)^(start+j)) = fermat_run_weight start width"
proof (induction width)
  case 0
  then show ?case by (simp add: fermat_run_weight_def)
next
  case (Suc width)
  have sum_step:
    "(\<Sum>j\<in>{..<Suc width}. (2::int)^(start+j)) =
      (\<Sum>j\<in>{..<width}. (2::int)^(start+j)) +
        (2::int)^(start+width)"
    by (simp only: sum.lessThan_Suc)
  have weight_step:
    "fermat_run_weight start (Suc width) =
      fermat_run_weight start width + (2::int)^(start+width)"
    unfolding fermat_run_weight_def
    by (simp add: power_Suc algebra_simps)
  show ?case
    using sum_step Suc.IH weight_step by simp
qed

theorem fermat_guarded_unit_run_delta:
  fixes bits :: "nat \<Rightarrow> bool"
  assumes guard: "\<And>j. j < width \<Longrightarrow> bits (start+j) = expected"
  shows "fermat_run_slice_value start width (\<lambda>i. \<not> bits i) -
      fermat_run_slice_value start width bits =
    (if expected then -fermat_run_weight start width
      else fermat_run_weight start width)"
proof -
  have pointwise:
    "\<And>j. j < width \<Longrightarrow>
      (if \<not> bits (start+j) then (2::int)^(start+j) else 0) -
        (if bits (start+j) then (2::int)^(start+j) else 0) =
      (if expected then -1 else 1) * (2::int)^(start+j)"
    using guard by (cases expected) simp_all
  have sum_difference:
    "(\<Sum>j\<in>{..<width}.
        (if \<not> bits (start+j) then (2::int)^(start+j) else 0) -
          (if bits (start+j) then (2::int)^(start+j) else 0)) =
      (if expected then -1 else 1) *
        (\<Sum>j\<in>{..<width}. (2::int)^(start+j))"
  proof -
    have terms:
      "(\<Sum>j\<in>{..<width}.
          (if \<not> bits (start+j) then (2::int)^(start+j) else 0) -
            (if bits (start+j) then (2::int)^(start+j) else 0)) =
        (\<Sum>j\<in>{..<width}.
          (if expected then -1 else 1) * (2::int)^(start+j))"
    proof (rule sum.cong)
      show "{..<width} = {..<width}" by simp
      fix j
      assume member: "j \<in> {..<width}"
      then have j_below: "j < width" by simp
      show "(if \<not> bits (start+j) then (2::int)^(start+j) else 0) -
          (if bits (start+j) then (2::int)^(start+j) else 0) =
        (if expected then -1 else 1) * (2::int)^(start+j)"
        by (rule pointwise[OF j_below])
    qed
    show ?thesis using terms by (simp add: sum_distrib_left)
  qed
  have delta:
    "fermat_run_slice_value start width (\<lambda>i. \<not> bits i) -
      fermat_run_slice_value start width bits =
      (\<Sum>j\<in>{..<width}.
        (if \<not> bits (start+j) then (2::int)^(start+j) else 0) -
          (if bits (start+j) then (2::int)^(start+j) else 0))"
    by (simp add: fermat_run_slice_value_def sum_subtractf)
  show ?thesis
    using delta sum_difference fermat_run_weight_sum[of start width]
    by (cases expected) (simp_all add: fermat_run_weight_def)
qed

theorem fermat_guarded_unit_run_fold_update:
  assumes guard: "\<And>j. j < width \<Longrightarrow> bits (start+j) = expected"
  shows "(base + fermat_run_slice_value start width (\<lambda>i. \<not> bits i)) mod
      ((2::int)^modulus_width + 1) =
    (base + fermat_run_slice_value start width bits +
      (if expected then -fermat_run_weight start width
        else fermat_run_weight start width)) mod
      ((2::int)^modulus_width + 1)"
proof -
  have delta:
    "fermat_run_slice_value start width (\<lambda>i. \<not> bits i) -
      fermat_run_slice_value start width bits =
      (if expected then -fermat_run_weight start width
        else fermat_run_weight start width)"
    using fermat_guarded_unit_run_delta
      [where start=start and width=width and bits=bits and expected=expected,
        OF guard] .
  have value_update:
    "fermat_run_slice_value start width (\<lambda>i. \<not> bits i) =
      fermat_run_slice_value start width bits +
        (if expected then -fermat_run_weight start width
          else fermat_run_weight start width)"
    using delta by linarith
  show ?thesis using value_update by (simp add: add.assoc)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms fermat_dyadic_unit_source_equation fermat_dyadic_unit_positive
      fermat_dyadic_unit_odd fermat_dyadic_unit_pivot_factorization
      fermat_dyadic_unit_pivot_exact_valuation
      fermat_dyadic_unit_initial_values
      fermat_dyadic_unit_fixed_prefix fermat_run_weight_sum
      fermat_guarded_unit_run_delta fermat_guarded_unit_run_fold_update}) then ()
    else error "Dyadic Fermat unit/pivot laws depend on an oracle";
\<close>

end
