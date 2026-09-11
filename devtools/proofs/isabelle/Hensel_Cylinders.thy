theory Hensel_Cylinders
  imports Main
begin

text \<open>Exact dyadic cylinders and integral affine branch pullbacks.  The
results below make no claim that arbitrary Collatz branches are admissible or
that a recursive implementation has polylogarithmic cost.\<close>

definition cylinder :: "nat \<Rightarrow> int \<Rightarrow> int set" where
  "cylinder q r = {x. \<exists>k. x = r + (2::int)^q*k}"

definition integral_branch ::
    "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "integral_branch a b E x y \<longleftrightarrow> a*x+b = (2::int)^E*y"

definition pullback_set ::
    "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> int set \<Rightarrow> int set" where
  "pullback_set a b E A = {x. \<exists>y\<in>A. integral_branch a b E x y}"

definition cylinder_pullback ::
    "int \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int set" where
  "cylinder_pullback a b E q r = pullback_set a b E (cylinder q r)"

lemma cylinder_pullback_congruence:
  "cylinder_pullback a b E q r =
    {x. (2::int)^(q+E) dvd (a*x+b-(2::int)^E*r)}"
proof (rule set_eqI; rule iffI)
  fix x
  assume "x \<in> cylinder_pullback a b E q r"
  then obtain y k where
      y: "y = r + (2::int)^q*k"
      and branch: "a*x+b = (2::int)^E*y"
    by (auto simp: cylinder_pullback_def pullback_set_def cylinder_def
        integral_branch_def)
  have "a*x+b-(2::int)^E*r = (2::int)^(q+E)*k"
    using y branch by (simp add: power_add algebra_simps)
  then show "x \<in> {x. (2::int)^(q+E) dvd
      (a*x+b-(2::int)^E*r)}"
    by (auto simp: dvd_def)
next
  fix x
  assume "x \<in> {x. (2::int)^(q+E) dvd
      (a*x+b-(2::int)^E*r)}"
  then obtain k where
    k: "a*x+b-(2::int)^E*r = (2::int)^(q+E)*k"
    by (auto simp: dvd_def)
  let ?y = "r + (2::int)^q*k"
  have branch: "a*x+b = (2::int)^E*?y"
    using k by (simp add: power_add algebra_simps)
  show "x \<in> cylinder_pullback a b E q r"
    using branch by (auto simp: cylinder_pullback_def pullback_set_def
        cylinder_def integral_branch_def)
qed

lemma cylinder_zero [simp]: "cylinder 0 r = UNIV"
proof (rule set_eqI)
  fix x :: int
  show "x \<in> cylinder 0 r \<longleftrightarrow> x \<in> UNIV"
    by (simp add: cylinder_def; rule exI[of _ "x-r"]; simp)
qed

lemma zero_precision_retains_integrality:
  "cylinder_pullback a b E 0 r = {x. (2::int)^E dvd a*x+b}"
  by (simp add: cylinder_pullback_def pullback_set_def integral_branch_def
      dvd_def)

lemma pullback_respects_cylinder_congruence:
  assumes "cylinder q r = cylinder q s"
  shows "cylinder_pullback a b E q r = cylinder_pullback a b E q s"
  using assms by (simp add: cylinder_pullback_def)

lemma pullback_sibling_union:
  "pullback_set a b E (L \<union> R) =
    pullback_set a b E L \<union> pullback_set a b E R"
  by (auto simp: pullback_set_def)

lemma cylinder_sibling_union:
  "cylinder (Suc q) r \<union> cylinder (Suc q) (r+(2::int)^q) =
    cylinder q r"
proof (rule set_eqI; rule iffI)
  fix x
  assume "x \<in> cylinder (Suc q) r \<union>
      cylinder (Suc q) (r+(2::int)^q)"
  then consider
      (left) k where "x = r + (2::int)^(Suc q)*k"
    | (right) k where "x = r+(2::int)^q + (2::int)^(Suc q)*k"
    by (auto simp: cylinder_def)
  then show "x \<in> cylinder q r"
  proof cases
    case (left k)
    have "x = r + (2::int)^q*(2*k)"
      using left by (simp add: power_Suc algebra_simps)
    then show ?thesis by (auto simp: cylinder_def)
  next
    case (right k)
    have "x = r + (2::int)^q*(2*k+1)"
      using right by (simp add: power_Suc algebra_simps)
    then show ?thesis by (auto simp: cylinder_def)
  qed
next
  fix x
  assume "x \<in> cylinder q r"
  then obtain k where x: "x = r + (2::int)^q*k"
    by (auto simp: cylinder_def)
  show "x \<in> cylinder (Suc q) r \<union>
      cylinder (Suc q) (r+(2::int)^q)"
  proof (cases "even k")
    case True
    then obtain h where k: "k = 2*h" by (elim evenE)
    have "x = r + (2::int)^(Suc q)*h"
      using x k by (simp add: power_Suc algebra_simps)
    then show ?thesis by (auto simp: cylinder_def)
  next
    case False
    then have "odd k" by simp
    then obtain h where k: "k = 2*h+1" by (elim oddE)
    have "x = r+(2::int)^q + (2::int)^(Suc q)*h"
      using x k by (simp add: power_Suc algebra_simps)
    then show ?thesis by (auto simp: cylinder_def)
  qed
qed

corollary cylinder_pullback_sibling_union:
  "cylinder_pullback a b E q r =
    cylinder_pullback a b E (Suc q) r \<union>
    cylinder_pullback a b E (Suc q) (r+(2::int)^q)"
proof -
  have siblings: "cylinder q r = cylinder (Suc q) r \<union>
      cylinder (Suc q) (r+(2::int)^q)"
    using cylinder_sibling_union[of q r] by simp
  show ?thesis
    by (simp add: cylinder_pullback_def siblings pullback_sibling_union)
qed

lemma branch_composition_forward:
  assumes "integral_branch a1 b1 E1 x y"
      and "integral_branch a2 b2 E2 y z"
  shows "integral_branch (a2*a1) (a2*b1+(2::int)^E1*b2)
    (E1+E2) x z"
proof -
  have first: "a1*x+b1 = (2::int)^E1*y"
    using assms(1) by (simp add: integral_branch_def)
  have second: "a2*y+b2 = (2::int)^E2*z"
    using assms(2) by (simp add: integral_branch_def)
  have "(a2*a1)*x + (a2*b1+(2::int)^E1*b2) =
      a2*(a1*x+b1) + (2::int)^E1*b2"
    by (simp add: algebra_simps)
  also have "... = a2*((2::int)^E1*y) + (2::int)^E1*b2"
    using first by simp
  also have "... = (2::int)^E1*(a2*y+b2)"
    by (simp add: algebra_simps)
  also have "... = (2::int)^E1*((2::int)^E2*z)"
    using second by simp
  also have "... = (2::int)^(E1+E2)*z"
    by (simp add: power_add algebra_simps)
  finally show ?thesis by (simp add: integral_branch_def)
qed

theorem branch_composition_exact:
  "(\<exists>y. integral_branch a1 b1 E1 x y \<and>
      integral_branch a2 b2 E2 y z) \<longleftrightarrow>
    ((2::int)^E1 dvd a1*x+b1 \<and>
      integral_branch (a2*a1) (a2*b1+(2::int)^E1*b2)
        (E1+E2) x z)"
proof
  assume "\<exists>y. integral_branch a1 b1 E1 x y \<and>
      integral_branch a2 b2 E2 y z"
  then obtain y where first: "integral_branch a1 b1 E1 x y"
      and second: "integral_branch a2 b2 E2 y z" by blast
  have "(2::int)^E1 dvd a1*x+b1"
    using first by (auto simp: integral_branch_def dvd_def)
  moreover have "integral_branch (a2*a1)
      (a2*b1+(2::int)^E1*b2) (E1+E2) x z"
    using first second by (rule branch_composition_forward)
  ultimately show "(2::int)^E1 dvd a1*x+b1 \<and>
      integral_branch (a2*a1) (a2*b1+(2::int)^E1*b2)
        (E1+E2) x z" by blast
next
  assume rhs: "(2::int)^E1 dvd a1*x+b1 \<and>
      integral_branch (a2*a1) (a2*b1+(2::int)^E1*b2)
        (E1+E2) x z"
  then obtain y where first_eq: "a1*x+b1 = (2::int)^E1*y"
    by (auto simp: dvd_def)
  have first: "integral_branch a1 b1 E1 x y"
    using first_eq by (simp add: integral_branch_def)
  have nonzero: "(2::int)^E1 \<noteq> 0" by simp
  have composite: "(a2*a1)*x + (a2*b1+(2::int)^E1*b2) =
      (2::int)^(E1+E2)*z"
    using rhs by (simp add: integral_branch_def)
  have multiplied: "(2::int)^E1*(a2*y+b2) =
      (2::int)^E1*((2::int)^E2*z)"
  proof -
    have "(2::int)^E1*(a2*y+b2) =
        a2*((2::int)^E1*y) + (2::int)^E1*b2"
      by (simp add: algebra_simps)
    also have "... = a2*(a1*x+b1) + (2::int)^E1*b2"
      using first_eq by simp
    also have "... = (a2*a1)*x + (a2*b1+(2::int)^E1*b2)"
      by (simp add: algebra_simps)
    also have "... = (2::int)^(E1+E2)*z" by (rule composite)
    also have "... = (2::int)^E1*((2::int)^E2*z)"
      by (simp add: power_add algebra_simps)
    finally show ?thesis .
  qed
  have second: "integral_branch a2 b2 E2 y z"
    using nonzero multiplied by (simp add: integral_branch_def)
  show "\<exists>y. integral_branch a1 b1 E1 x y \<and>
      integral_branch a2 b2 E2 y z"
    using first second by blast
qed

theorem odd_inverse_cylinder_pullback:
  fixes a b rho r :: int
    and q E :: nat
  defines "M \<equiv> (2::int)^(q+E)"
  assumes odd: "odd a"
      and inverse: "\<And>z. M dvd a*z \<longleftrightarrow> M dvd z"
      and anchor: "M dvd a*rho+b-(2::int)^E*r"
  shows "cylinder_pullback a b E q r = cylinder (q+E) rho"
proof -
  have shifted: "a*x+b-(2::int)^E*r =
      a*(x-rho) + (a*rho+b-(2::int)^E*r)" for x
    by (simp add: algebra_simps)
  have divisibility: "M dvd a*x+b-(2::int)^E*r \<longleftrightarrow> M dvd x-rho" for x
  proof -
    have equation: "a*x+b-(2::int)^E*r =
        a*(x-rho) + (a*rho+b-(2::int)^E*r)"
      by (rule shifted)
    have "M dvd a*x+b-(2::int)^E*r \<longleftrightarrow> M dvd a*(x-rho)"
    proof
      assume whole: "M dvd a*x+b-(2::int)^E*r"
      have "M dvd (a*x+b-(2::int)^E*r) -
          (a*rho+b-(2::int)^E*r)"
        using whole anchor by (rule dvd_diff)
      then show "M dvd a*(x-rho)"
        using equation by (simp add: algebra_simps)
    next
      assume variable: "M dvd a*(x-rho)"
      have "M dvd a*(x-rho) + (a*rho+b-(2::int)^E*r)"
        using variable anchor by (rule dvd_add)
      then show "M dvd a*x+b-(2::int)^E*r"
        by (subst equation; assumption)
    qed
    also have "... \<longleftrightarrow> M dvd x-rho" by (rule inverse)
    finally show ?thesis .
  qed
  show ?thesis
  proof (rule set_eqI)
    fix x
    show "x \<in> cylinder_pullback a b E q r \<longleftrightarrow>
        x \<in> cylinder (q+E) rho"
      using divisibility[of x]
      by (simp add: cylinder_pullback_congruence cylinder_def M_def dvd_def
          algebra_simps)
  qed
qed

lemma cylinder_refines_six:
  assumes "6 \<le> q"
  shows "cylinder q r \<subseteq> cylinder 6 r"
proof -
  obtain n where q: "q = 6+n" using assms by (metis le_iff_add)
  show ?thesis
  proof
    fix x
    assume "x \<in> cylinder q r"
    then obtain k where x: "x = r + (2::int)^q*k"
      by (auto simp: cylinder_def)
    have "x = r + (2::int)^6*((2::int)^n*k)"
      using x by (simp add: q power_add algebra_simps)
    then show "x \<in> cylinder 6 r" by (auto simp: cylinder_def)
  qed
qed

lemma cylinder_recenter:
  assumes "s \<in> cylinder q r"
  shows "cylinder q s = cylinder q r"
proof -
  obtain h where s: "s = r + (2::int)^q*h"
    using assms by (auto simp: cylinder_def)
  show ?thesis
  proof (rule set_eqI; rule iffI)
    fix x
    assume "x \<in> cylinder q s"
    then obtain k where "x = s + (2::int)^q*k"
      by (auto simp: cylinder_def)
    then have "x = r + (2::int)^q*(h+k)"
      using s by (simp add: algebra_simps)
    then show "x \<in> cylinder q r" by (auto simp: cylinder_def)
  next
    fix x
    assume "x \<in> cylinder q r"
    then obtain k where "x = r + (2::int)^q*k"
      by (auto simp: cylinder_def)
    then have "x = s + (2::int)^q*(k-h)"
      using s by (simp add: algebra_simps)
    then show "x \<in> cylinder q s" by (auto simp: cylinder_def)
  qed
qed

lemma distinct_cylinders_disjoint:
  assumes "s \<notin> cylinder q r"
  shows "cylinder q r \<inter> cylinder q s = {}"
proof (rule ccontr)
  assume "cylinder q r \<inter> cylinder q s \<noteq> {}"
  then obtain x where xr: "x \<in> cylinder q r"
      and xs: "x \<in> cylinder q s" by blast
  obtain k where x1: "x = r + (2::int)^q*k"
    using xr by (auto simp: cylinder_def)
  obtain h where x2: "x = s + (2::int)^q*h"
    using xs by (auto simp: cylinder_def)
  have "s = r + (2::int)^q*(k-h)"
    using x1 x2 by (simp add: algebra_simps)
  then have "s \<in> cylinder q r" by (auto simp: cylinder_def)
  then show False using assms by contradiction
qed

lemma radix64_match_consumes_six:
  assumes "6 \<le> q" "d \<in> cylinder 6 r"
  shows "cylinder q r \<inter> cylinder 6 d = cylinder q r"
proof -
  have refine: "cylinder q r \<subseteq> cylinder 6 r"
    using assms(1) by (rule cylinder_refines_six)
  have equal: "cylinder 6 d = cylinder 6 r"
    using assms(2) by (rule cylinder_recenter)
  show ?thesis using refine equal by blast
qed

lemma radix64_mismatch_is_empty:
  assumes "6 \<le> q" "d \<notin> cylinder 6 r"
  shows "cylinder q r \<inter> cylinder 6 d = {}"
proof -
  have refine: "cylinder q r \<subseteq> cylinder 6 r"
    using assms(1) by (rule cylinder_refines_six)
  have disjoint: "cylinder 6 r \<inter> cylinder 6 d = {}"
    using assms(2) by (rule distinct_cylinders_disjoint)
  show ?thesis using refine disjoint by blast
qed

lemma radix64_shifted_tail:
  "d+64*x \<in> cylinder (q+6) (d+64*r) \<longleftrightarrow>
    x \<in> cylinder q r"
proof
  assume "d+64*x \<in> cylinder (q+6) (d+64*r)"
  then obtain k where equation:
    "d+64*x = d+64*r + (2::int)^(q+6)*k"
    by (auto simp: cylinder_def)
  have "64*x = 64*(r+(2::int)^q*k)"
    using equation by (simp add: power_add algebra_simps)
  then have "x = r+(2::int)^q*k" by simp
  then show "x \<in> cylinder q r" by (auto simp: cylinder_def)
next
  assume "x \<in> cylinder q r"
  then obtain k where equation: "x = r+(2::int)^q*k"
    by (auto simp: cylinder_def)
  have "d+64*x = d+64*r + (2::int)^(q+6)*k"
    using equation by (simp add: power_add algebra_simps)
  then show "d+64*x \<in> cylinder (q+6) (d+64*r)"
    by (auto simp: cylinder_def)
qed

corollary radix64_matching_digit_consumes_six:
  assumes "6 \<le> q" "d = r mod 64"
  shows "d+64*x \<in> cylinder q r \<longleftrightarrow>
    x \<in> cylinder (q-6) (r div 64)"
proof -
  have exponent: "q-6+6 = q" using assms(1) by arith
  have residue: "d+64*(r div 64) = r"
    using div_mult_mod_eq[of r 64] assms(2)
    by (simp add: algebra_simps)
  show ?thesis
    using radix64_shifted_tail[of d x "q-6" "r div 64"]
    by (simp only: exponent residue)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms cylinder_pullback_congruence zero_precision_retains_integrality
      pullback_respects_cylinder_congruence pullback_sibling_union
      cylinder_sibling_union cylinder_pullback_sibling_union
      branch_composition_exact odd_inverse_cylinder_pullback
      radix64_match_consumes_six radix64_mismatch_is_empty
      radix64_shifted_tail radix64_matching_digit_consumes_six}) then ()
    else error "Hensel cylinder proof depends on an oracle";
\<close>

end
