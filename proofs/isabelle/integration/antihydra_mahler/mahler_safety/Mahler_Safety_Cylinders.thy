theory Mahler_Safety_Cylinders
  imports Complex_Main "Antihydra.Antihydra_Source_Barrier"
begin

(* Adapted from the supplied 2026-09-20 Mahler safety release.
   Upstream SHA-256: 34761d4e56e498b9f2bfacf2a928562b5792bcfbdcedf0f43c1e4c7c8b783350
   Scope and import changes: docs/research/antihydra-mahler.md. *)

text \<open>Safety is the original fractional-part condition, not the existence
of a child in the unrestricted w tree and not Antihydra ledger survival.
The integer source is the existing Antihydra mahler_orbit; no second
source recurrence or ledger is defined here.\<close>

definition z_candidate :: "real \<Rightarrow> bool" where
  "z_candidate x \<longleftrightarrow> 0 < x \<and> (\<forall>n::nat. frac (x * (3/2)^n) < 1/2)"

definition safe_prefix :: "nat \<Rightarrow> real \<Rightarrow> bool" where
  "safe_prefix N x \<longleftrightarrow> (\<forall>n\<le>N. frac (x * (3/2)^n) < 1/2)"

lemma candidate_prefix:
  "z_candidate x \<Longrightarrow> safe_prefix N x"
  by (auto simp: z_candidate_def safe_prefix_def)

lemma candidate_scaled:
  assumes "z_candidate x"
  shows "z_candidate (x*(3/2)^m)"
proof -
  have positive: "0 < x*(3/2)^m"
    using assms by (auto simp: z_candidate_def)
  have safe: "frac ((x*(3/2)^m)*(3/2)^n) < 1/2" for n :: nat
    using assms unfolding z_candidate_def
    by (metis mult.assoc power_add)
  show ?thesis using positive safe by (simp add: z_candidate_def)
qed

lemma candidate_integer_part:
  assumes "z_candidate x"
  shows "x = of_nat (nat (floor x)) + frac x"
    "0 \<le> frac x" "frac x < 1/2"
proof -
  have nonnegative: "0 \<le> floor x"
    using assms by (auto simp: z_candidate_def intro: less_imp_le)
  show "x = of_nat (nat (floor x)) + frac x"
    using nonnegative by (simp add: frac_def)
  show "0 \<le> frac x" by simp
  show "frac x < 1/2" using candidate_prefix[OF assms, of 0]
    by (simp add: safe_prefix_def)
qed

lemma mahler_orbit_one [simp]: "mahler_orbit D 1 = mahler_D_step D"
  by (simp add: One_nat_def)

lemma mahler_orbit_numeral [simp]:
  "mahler_orbit D (numeral n) = mahler_D_step (mahler_orbit D (pred_numeral n))"
  by (simp only: numeral_eq_Suc mahler_orbit.simps)

lemma centered_source_commutes:
  "(3*(D+1) - (D+1) mod 2) div 2 = mahler_D_step D + 1"
  using centered_return_commutes[of D]
  by (simp only: antihydra_h_step_def)

lemma safe_step_interval:
  fixes y :: real
  assumes lo: "of_nat D \<le> y" and hi: "y < of_nat D + 1/2"
    and safe: "frac ((3/2)*y) < 1/2"
  shows "of_nat (mahler_D_step D) \<le> (3/2)*y \<and>
    (3/2)*y < of_nat (mahler_D_step D) + 1/2"
proof (cases D rule: nat_mod_two_cases)
  case (1 k)
  have lower: "of_int (int (3*k)) \<le> (3/2)*y"
    using lo 1 by (simp add: of_nat_mult; linarith)
  have upper: "(3/2)*y < of_int (int (3*k)) + 1"
    using hi 1 by (simp add: of_nat_mult; linarith)
  have floor: "floor ((3/2)*y) = int (3*k)"
    by (rule floor_unique[OF lower upper])
  have step: "mahler_D_step D = 3*k"
    using 1 by (simp add: mahler_D_step_def algebra_simps)
  have bound: "(3/2)*y - of_nat (3*k) < 1/2"
    using safe by (simp only: frac_def floor of_int_of_nat_eq)
  show ?thesis unfolding step using lower bound by (simp; linarith)
next
  case (2 k)
  have lower: "of_nat (3*k) + 3/2 \<le> (3/2)*y"
    using lo 2 by (simp add: of_nat_mult; linarith)
  have upper: "(3/2)*y < of_nat (3*k) + 9/4"
    using hi 2 by (simp add: of_nat_mult; linarith)
  have after: "of_nat (3*k+2) \<le> (3/2)*y"
  proof (rule ccontr)
    assume "\<not> of_nat (3*k+2) \<le> (3/2)*y"
    then have small: "(3/2)*y < of_nat (3*k+1) + 1" by simp
    have large: "of_int (int (3*k+1)) \<le> (3/2)*y" using lower by (simp; linarith)
    have floor: "floor ((3/2)*y) = int (3*k+1)"
      by (rule floor_unique[OF large]) (use small in simp)
    have bound: "(3/2)*y - of_nat (3*k+1) < 1/2"
      using safe by (simp only: frac_def floor of_int_of_nat_eq)
    from bound lower show False by (simp; linarith)
  qed
  have lower2: "of_int (int (3*k+2)) \<le> (3/2)*y" using after by simp
  have upper2: "(3/2)*y < of_int (int (3*k+2)) + 1"
    using upper by (simp; linarith)
  have floor: "floor ((3/2)*y) = int (3*k+2)"
    by (rule floor_unique[OF lower2 upper2])
  have step: "mahler_D_step D = 3*k+2"
    using 2 by (simp add: mahler_D_step_def algebra_simps)
  have bound: "(3/2)*y - of_nat (3*k+2) < 1/2"
    using safe by (simp only: frac_def floor of_int_of_nat_eq)
  show ?thesis unfolding step using after bound by linarith
qed

theorem safe_prefix_source_bounds:
  fixes x :: real
  assumes safe: "safe_prefix N x"
    and lo: "of_nat D \<le> x" and hi: "x < of_nat D + 1/2"
    and nN: "n \<le> N"
  shows "of_nat (mahler_orbit D n) \<le> x*(3/2)^n \<and>
    x*(3/2)^n < of_nat (mahler_orbit D n)+1/2"
  using nN
proof (induct n)
  case 0
  then show ?case using lo hi by simp
next
  case (Suc n)
  have nN: "n \<le> N" using Suc.prems by simp
  have IH: "of_nat (mahler_orbit D n) \<le> x*(3/2)^n \<and>
    x*(3/2)^n < of_nat (mahler_orbit D n)+1/2" by (rule Suc.hyps[OF nN])
  have step: "frac ((3/2)*(x*(3/2)^n)) < 1/2"
    using safe Suc.prems by (auto simp: safe_prefix_def power_Suc algebra_simps)
  show ?case
    using safe_step_interval[OF IH[THEN conjunct1] IH[THEN conjunct2] step]
    by (simp add: power_Suc algebra_simps)
qed

lemma frac_nat_translate:
  "frac (x + of_nat k) = (frac x :: real)"
  using frac_add_of_int_right[of x "int k"] by simp

theorem safe_prefix_exact:
  fixes x :: real
  assumes lo: "of_nat D \<le> x" and hi: "x < of_nat D + 1/2"
  shows "safe_prefix N x \<longleftrightarrow>
    (\<forall>n\<le>N. of_nat (mahler_orbit D n) \<le> x*(3/2)^n \<and>
      x*(3/2)^n < of_nat (mahler_orbit D n)+1/2)"
proof
  assume "safe_prefix N x"
  then show "\<forall>n\<le>N. of_nat (mahler_orbit D n) \<le> x*(3/2)^n \<and>
      x*(3/2)^n < of_nat (mahler_orbit D n)+1/2"
    using safe_prefix_source_bounds[OF _ lo hi] by blast
next
  assume all: "\<forall>n\<le>N. of_nat (mahler_orbit D n) \<le> x*(3/2)^n \<and>
      x*(3/2)^n < of_nat (mahler_orbit D n)+1/2"
  show "safe_prefix N x"
    unfolding safe_prefix_def
  proof (intro allI impI)
    fix n assume "n \<le> N"
    then have bounds: "of_nat (mahler_orbit D n) \<le> x*(3/2)^n"
      "x*(3/2)^n < of_nat (mahler_orbit D n)+1/2" using all by auto
    have lower: "of_int (int (mahler_orbit D n)) \<le> x*(3/2)^n"
      using bounds(1) by simp
    have upper: "x*(3/2)^n < of_int (int (mahler_orbit D n))+1"
      using bounds(2) by (simp; linarith)
    have floor: "floor (x*(3/2)^n) = int (mahler_orbit D n)"
      by (rule floor_unique[OF lower upper])
    show "frac (x*(3/2)^n) < 1/2"
      using bounds(2) by (simp add: frac_def floor)
  qed
qed

lemma all_upto_six:
  "(\<forall>n\<le>(6::nat). P n) \<longleftrightarrow>
    (P 0 \<and> P 1 \<and> P 2 \<and> P 3 \<and> P 4 \<and> P 5 \<and> P 6)"
proof
  assume "\<forall>n\<le>(6::nat). P n"
  then show "P 0 \<and> P 1 \<and> P 2 \<and> P 3 \<and> P 4 \<and> P 5 \<and> P 6" by auto
next
  assume facts: "P 0 \<and> P 1 \<and> P 2 \<and> P 3 \<and> P 4 \<and> P 5 \<and> P 6"
  show "\<forall>n\<le>(6::nat). P n"
  proof (intro allI impI)
    fix n :: nat assume "n \<le> 6"
    then have "n=0 \<or> n=1 \<or> n=2 \<or> n=3 \<or> n=4 \<or> n=5 \<or> n=6" by arith
    then show "P n" using facts by blast
  qed
qed

theorem six_step_translation:
  fixes x :: real and k :: nat
  shows "safe_prefix 6 (x + 64*of_nat k) \<longleftrightarrow> safe_prefix 6 x"
proof -
  have invariant: "frac ((x+64*of_nat k)*(3/2)^n) = frac (x*(3/2)^n)"
    if "n \<le> 6" for n :: nat
  proof -
    have cases: "n=0 \<or> n=1 \<or> n=2 \<or> n=3 \<or> n=4 \<or> n=5 \<or> n=6"
      using that by arith
    have scale: "(64::real)*(3/2)^n = of_nat (2^(6-n)*3^n)"
      using cases by (elim disjE; simp add: power_divide)
    have eq: "(x+64*of_nat k)*(3/2)^n =
      x*(3/2)^n + of_nat k*(64*(3/2)^n)" by (simp add: algebra_simps)
    show ?thesis
      unfolding eq scale
      using frac_nat_translate[of "x*(3/2)^n" "k*(2^(6-n)*3^n)"]
      by simp
  qed
  show ?thesis unfolding safe_prefix_def using invariant by simp
qed

lemma unsafe_source_3:
  fixes x :: real
  assumes lo: "3 \<le> x" and hi: "x < 7/2"
  shows "\<not> safe_prefix 6 x"
proof
  assume safe: "safe_prefix 6 x"
  have A: "of_nat (mahler_orbit 3 1) \<le> x*(3/2)^1 \<and>
    x*(3/2)^1 < of_nat (mahler_orbit 3 1)+1/2"
    using safe_prefix_source_bounds[OF safe, of 3 1] lo hi by simp
  have B: "of_nat (mahler_orbit 3 2) \<le> x*(3/2)^2 \<and>
    x*(3/2)^2 < of_nat (mahler_orbit 3 2)+1/2"
    using safe_prefix_source_bounds[OF safe, of 3 2] lo hi by simp
  have calc: "mahler_orbit 3 2 = 8"
    by (simp add: mahler_D_step_def)
  have lower: "(8::real) \<le> x*9/4"
    using B by (simp add: mahler_D_step_def power_divide)
  from lower hi show False by linarith
qed

lemma distinct_safe_candidates_in_cell_impossible:
  assumes cx: "z_candidate x" and cy: "z_candidate y"
    and xlo: "of_nat D \<le> x" and xhi: "x < of_nat D + 1/2"
    and ylo: "of_nat D \<le> y" and yhi: "y < of_nat D + 1/2"
    and order: "x < y"
  shows False
proof -
  have positive: "0 < y-x" using order by linarith
  obtain n :: nat where large: "(1/2)/(y-x) < (3/2::real)^n"
    using real_arch_pow[of "3/2" "(1/2)/(y-x)"] by auto
  have growth: "1/2 < (y-x)*(3/2)^n"
    using large positive by (simp add: pos_divide_less_eq algebra_simps)
  have X: "of_nat (mahler_orbit D n) \<le> x*(3/2)^n"
    using safe_prefix_source_bounds[OF candidate_prefix[OF cx, of n] xlo xhi, of n]
    by simp
  have Y: "y*(3/2)^n < of_nat (mahler_orbit D n)+1/2"
    using safe_prefix_source_bounds[OF candidate_prefix[OF cy, of n] ylo yhi, of n]
    by simp
  from growth X Y show False by (simp add: algebra_simps; linarith)
qed

theorem at_most_one_candidate_per_cell:
  assumes "z_candidate x" "z_candidate y"
    "of_nat D \<le> x" "x < of_nat D + 1/2"
    "of_nat D \<le> y" "y < of_nat D + 1/2"
  shows "x=y"
  using distinct_safe_candidates_in_cell_impossible[OF assms]
    distinct_safe_candidates_in_cell_impossible[OF assms(2,1,5,6,3,4)]
  by (meson less_linear)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms candidate_prefix safe_step_interval safe_prefix_source_bounds
      six_step_translation unsafe_source_3 at_most_one_candidate_per_cell
      centered_source_commutes})
    then () else error "Mahler safety theorem depends on an oracle";
\<close>

end
