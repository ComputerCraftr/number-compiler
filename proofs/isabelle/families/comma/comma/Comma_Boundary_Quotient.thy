theory Comma_Boundary_Quotient
  imports Comma_Child_Cylinder "HOL-Number_Theory.Mod_Exp"
begin

text \<open>The decimal seam is a boundary calculation.  These statements
use the literal child relation and keep the exponent, hence the elapsed
term count, outside the finite phase coordinate.\<close>

definition comma_headroom :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_headroom f p k = (f + 1) * 10 ^ p - k"

definition comma_near_boundary :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_near_boundary a p = a * 10 ^ p - 1"

definition comma_zero_boundary :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_zero_boundary a p = a * 10 ^ p"

lemma comma_sector_headroom:
  assumes "comma_sector f p k"
  shows "k + comma_headroom f p k = (f + 1) * 10 ^ p"
  using assms by (simp add: comma_sector_def comma_headroom_def)

lemma comma_current_sector_candidate:
  assumes sector: "comma_sector f p k"
    and less_nine: "f < 9"
  shows "comma_sector f p (k + 10 * (k mod 10) + f) \<longleftrightarrow>
    10 * (k mod 10) + f < comma_headroom f p k"
  using sector less_nine
  by (auto simp: comma_sector_def comma_headroom_def; linarith)

lemma comma_fork_headroom_digit:
  assumes sector: "comma_sector f p k"
    and exponent: "p \<ge> 1"
    and less_nine: "f < 9"
    and fork: "comma_headroom f p k = 10 * (k mod 10) + f + 1"
  shows "k mod 10 = 9 - f"
proof -
  let ?d = "k mod 10"
  let ?h = "comma_headroom f p k"
  have divisible: "((f + 1) * 10 ^ p) mod 10 = 0"
    using exponent by (cases p) auto
  have sum: "k + ?h = (f + 1) * 10 ^ p"
    using comma_sector_headroom[OF sector] .
  have digits: "k = 10 * (k div 10) + ?d"
    by simp
  have decimal: "(f + 1) * 10 ^ p =
      10 * (k div 10 + ?d) + (?d + f + 1)"
    using sum fork digits by (simp add: algebra_simps; linarith)
  have reduced: "(10 * (k div 10 + ?d) + (?d + f + 1)) mod 10 =
      (?d + f + 1) mod 10"
    by (rule mod_mult_self4)
  have remainder: "((f + 1) * 10 ^ p) mod 10 =
      (?d + f + 1) mod 10"
    by (subst decimal, rule reduced)
  have phase: "(?d + f + 1) mod 10 = 0"
    using divisible remainder by simp
  have bounds: "1 \<le> ?d + f + 1" "?d + f + 1 \<le> 19"
    using less_nine by auto
  have divides: "10 dvd ?d + f + 1"
    using phase by (simp add: dvd_eq_mod_eq_0)
  obtain q where quotient: "?d + f + 1 = 10 * q"
    using divides unfolding dvd_def by blast
  have "q = 1" using quotient bounds by linarith
  then have "?d + f + 1 = 10" using quotient by simp
  then show ?thesis by arith
qed

lemma comma_fork_normal_form_from_headroom:
  assumes sector: "comma_sector f p k"
    and exponent: "p \<ge> 1"
    and less_nine: "f < 9"
    and fork: "comma_headroom f p k = 10 * (k mod 10) + f + 1"
  shows "k = (f + 1) * 10 ^ p - (91 - 9 * f)"
    and "k + 10 * (k mod 10) + f = comma_near_boundary (f + 1) p"
    and "k + 10 * (k mod 10) + f + 1 = comma_zero_boundary (f + 1) p"
proof -
  have digit: "k mod 10 = 9 - f"
    using comma_fork_headroom_digit[OF sector exponent less_nine fork] .
  have sum: "k + comma_headroom f p k = (f + 1) * 10 ^ p"
    using comma_sector_headroom[OF sector] .
  have head: "comma_headroom f p k = 91 - 9 * f"
    using fork digit less_nine by arith
  show "k = (f + 1) * 10 ^ p - (91 - 9 * f)"
    using sum head by arith
  show "k + 10 * (k mod 10) + f = comma_near_boundary (f + 1) p"
    using sum fork by (simp add: comma_near_boundary_def; arith)
  show "k + 10 * (k mod 10) + f + 1 = comma_zero_boundary (f + 1) p"
    using sum fork by (simp add: comma_zero_boundary_def; arith)
qed

lemma comma_nine_sector_landmine_normal_form:
  assumes sector: "comma_sector 9 p k"
    and exponent: "p \<ge> 1"
    and lower: "10 * (k mod 10) + 1 < comma_headroom 9 p k"
    and upper: "comma_headroom 9 p k \<le> 10 * (k mod 10) + 9"
  shows "1 \<le> k mod 10" "k mod 10 \<le> 8"
    "comma_headroom 9 p k = 10 + 9 * (k mod 10)"
    "k = 10 ^ (p + 1) - (10 + 9 * (k mod 10))"
proof -
  let ?d = "k mod 10"
  let ?h = "comma_headroom 9 p k"
  let ?t = "?h - 10 * ?d"
  have sum: "k + ?h = 10 * 10 ^ p"
    using comma_sector_headroom[OF sector] by simp
  have zero: "((10::nat) * 10 ^ p) mod 10 = 0" by simp
  have congruent: "(?d + ?h) mod 10 = 0"
  proof -
    have "(k + ?h) mod 10 = (?d + ?h) mod 10"
      by (simp add: mod_add_left_eq)
    then show ?thesis using sum zero by simp
  qed
  have t_bounds: "2 \<le> ?t" "?t \<le> 9"
    using lower upper by linarith+
  have h_decomp: "?h = 10 * ?d + ?t"
    using lower by simp
  have decimal: "?d + ?h = 10 * ?d + (?d + ?t)"
    using h_decomp by arith
  have reduced: "(10 * ?d + (?d + ?t)) mod 10 =
      (?d + ?t) mod 10"
    by (rule mod_mult_self4)
  have phase: "(?d + ?t) mod 10 = 0"
    using congruent decimal reduced by metis
  have digit_bound: "?d \<le> 9" by simp
  have divides: "10 dvd ?d + ?t"
    using phase by (simp add: dvd_eq_mod_eq_0)
  obtain q where quotient: "?d + ?t = 10 * q"
    using divides unfolding dvd_def by blast
  have "q = 1" using quotient t_bounds digit_bound by linarith
  then have sum_ten: "?d + ?t = 10" using quotient by simp
  show "1 \<le> ?d" "?d \<le> 8"
    using sum_ten t_bounds by arith+
  have h: "?h = 10 + 9 * ?d"
    using sum_ten h_decomp by arith
  then show "?h = 10 + 9 * ?d" .
  have decimal: "10 * 10 ^ p = 10 ^ (p + 1)"
    by (simp add: power_add)
  have complete: "k + (10 + 9 * ?d) = 10 ^ (p + 1)"
    using sum h decimal by simp
  have "k = (k + (10 + 9 * ?d)) - (10 + 9 * ?d)"
    by simp
  also have "... = 10 ^ (p + 1) - (10 + 9 * ?d)"
    using complete by simp
  finally show "k = 10 ^ (p + 1) - (10 + 9 * ?d)" .
qed

definition comma_cycle_length :: "nat \<Rightarrow> nat" where
  "comma_cycle_length f = 10 div gcd f 10"

definition comma_cycle_displacements :: "nat set" where
  "comma_cycle_displacements =
    {60,80,100,120,140,210,220,230,240,260,270,280,290,
     460,480,520,540}"

definition comma_sector_displacements :: "nat \<Rightarrow> nat set" where
  "comma_sector_displacements f =
    set (map (\<lambda>d. comma_period_displacement f d (comma_cycle_length f))
      [(0::nat)..<10])"

text \<open>Only the modular part of the exponent quotient is established
here.  A complete macro lifting theorem must additionally preserve all
interior guards, literal elapsed weights, and both child alternatives.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sector_headroom comma_current_sector_candidate
      comma_fork_headroom_digit comma_fork_normal_form_from_headroom
      comma_nine_sector_landmine_normal_form})
    then () else error "Comma boundary proof depends on an oracle";
\<close>
end
