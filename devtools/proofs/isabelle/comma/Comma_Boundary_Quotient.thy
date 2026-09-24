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

lemma comma_sector_displacements_1: "comma_sector_displacements 1 = {460}"
  unfolding comma_sector_displacements_def comma_cycle_length_def
    comma_period_displacement_def by code_simp
lemma comma_sector_displacements_2: "comma_sector_displacements 2 = {210,260}"
  unfolding comma_sector_displacements_def comma_cycle_length_def
    comma_period_displacement_def by code_simp
lemma comma_sector_displacements_3: "comma_sector_displacements 3 = {480}"
  unfolding comma_sector_displacements_def comma_cycle_length_def
    comma_period_displacement_def by code_simp
lemma comma_sector_displacements_4: "comma_sector_displacements 4 = {220,270}"
  unfolding comma_sector_displacements_def comma_cycle_length_def
    comma_period_displacement_def by code_simp
lemma comma_sector_displacements_5:
  "comma_sector_displacements 5 = {60,80,100,120,140}"
  unfolding comma_sector_displacements_def comma_cycle_length_def
    comma_period_displacement_def by code_simp
lemma comma_sector_displacements_6: "comma_sector_displacements 6 = {230,280}"
  unfolding comma_sector_displacements_def comma_cycle_length_def
    comma_period_displacement_def by code_simp
lemma comma_sector_displacements_7: "comma_sector_displacements 7 = {520}"
  unfolding comma_sector_displacements_def comma_cycle_length_def
    comma_period_displacement_def by code_simp
lemma comma_sector_displacements_8: "comma_sector_displacements 8 = {240,290}"
  unfolding comma_sector_displacements_def comma_cycle_length_def
    comma_period_displacement_def by code_simp
lemma comma_sector_displacements_9: "comma_sector_displacements 9 = {540}"
  unfolding comma_sector_displacements_def comma_cycle_length_def
    comma_period_displacement_def by code_simp

lemma comma_cycle_displacement_catalog:
  "set (concat (map (\<lambda>f. map
      (\<lambda>d. comma_period_displacement f d (comma_cycle_length f))
      [(0::nat)..<10]) [(1::nat)..<10])) =
    comma_cycle_displacements"
proof -
  have source: "[(1::nat)..<10] = [1,2,3,4,5,6,7,8,9]"
    by code_simp
  have lifted: "\<And>f. (\<lambda>d. comma_period_displacement f d
      (comma_cycle_length f)) ` {0..<10} = comma_sector_displacements f"
    by (simp add: comma_sector_displacements_def)
  have first: "comma_sector_displacements (Suc 0) = {460}"
    using comma_sector_displacements_1 by simp
  show ?thesis
    unfolding source comma_cycle_displacements_def
    by (auto simp: lifted first
      comma_sector_displacements_2 comma_sector_displacements_3
      comma_sector_displacements_4 comma_sector_displacements_5
      comma_sector_displacements_6 comma_sector_displacements_7
      comma_sector_displacements_8 comma_sector_displacements_9)
qed

text \<open>Only the modular part of the exponent quotient is established
here.  A complete macro lifting theorem must additionally preserve all
interior guards, literal elapsed weights, and both child alternatives.\<close>

lemma comma_power_period_924:
  assumes "P \<in> comma_cycle_displacements" "p \<ge> 5"
  shows "10 ^ (p + 924) mod P = 10 ^ p mod P"
proof -
  have m60: "(10::nat) ^ 929 mod 60 = 10 ^ 5 mod 60"
  proof -
    have "mod_exp (10::nat) 929 60 = mod_exp 10 5 60"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m80: "(10::nat) ^ 929 mod 80 = 10 ^ 5 mod 80"
  proof -
    have "mod_exp (10::nat) 929 80 = mod_exp 10 5 80"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m100: "(10::nat) ^ 929 mod 100 = 10 ^ 5 mod 100"
  proof -
    have "mod_exp (10::nat) 929 100 = mod_exp 10 5 100"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m120: "(10::nat) ^ 929 mod 120 = 10 ^ 5 mod 120"
  proof -
    have "mod_exp (10::nat) 929 120 = mod_exp 10 5 120"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m140: "(10::nat) ^ 929 mod 140 = 10 ^ 5 mod 140"
  proof -
    have "mod_exp (10::nat) 929 140 = mod_exp 10 5 140"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m210: "(10::nat) ^ 929 mod 210 = 10 ^ 5 mod 210"
  proof -
    have "mod_exp (10::nat) 929 210 = mod_exp 10 5 210"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m220: "(10::nat) ^ 929 mod 220 = 10 ^ 5 mod 220"
  proof -
    have "mod_exp (10::nat) 929 220 = mod_exp 10 5 220"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m230: "(10::nat) ^ 929 mod 230 = 10 ^ 5 mod 230"
  proof -
    have "mod_exp (10::nat) 929 230 = mod_exp 10 5 230"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m240: "(10::nat) ^ 929 mod 240 = 10 ^ 5 mod 240"
  proof -
    have "mod_exp (10::nat) 929 240 = mod_exp 10 5 240"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m260: "(10::nat) ^ 929 mod 260 = 10 ^ 5 mod 260"
  proof -
    have "mod_exp (10::nat) 929 260 = mod_exp 10 5 260"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m270: "(10::nat) ^ 929 mod 270 = 10 ^ 5 mod 270"
  proof -
    have "mod_exp (10::nat) 929 270 = mod_exp 10 5 270"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m280: "(10::nat) ^ 929 mod 280 = 10 ^ 5 mod 280"
  proof -
    have "mod_exp (10::nat) 929 280 = mod_exp 10 5 280"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m290: "(10::nat) ^ 929 mod 290 = 10 ^ 5 mod 290"
  proof -
    have "mod_exp (10::nat) 929 290 = mod_exp 10 5 290"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m460: "(10::nat) ^ 929 mod 460 = 10 ^ 5 mod 460"
  proof -
    have "mod_exp (10::nat) 929 460 = mod_exp 10 5 460"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m480: "(10::nat) ^ 929 mod 480 = 10 ^ 5 mod 480"
  proof -
    have "mod_exp (10::nat) 929 480 = mod_exp 10 5 480"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m520: "(10::nat) ^ 929 mod 520 = 10 ^ 5 mod 520"
  proof -
    have "mod_exp (10::nat) 929 520 = mod_exp 10 5 520"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have m540: "(10::nat) ^ 929 mod 540 = 10 ^ 5 mod 540"
  proof -
    have "mod_exp (10::nat) 929 540 = mod_exp 10 5 540"
      by simp
    then show ?thesis by (simp only: mod_exp_def)
  qed
  have finite: "\<forall>Q \<in> comma_cycle_displacements.
      10 ^ 929 mod Q = 10 ^ 5 mod Q"
  proof (intro ballI)
    fix Q
    assume member: "Q \<in> comma_cycle_displacements"
    have choices: "Q = 60 \<or> Q = 80 \<or> Q = 100 \<or>
      Q = 120 \<or> Q = 140 \<or> Q = 210 \<or> Q = 220 \<or>
      Q = 230 \<or> Q = 240 \<or> Q = 260 \<or> Q = 270 \<or>
      Q = 280 \<or> Q = 290 \<or> Q = 460 \<or> Q = 480 \<or>
      Q = 520 \<or> Q = 540"
      using member by (simp add: comma_cycle_displacements_def)
    show "10 ^ 929 mod Q = 10 ^ 5 mod Q"
      using choices m60 m80 m100 m120 m140 m210 m220 m230 m240 m260 m270 m280 m290 m460 m480 m520 m540 by blast
  qed
  have base: "10 ^ 929 mod P = 10 ^ 5 mod P"
    using finite assms(1) by blast
  obtain t where t: "p = 5 + t"
    using assms(2) by (auto simp: le_iff_add)
  have exponent: "p + 924 = 929 + t" using t by arith
  have left_power: "(10::nat) ^ (p + 924) = 10 ^ 929 * 10 ^ t"
    using exponent by (simp only: exponent power_add)
  have right_power: "(10::nat) ^ p = 10 ^ 5 * 10 ^ t"
    using t by (simp only: t power_add)
  have "10 ^ (p + 924) mod P = (10 ^ 929 * 10 ^ t) mod P"
    by (simp only: left_power)
  also have "... = ((10 ^ 929 mod P) * 10 ^ t) mod P"
    by (rule mod_mult_left_eq[symmetric])
  also have "... = ((10 ^ 5 mod P) * 10 ^ t) mod P"
    using base by (simp only: base)
  also have "... = (10 ^ 5 * 10 ^ t) mod P"
    by (rule mod_mult_left_eq)
  also have "... = 10 ^ p mod P"
    by (simp only: right_power)
  finally show ?thesis .
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sector_headroom comma_current_sector_candidate
      comma_fork_headroom_digit comma_fork_normal_form_from_headroom
      comma_nine_sector_landmine_normal_form
      comma_sector_displacements_1 comma_sector_displacements_2
      comma_sector_displacements_3 comma_sector_displacements_4
      comma_sector_displacements_5 comma_sector_displacements_6
      comma_sector_displacements_7 comma_sector_displacements_8
      comma_sector_displacements_9
      comma_cycle_displacement_catalog comma_power_period_924})
    then () else error "Comma boundary proof depends on an oracle";
\<close>
end
