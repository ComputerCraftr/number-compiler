theory Comma_C1_Phase_Power
  imports Comma_C1_Carry_Generator.Comma_C1_Return
begin

declare comma_c1_iter.simps[simp del]

text \<open>The runtime phase advance is the exact fifty-step CRT power.
The residue-four coordinate has period two; the residue-twenty-five
coordinate has the displayed affine quadratic orbit formula.\<close>

definition comma_c1_mod25_raw :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_mod25_raw f q n =
    (1 + 10 * n) * q + f * (n + 5 * n * (n - 1))"


lemma comma_c1_mod25_raw_succ:
  fixes f q n :: nat
  shows "11 * comma_c1_mod25_raw f q n + f =
    comma_c1_mod25_raw f q (Suc n) +
      25 * (4 * n * q + 2 * n * (n - 1) * f)"
  by (cases n) (simp_all add: comma_c1_mod25_raw_def algebra_simps)


lemma comma_c1_mod25_raw_shift25:
  fixes f q n :: nat
  shows "comma_c1_mod25_raw f q (n + 25) =
    comma_c1_mod25_raw f q n +
      25 * (10 * q + f * (10 * n + 121))"
  by (cases n) (simp_all add: comma_c1_mod25_raw_def algebra_simps)


lemma comma_c1_mod25_raw_period_under50:
  fixes f q t :: nat
  assumes "t < 50"
  shows "comma_c1_mod25_raw f q t mod 25 =
    comma_c1_mod25_raw f q (t mod 25) mod 25"
proof -
  let ?e = "t mod 25"
  let ?k = "t div 25"
  have split: "t = ?e + 25 * ?k" by (simp add: mult.commute)
  have ebound: "?e < 25" by simp
  have kbound: "?k < 2" using assms split ebound by arith
  have shift_mod:
    "comma_c1_mod25_raw f q (?e + 25) mod 25 =
      comma_c1_mod25_raw f q ?e mod 25"
  proof -
    let ?K = "10 * q + f * (10 * ?e + 121)"
    have shift: "comma_c1_mod25_raw f q (?e + 25) =
        comma_c1_mod25_raw f q ?e + 25 * ?K"
      by (rule comma_c1_mod25_raw_shift25)
    have multiple: "(25 * ?K) mod 25 = 0"
      by (simp only: mod_mult_self1_is_0)
    have "(comma_c1_mod25_raw f q ?e + 25 * ?K) mod 25 =
        (comma_c1_mod25_raw f q ?e mod 25 + (25 * ?K) mod 25) mod 25"
      by (rule mod_add_eq[symmetric])
    also have "... = comma_c1_mod25_raw f q ?e mod 25"
      using multiple by simp
    finally show ?thesis using shift by simp
  qed
  show ?thesis
  proof (cases "?k = 0")
    case True
    then show ?thesis using split by simp
  next
    case False
    have k_one: "?k = 1" using kbound False by arith
    have t_eq: "t = ?e + 25" using split k_one by simp
    show ?thesis using t_eq shift_mod by simp
  qed
qed


lemma comma_c1_mod25_iter_formula:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "c1_mod25 (comma_c1_iter n C) =
    comma_c1_mod25_raw (c1_sector C) (c1_mod25 C) n mod 25"
proof (induction n)
  case 0
  then show ?case
    using admitted by (simp add: comma_c1_phase_admitted_def comma_c1_mod25_raw_def
        comma_c1_iter.simps(1))
next
  case (Suc n)
  let ?f = "c1_sector C"
  let ?q = "c1_mod25 C"
  let ?A = "comma_c1_mod25_raw ?f ?q n"
  have sector: "c1_sector (comma_c1_iter n C) = ?f"
    by (rule comma_c1_iter_sector)
  have qstep:
    "c1_mod25 (comma_c1_iter (Suc n) C) =
      (11 * c1_mod25 (comma_c1_iter n C) + ?f) mod 25"
    using sector by (simp add: comma_c1_step_def comma_c1_iter.simps(2))
  have absorb:
    "(11 * (?A mod 25) + ?f) mod 25 = (11 * ?A + ?f) mod 25"
  proof -
    have "(11 * (?A mod 25) + ?f) mod 25 =
        ((11 * (?A mod 25)) mod 25 + ?f) mod 25"
      by (rule mod_add_left_eq[symmetric])
    also have "... = ((11 * ?A) mod 25 + ?f) mod 25"
      by (simp only: mod_mult_right_eq)
    also have "... = (11 * ?A + ?f) mod 25"
      by (rule mod_add_left_eq)
    finally show ?thesis .
  qed
  have polynomial:
    "11 * ?A + ?f = comma_c1_mod25_raw ?f ?q (Suc n) +
      25 * (4 * n * ?q + 2 * n * (n - 1) * ?f)"
    by (rule comma_c1_mod25_raw_succ)
  have polynomial_mod:
    "(11 * ?A + ?f) mod 25 =
      comma_c1_mod25_raw ?f ?q (Suc n) mod 25"
  proof -
    let ?K = "4 * n * ?q + 2 * n * (n - 1) * ?f"
    have multiple: "(25 * ?K) mod 25 = 0"
      by (simp only: mod_mult_self1_is_0)
    have "(comma_c1_mod25_raw ?f ?q (Suc n) + 25 * ?K) mod 25 =
        (comma_c1_mod25_raw ?f ?q (Suc n) mod 25 + (25 * ?K) mod 25) mod 25"
      by (rule mod_add_eq[symmetric])
    also have "... = comma_c1_mod25_raw ?f ?q (Suc n) mod 25"
      using multiple by simp
    finally show ?thesis using polynomial by simp
  qed
  show ?case
    using qstep Suc.IH absorb polynomial_mod by simp
qed


lemma comma_c1_mod4_first:
  fixes f q :: nat
  assumes "q < 4"
  shows "(3 * q + f) mod 4 = (f + 4 - q) mod 4"
proof (cases q)
  case 0
  have shift: "(f + 4) mod 4 = f mod 4"
  proof -
    have "(f + 4) mod 4 = (f mod 4 + 4 mod 4) mod 4"
      by (rule mod_add_eq[symmetric])
    also have "... = f mod 4" by simp
    finally show ?thesis .
  qed
  show ?thesis using 0 shift by simp
next
  case (Suc r)
  have rbound: "r < 3" using assms Suc by arith
  have raw: "3 * q + f = (f + 4 - q) + 4 * r"
    using Suc rbound by arith
  have multiple: "(4 * r) mod 4 = 0"
    by (simp only: mod_mult_self1_is_0)
  have residue: "((f + 4 - q) + 4 * r) mod 4 =
      (f + 4 - q) mod 4"
  proof -
    have "((f + 4 - q) + 4 * r) mod 4 =
        ((f + 4 - q) mod 4 + (4 * r) mod 4) mod 4"
      by (rule mod_add_eq[symmetric])
    also have "... = (f + 4 - q) mod 4" using multiple by simp
    finally show ?thesis .
  qed
  show ?thesis using raw residue by simp
qed


lemma comma_c1_mod4_second:
  fixes f q :: nat
  assumes "q < 4"
  shows "(3 * ((f + 4 - q) mod 4) + f) mod 4 = q"
proof -
  let ?r = "f + 4 - q"
  let ?h = "?r mod 4"
  let ?k = "f + 3 - q"
  have qbound: "q mod 4 = q" using assms by simp
  have mult: "(3 * ?h) mod 4 = (3 * ?r) mod 4"
    by (simp only: mod_mult_right_eq)
  have raw: "3 * ?r + f = q + 4 * ?k"
    using assms by arith
  have multiple: "(4 * ?k) mod 4 = 0"
    by (simp only: mod_mult_self1_is_0)
  have "(3 * ?h + f) mod 4 = ((3 * ?h) mod 4 + f mod 4) mod 4"
    by (rule mod_add_eq[symmetric])
  also have "... = ((3 * ?r) mod 4 + f mod 4) mod 4"
    by (simp only: mult)
  also have "... = (3 * ?r + f) mod 4"
    by (rule mod_add_eq)
  also have "... = (q + 4 * ?k) mod 4"
    by (simp only: raw)
  also have "... = q" using qbound multiple by simp
  finally show ?thesis .
qed


lemma comma_c1_mod4_iter_parity:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "c1_mod4 (comma_c1_iter n C) =
    (if n mod 2 = 0 then c1_mod4 C
     else (c1_sector C + 4 - c1_mod4 C) mod 4)"
proof (induction n)
  case 0
  then show ?case by (simp add: comma_c1_iter.simps(1))
next
  case (Suc n)
  let ?f = "c1_sector C"
  let ?q = "c1_mod4 C"
  let ?h = "(?f + 4 - ?q) mod 4"
  have qbound: "?q < 4"
    using admitted by (simp add: comma_c1_phase_admitted_def)
  have sector: "c1_sector (comma_c1_iter n C) = ?f"
    by (rule comma_c1_iter_sector)
  have recurrence:
    "c1_mod4 (comma_c1_iter (Suc n) C) =
      (3 * c1_mod4 (comma_c1_iter n C) + ?f) mod 4"
    using sector by (simp add: comma_c1_step_def comma_c1_iter.simps(2))
  have parity_bound: "n mod 2 < 2" by simp
  have first: "(3 * ?q + ?f) mod 4 = ?h"
    using comma_c1_mod4_first[OF qbound] by simp
  have second: "(3 * ?h + ?f) mod 4 = ?q"
    using comma_c1_mod4_second[OF qbound] by simp
  show ?case
  proof (cases "n mod 2 = 0")
    case True
    have next_parity: "Suc n mod 2 = 1" using True by presburger
    show ?thesis using recurrence Suc.IH True next_parity first by simp
  next
    case False
    have odd: "n mod 2 = 1" using parity_bound False by arith
    have next_parity: "Suc n mod 2 = 0" using odd by presburger
    show ?thesis using recurrence Suc.IH odd next_parity second by simp
  qed
qed

definition comma_c1_advance :: "comma_c1_phase \<Rightarrow> nat \<Rightarrow> comma_c1_phase" where
  "comma_c1_advance C n =
    (let t = n mod 50;
         e = t mod 25
     in \<lparr>c1_sector = c1_sector C,
          c1_mod4 = (if t mod 2 = 0 then c1_mod4 C
                     else (c1_sector C + 4 - c1_mod4 C) mod 4),
          c1_mod25 = comma_c1_mod25_raw (c1_sector C) (c1_mod25 C) e mod 25\<rparr>)"


lemma comma_c1_advance_refines_residue:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_advance C n = comma_c1_iter (n mod 50) C"
proof -
  let ?t = "n mod 50"
  let ?e = "?t mod 25"
  have t_bound: "?t < 50" by simp
  have q4:
    "c1_mod4 (comma_c1_iter ?t C) =
      (if ?t mod 2 = 0 then c1_mod4 C
       else (c1_sector C + 4 - c1_mod4 C) mod 4)"
    by (rule comma_c1_mod4_iter_parity[OF admitted])
  have q25_iter:
    "c1_mod25 (comma_c1_iter ?t C) =
      comma_c1_mod25_raw (c1_sector C) (c1_mod25 C) ?t mod 25"
    by (rule comma_c1_mod25_iter_formula[OF admitted])
  have q25:
    "comma_c1_mod25_raw (c1_sector C) (c1_mod25 C) ?t mod 25 =
      comma_c1_mod25_raw (c1_sector C) (c1_mod25 C) ?e mod 25"
    by (rule comma_c1_mod25_raw_period_under50[OF t_bound])
  have sector: "c1_sector (comma_c1_iter ?t C) = c1_sector C"
    by (rule comma_c1_iter_sector)
  show ?thesis
    using q4 q25_iter q25 sector
    by (cases C) (simp add: comma_c1_advance_def Let_def)
qed


lemma comma_c1_mod25_raw50:
  fixes f q :: nat
  shows "comma_c1_mod25_raw f q 50 mod 25 = q mod 25"
proof -
  have raw:
    "comma_c1_mod25_raw f q 50 = q + 25 * (20 * q + 492 * f)"
    by (simp add: comma_c1_mod25_raw_def algebra_simps)
  let ?K = "20 * q + 492 * f"
  have multiple: "(25 * ?K) mod 25 = 0"
    by (simp only: mod_mult_self1_is_0)
  have "(q + 25 * ?K) mod 25 = (q mod 25 + (25 * ?K) mod 25) mod 25"
    by (rule mod_add_eq[symmetric])
  also have "... = q mod 25" using multiple by simp
  finally show ?thesis using raw by simp
qed


lemma comma_c1_iter_period50:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_iter 50 C = C"
proof -
  have q4:
    "c1_mod4 (comma_c1_iter 50 C) = c1_mod4 C"
    using comma_c1_mod4_iter_parity[OF admitted, of 50] by simp
  have formula:
    "c1_mod25 (comma_c1_iter 50 C) =
      comma_c1_mod25_raw (c1_sector C) (c1_mod25 C) 50 mod 25"
    by (rule comma_c1_mod25_iter_formula[OF admitted, where n=50])
  have qbound: "c1_mod25 C < 25"
    using admitted by (simp add: comma_c1_phase_admitted_def)
  have q25: "c1_mod25 (comma_c1_iter 50 C) = c1_mod25 C"
    using formula comma_c1_mod25_raw50 qbound by simp
  have sector: "c1_sector (comma_c1_iter 50 C) = c1_sector C"
    by (rule comma_c1_iter_sector)
  show ?thesis
    by (rule comma_c1_phase.equality) (simp_all add: sector q4 q25)
qed


lemma comma_c1_iter_commute:
  "comma_c1_iter m (comma_c1_iter n C) =
    comma_c1_iter n (comma_c1_iter m C)"
proof -
  have left: "comma_c1_iter (n + m) C =
      comma_c1_iter m (comma_c1_iter n C)"
    by (rule comma_c1_iter_add)
  have right: "comma_c1_iter (m + n) C =
      comma_c1_iter n (comma_c1_iter m C)"
    by (rule comma_c1_iter_add)
  show ?thesis using left right by (simp add: add.commute)
qed


lemma comma_c1_iter_multiple50:
  assumes period: "comma_c1_iter 50 C = C"
  shows "comma_c1_iter (50 * k) C = C"
proof (induction k)
  case 0
  then show ?case by (simp add: comma_c1_iter.simps(1))
next
  case (Suc k)
  have step:
    "comma_c1_iter (50 * k + 50) C = comma_c1_iter (50 * k) C"
  proof -
    have "comma_c1_iter (50 * k + 50) C =
        comma_c1_iter 50 (comma_c1_iter (50 * k) C)"
      by (rule comma_c1_iter_add)
    also have "... = comma_c1_iter (50 * k) (comma_c1_iter 50 C)"
      by (rule comma_c1_iter_commute)
    also have "... = comma_c1_iter (50 * k) C"
      using period by simp
    finally show ?thesis .
  qed
  have exponent: "50 * Suc k = 50 * k + 50" by arith
  show ?case using step Suc.IH exponent by (simp add: add.commute)
qed


lemma comma_c1_iter_mod50:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_iter n C = comma_c1_iter (n mod 50) C"
proof -
  have period: "comma_c1_iter 50 C = C"
    by (rule comma_c1_iter_period50[OF admitted])
  have cycles: "comma_c1_iter (50 * (n div 50)) C = C"
    by (rule comma_c1_iter_multiple50[OF period])
  have split: "n = 50 * (n div 50) + n mod 50"
    by (simp add: mult.commute)
  have composition:
    "comma_c1_iter (50 * (n div 50) + n mod 50) C =
      comma_c1_iter (n mod 50) (comma_c1_iter (50 * (n div 50)) C)"
    by (rule comma_c1_iter_add)
  have composed:
    "comma_c1_iter n C =
      comma_c1_iter (n mod 50) (comma_c1_iter (50 * (n div 50)) C)"
    using split composition by metis
  show ?thesis using composed cycles by simp
qed


lemma comma_c1_count_multiple50:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_count C (50 * k) = k * comma_c1_count C 50"
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have period: "comma_c1_iter 50 C = C"
    by (rule comma_c1_iter_period50[OF admitted])
  have iterate: "comma_c1_iter (50 * k) C = C"
    by (rule comma_c1_iter_multiple50[OF period])
  have split: "50 * Suc k = 50 * k + 50" by arith
  have cocycle:
    "comma_c1_count C (50 * k + 50) =
      comma_c1_count C (50 * k) +
        comma_c1_count (comma_c1_iter (50 * k) C) 50"
    by (rule comma_c1_count_add)
  show ?case using Suc.IH iterate split cocycle
    by (simp add: algebra_simps)
qed


lemma comma_c1_iter_period1600:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_iter (n + 1600) C = comma_c1_iter n C"
proof -
  have D_admitted: "comma_c1_phase_admitted (comma_c1_iter n C)"
    by (rule comma_c1_iter_closed[OF admitted])
  have period50: "comma_c1_iter 50 (comma_c1_iter n C) =
      comma_c1_iter n C"
    by (rule comma_c1_iter_period50[OF D_admitted])
  have period_blocks:
    "comma_c1_iter (50 * 32) (comma_c1_iter n C) = comma_c1_iter n C"
    by (rule comma_c1_iter_multiple50[OF period50])
  have period1600: "comma_c1_iter 1600 (comma_c1_iter n C) =
      comma_c1_iter n C"
    using period_blocks by simp
  have composition:
    "comma_c1_iter (n + 1600) C =
      comma_c1_iter 1600 (comma_c1_iter n C)"
    by (rule comma_c1_iter_add)
  show ?thesis using composition period1600 by simp
qed


lemma comma_c1_count_mod32_period1600:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_count C (n + 1600) mod 32 =
    comma_c1_count C n mod 32"
proof -
  let ?D = "comma_c1_iter n C"
  have D_admitted: "comma_c1_phase_admitted ?D"
    by (rule comma_c1_iter_closed[OF admitted])
  have blocks:
    "comma_c1_count ?D (50 * 32) = 32 * comma_c1_count ?D 50"
    by (rule comma_c1_count_multiple50[OF D_admitted])
  have split: "(1600::nat) = 50 * 32" by simp
  have cocycle:
    "comma_c1_count C (n + 1600) =
      comma_c1_count C n + comma_c1_count ?D 1600"
    by (rule comma_c1_count_add)
  have blocks1600:
    "comma_c1_count ?D 1600 = 32 * comma_c1_count ?D 50"
    using blocks by (simp only: split[symmetric])
  have total: "comma_c1_count C (n + 1600) =
      comma_c1_count C n + 32 * comma_c1_count ?D 50"
    by (simp only: cocycle blocks1600)
  show ?thesis by (simp only: total mod_mult_self2)
qed


lemma comma_c1_return_pair_period1600:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "c1_target (comma_c1_return C (n + 1600)) =
      c1_target (comma_c1_return C n) \<and>
    c1_count (comma_c1_return C (n + 1600)) mod 32 =
      c1_count (comma_c1_return C n) mod 32"
proof -
  have target:
    "c1_target (comma_c1_return C (n + 1600)) =
      c1_target (comma_c1_return C n)"
    using comma_c1_iter_period1600[OF admitted, of n]
    by (simp add: comma_c1_return_def)
  have count:
    "c1_count (comma_c1_return C (n + 1600)) mod 32 =
      c1_count (comma_c1_return C n) mod 32"
    using comma_c1_count_mod32_period1600[OF admitted, of n]
    by (simp add: comma_c1_return_def)
  show ?thesis using target count by simp
qed


lemma comma_c1_quotient_modulus:
  fixes A P M :: nat
  assumes P_positive: "0 < P"
  shows "(A div P) mod M = (A mod (P * M)) div P"
proof -
  have remainder:
    "A mod (P * M) = P * ((A div P) mod M) + A mod P"
    by (rule mod_mult2_eq)
  show ?thesis using remainder P_positive
    by (simp add: div_add1_eq mult.commute)
qed

lemma comma_c1_count_phase50_decomposition:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_count C n =
    (n div 50) * comma_c1_count C 50 + comma_c1_count C (n mod 50)"
proof -
  have period: "comma_c1_iter 50 C = C"
    by (rule comma_c1_iter_period50[OF admitted])
  have cycle_iter: "comma_c1_iter (50 * (n div 50)) C = C"
    by (rule comma_c1_iter_multiple50[OF period])
  have cycle_count:
    "comma_c1_count C (50 * (n div 50)) =
      (n div 50) * comma_c1_count C 50"
    by (rule comma_c1_count_multiple50[OF admitted])
  have split: "n = 50 * (n div 50) + n mod 50"
    by (simp add: mult.commute)
  have cocycle:
    "comma_c1_count C (50 * (n div 50) + n mod 50) =
      comma_c1_count C (50 * (n div 50)) +
        comma_c1_count (comma_c1_iter (50 * (n div 50)) C) (n mod 50)"
    by (rule comma_c1_count_add)
  have blocks:
    "comma_c1_count C (50 * (n div 50) + n mod 50) =
      (n div 50) * comma_c1_count C 50 + comma_c1_count C (n mod 50)"
    by (simp only: cocycle cycle_iter cycle_count)
  show ?thesis using split blocks by metis
qed

lemma comma_c1_iter_mod1600:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_iter n C = comma_c1_iter (n mod 1600) C"
proof -
  have residue: "(n mod 1600) mod 50 = n mod 50"
    by (rule mod_mod_cancel) simp
  show ?thesis
    using comma_c1_iter_mod50[OF admitted, of n]
      comma_c1_iter_mod50[OF admitted, of "n mod 1600"] residue by metis
qed

lemma comma_c1_count_mod32_mod1600:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_count C n mod 32 =
    comma_c1_count C (n mod 1600) mod 32"
proof -
  have remainder: "(n mod 1600) mod 50 = n mod 50"
    by (rule mod_mod_cancel) simp
  have quotient: "(n div 50) mod 32 = (n mod 1600) div 50"
    using comma_c1_quotient_modulus[where A=n and P=50 and M=32] by simp
  have product:
    "((n div 50) * comma_c1_count C 50) mod 32 =
      (((n mod 1600) div 50) * comma_c1_count C 50) mod 32"
  proof -
    have "((n div 50) * comma_c1_count C 50) mod 32 =
        (((n div 50) mod 32) * comma_c1_count C 50) mod 32"
      by (rule mod_mult_left_eq[symmetric])
    also have "... =
        (((n mod 1600) div 50) * comma_c1_count C 50) mod 32"
      by (simp only: quotient)
    finally show ?thesis .
  qed
  have original:
    "comma_c1_count C n =
      (n div 50) * comma_c1_count C 50 + comma_c1_count C (n mod 50)"
    by (rule comma_c1_count_phase50_decomposition[OF admitted])
  have reduced:
    "comma_c1_count C (n mod 1600) =
      ((n mod 1600) div 50) * comma_c1_count C 50 +
        comma_c1_count C ((n mod 1600) mod 50)"
    by (rule comma_c1_count_phase50_decomposition[OF admitted])
  have "comma_c1_count C n mod 32 =
      ((n div 50) * comma_c1_count C 50 +
        comma_c1_count C (n mod 50)) mod 32"
    by (rule arg_cong[OF original])
  also have "... =
      (((n div 50) * comma_c1_count C 50) mod 32 +
        comma_c1_count C (n mod 50) mod 32) mod 32"
    by (rule mod_add_eq[symmetric])
  also have "... =
      ((((n mod 1600) div 50) * comma_c1_count C 50) mod 32 +
        comma_c1_count C ((n mod 1600) mod 50) mod 32) mod 32"
    by (simp only: product remainder)
  also have "... =
      (((n mod 1600) div 50) * comma_c1_count C 50 +
        comma_c1_count C ((n mod 1600) mod 50)) mod 32"
    by (rule mod_add_eq)
  also have "... = comma_c1_count C (n mod 1600) mod 32"
    by (rule arg_cong[OF reduced[symmetric]])
  finally show ?thesis .
qed

lemma comma_c1_return_mod1600:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "c1_target (comma_c1_return C n) =
      c1_target (comma_c1_return C (n mod 1600)) \<and>
    c1_count (comma_c1_return C n) mod 32 =
      c1_count (comma_c1_return C (n mod 1600)) mod 32"
  using comma_c1_iter_mod1600[OF admitted, of n]
    comma_c1_count_mod32_mod1600[OF admitted, of n]
  by (simp add: comma_c1_return_def)


lemma comma_c1_advance_refines_iter:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_advance C n = comma_c1_iter n C"
proof -
  have residue: "comma_c1_advance C n = comma_c1_iter (n mod 50) C"
    by (rule comma_c1_advance_refines_residue[OF admitted])
  have period: "comma_c1_iter n C = comma_c1_iter (n mod 50) C"
    by (rule comma_c1_iter_mod50[OF admitted])
  show ?thesis using residue period by simp
qed


definition comma_c1_powered_return ::
  "comma_c1_phase \<Rightarrow> nat \<Rightarrow> comma_c1_return" where
  "comma_c1_powered_return C n =
    (let total = comma_c1_decode (c1_mod4 C) (c1_mod25 C) +
        comma_c1_displacement_prefix C n
     in \<lparr>c1_target = comma_c1_advance C n,
          c1_count = total div 100\<rparr>)"

lemma comma_c1_powered_return_exact:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_powered_return C n = comma_c1_return C n"
proof -
  let ?x = "comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  let ?P = "comma_c1_displacement_prefix C n"
  have target:
    "comma_c1_advance C n = c1_target (comma_c1_return C n)"
    using comma_c1_advance_refines_iter[OF admitted]
    by (simp add: comma_c1_return_def)
  have count:
    "(?x + ?P) div 100 = c1_count (comma_c1_return C n)"
    using comma_c1_count_complete_cycles[OF admitted, of n]
    by (simp add: comma_c1_return_def)
  show ?thesis
    unfolding comma_c1_powered_return_def
    using target count by (simp add: Let_def comma_c1_return_def)
qed


lemma comma_c1_advance_remainder:
  fixes n :: nat
  shows "(n mod 50) mod 2 = n mod 2 \<and> (n mod 50) mod 25 = n mod 25"
proof -
  have d2: "(2::nat) dvd 50" by simp
  have d25: "(25::nat) dvd 50" by simp
  show ?thesis by (simp only: mod_mod_cancel[OF d2] mod_mod_cancel[OF d25])
qed

ML \<open>
  val checked = @{thms comma_c1_mod25_raw_succ comma_c1_mod25_raw_shift25
    comma_c1_mod25_raw_period_under50 comma_c1_mod25_iter_formula
    comma_c1_mod4_first comma_c1_mod4_second comma_c1_mod4_iter_parity
    comma_c1_advance_refines_residue comma_c1_mod25_raw50
    comma_c1_iter_period50 comma_c1_iter_commute comma_c1_iter_multiple50
    comma_c1_iter_mod50 comma_c1_count_multiple50 comma_c1_iter_period1600
    comma_c1_count_mod32_period1600 comma_c1_return_pair_period1600
    comma_c1_quotient_modulus comma_c1_count_phase50_decomposition
    comma_c1_iter_mod1600 comma_c1_count_mod32_mod1600
    comma_c1_return_mod1600 comma_c1_advance_refines_iter
    comma_c1_powered_return_exact comma_c1_advance_remainder};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1 phase power proof depends on an oracle";
\<close>

end
