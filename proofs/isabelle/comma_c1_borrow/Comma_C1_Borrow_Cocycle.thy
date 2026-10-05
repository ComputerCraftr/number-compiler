theory Comma_C1_Borrow_Cocycle
  imports Comma_C1_Phase_Power.Comma_C1_Phase_Power
begin

text \<open>Local adjacent-sector suffix algebra.  The sector guard is explicit:
these lemmas model f and f+1 only when both are legal sectors.  They do not
assert a future-selector or macro quotient theorem.\<close>

definition comma_c1_borrow_raw :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_borrow_raw f x = x + 10 * (x mod 10) + f"

lemma comma_c1_borrow_raw_phase_step:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_borrow_raw (c1_sector C)
      (comma_c1_decode (c1_mod4 C) (c1_mod25 C)) =
    100 * comma_c1_count C 1 +
      comma_c1_decode (c1_mod4 (comma_c1_iter 1 C))
        (c1_mod25 (comma_c1_iter 1 C))"
proof -
  have physical:
    "comma_fixed_iter (c1_sector C) 1
        (100 * 0 + comma_c1_decode (c1_mod4 C) (c1_mod25 C)) =
      100 * (0 + comma_c1_count C 1) +
        comma_c1_decode (c1_mod4 (comma_c1_iter 1 C))
          (c1_mod25 (comma_c1_iter 1 C))"
    using comma_c1_iter_physical[OF admitted, where H=0 and n=1] .
  show ?thesis using physical by (simp add: comma_c1_borrow_raw_def)
qed

definition comma_c1_suffix_borrow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_suffix_borrow x y = (if y < x then 1 else 0)"

definition comma_c1_suffix_delta :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_suffix_delta x y = (y + 100 - x) mod 100"

definition comma_c1_digit_extra :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_digit_extra d delta = (if 10 \<le> d + delta mod 10 then 1 else 0)"


lemma comma_c1_suffix_delta_bound:
  "comma_c1_suffix_delta x y < 100"
  by (simp add: comma_c1_suffix_delta_def)


lemma comma_c1_suffix_delta_borrow:
  assumes "x < 100" "y < 100"
  shows "y + 100 * comma_c1_suffix_borrow x y =
      x + comma_c1_suffix_delta x y"
proof (cases "y < x")
  case True
  have b: "comma_c1_suffix_borrow x y = 1"
    by (simp add: comma_c1_suffix_borrow_def True)
  have d: "comma_c1_suffix_delta x y = y + 100 - x"
  proof -
    have "y + 100 - x < 100" using True by arith
    then show ?thesis by (simp add: comma_c1_suffix_delta_def)
  qed
  show ?thesis using assms b d by arith
next
  case False
  have le: "x \<le> y" using False by arith
  have b: "comma_c1_suffix_borrow x y = 0"
    by (simp add: comma_c1_suffix_borrow_def False)
  have d: "comma_c1_suffix_delta x y = y - x"
  proof -
    have split: "y + 100 - x = 100 + (y - x)" using le by arith
    have rem: "y - x < 100" using assms(2) by arith
    show ?thesis unfolding comma_c1_suffix_delta_def
      by (simp only: split mod_add_left_eq; simp add: rem)
  qed
  show ?thesis using b d le by arith
qed


lemma comma_c1_borrow_digit_identity:
  assumes xa: "xA < 100" and xb: "xB < 100"
  defines "delta \<equiv> comma_c1_suffix_delta xA xB"
  defines "b \<equiv> comma_c1_suffix_borrow xA xB"
  defines "e \<equiv> comma_c1_digit_extra (xA mod 10) delta"
  shows "xB mod 10 + 10 * e = xA mod 10 + delta mod 10"
proof -
  have input: "xB + 100 * b = xA + delta"
    using comma_c1_suffix_delta_borrow[OF xa xb]
    by (simp only: b_def delta_def)
  have scale100: "100 * b = 10 * (10 * b)" by arith
  have m100: "(100 * b) mod 10 = 0"
    by (simp only: scale100 mod_mult_self1_is_0)
  have mleft: "(xB + 100 * b) mod 10 = xB mod 10"
  proof -
    have "(xB + 100 * b) mod 10 =
        (xB mod 10 + (100 * b) mod 10) mod 10"
      by (rule mod_add_eq[symmetric])
    then show ?thesis using m100 by simp
  qed
  have mright: "(xA + delta) mod 10 =
      (xA mod 10 + delta mod 10) mod 10"
    by (rule mod_add_eq[symmetric])
  have digit_mod: "xB mod 10 = (xA mod 10 + delta mod 10) mod 10"
    using arg_cong[where f="\<lambda>z::nat. z mod 10", OF input] mleft mright
    by simp
  let ?t = "xA mod 10 + delta mod 10"
  have d10: "xA mod 10 < 10" by simp
  have dr10: "delta mod 10 < 10" by simp
  have tb: "?t < 20" using d10 dr10 by arith
  have tq: "?t div 10 = (if 10 \<le> ?t then 1 else 0)"
    by (rule comma_nat_div10_lt20[OF tb])
  have e_eq: "e = ?t div 10"
    using tq by (simp add: e_def comma_c1_digit_extra_def)
  have split: "?t = 10 * (?t div 10) + ?t mod 10" by simp
  show ?thesis using digit_mod tq e_eq split by arith
qed


lemma comma_c1_borrow_balance_arithmetic:
  fixes xA xB d sA sB r t b e f :: nat
  assumes input: "xB + 100 * b = xA + d"
    and digits: "sB + 10 * e = sA + r"
    and split: "d = 10 * t + r"
  shows "xB + 10 * sB + f + 1 + 100 * (t + b + e) =
      xA + 10 * sA + f + 11 * d + 1"
  using input digits split by arith


lemma comma_c1_borrow_raw_balance:
  assumes xa: "xA < 100" and xb: "xB < 100" and fpos: "1 \<le> f" and f: "f \<le> 8"
  defines "delta \<equiv> comma_c1_suffix_delta xA xB"
  defines "b \<equiv> comma_c1_suffix_borrow xA xB"
  defines "e \<equiv> comma_c1_digit_extra (xA mod 10) delta"
  shows "comma_c1_borrow_raw (f + 1) xB +
       100 * (delta div 10 + b + e) =
       comma_c1_borrow_raw f xA + 11 * delta + 1"
proof -
  have input: "xB + 100 * b = xA + delta"
    using comma_c1_suffix_delta_borrow[OF xa xb]
    by (simp only: b_def delta_def)
  have digits: "xB mod 10 + 10 * e = xA mod 10 + delta mod 10"
    using comma_c1_borrow_digit_identity[OF xa xb]
    by (simp only: delta_def b_def e_def)
  have delta_split: "delta = 10 * (delta div 10) + delta mod 10" by simp
  have balance:
    "xB + 10 * (xB mod 10) + f + 1 +
        100 * (delta div 10 + b + e) =
      xA + 10 * (xA mod 10) + f + 11 * delta + 1"
    by (rule comma_c1_borrow_balance_arithmetic[OF input digits delta_split])
  show ?thesis
    using balance unfolding comma_c1_borrow_raw_def
    by (simp add: algebra_simps)
qed


lemma comma_c1_borrow_output_balance_arithmetic:
  fixes rawA rawB cA cB xA xB b' delta' u offset :: nat
  assumes step: "rawB + 100 * u = rawA + offset"
    and splitA: "rawA = 100 * cA + xA"
    and splitB: "rawB = 100 * cB + xB"
    and borrow: "xB + 100 * b' = xA + delta'"
  shows "offset + 100 * (cA + b') = delta' + 100 * (cB + u)"
  using step splitA splitB borrow by arith


lemma comma_c1_borrow_output_balance:
  assumes xa: "xA < 100" and xb: "xB < 100" and fpos: "1 \<le> f" and f: "f \<le> 8"
  defines "delta \<equiv> comma_c1_suffix_delta xA xB"
  defines "b \<equiv> comma_c1_suffix_borrow xA xB"
  defines "e \<equiv> comma_c1_digit_extra (xA mod 10) delta"
  defines "rawA \<equiv> comma_c1_borrow_raw f xA"
  defines "rawB \<equiv> comma_c1_borrow_raw (f + 1) xB"
  defines "cA \<equiv> rawA div 100"
  defines "cB \<equiv> rawB div 100"
  defines "xA' \<equiv> rawA mod 100"
  defines "xB' \<equiv> rawB mod 100"
  defines "b' \<equiv> comma_c1_suffix_borrow xA' xB'"
  defines "delta' \<equiv> comma_c1_suffix_delta xA' xB'"
  shows "11 * delta + 1 + 100 * (cA + b') =
      delta' + 100 * (cB + delta div 10 + b + e)"
proof -
  have raw: "rawB + 100 * (delta div 10 + b + e) = rawA + 11 * delta + 1"
    using comma_c1_borrow_raw_balance[OF xa xb fpos f]
    by (simp only: delta_def b_def e_def rawA_def rawB_def)
  have xa_bound: "xA' < 100" by (simp add: xA'_def)
  have xb_bound: "xB' < 100" by (simp add: xB'_def)
  have out: "xB' + 100 * b' = xA' + delta'"
    using comma_c1_suffix_delta_borrow[OF xa_bound xb_bound]
    by (simp only: xA'_def xB'_def b'_def delta'_def)
  have a_split: "rawA = 100 * cA + xA'"
    unfolding cA_def xA'_def by simp
  have b_split: "rawB = 100 * cB + xB'"
    unfolding cB_def xB'_def by simp
  have raw_associated:
    "rawB + 100 * (delta div 10 + (b + e)) = rawA + (11 * delta + 1)"
    using raw by (simp only: add.assoc)
  have projected:
    "11 * delta + 1 + 100 * (cA + b') =
      delta' + 100 * (cB + (delta div 10 + (b + e)))"
    by (rule comma_c1_borrow_output_balance_arithmetic[
        OF raw_associated a_split b_split out])
  show ?thesis using projected by (simp only: add.assoc)
qed


lemma comma_c1_borrow_delta_step:
  assumes xa: "xA < 100" and xb: "xB < 100" and fpos: "1 \<le> f" and f: "f \<le> 8"
  defines "delta \<equiv> comma_c1_suffix_delta xA xB"
  defines "b \<equiv> comma_c1_suffix_borrow xA xB"
  defines "e \<equiv> comma_c1_digit_extra (xA mod 10) delta"
  defines "rawA \<equiv> comma_c1_borrow_raw f xA"
  defines "rawB \<equiv> comma_c1_borrow_raw (f + 1) xB"
  defines "cA \<equiv> rawA div 100"
  defines "cB \<equiv> rawB div 100"
  defines "xA' \<equiv> rawA mod 100"
  defines "xB' \<equiv> rawB mod 100"
  defines "delta' \<equiv> comma_c1_suffix_delta xA' xB'"
  defines "b' \<equiv> comma_c1_suffix_borrow xA' xB'"
  shows "delta' = (11 * delta + 1) mod 100"
proof -
  have balance: "11 * delta + 1 + 100 * (cA + b') =
      delta' + 100 * (cB + delta div 10 + b + e)"
    using comma_c1_borrow_output_balance[OF xa xb fpos f]
    by (simp only: delta_def b_def e_def rawA_def rawB_def cA_def cB_def
        xA'_def xB'_def b'_def delta'_def)
  have dlt: "delta' < 100"
    by (simp add: delta'_def comma_c1_suffix_delta_def)
  have leftmod: "(11 * delta + 1 + 100 * (cA + b')) mod 100 =
      (11 * delta + 1) mod 100"
  proof -
    have mult: "(100 * (cA + b')) mod 100 = 0"
      by (simp only: mod_mult_self1_is_0)
    have "(11 * delta + 1 + 100 * (cA + b')) mod 100 =
        ((11 * delta + 1) mod 100 + (100 * (cA + b')) mod 100) mod 100"
      by (rule mod_add_eq[symmetric])
    also have "... = (11 * delta + 1) mod 100" using mult by simp
    finally show ?thesis .
  qed
  have rightmod: "(delta' + 100 * (cB + delta div 10 + b + e)) mod 100 = delta'"
  proof -
    have mult: "(100 * (cB + delta div 10 + b + e)) mod 100 = 0"
      by (simp only: mod_mult_self1_is_0)
    have "(delta' + 100 * (cB + delta div 10 + b + e)) mod 100 =
        (delta' mod 100 + (100 * (cB + delta div 10 + b + e)) mod 100) mod 100"
      by (rule mod_add_eq[symmetric])
    also have "... = delta'" using mult dlt by simp
    finally show ?thesis .
  qed
  have congr: "(11 * delta + 1) mod 100 = delta'"
    using arg_cong[where f="\<lambda>z::nat. z mod 100", OF balance]
      leftmod rightmod by simp
  then show ?thesis by simp
qed


lemma comma_c1_borrow_innovation_exact:
  assumes xa: "xA < 100" and xb: "xB < 100" and fpos: "1 \<le> f" and f: "f \<le> 8"
  defines "delta \<equiv> comma_c1_suffix_delta xA xB"
  defines "b \<equiv> comma_c1_suffix_borrow xA xB"
  defines "e \<equiv> comma_c1_digit_extra (xA mod 10) delta"
  defines "rawA \<equiv> comma_c1_borrow_raw f xA"
  defines "rawB \<equiv> comma_c1_borrow_raw (f + 1) xB"
  defines "cA \<equiv> rawA div 100"
  defines "cB \<equiv> rawB div 100"
  defines "xA' \<equiv> rawA mod 100"
  defines "xB' \<equiv> rawB mod 100"
  defines "delta' \<equiv> comma_c1_suffix_delta xA' xB'"
  defines "b' \<equiv> comma_c1_suffix_borrow xA' xB'"
  shows "int cB - int cA + int b - int b' =
      int ((11 * delta + 1) div 100) - int (delta div 10) - int e"
proof -
  have balance: "11 * delta + 1 + 100 * (cA + b') =
      delta' + 100 * (cB + delta div 10 + b + e)"
    using comma_c1_borrow_output_balance[OF xa xb fpos f]
    by (simp only: delta_def b_def e_def rawA_def rawB_def cA_def cB_def
        xA'_def xB'_def b'_def delta'_def)
  have delta_bound: "delta' < 100"
    by (simp add: delta'_def comma_c1_suffix_delta_def)
  have hundred_ne: "(100::nat) \<noteq> 0" by simp
  have left_div:
    "(11 * delta + 1 + 100 * (cA + b')) div 100 =
      cA + b' + (11 * delta + 1) div 100"
    by (simp only: div_mult_self2[OF hundred_ne] add.commute)
  have right_div:
    "(delta' + 100 * (cB + delta div 10 + b + e)) div 100 =
      cB + delta div 10 + b + e"
  proof -
    have split:
      "(delta' + 100 * (cB + delta div 10 + b + e)) div 100 =
        cB + delta div 10 + b + e + delta' div 100"
      by (simp only: div_mult_self2[OF hundred_ne] add.commute)
    show ?thesis using split delta_bound by simp
  qed
  have quotient:
    "(11 * delta + 1) div 100 + cA + b' =
      cB + delta div 10 + b + e"
    using arg_cong[where f="\<lambda>z::nat. z div 100", OF balance]
      left_div right_div by arith
  show ?thesis using quotient by arith
qed

definition comma_c1_borrow_innovation ::
    "comma_c1_phase \<Rightarrow> comma_c1_phase \<Rightarrow> nat \<Rightarrow> int" where
  "comma_c1_borrow_innovation P Q n =
    int (comma_c1_count Q n) - int (comma_c1_count P n) +
      int (comma_c1_suffix_borrow
        (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
        (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q))) -
      int (comma_c1_suffix_borrow
        (comma_c1_decode (c1_mod4 (comma_c1_iter n P))
          (c1_mod25 (comma_c1_iter n P)))
        (comma_c1_decode (c1_mod4 (comma_c1_iter n Q))
          (c1_mod25 (comma_c1_iter n Q))))"


lemma comma_c1_borrow_innovation_add:
  "comma_c1_borrow_innovation P Q (m + n) =
    comma_c1_borrow_innovation P Q m +
      comma_c1_borrow_innovation (comma_c1_iter m P) (comma_c1_iter m Q) n"
  unfolding comma_c1_borrow_innovation_def
  by (simp add: comma_c1_count_add comma_c1_iter_add algebra_simps)


definition comma_c1_borrow_step_innovation_formula ::
    "comma_c1_phase \<Rightarrow> comma_c1_phase \<Rightarrow> int" where
  "comma_c1_borrow_step_innovation_formula P Q =
    int ((11 * comma_c1_suffix_delta
      (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
      (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q)) + 1) div 100) -
    int (comma_c1_suffix_delta
      (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
      (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q)) div 10) -
    int (comma_c1_digit_extra
      (comma_c1_decode (c1_mod4 P) (c1_mod25 P) mod 10)
      (comma_c1_suffix_delta
        (comma_c1_decode (c1_mod4 P) (c1_mod25 P))
        (comma_c1_decode (c1_mod4 Q) (c1_mod25 Q))))"

lemma comma_c1_borrow_innovation_one_step_exact:
  assumes p_admitted: "comma_c1_phase_admitted P"
    and q_admitted: "comma_c1_phase_admitted Q"
    and adjacent: "c1_sector Q = c1_sector P + 1"
  shows "comma_c1_borrow_innovation P Q 1 =
      comma_c1_borrow_step_innovation_formula P Q"
proof -
  let ?xA = "comma_c1_decode (c1_mod4 P) (c1_mod25 P)"
  let ?xB = "comma_c1_decode (c1_mod4 Q) (c1_mod25 Q)"
  let ?f = "c1_sector P"
  let ?rawA = "comma_c1_borrow_raw ?f ?xA"
  let ?rawB = "comma_c1_borrow_raw (?f + 1) ?xB"
  let ?b = "comma_c1_suffix_borrow ?xA ?xB"
  let ?b' = "comma_c1_suffix_borrow (?rawA mod 100) (?rawB mod 100)"
  have xa: "?xA < 100" by (simp add: comma_c1_decode_def)
  have xb: "?xB < 100" by (simp add: comma_c1_decode_def)
  have fpos: "1 \<le> ?f" and fbound: "?f \<le> 8"
  proof -
    show "1 \<le> ?f" using p_admitted by (simp add: comma_c1_phase_admitted_def)
    have qbound: "c1_sector Q \<le> 9"
      using q_admitted by (simp add: comma_c1_phase_admitted_def)
    show "?f \<le> 8" using adjacent qbound by arith
  qed
  have rawA:
    "?rawA = 100 * comma_c1_count P 1 +
      comma_c1_decode (c1_mod4 (comma_c1_iter 1 P))
        (c1_mod25 (comma_c1_iter 1 P))"
    using comma_c1_borrow_raw_phase_step[OF p_admitted] by simp
  have rawB:
    "?rawB = 100 * comma_c1_count Q 1 +
      comma_c1_decode (c1_mod4 (comma_c1_iter 1 Q))
        (c1_mod25 (comma_c1_iter 1 Q))"
    using comma_c1_borrow_raw_phase_step[OF q_admitted] adjacent by simp
  have stepA_bound:
    "comma_c1_decode (c1_mod4 (comma_c1_iter 1 P))
        (c1_mod25 (comma_c1_iter 1 P)) < 100"
    by (simp add: comma_c1_decode_def)
  have stepB_bound:
    "comma_c1_decode (c1_mod4 (comma_c1_iter 1 Q))
        (c1_mod25 (comma_c1_iter 1 Q)) < 100"
    by (simp add: comma_c1_decode_def)
  have rawA_parts:
    "?rawA div 100 = comma_c1_count P 1"
    "?rawA mod 100 =
      comma_c1_decode (c1_mod4 (comma_c1_iter 1 P))
        (c1_mod25 (comma_c1_iter 1 P))"
    using rawA stepA_bound by simp_all
  have rawB_parts:
    "?rawB div 100 = comma_c1_count Q 1"
    "?rawB mod 100 =
      comma_c1_decode (c1_mod4 (comma_c1_iter 1 Q))
        (c1_mod25 (comma_c1_iter 1 Q))"
    using rawB stepB_bound by simp_all
  have local_exact:
    "int (?rawB div 100) - int (?rawA div 100) + int ?b - int ?b' =
      comma_c1_borrow_step_innovation_formula P Q"
    using comma_c1_borrow_innovation_exact[OF xa xb fpos fbound]
    by (simp only: comma_c1_borrow_step_innovation_formula_def
        comma_c1_suffix_delta_def comma_c1_suffix_borrow_def
        comma_c1_digit_extra_def comma_c1_borrow_raw_def)
  have assembled:
    "comma_c1_borrow_innovation P Q 1 =
      int (?rawB div 100) - int (?rawA div 100) + int ?b - int ?b'"
    unfolding comma_c1_borrow_innovation_def
    using rawA_parts rawB_parts by simp
  show ?thesis using assembled local_exact by simp
qed

lemma comma_c1_borrow_high_cocycle:
  fixes HA HB cA cB b b' :: nat
  defines "D \<equiv> int HB - int HA - int b"
  defines "D' \<equiv> int (HB + cB) - int (HA + cA) - int b'"
  defines "zeta \<equiv> int cB - int cA + int b - int b'"
  shows "D' = D + zeta"
  using D_def D'_def zeta_def by arith

ML \<open>
  val checked = @{thms comma_c1_borrow_raw_phase_step
    comma_c1_suffix_delta_bound comma_c1_suffix_delta_borrow
    comma_c1_borrow_digit_identity comma_c1_borrow_balance_arithmetic
    comma_c1_borrow_raw_balance
    comma_c1_borrow_output_balance_arithmetic
    comma_c1_borrow_output_balance comma_c1_borrow_delta_step
    comma_c1_borrow_innovation_exact comma_c1_borrow_innovation_add
    comma_c1_borrow_innovation_one_step_exact
    comma_c1_borrow_high_cocycle};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1 borrow cocycle proof depends on an oracle";
\<close>
end
