theory Comma_C1_Phase
  imports Comma_Arithmetic.Comma_Child_Cylinder
begin

text \<open>The low two decimal digits are carried by their CRT residues.
The decoder is a specification function; the state itself stores only the
sector and the two residues modulo 4 and 25.\<close>

record comma_c1_phase =
  c1_sector :: nat
  c1_mod4 :: nat
  c1_mod25 :: nat

definition comma_c1_phase_admitted :: "comma_c1_phase \<Rightarrow> bool" where
  "comma_c1_phase_admitted C \<longleftrightarrow>
    1 \<le> c1_sector C \<and> c1_sector C \<le> 9 \<and>
    c1_mod4 C < 4 \<and> c1_mod25 C < 25"

definition comma_c1_decode :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_c1_decode q4 q25 = (25 * q4 + 76 * q25) mod 100"

definition comma_c1_phase_of :: "nat \<Rightarrow> nat \<Rightarrow> comma_c1_phase" where
  "comma_c1_phase_of f x =
    \<lparr>c1_sector = f, c1_mod4 = x mod 4, c1_mod25 = x mod 25\<rparr>"

definition comma_c1_step :: "comma_c1_phase \<Rightarrow> comma_c1_phase" where
  "comma_c1_step C =
    \<lparr>c1_sector = c1_sector C,
      c1_mod4 = (3 * c1_mod4 C + c1_sector C) mod 4,
      c1_mod25 = (11 * c1_mod25 C + c1_sector C) mod 25\<rparr>"


lemma comma_c1_decode_mod4_divides: "(4::nat) dvd 100"
  by simp


lemma comma_c1_decode_mod4_coefficients:
  fixes q4 q25 :: nat
  shows
  "25 * q4 + 76 * q25 = q4 + 4 * (6 * q4 + 19 * q25)"
  by (simp add: algebra_simps; arith)


lemma comma_c1_decode_mod4_raw:
  fixes q4 q25 :: nat
  shows
  "(25 * q4 + 76 * q25) mod 4 = q4 mod 4"
proof -
  let ?k = "6 * q4 + 19 * q25"
  have multiple: "(4 * ?k) mod 4 = 0"
    by (simp only: mod_mult_self1_is_0)
  have residue: "(q4 + 4 * ?k) mod 4 = q4 mod 4"
  proof -
    have "(q4 + 4 * ?k) mod 4 = (q4 mod 4 + (4 * ?k) mod 4) mod 4"
      by (rule mod_add_eq[symmetric])
    also have "... = q4 mod 4" using multiple by simp
    finally show ?thesis .
  qed
  show ?thesis
    by (simp only: comma_c1_decode_mod4_coefficients residue)
qed


lemma comma_c1_decode_mod4:
  "comma_c1_decode q4 q25 mod 4 = q4 mod 4"
  unfolding comma_c1_decode_def
  by (simp only: mod_mod_cancel[OF comma_c1_decode_mod4_divides]
      comma_c1_decode_mod4_raw)


lemma comma_c1_decode_mod25_divides: "(25::nat) dvd 100"
  by simp


lemma comma_c1_decode_mod25_coefficients:
  fixes q4 q25 :: nat
  shows
  "25 * q4 + 76 * q25 = q25 + 25 * (q4 + 3 * q25)"
  by (simp add: algebra_simps; arith)


lemma comma_c1_decode_mod25_raw:
  fixes q4 q25 :: nat
  shows
  "(25 * q4 + 76 * q25) mod 25 = q25 mod 25"
proof -
  let ?k = "q4 + 3 * q25"
  have multiple: "(25 * ?k) mod 25 = 0"
    by (simp only: mod_mult_self1_is_0)
  have residue: "(q25 + 25 * ?k) mod 25 = q25 mod 25"
  proof -
    have "(q25 + 25 * ?k) mod 25 = (q25 mod 25 + (25 * ?k) mod 25) mod 25"
      by (rule mod_add_eq[symmetric])
    also have "... = q25 mod 25" using multiple by simp
    finally show ?thesis .
  qed
  show ?thesis
    by (simp only: comma_c1_decode_mod25_coefficients residue)
qed


lemma comma_c1_decode_mod25:
  "comma_c1_decode q4 q25 mod 25 = q25 mod 25"
  unfolding comma_c1_decode_def
  by (simp only: mod_mod_cancel[OF comma_c1_decode_mod25_divides]
      comma_c1_decode_mod25_raw)



lemma comma_c1_decode_residue_expansion:
  fixes x :: nat
  shows
  "25 * (x mod 4) + 76 * (x mod 25) +
      100 * (x div 4 + 19 * (x div 25)) = 101 * x"
proof -
  have split4: "x = x mod 4 + 4 * (x div 4)" by simp
  have split25: "x = x mod 25 + 25 * (x div 25)" by simp
  have scale4: "25 * x = 25 * (x mod 4) + 100 * (x div 4)"
  proof -
    have "25 * x = 25 * (x mod 4 + 4 * (x div 4))"
      by (rule arg_cong[where f="\<lambda>z::nat. 25 * z", OF split4])
    also have "... = 25 * (x mod 4) + 100 * (x div 4)"
      by (simp only: distrib_left mult.assoc[symmetric]; simp)
    finally show ?thesis .
  qed
  have scale76: "76 * x = 76 * (x mod 25) + 1900 * (x div 25)"
  proof -
    have "76 * x = 76 * (x mod 25 + 25 * (x div 25))"
      by (rule arg_cong[where f="\<lambda>z::nat. 76 * z", OF split25])
    also have "... = 76 * (x mod 25) + 1900 * (x div 25)"
      by (simp only: distrib_left mult.assoc[symmetric]; simp)
    finally show ?thesis .
  qed
  have "25 * x + 76 * x = 101 * x" by arith
  with scale4 scale76 show ?thesis
    by (simp add: algebra_simps; arith)
qed


lemma comma_c1_decode_residue:
  "comma_c1_decode (x mod 4) (x mod 25) = x mod 100"
proof -
  have expand: "25 * (x mod 4) + 76 * (x mod 25) +
      100 * (x div 4 + 19 * (x div 25)) = 101 * x"
    by (rule comma_c1_decode_residue_expansion)
  have congruent:
    "(25 * (x mod 4) + 76 * (x mod 25)) mod 100 = x mod 100"
  proof -
    let ?A = "25 * (x mod 4) + 76 * (x mod 25)"
    let ?K = "x div 4 + 19 * (x div 25)"
    have reduced:
      "(?A + 100 * ?K) mod 100 =
        (101 * x) mod 100"
      by (rule arg_cong[where f="\<lambda>z::nat. z mod 100", OF expand])
    have multiple: "(100 * ?K) mod 100 = 0"
      by (simp only: mod_mult_self1_is_0)
    have left: "(?A + 100 * ?K) mod 100 = ?A mod 100"
    proof -
      have "(?A + 100 * ?K) mod 100 =
          (?A mod 100 + (100 * ?K) mod 100) mod 100"
        by (rule mod_add_eq[symmetric])
      also have "... = ?A mod 100" using multiple by simp
      finally show ?thesis .
    qed
    have scaled: "101 * x = x + 100 * x" by arith
    have multiple_x: "(100 * x) mod 100 = 0"
      by (simp only: mod_mult_self1_is_0)
    have right: "(101 * x) mod 100 = x mod 100"
    proof -
      have "(101 * x) mod 100 = (x + 100 * x) mod 100"
        by (simp only: scaled)
      also have "... = (x mod 100 + (100 * x) mod 100) mod 100"
        by (rule mod_add_eq[symmetric])
      also have "... = x mod 100" using multiple_x by simp
      finally show ?thesis .
    qed
    show ?thesis
    proof -
      have "?A mod 100 = (?A + 100 * ?K) mod 100"
        by (rule left[symmetric])
      also have "... = (101 * x) mod 100" by (rule reduced)
      also have "... = x mod 100" by (rule right)
      finally show ?thesis .
    qed
  qed
  show ?thesis by (simp add: comma_c1_decode_def congruent)
qed


lemma comma_c1_decode_roundtrip:
  assumes "q4 < 4" "q25 < 25"
  shows "comma_c1_decode q4 q25 mod 4 = q4"
    and "comma_c1_decode q4 q25 mod 25 = q25"
  using assms by (simp_all add: comma_c1_decode_mod4 comma_c1_decode_mod25)

lemma comma_c1_phase_of_admitted:
  assumes "1 \<le> f" "f \<le> 9"
  shows "comma_c1_phase_admitted (comma_c1_phase_of f x)"
  using assms by (simp add: comma_c1_phase_admitted_def comma_c1_phase_of_def)

lemma comma_c1_phase_of_decode:
  "comma_c1_phase_of (c1_sector C)
      (comma_c1_decode (c1_mod4 C) (c1_mod25 C)) =
    C"
  if "comma_c1_phase_admitted C"
  using that
  by (cases C) (simp add: comma_c1_phase_of_def comma_c1_phase_admitted_def
      comma_c1_decode_mod4 comma_c1_decode_mod25)

lemma comma_c1_step_closed:
  assumes "comma_c1_phase_admitted C"
  shows "comma_c1_phase_admitted (comma_c1_step C)"
  using assms by (cases C) (simp add: comma_c1_phase_admitted_def comma_c1_step_def)

lemma comma_c1_step_crt_exact:
  "comma_c1_decode (c1_mod4 (comma_c1_step C))
       (c1_mod25 (comma_c1_step C)) =
     (11 * comma_c1_decode (c1_mod4 C) (c1_mod25 C) + c1_sector C) mod 100"
proof -
  let ?x = "comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  let ?y = "11 * ?x + c1_sector C"
  have r4: "?x mod 4 = c1_mod4 C mod 4"
    by (rule comma_c1_decode_mod4)
  have r25: "?x mod 25 = c1_mod25 C mod 25"
    by (rule comma_c1_decode_mod25)
  have product4: "(11 * ?x) mod 4 = (3 * c1_mod4 C) mod 4"
  proof -
    have "(11 * ?x) mod 4 = ((11 mod 4) * (?x mod 4)) mod 4"
      by (rule mod_mult_eq[symmetric])
    also have "... = ((3 mod 4) * (c1_mod4 C mod 4)) mod 4"
      using r4 by simp
    also have "... = (3 * c1_mod4 C) mod 4"
      by (rule mod_mult_eq)
    finally show ?thesis .
  qed
  have product25: "(11 * ?x) mod 25 = (11 * c1_mod25 C) mod 25"
  proof -
    have "(11 * ?x) mod 25 = ((11 mod 25) * (?x mod 25)) mod 25"
      by (rule mod_mult_eq[symmetric])
    also have "... = ((11 mod 25) * (c1_mod25 C mod 25)) mod 25"
      using r25 by simp
    also have "... = (11 * c1_mod25 C) mod 25"
      by (rule mod_mult_eq)
    finally show ?thesis .
  qed
  have y4: "?y mod 4 = (3 * c1_mod4 C + c1_sector C) mod 4"
    by (rule mod_add_cong[OF product4 refl])
  have y25: "?y mod 25 = (11 * c1_mod25 C + c1_sector C) mod 25"
    by (rule mod_add_cong[OF product25 refl])
  have decode:
    "comma_c1_decode (?y mod 4) (?y mod 25) = ?y mod 100"
    by (rule comma_c1_decode_residue)
  show ?thesis
    unfolding comma_c1_step_def
    using decode y4 y25 by simp
qed


lemma comma_c1_step_refines_phase_step:
  assumes "x < 100" "C = comma_c1_phase_of f x"
  shows "comma_c1_decode (c1_mod4 (comma_c1_step C))
      (c1_mod25 (comma_c1_step C)) =
    comma_phase_step f (x div 10) (x mod 10) mod 100"
proof -
  have phase:
    "comma_c1_decode (c1_mod4 (comma_c1_step C))
        (c1_mod25 (comma_c1_step C)) =
      (11 * comma_c1_decode (c1_mod4 C) (c1_mod25 C) + f) mod 100"
    using comma_c1_step_crt_exact assms
    by (simp add: comma_c1_phase_of_def)
  have low: "comma_c1_decode (c1_mod4 C) (c1_mod25 C) = x"
    using assms by (simp add: comma_c1_phase_of_def comma_c1_decode_residue)
  have decimal:
    "(11 * x + f) mod 100 =
      comma_phase_step f (x div 10) (x mod 10) mod 100"
  proof -
    let ?t = "x div 10"
    let ?d = "x mod 10"
    let ?p = "comma_phase_step f ?t ?d"
    have split: "x = 10 * ?t + ?d" by (simp add: mult.commute)
    have raw: "11 * x + f = ?p + 100 * ?t"
      unfolding comma_phase_step_def using split by arith
    have multiple: "(100 * ?t) mod 100 = 0"
      by (simp only: mod_mult_self1_is_0)
    have residue: "(?p + 100 * ?t) mod 100 = ?p mod 100"
    proof -
      have "(?p + 100 * ?t) mod 100 =
          (?p mod 100 + (100 * ?t) mod 100) mod 100"
        by (rule mod_add_eq[symmetric])
      also have "... = ?p mod 100" using multiple by simp
      finally show ?thesis .
    qed
    show ?thesis by (simp only: raw residue)
  qed
  show ?thesis using phase low decimal by simp
qed


definition comma_c0 :: "comma_c1_phase \<Rightarrow> bool" where
  "comma_c0 C \<longleftrightarrow>
    10 \<le> (comma_c1_decode (c1_mod4 C) (c1_mod25 C)) mod 10 + c1_sector C"

definition comma_c1 :: "comma_c1_phase \<Rightarrow> bool" where
  "comma_c1 C \<longleftrightarrow>
    10 \<le> (comma_c1_decode (c1_mod4 C) (c1_mod25 C)) div 10 +
      (comma_c1_decode (c1_mod4 C) (c1_mod25 C)) mod 10 +
      (if comma_c0 C then 1 else 0)"

lemma comma_c0_exact:
  assumes "x < 100" "C = comma_c1_phase_of f x"
  shows "comma_c0 C \<longleftrightarrow> 10 \<le> x mod 10 + f"
  using assms by (simp add: comma_c0_def comma_c1_phase_of_def
      comma_c1_decode_residue)

lemma comma_c1_exact:
  assumes "x < 100" "C = comma_c1_phase_of f x"
  shows "comma_c1 C \<longleftrightarrow>
    10 \<le> x div 10 + x mod 10 + (if 10 \<le> x mod 10 + f then 1 else 0)"
  using assms by (simp add: comma_c1_def comma_c0_exact[OF assms]
      comma_c0_def comma_c1_phase_of_def comma_c1_decode_residue)

lemma comma_nat_div10_lt20:
  fixes t :: nat
  assumes "t < 20"
  shows "t div 10 = (if 10 \<le> t then 1 else 0)"
proof -
  have decomposition: "t = 10 * (t div 10) + t mod 10"
    by (simp add: mult.commute)
  have remainder: "t mod 10 < 10" by simp
  show ?thesis
  proof (cases "10 \<le> t")
    case True
    have quotient: "t div 10 = 1"
      using True assms decomposition remainder by arith
    then show ?thesis by simp
  next
    case False
    have quotient: "t div 10 = 0"
      using False decomposition remainder by arith
    then show ?thesis by simp
  qed
qed

lemma comma_c1_spatiotemporal_step:
  assumes "x < 100" "C = comma_c1_phase_of f x" "f \<le> 9"
  shows "x + 10 * (x mod 10) + f =
      100 * (if comma_c1 C then 1 else 0) +
        comma_c1_decode (c1_mod4 (comma_c1_step C))
          (c1_mod25 (comma_c1_step C))"
proof -
  let ?d = "x mod 10"
  let ?t = "x div 10"
  let ?c0 = "if 10 \<le> ?d + f then (1::nat) else 0"
  let ?v = "?t + ?d + ?c0"
  let ?S = "x + 10 * ?d + f"
  have digits: "x = 10 * ?t + ?d" by simp
  have d_bound: "?d < 10" by simp
  have sum_bound: "?d + f < 20" using d_bound assms(3) by arith
  have c0quot: "(?d + f) div 10 = ?c0"
    by (rule comma_nat_div10_lt20[OF sum_bound])
  have c0: "?c0 = (?d + f) div 10"
    by (rule sym[OF c0quot])
  have phase_digits:
    "comma_phase_step f ?t ?d = 10 * ?v + (?d + f) mod 10"
    using comma_phase_carry[OF d_bound] c0 by simp
  have phase_step: "?S = comma_phase_step f ?t ?d"
    unfolding comma_phase_step_def using digits by arith
  have refined:
    "comma_c1_decode (c1_mod4 (comma_c1_step C))
        (c1_mod25 (comma_c1_step C)) =
      comma_phase_step f ?t ?d mod 100"
    by (rule comma_c1_step_refines_phase_step[OF assms(1,2)])
  have crt:
    "comma_c1_decode (c1_mod4 (comma_c1_step C))
        (c1_mod25 (comma_c1_step C)) = ?S mod 100"
    using refined phase_step by simp
  have t_bound: "?t < 10"
    using assms(1) by (simp add: div_less_iff_less_mult)
  have c0_bound: "?c0 \<le> 1" by (simp split: if_splits)
  have v_bound: "?v < 20" using t_bound d_bound c0_bound by arith
  have c1_spec: "comma_c1 C \<longleftrightarrow> 10 \<le> ?v"
    using comma_c1_exact[OF assms(1,2)] by simp
  have vquot: "?v div 10 = (if 10 \<le> ?v then 1 else 0)"
    by (rule comma_nat_div10_lt20[OF v_bound])
  have phase_quotient:
    "comma_phase_step f ?t ?d div 10 = ?v"
    using comma_phase_quotient[OF d_bound] c0 by simp
  have nested_div:
    "?S div 100 = (comma_phase_step f ?t ?d div 10) div 10"
  proof -
    have "?S div 100 = ?S div (10 * 10)" by simp
    also have "... = (?S div 10) div 10"
      by (rule div_mult2_eq)
    also have "... = (comma_phase_step f ?t ?d div 10) div 10"
      using phase_step by simp
    finally show ?thesis .
  qed
  have c1quot: "?S div 100 = (if comma_c1 C then 1 else 0)"
    using nested_div phase_quotient vquot c1_spec by simp
  have split:
    "?S = 100 * (?S div 100) + (?S mod 100)"
    by simp
  show ?thesis
    using crt c1quot split by simp
qed


lemma comma_decimal_high_mod10 [simp]:
  fixes H x :: nat
  shows "(100 * H + x) mod 10 = x mod 10"
proof -
  have scaled: "100 * H = 10 * (10 * H)" by arith
  have high_multiple: "(100 * H) mod 10 = 0"
    by (simp only: scaled mod_mult_self1_is_0)
  have "(100 * H + x) mod 10 =
      ((100 * H) mod 10 + x mod 10) mod 10"
    by (rule mod_add_eq[symmetric])
  also have "... = x mod 10" using high_multiple by simp
  finally show ?thesis .
qed

lemma comma_c1_high_prefix_step:
  fixes H x f :: nat
  assumes "x < 100" "C = comma_c1_phase_of f x" "f \<le> 9"
  shows "(100 * H + x) + 10 * ((100 * H + x) mod 10) + f =
      100 * (H + (if comma_c1 C then 1 else 0)) +
        comma_c1_decode (c1_mod4 (comma_c1_step C))
          (c1_mod25 (comma_c1_step C))"
proof -
  have low: "(100 * H + x) mod 10 = x mod 10" by simp
  have local:
    "x + 10 * (x mod 10) + f =
      100 * (if comma_c1 C then 1 else 0) +
        comma_c1_decode (c1_mod4 (comma_c1_step C))
          (c1_mod25 (comma_c1_step C))"
    by (rule comma_c1_spatiotemporal_step[OF assms])
  show ?thesis using low local by (simp add: algebra_simps)
qed

fun comma_c1_iter :: "nat \<Rightarrow> comma_c1_phase \<Rightarrow> comma_c1_phase" where
  "comma_c1_iter 0 C = C"
| "comma_c1_iter (Suc n) C = comma_c1_step (comma_c1_iter n C)"

lemma comma_c1_iter_sector:
  "c1_sector (comma_c1_iter n C) = c1_sector C"
  by (induction n) (simp_all add: comma_c1_step_def)

lemma comma_c1_iter_low_digit:
  "comma_c1_decode (c1_mod4 (comma_c1_iter n C))
      (c1_mod25 (comma_c1_iter n C)) mod 10 =
    (comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10 +
      n * c1_sector C) mod 10"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?y = "comma_c1_decode (c1_mod4 (comma_c1_iter n C))
      (c1_mod25 (comma_c1_iter n C))"
  let ?initial = "comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
  let ?f = "c1_sector C"
  have iter_sector: "c1_sector (comma_c1_iter n C) = ?f"
    by (rule comma_c1_iter_sector)
  have stepped:
    "comma_c1_decode (c1_mod4 (comma_c1_step (comma_c1_iter n C)))
        (c1_mod25 (comma_c1_step (comma_c1_iter n C))) =
      (11 * ?y + ?f) mod 100"
    using comma_c1_step_crt_exact[of "comma_c1_iter n C"] iter_sector by simp
  have exact:
    "comma_c1_decode (c1_mod4 (comma_c1_iter (Suc n) C))
        (c1_mod25 (comma_c1_iter (Suc n) C)) = (11 * ?y + ?f) mod 100"
    by (simp only: comma_c1_iter.simps stepped)
  have divides: "(10::nat) dvd 100" by simp
  have multiple: "(10 * ?y) mod 10 = 0"
    by (simp only: mod_mult_self1_is_0)
  have times_eleven: "(11 * ?y) mod 10 = ?y mod 10"
  proof -
    have identity: "11 * ?y = 10 * ?y + ?y" by arith
    have "(11 * ?y) mod 10 = (10 * ?y + ?y) mod 10"
      by (simp only: identity)
    also have "... = ((10 * ?y) mod 10 + ?y mod 10) mod 10"
      by (rule mod_add_eq[symmetric])
    also have "... = ?y mod 10" using multiple by simp
    finally show ?thesis .
  qed
  have step_digit:
    "comma_c1_decode (c1_mod4 (comma_c1_iter (Suc n) C))
        (c1_mod25 (comma_c1_iter (Suc n) C)) mod 10 =
      (?y + ?f) mod 10"
  proof -
    have "comma_c1_decode (c1_mod4 (comma_c1_iter (Suc n) C))
        (c1_mod25 (comma_c1_iter (Suc n) C)) mod 10 =
      ((11 * ?y + ?f) mod 100) mod 10"
      by (simp only: exact)
    also have "... = (11 * ?y + ?f) mod 10"
      by (rule mod_mod_cancel[OF divides])
    also have "... = (?y + ?f) mod 10"
      by (rule mod_add_cong[OF times_eleven refl])
    finally show ?thesis .
  qed
  have append:
    "(?y + ?f) mod 10 = (?initial mod 10 + n * ?f + ?f) mod 10"
    by (rule mod_add_cong[OF Suc.IH refl])
  have successor:
    "(?initial mod 10 + n * ?f + ?f) mod 10 =
      (?initial mod 10 + Suc n * ?f) mod 10"
    by (simp add: algebra_simps)
  show ?case using step_digit append successor by simp
qed


lemma comma_c0_mechanical_step:
  assumes "1 \<le> c1_sector C" "c1_sector C \<le> 9"
  shows "(comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10 +
      (Suc n) * c1_sector C) div 10 =
    (comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10 +
      n * c1_sector C) div 10 +
      (if comma_c0 (comma_c1_iter n C) then 1 else 0)"
proof -
  let ?f = "c1_sector C"
  let ?d = "comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10"
  let ?a = "?d + n * ?f"
  let ?r = "?a mod 10"
  have phase: "comma_c1_decode (c1_mod4 (comma_c1_iter n C))
      (c1_mod25 (comma_c1_iter n C)) mod 10 = ?r"
    using comma_c1_iter_low_digit[of n C] by simp
  have sector: "c1_sector (comma_c1_iter n C) = c1_sector C"
    by (rule comma_c1_iter_sector)
  have carry: "comma_c0 (comma_c1_iter n C) \<longleftrightarrow> 10 \<le> ?r + ?f"
    using phase sector by (simp add: comma_c0_def)
  have rbound: "?r < 10" by simp
  have fbound: "?f < 10" using assms by simp
  have sum_bound: "?r + ?f < 20" using rbound fbound by arith
  have rquot: "(?r + ?f) div 10 = (if 10 \<le> ?r + ?f then 1 else 0)"
    by (rule comma_nat_div10_lt20[OF sum_bound])
  have split: "?a = 10 * (?a div 10) + ?r" by simp
  have decomposition:
    "?a + ?f = (?r + ?f) + 10 * (?a div 10)"
    using split by arith
  have ten_nonzero: "(10::nat) \<noteq> 0" by simp
  have shifted_quotient:
    "((?r + ?f) + 10 * (?a div 10)) div 10 =
      (?a div 10) + (?r + ?f) div 10"
    by (simp only: div_mult_self2[OF ten_nonzero] add.commute)
  have quotient: "(?a + ?f) div 10 = ?a div 10 + (if 10 \<le> ?r + ?f then 1 else 0)"
  proof -
    have "(?a + ?f) div 10 = ((?r + ?f) + 10 * (?a div 10)) div 10"
      by (simp only: decomposition)
    also have "... = ?a div 10 + (?r + ?f) div 10"
      by (rule shifted_quotient)
    also have "... = ?a div 10 + (if 10 \<le> ?r + ?f then 1 else 0)"
      using rquot by simp
    finally show ?thesis .
  qed
  have succ: "?d + (Suc n) * ?f = ?a + ?f"
    by (simp add: algebra_simps)
  show ?thesis by (simp only: succ carry quotient)
qed


ML \<open>
  val checked = @{thms comma_c1_decode_residue comma_c1_step_closed
    comma_c1_step_crt_exact comma_c1_step_refines_phase_step
    comma_c0_exact comma_c1_exact comma_c1_spatiotemporal_step
    comma_c1_iter_low_digit comma_c0_mechanical_step};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1 phase proof depends on an oracle";
\<close>
end
