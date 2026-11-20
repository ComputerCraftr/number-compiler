theory Five_Reverse_Reflected_H
  imports Five_Reverse_Bounds
begin

text \<open>
The reflected digit operator E is represented by the parity mask P.  Its
decimal-shift law yields a fixed-precision successor quotient for
H = E composed with multiplication by five.  The proof here concerns the
the unnormalized auxiliary operator and its transport to the physical orbit.
\<close>

function five_parity_mask :: "nat \<Rightarrow> nat" where
  "five_parity_mask n =
    (if n < 10 then n mod 2 else
      n mod 2 + 10 * five_parity_mask (n div 10))"
  by pat_completeness auto

termination
  by (relation "measure id") auto

(* Keep the recursive equation explicit: unrestricted simp unfolding here
   walks the entire decimal expansion whenever the argument is symbolic. *)
declare five_parity_mask.simps[simp del]
declare decimal_digit_count.simps[simp del]
declare decimal_reverse.simps[simp del]

fun five_fixed_reverse :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "five_fixed_reverse 0 n = 0"
| "five_fixed_reverse (Suc width) n =
    n mod 10 * 10 ^ width + five_fixed_reverse width (n div 10)"

lemma five_fixed_reverse_decimal:
  "five_fixed_reverse (decimal_digit_count n) n = decimal_reverse n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    then show ?thesis
      by (simp add: decimal_digit_count.simps decimal_reverse.simps)
  next
    case False
    have smaller: "n div 10 < n" using False by simp
    have count: "decimal_digit_count n =
        Suc (decimal_digit_count (n div 10))"
      using False by (simp add: decimal_digit_count.simps)
    have reverse: "decimal_reverse n =
        n mod 10 * 10 ^ decimal_digit_count (n div 10) +
          decimal_reverse (n div 10)"
      using False count by (simp add: decimal_reverse.simps)
    show ?thesis
      using less.IH[OF smaller] by (simp only: count five_fixed_reverse.simps reverse)
  qed
qed

definition five_reflected_E :: "nat \<Rightarrow> nat" where
  "five_reflected_E n = (n + 99 * five_parity_mask n) div 2"

definition five_reflected_H :: "nat \<Rightarrow> nat" where
  "five_reflected_H n = five_reflected_E (5 * n)"

function five_reflected_normalize :: "nat \<Rightarrow> nat" where
  "five_reflected_normalize n =
    (if n = 0 \<or> n mod 10 \<noteq> 0 then n
      else five_reflected_normalize (n div 10))"
  by pat_completeness auto

termination
  by (relation "measure id") auto

declare five_reflected_normalize.simps[simp del]

fun five_reflected_H_iter :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "five_reflected_H_iter 0 n = n"
| "five_reflected_H_iter (Suc k) n =
    five_reflected_H (five_reflected_H_iter k n)"

lemma five_parity_mask_lt_ten [simp]:
  assumes "n < 10"
  shows "five_parity_mask n = n mod 2"
  using assms by (simp add: five_parity_mask.simps)

lemma five_parity_mask_digit_equation:
  "five_parity_mask n = n mod 2 + 10 * five_parity_mask (n div 10)"
proof (cases "n < 10")
  case True
  then have quotient: "n div 10 = 0" by simp
  show ?thesis using True quotient by simp
next
  case False
  have equation:
    "five_parity_mask n =
      (if n < 10 then n mod 2 else
        n mod 2 + 10 * five_parity_mask (n div 10))"
    by (rule five_parity_mask.simps)
  show ?thesis using equation False by simp
qed

lemma five_parity_mask_even_remainder:
  "five_parity_mask n mod 2 = n mod 2"
proof -
  have equation: "five_parity_mask n =
      n mod 2 + 10 * five_parity_mask (n div 10)"
    by (rule five_parity_mask_digit_equation)
  have tail: "(10 * five_parity_mask (n div 10)) mod 2 = 0" by simp
  have joined:
    "(n mod 2 + 10 * five_parity_mask (n div 10)) mod 2 =
      ((n mod 2) mod 2 +
        (10 * five_parity_mask (n div 10)) mod 2) mod 2"
    by (rule mod_add_cong) simp_all
  show ?thesis using equation joined tail by simp
qed

lemma five_parity_weighted_even:
  fixes n m :: nat
  assumes parity: "m mod 2 = n mod 2"
  shows "(n + 99 * m) mod 2 = 0"
proof -
  have coefficient: "(99::nat) mod 2 = 1 mod 2" by simp
  have weighted: "(99 * m) mod 2 = (1 * m) mod 2"
    by (rule mod_mult_cong[OF coefficient refl])
  have joined:
    "(n + 99 * m) mod 2 = ((n mod 2) + ((99 * m) mod 2)) mod 2"
    by (rule mod_add_cong) simp_all
  have doubled: "(n mod 2) + (n mod 2) = 2 * (n mod 2)"
    by simp
  show ?thesis using joined weighted parity doubled by simp
qed

lemma five_reflected_terminal_digit_mod_ten:
  fixes a d :: nat
  assumes a_even: "a mod 2 = 0" and d_bound: "d < 10"
  shows "(10 * a + d + 99 * (d mod 2)) div 2 mod 10 = d div 2"
proof -
  have divisor: "2 dvd a"
    using a_even by (simp add: mod_eq_0_iff_dvd)
  then obtain u where a_value: "a = 2 * u"
    by (elim dvdE)
  have digit_cases:
    "d = 0 \<or> d = 1 \<or> d = 2 \<or> d = 3 \<or> d = 4 \<or>
      d = 5 \<or> d = 6 \<or> d = 7 \<or> d = 8 \<or> d = 9"
    using d_bound by arith
  have numerator:
    "10 * a + d + 99 * (d mod 2) =
      (10 * u) * 2 + (d + 99 * (d mod 2))"
    by (simp add: a_value algebra_simps)
  have quotient:
    "((10 * u) * 2 + (d + 99 * (d mod 2))) div 2 =
      10 * u + (d + 99 * (d mod 2)) div 2"
    by (rule div_mult_self3) simp
  have strip:
    "(10 * u + (d + 99 * (d mod 2)) div 2) mod 10 =
      ((d + 99 * (d mod 2)) div 2) mod 10"
    by (rule mod_mult_self4)
  show ?thesis
    unfolding numerator quotient strip
    using digit_cases
    by (elim disjE; simp)
qed

lemma five_parity_mask_ten_mul:
  "five_parity_mask (10 * n) = 10 * five_parity_mask n"
proof (cases "n=0")
  case True
  then show ?thesis by simp
next
  case False
  then have bound: "10 \<le> 10 * n" by simp
  have quotient: "(10 * n) div 10 = n" by simp
  have remainder: "(10 * n) mod 10 = 0" by simp
  have unfolded:
    "five_parity_mask (10*n) =
      (if 10*n < 10 then (10*n) mod 2 else
        (10*n) mod 2 + 10 * five_parity_mask ((10*n) div 10))"
    by (rule five_parity_mask.simps)
  show ?thesis
    using unfolded bound quotient remainder by simp
qed

lemma five_decimal_shift_power:
  fixes f :: "nat \<Rightarrow> nat"
  assumes scale: "\<And>m. f (10 * m) = 10 * f m"
  shows "f (10^k * n) = 10^k * f n"
proof (induction k)
  case 0
  show ?case by simp
next
  case (Suc k)
  have step: "(10::nat)^Suc k * n = 10 * (10^k * n)"
    by (simp add: power_Suc mult.assoc)
  show ?case by (simp only: step scale Suc.IH power_Suc mult.assoc)
qed

lemma five_parity_mask_power_ten:
  "five_parity_mask ((10::nat)^k * n) = 10^k * five_parity_mask n"
  by (rule five_decimal_shift_power[where f=five_parity_mask])
     (rule five_parity_mask_ten_mul)

lemma five_reflected_E_ten_mul:
  "five_reflected_E (10 * n) = 10 * five_reflected_E n"
proof -
  have mask: "five_parity_mask (10 * n) = 10 * five_parity_mask n"
    by (rule five_parity_mask_ten_mul)
  have numerator:
    "10 * n + 99 * five_parity_mask (10 * n) =
      10 * (n + 99 * five_parity_mask n)"
    by (simp only: mask; simp add: algebra_simps)
  have even: "(n + 99 * five_parity_mask n) mod 2 = 0"
    by (rule five_parity_weighted_even[OF five_parity_mask_even_remainder])
  have divisor: "2 dvd n + 99 * five_parity_mask n"
    using even by (simp add: mod_eq_0_iff_dvd)
  then obtain k where exact: "n + 99 * five_parity_mask n = 2 * k"
    by (elim dvdE)
  have quotient: "(n + 99 * five_parity_mask n) div 2 = k"
    using exact by simp
  have scaled_value:
    "10 * (n + 99 * five_parity_mask n) = 2 * (10 * k)"
    by (simp add: exact mult.assoc[symmetric] mult.left_commute)
  have scaled_quotient: "(10 * (n + 99 * five_parity_mask n)) div 2 = 10 * k"
    using scaled_value by simp
  show ?thesis
    unfolding five_reflected_E_def
    using numerator quotient scaled_quotient by simp
qed

lemma five_reflected_E_power_ten:
  "five_reflected_E ((10::nat)^k * n) = 10^k * five_reflected_E n"
  by (rule five_decimal_shift_power[where f=five_reflected_E])
     (rule five_reflected_E_ten_mul)

lemma five_reflected_H_power_ten:
  "five_reflected_H ((10::nat)^k * n) = 10^k * five_reflected_H n"
  unfolding five_reflected_H_def
  using five_reflected_E_power_ten[of k "5*n"]
  by (simp add: algebra_simps)

lemma five_reflected_H_iter_power_ten:
  "five_reflected_H_iter t ((10::nat)^k * n) =
    10^k * five_reflected_H_iter t n"
  by (induction t) (simp_all add: five_reflected_H_power_ten)

lemma five_reflected_E_digit_equation:
  "five_reflected_E n =
    10 * five_reflected_E (n div 10) +
      ((n mod 10) + 99 * ((n mod 10) mod 2)) div 2"
proof -
  let ?q = "n div 10"
  let ?d = "n mod 10"
  have source: "n = 10 * ?q + ?d" by simp
  have two_dvd_ten: "(2::nat) dvd 10" by simp
  have digit_parity: "?d mod 2 = n mod 2"
    by (rule mod_mod_cancel[OF two_dvd_ten])
  have mask: "five_parity_mask n = ?d mod 2 + 10 * five_parity_mask ?q"
  proof -
    have equation: "five_parity_mask n =
        n mod 2 + 10 * five_parity_mask (n div 10)"
      by (rule five_parity_mask_digit_equation)
    show ?thesis using equation digit_parity by metis
  qed
  have parity: "five_parity_mask ?q mod 2 = ?q mod 2"
    by (rule five_parity_mask_even_remainder)
  let ?a = "?q + 99 * five_parity_mask ?q"
  let ?b = "?d + 99 * (?d mod 2)"
  have numerator: "n + 99 * five_parity_mask n = 10*?a + ?b"
  proof -
    have "n + 99 * five_parity_mask n =
        (10 * ?q + ?d) + 99 * five_parity_mask n"
      by (rule arg_cong[where
        f="\<lambda>value. value + 99 * five_parity_mask n"]) (rule source)
    also have "... = (10 * ?q + ?d) +
        99 * (?d mod 2 + 10 * five_parity_mask ?q)"
      by (rule arg_cong[where
        f="\<lambda>value. (10 * ?q + ?d) + 99 * value"]) (rule mask)
    also have "... = 10 * ?a + ?b" by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  have a_even: "?a mod 2 = 0"
    by (rule five_parity_weighted_even[OF parity])
  then obtain u where a_value: "?a = 2*u"
    by (metis mod_eq_0_iff_dvd dvd_def)
  have factor: "10 * ?a = 2 * (10*u)"
    by (simp only: a_value mult.left_commute)
  have quotient: "?a div 2 = u" by (simp add: a_value)
  show ?thesis
    unfolding five_reflected_E_def numerator factor quotient
    by (rule div_mult_self4) simp
qed

lemma five_reflected_E_mod_ten:
  "five_reflected_E n mod 10 = (n mod 10) div 2"
proof -
  let ?d = "n mod 10"
  have d_bound: "?d < 10" by simp
  have digit:
    "(10 * 0 + ?d + 99 * (?d mod 2)) div 2 mod 10 = ?d div 2"
    by (rule five_reflected_terminal_digit_mod_ten) (simp_all add: d_bound)
  show ?thesis
    unfolding five_reflected_E_digit_equation[of n]
    using digit by (simp only: mod_mult_self4 mult_zero_left mult_zero_right add_0)
qed

lemma five_reflected_E_mod_power_ten_cong:
  assumes "n mod 10^k = m mod 10^k"
  shows "five_reflected_E n mod 10^k = five_reflected_E m mod 10^k"
  using assms
proof (induction k arbitrary: n m)
  case 0
  then show ?case by simp
next
  case (Suc k)
  let ?a = "n div 10 mod 10^k"
  let ?b = "m div 10 mod 10^k"
  let ?d = "n mod 10"
  let ?e = "m mod 10"
  have same: "10 * ?a + ?d = 10 * ?b + ?e"
    using Suc.prems by (simp only: power_Suc mod_mult2_eq)
  have digits: "?d = ?e"
  proof -
    have "(10 * ?a + ?d) mod 10 = (10 * ?b + ?e) mod 10"
      by (rule arg_cong[OF same])
    then show ?thesis by (simp only: mod_mult_self4 mod_mod_trivial)
  qed
  have quotients: "?a = ?b"
  proof -
    have "(10 * ?a + ?d) div 10 = (10 * ?b + ?e) div 10"
      by (rule arg_cong[OF same])
    then show ?thesis
      by (simp add: mult.commute[of "10::nat"])
  qed
  have prefixes:
    "five_reflected_E (n div 10) mod 10^k =
      five_reflected_E (m div 10) mod 10^k"
    by (rule Suc.IH[OF quotients])
  have scaled:
    "(10 * five_reflected_E (n div 10)) mod (10 * 10^k) =
      (10 * five_reflected_E (m div 10)) mod (10 * 10^k)"
    by (simp only: mod_mult_mult1 prefixes)
  have units:
    "((?d + 99 * (?d mod 2)) div 2) mod (10 * 10^k) =
      ((?e + 99 * (?e mod 2)) div 2) mod (10 * 10^k)"
    by (simp only: digits)
  show ?case
    unfolding power_Suc five_reflected_E_digit_equation[of n]
      five_reflected_E_digit_equation[of m]
    by (rule mod_add_cong[OF scaled units])
qed

lemma five_reflected_H_mod_power_ten_cong:
  assumes "n mod 10^k = m mod 10^k"
  shows "five_reflected_H n mod 10^k = five_reflected_H m mod 10^k"
proof -
  have "(5 * n) mod 10^k = (5 * m) mod 10^k"
    by (rule mod_mult_cong) (rule refl, rule assms)
  then show ?thesis
    unfolding five_reflected_H_def
    by (rule five_reflected_E_mod_power_ten_cong)
qed

lemma five_reflected_H_iter_mod_power_ten_cong:
  assumes "n mod 10^k = m mod 10^k"
  shows "five_reflected_H_iter t n mod 10^k =
    five_reflected_H_iter t m mod 10^k"
proof (induction t)
  case 0
  show ?case using assms by (simp only: five_reflected_H_iter.simps)
next
  case (Suc t)
  show ?case
    unfolding five_reflected_H_iter.simps
    by (rule five_reflected_H_mod_power_ten_cong[OF Suc.IH])
qed

theorem five_reflected_H_iter_truncated_source:
  "five_reflected_H_iter t (n mod 10^k) mod 10^k =
    five_reflected_H_iter t n mod 10^k"
  by (rule five_reflected_H_iter_mod_power_ten_cong) simp

lemma five_reflected_H_mod_ten:
  "five_reflected_H n mod 10 = (5 * n mod 10) div 2"
  unfolding five_reflected_H_def
  by (rule five_reflected_E_mod_ten)

lemma five_reflected_H_iter_one_mod_ten:
  "five_reflected_H n mod 10 = 0 \<or> five_reflected_H n mod 10 = 2"
proof -
  have scaled: "(5 * n) mod (5 * 2) = 5 * (n mod 2)"
    by (rule mod_mult_mult1)
  have source: "(5 * n) mod 10 = 5 * (n mod 2)"
    using scaled by simp
  have phase: "n mod 2 = 0 \<or> n mod 2 = 1"
  proof -
    have bound: "n mod 2 < 2" by simp
    show ?thesis using bound by arith
  qed
  show ?thesis
    using five_reflected_H_mod_ten[of n] source phase by auto
qed

lemma five_reflected_H_squared_mod_ten:
  "five_reflected_H_iter 2 n mod 10 = 0"
proof -
  have one: "five_reflected_H n mod 10 = 0 \<or> five_reflected_H n mod 10 = 2"
    by (rule five_reflected_H_iter_one_mod_ten)
  have second:
    "five_reflected_H (five_reflected_H n) mod 10 =
      (5 * five_reflected_H n mod 10) div 2"
    by (rule five_reflected_H_mod_ten)
  have reduced:
    "(5 * five_reflected_H n) mod 10 =
      (5 * (five_reflected_H n mod 10)) mod 10"
    by (rule mod_mult_right_eq[symmetric])
  have two: "(2::nat) = Suc (Suc 0)" by simp
  show ?thesis
    unfolding two five_reflected_H_iter.simps
    using one second reduced by auto
qed

lemma five_reflected_H_iter_even_precision:
  "five_reflected_H_iter (2*k) n mod 10^k = 0"
proof (induction k arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have previous: "five_reflected_H_iter (2*k) n mod 10^k = 0"
    by (rule Suc.IH)
  obtain q where q:
    "five_reflected_H_iter (2*k) n = 10^k * q"
    using previous by (metis mod_eq_0_iff_dvd dvd_def)
  have shift:
    "five_reflected_H_iter 2 (10^k * q) =
      10^k * five_reflected_H_iter 2 q"
    by (rule five_reflected_H_iter_power_ten)
  have square: "five_reflected_H_iter 2 q mod 10 = 0"
    by (rule five_reflected_H_squared_mod_ten)
  obtain r where r: "five_reflected_H_iter 2 q = 10 * r"
    using square by (metis dvd_def mod_eq_0_iff_dvd mult.commute)
  have iterate:
    "five_reflected_H_iter (2 * Suc k) n =
      five_reflected_H_iter 2 (five_reflected_H_iter (2*k) n)"
  proof -
    have count: "2 * Suc k = Suc (Suc (2*k))" by simp
    have two: "(2::nat) = Suc (Suc 0)" by simp
    have right: "five_reflected_H_iter 2 (five_reflected_H_iter (2*k) n) =
      five_reflected_H (five_reflected_H (five_reflected_H_iter (2*k) n))"
      by (simp only: two five_reflected_H_iter.simps)
    show ?thesis by (simp only: count right five_reflected_H_iter.simps)
  qed
  show ?case
    using q shift square iterate
    using r by (simp add: power_Suc algebra_simps)
qed

theorem five_reflected_H_iter_cutoff:
  assumes "2*k \<le> t"
  shows "five_reflected_H_iter t n mod 10^k = 0"
proof -
  have base: "five_reflected_H_iter (2*k) n mod 10^k = 0"
    by (rule five_reflected_H_iter_even_precision)
  have zero: "five_reflected_H 0 = 0"
    by (simp add: five_reflected_H_def five_reflected_E_def)
  have extra: "five_reflected_H_iter (2*k + r) n mod 10^k = 0" for r
  proof (induction r)
    case 0
    then show ?case using base by simp
  next
    case (Suc r)
    have congruent:
      "five_reflected_H_iter (2*k + r) n mod 10^k = 0 mod 10^k"
      using Suc.IH by simp
    have "five_reflected_H (five_reflected_H_iter (2*k + r) n) mod 10^k =
        five_reflected_H 0 mod 10^k"
      by (rule five_reflected_H_mod_power_ten_cong[OF congruent])
    then show ?case by (simp add: zero)
  qed
  have count: "2*k + (t - 2*k) = t"
    using assms by simp
  show ?thesis using extra[of "t - 2*k"] by (simp only: count)
qed

lemma five_reflected_H_moving_cut:
  assumes cut: "five_reflected_H_iter t n mod 10^v = 0"
  shows "(five_reflected_H_iter t (n mod 10^(v+k)) mod 10^(v+k)) div 10^v =
    (five_reflected_H_iter t n div 10^v) mod 10^k"
proof -
  let ?h = "five_reflected_H_iter t n"
  have factor: "(10::nat)^(v+k) = 10^v * 10^k"
    by (rule power_add)
  have residue: "?h mod 10^(v+k) = 10^v * (?h div 10^v mod 10^k)"
    unfolding factor mod_mult2_eq cut by simp
  have truncated:
    "five_reflected_H_iter t (n mod 10^(v+k)) mod 10^(v+k) =
      ?h mod 10^(v+k)"
    by (rule five_reflected_H_iter_truncated_source)
  show ?thesis by (simp only: truncated residue; simp)
qed

lemma five_fixed_reverse_bound:
  "five_fixed_reverse w n < (10::nat)^w"
proof (induction w arbitrary: n)
  case 0
  show ?case by simp
next
  case (Suc w)
  have digit: "n mod 10 < 10" by simp
  have tail: "five_fixed_reverse w (n div 10) < (10::nat)^w"
    by (rule Suc.IH)
  have scaled: "(n mod 10) * 10^w \<le> 9 * (10::nat)^w"
    by (rule mult_right_mono) (use digit in arith, simp)
  show ?case
    using scaled tail by (simp only: five_fixed_reverse.simps power_Suc; linarith)
qed

lemma five_fixed_reverse_high_digit:
  assumes bound: "b < (10::nat)^w" and digit: "a < 10"
  shows "five_fixed_reverse (Suc w) (a * 10^w + b) =
    10 * five_fixed_reverse w b + a"
  using bound
proof (induction w arbitrary: b)
  case 0
  then have "b = 0" by simp
  then show ?case using digit by simp
next
  case (Suc w)
  have bound': "b div 10 < (10::nat)^w"
    using Suc.prems
    by (simp add: div_less_iff_less_mult power_Suc mult.commute)
  have factor: "a * 10 ^ Suc w = 10 * (a * 10^w)"
    by (simp add: power_Suc algebra_simps)
  have quotient: "(a * 10 ^ Suc w + b) div 10 = a * 10^w + b div 10"
    unfolding factor by simp
  have remainder: "(a * 10 ^ Suc w + b) mod 10 = b mod 10"
    unfolding factor by simp
  have smaller:
    "five_fixed_reverse (Suc w) (a * 10^w + b div 10) =
      10 * five_fixed_reverse w (b div 10) + a"
    by (rule Suc.IH[OF bound'])
  have initial:
    "five_fixed_reverse (Suc (Suc w)) (a * 10 ^ Suc w + b) =
      ((a * 10 ^ Suc w + b) mod 10) * 10 ^ Suc w +
        five_fixed_reverse (Suc w) ((a * 10 ^ Suc w + b) div 10)"
    by (rule five_fixed_reverse.simps)
  have reduced:
    "((a * 10 ^ Suc w + b) mod 10) * 10 ^ Suc w +
        five_fixed_reverse (Suc w) ((a * 10 ^ Suc w + b) div 10) =
      (b mod 10) * 10 ^ Suc w +
        five_fixed_reverse (Suc w) (a * 10^w + b div 10)"
    by (simp only: quotient remainder)
  have transported:
    "(b mod 10) * 10 ^ Suc w +
        five_fixed_reverse (Suc w) (a * 10^w + b div 10) =
      (b mod 10) * 10 ^ Suc w +
        (10 * five_fixed_reverse w (b div 10) + a)"
    by (rule arg_cong[where f="\<lambda>v. (b mod 10) * 10 ^ Suc w + v"]) (rule smaller)
  have rearranged:
    "(b mod 10) * 10 ^ Suc w + (10 * five_fixed_reverse w (b div 10) + a) =
      10 * five_fixed_reverse (Suc w) b + a"
    by (simp only: five_fixed_reverse.simps power_Suc algebra_simps)
  show ?case by (rule trans[OF initial trans[OF reduced trans[OF transported rearranged]]])
qed

lemma five_reflected_high_digit_split:
  fixes d a :: nat
  assumes "d < 10" "a < 5"
  shows "(5*d+a) mod 10 = 5*(d mod 2)+a"
    and "(5*d+a) div 10 = d div 2"
proof -
  have ds: "d=0 \<or> d=1 \<or> d=2 \<or> d=3 \<or> d=4 \<or> d=5 \<or> d=6 \<or> d=7 \<or> d=8 \<or> d=9"
    using assms by arith
  have as_: "a=0 \<or> a=1 \<or> a=2 \<or> a=3 \<or> a=4"
    using assms by arith
  show "(5*d+a) mod 10 = 5*(d mod 2)+a"
    using ds as_ by (elim disjE; simp)
  show "(5*d+a) div 10 = d div 2"
    using ds as_ by (elim disjE; simp)
qed

lemma five_fixed_reverse_reflected_product:
  assumes bound: "x < (10::nat)^w" and carry: "c < 5"
  shows "five_fixed_reverse (Suc w) (5 * five_fixed_reverse w x + c) =
    five_reflected_E x + c * 10^w"
  using bound
proof (induction w arbitrary: x)
  case 0
  then have "x = 0" by simp
  then show ?case using carry
    by (simp add: five_reflected_E_def five_parity_mask.simps)
next
  case (Suc w)
  let ?q = "x div 10"
  let ?d = "x mod 10"
  let ?z = "5 * five_fixed_reverse w ?q + c"
  let ?a = "?z div 10^w"
  let ?b = "?z mod 10^w"
  have q_bound: "?q < (10::nat)^w"
    using Suc.prems
    by (simp add: div_less_iff_less_mult power_Suc mult.commute)
  have digit: "?d < 10" by simp
  have rb: "five_fixed_reverse w ?q < (10::nat)^w"
    by (rule five_fixed_reverse_bound)
  have z_bound: "?z < 5 * 10^w" using rb carry by linarith
  have power_positive: "(0::nat) < 10^w" by simp
  have a_bound: "?a < 5"
    using z_bound power_positive by (simp add: div_less_iff_less_mult)
  have b_bound: "?b < (10::nat)^w" by simp
  have z_split: "?z = ?a * 10^w + ?b"
    using div_mult_mod_eq[of ?z "10^w"] by (simp add: mult.commute)
  have p_bound: "5 * ?d + ?a < 100" using digit a_bound by linarith
  have product:
    "5 * five_fixed_reverse (Suc w) x + c = (5*?d+?a)*10^w+?b"
    using z_split by (simp only: five_fixed_reverse.simps; simp add: algebra_simps; linarith)
  have reverse_split:
    "five_fixed_reverse (Suc w) ?z = five_fixed_reverse (Suc w) (?a * 10^w + ?b)"
    by (rule arg_cong[OF z_split])
  have reverse_high:
    "five_fixed_reverse (Suc w) (?a * 10^w + ?b) = 10 * five_fixed_reverse w ?b + ?a"
    by (rule five_fixed_reverse_high_digit[OF b_bound]) (use a_bound in simp)
  have b_reversal:
    "five_fixed_reverse (Suc w) ?z = 10 * five_fixed_reverse w ?b + ?a"
    by (rule trans[OF reverse_split reverse_high])
  have induction:
    "five_fixed_reverse (Suc w) ?z = five_reflected_E ?q + c * 10^w"
    by (rule Suc.IH[OF q_bound])
  have raw_reflected:
    "five_reflected_E x = 10 * five_reflected_E ?q + (?d+99*(?d mod 2)) div 2"
    by (rule five_reflected_E_digit_equation)
  have digit_cases: "?d=0 \<or> ?d=1 \<or> ?d=2 \<or> ?d=3 \<or> ?d=4 \<or> ?d=5 \<or> ?d=6 \<or> ?d=7 \<or> ?d=8 \<or> ?d=9"
    using digit by arith
  have reflected:
    "five_reflected_E x = 10 * five_reflected_E ?q + ?d div 2 + 50*(?d mod 2)"
    using digit_cases raw_reflected by (elim disjE; simp)
  have split1: "(5*?d+?a) mod 10 = 5*(?d mod 2)+?a"
    and split2: "(5*?d+?a) div 10 = ?d div 2"
    using five_reflected_high_digit_split[OF digit a_bound] by auto
  let ?p = "5*?d+?a"
  let ?mid = "(?p mod 10)*10^w+?b"
  have upper: "?p div 10 < 10" using p_bound by simp
  have middle_bound: "?mid < (10::nat)^Suc w"
  proof -
    have digit_bound: "?p mod 10 < 10" by simp
    have scaled: "(?p mod 10) * 10^w \<le> 9 * (10::nat)^w"
      by (rule mult_right_mono) (use digit_bound in arith, simp)
    show ?thesis using scaled b_bound by (simp only: power_Suc; linarith)
  qed
  have p_split: "?p = 10 * (?p div 10) + ?p mod 10"
    using div_mult_mod_eq[of ?p 10] by (simp add: mult.commute)
  have decomp:
    "?p * 10^w + ?b = (?p div 10) * 10^Suc w + ?mid"
  proof -
    have "?p * 10^w + ?b = (10 * (?p div 10) + ?p mod 10) * 10^w + ?b"
      by (rule arg_cong[where f="\<lambda>v. v*10^w+?b"]) (rule p_split)
    also have "... = (?p div 10) * 10^Suc w + ?mid"
      by (simp only: power_Suc algebra_simps)
    finally show ?thesis .
  qed
  have high:
    "five_fixed_reverse (Suc (Suc w)) ((?p div 10) * 10^Suc w + ?mid) =
      10 * five_fixed_reverse (Suc w) ?mid + ?p div 10"
    by (rule five_fixed_reverse_high_digit[OF middle_bound upper])
  have middle:
    "five_fixed_reverse (Suc w) ?mid =
      10 * five_fixed_reverse w ?b + ?p mod 10"
    by (rule five_fixed_reverse_high_digit[OF b_bound]) simp
  have decomposition_lift:
    "five_fixed_reverse (Suc (Suc w)) (?p*10^w+?b) =
      five_fixed_reverse (Suc (Suc w)) ((?p div 10) * 10^Suc w + ?mid)"
    by (rule arg_cong[OF decomp])
  have middle_lift:
    "10 * five_fixed_reverse (Suc w) ?mid + ?p div 10 =
      10 * (10 * five_fixed_reverse w ?b + ?p mod 10) + ?p div 10"
    by (rule arg_cong[where f="\<lambda>v. 10*v + ?p div 10"]) (rule middle)
  have split_lift:
    "10 * (10 * five_fixed_reverse w ?b + ?p mod 10) + ?p div 10 =
      10 * (10 * five_fixed_reverse w ?b + (5*(?d mod 2)+?a)) + ?d div 2"
    by (simp only: split1 split2)
  have rearranged:
    "10 * (10 * five_fixed_reverse w ?b + (5*(?d mod 2)+?a)) + ?d div 2 =
      10 * (10 * five_fixed_reverse w ?b + ?a) +
        50*(?d mod 2)+?d div 2"
    by (simp only: algebra_simps)
  have append2:
    "five_fixed_reverse (Suc (Suc w)) (?p*10^w+?b) =
      10 * (10 * five_fixed_reverse w ?b + ?a) +
        50*(?d mod 2)+?d div 2"
    by (rule trans[OF decomposition_lift trans[OF high trans[OF middle_lift trans[OF split_lift rearranged]]]])
  have continuation:
    "10 * five_fixed_reverse w ?b + ?a = five_reflected_E ?q + c * 10^w"
    by (rule trans[OF b_reversal[symmetric] induction])
  have source_transport:
    "five_fixed_reverse (Suc (Suc w)) (5 * five_fixed_reverse (Suc w) x + c) =
      five_fixed_reverse (Suc (Suc w)) (?p*10^w+?b)"
    by (rule arg_cong[OF product])
  have final_arithmetic:
    "10 * (10 * five_fixed_reverse w ?b + ?a) + 50*(?d mod 2)+?d div 2 =
      five_reflected_E x + c * 10^Suc w"
    using continuation reflected by (simp only: power_Suc algebra_simps; linarith)
  show ?case by (rule trans[OF source_transport trans[OF append2 final_arithmetic]])
qed

lemma decimal_source_below_digit_power:
  "n < (10::nat)^decimal_digit_count n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    then show ?thesis by (simp add: decimal_digit_count.simps)
  next
    case False
    have smaller: "n div 10 < n" using False by simp
    have ih: "n div 10 < (10::nat)^decimal_digit_count (n div 10)"
      by (rule less.IH[OF smaller])
    have digit: "n mod 10 < 10" by simp
    have decomposition: "n = 10*(n div 10)+n mod 10"
      using div_mult_mod_eq[of n 10] by (simp add: mult.commute)
    have count: "decimal_digit_count n = Suc (decimal_digit_count (n div 10))"
      using False by (simp add: decimal_digit_count.simps)
    show ?thesis using ih digit decomposition
      by (simp only: count power_Suc; linarith)
  qed
qed

lemma five_reflected_normalize_times_ten:
  "five_reflected_normalize (10*n) = five_reflected_normalize n"
proof (cases "n = 0")
  case True
  then show ?thesis by (simp add: five_reflected_normalize.simps)
next
  case False
  then show ?thesis by (subst five_reflected_normalize.simps) simp
qed

lemma five_reflected_normalize_times_power:
  "five_reflected_normalize (10^z*n) = five_reflected_normalize n"
  by (induction z) (simp_all add: power_Suc five_reflected_normalize_times_ten mult.assoc)

lemma five_decimal_reverse_units_nonzero:
  assumes "n > 0"
  shows "decimal_reverse n mod 10 \<noteq> 0"
  using assms
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    then show ?thesis using less.prems by (simp add: decimal_reverse.simps)
  next
    case False
    have q_pos: "n div 10 > 0" using False by simp
    have smaller: "n div 10 < n" using False by simp
    have ih: "decimal_reverse (n div 10) mod 10 \<noteq> 0"
      by (rule less.IH[OF smaller q_pos])
    have count: "decimal_digit_count n = Suc (decimal_digit_count (n div 10))"
      using False by (simp add: decimal_digit_count.simps)
    have count_pos: "decimal_digit_count (n div 10) > 0"
      by (rule decimal_digit_count_positive)
    then obtain k where power: "decimal_digit_count (n div 10) = Suc k"
      by (cases "decimal_digit_count (n div 10)") auto
    have reverse: "decimal_reverse n = n mod 10 * 10 ^ decimal_digit_count (n div 10) + decimal_reverse (n div 10)"
      using False count by (simp add: decimal_reverse.simps)
    have residue: "decimal_reverse n mod 10 =
      (n mod 10 * 10 ^ decimal_digit_count (n div 10) +
        decimal_reverse (n div 10)) mod 10"
      by (rule arg_cong[OF reverse])
    have multiple:
      "n mod 10 * 10 ^ decimal_digit_count (n div 10) =
        10 * ((n mod 10) * 10^k)"
      by (simp only: power power_Suc; simp add: algebra_simps)
    have strip:
      "(n mod 10 * 10 ^ decimal_digit_count (n div 10) +
        decimal_reverse (n div 10)) mod 10 =
        decimal_reverse (n div 10) mod 10"
      by (simp only: multiple mod_mult_self4)
    have reduced: "decimal_reverse n mod 10 = decimal_reverse (n div 10) mod 10"
      by (rule trans[OF residue strip])
    show ?thesis using reduced ih by simp
  qed
qed

lemma five_reflected_normalize_decimal_reverse:
  "five_reflected_normalize (decimal_reverse n) = decimal_reverse n"
proof (cases "n = 0")
  case True
  then show ?thesis by (simp add: five_reflected_normalize.simps decimal_reverse.simps)
next
  case False
  then have "decimal_reverse n mod 10 \<noteq> 0"
    by (intro five_decimal_reverse_units_nonzero) simp
  then show ?thesis by (subst five_reflected_normalize.simps) simp
qed

lemma five_fixed_reverse_padding:
  assumes bound: "n < (10::nat)^w"
  shows "five_fixed_reverse (w+z) n = 10^z * five_fixed_reverse w n"
  using bound
proof (induction z)
  case 0
  show ?case by simp
next
  case (Suc z)
  have powers: "(10::nat)^w \<le> 10^(w+z)"
    by simp
  have padded_bound: "n < (10::nat)^(w+z)"
    using Suc.prems powers by arith
  have step: "five_fixed_reverse (Suc (w+z)) n = 10 * five_fixed_reverse (w+z) n"
    using five_fixed_reverse_high_digit[OF padded_bound, of 0] by simp
  show ?case using step Suc.IH[OF Suc.prems] by (simp add: power_Suc mult.assoc)
qed

lemma five_normalize_fixed_reverse:
  assumes bound: "n < (10::nat)^w"
  shows "five_reflected_normalize (five_fixed_reverse w n) = decimal_reverse n"
proof (cases "n = 0")
  case True
  then show ?thesis by (induction w) (simp_all add: five_reflected_normalize.simps decimal_reverse.simps)
next
  case False
  have digit_bound: "n < (10::nat)^decimal_digit_count n"
    by (rule decimal_source_below_digit_power)
  have lower: "10 ^ (decimal_digit_count n - 1) \<le> n"
    by (rule ten_power_digit_count_predecessor_le) (use False in simp)
  have pos: "0 < decimal_digit_count n"
    by (rule decimal_digit_count_positive)
  have minimum: "decimal_digit_count n \<le> w"
  proof (rule ccontr)
    assume "\<not> decimal_digit_count n \<le> w"
    then have exp: "w \<le> decimal_digit_count n - 1" using pos by arith
    have "(10::nat)^w \<le> 10 ^ (decimal_digit_count n - 1)"
      by (rule power_increasing) (use exp in simp_all)
    with lower bound show False by arith
  qed
  obtain z where width: "w = decimal_digit_count n + z"
    using minimum by (auto simp: le_iff_add)
  show ?thesis
    unfolding width five_fixed_reverse_padding[OF digit_bound] five_fixed_reverse_decimal
    by (simp only: five_reflected_normalize_times_power five_reflected_normalize_decimal_reverse)
qed

theorem five_reflected_physical_two_step:
  "five_reverse_step (five_reverse_step x) =
    5 * five_reflected_normalize (five_reflected_E x)"
proof -
  let ?w = "decimal_digit_count x"
  have source_bound: "x < (10::nat)^?w" by (rule decimal_source_below_digit_power)
  have reversed_bound: "5 * five_fixed_reverse ?w x < (10::nat)^Suc ?w"
    using five_fixed_reverse_bound[of ?w x] by (simp add: power_Suc; linarith)
  have zero_carry: "(0::nat) < 5" by simp
  have product: "five_fixed_reverse (Suc ?w) (5 * five_fixed_reverse ?w x) = five_reflected_E x"
    using five_fixed_reverse_reflected_product[OF source_bound zero_carry]
    by (simp only: mult_zero_left Nat.add_0_right)
  show ?thesis
    unfolding five_reverse_step_def
    using five_normalize_fixed_reverse[OF reversed_bound] product five_fixed_reverse_decimal
    by simp
qed

lemma five_reflected_normalize_factor:
  "\<exists>z. n = (10::nat)^z * five_reflected_normalize n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n = 0 \<or> n mod 10 \<noteq> 0")
    case True
    then have normalized: "five_reflected_normalize n = n"
      by (subst five_reflected_normalize.simps) simp
    show ?thesis using normalized by (intro exI[of _ 0]) simp
  next
    case False
    then have nonzero: "n \<noteq> 0" and divisible: "n mod 10 = 0" by auto
    have smaller: "n div 10 < n" using nonzero by simp
    obtain z where factor:
      "n div 10 = (10::nat)^z * five_reflected_normalize (n div 10)"
      using less.IH[OF smaller] by blast
    have quotient: "n = 10 * (n div 10)"
      using div_mult_mod_eq[of n 10] divisible by (simp add: mult.commute)
    have normalized: "five_reflected_normalize n = five_reflected_normalize (n div 10)"
      using False by (subst five_reflected_normalize.simps) simp
    have scaled:
      "10 * (n div 10) = 10 * ((10::nat)^z * five_reflected_normalize (n div 10))"
      by (rule arg_cong[OF factor])
    have "n = 10 * ((10::nat)^z * five_reflected_normalize (n div 10))"
      by (rule trans[OF quotient scaled])
    also have "... = (10::nat)^Suc z * five_reflected_normalize (n div 10)"
      by (simp only: power_Suc mult.assoc)
    also have "... = (10::nat)^Suc z * five_reflected_normalize n"
      by (rule arg_cong[OF normalized[symmetric]])
    finally have "n = (10::nat)^Suc z * five_reflected_normalize n" .
    then show ?thesis by blast
  qed
qed

lemma five_reflected_normalize_idempotent:
  "five_reflected_normalize (five_reflected_normalize n) = five_reflected_normalize n"
proof -
  obtain z where "n = 10^z * five_reflected_normalize n"
    using five_reflected_normalize_factor by blast
  then have "five_reflected_normalize n =
      five_reflected_normalize (10^z * five_reflected_normalize n)"
    by (rule arg_cong)
  then show ?thesis by (simp only: five_reflected_normalize_times_power)
qed

lemma five_reflected_H_normalize_commute:
  "five_reflected_normalize (five_reflected_H (five_reflected_normalize n)) =
    five_reflected_normalize (five_reflected_H n)"
proof -
  obtain z where factor: "n = 10^z * five_reflected_normalize n"
    using five_reflected_normalize_factor by blast
  have transported: "five_reflected_H n =
      five_reflected_H (10^z * five_reflected_normalize n)"
    by (rule arg_cong[OF factor])
  have scaled: "five_reflected_H n = 10^z * five_reflected_H (five_reflected_normalize n)"
    using transported by (simp only: five_reflected_H_power_ten)
  show ?thesis
    using arg_cong[OF scaled, where f=five_reflected_normalize]
    by (simp only: five_reflected_normalize_times_power)
qed

lemma five_reflected_physical_pair_on_normalized:
  "five_reverse_step (five_reverse_step (5 * five_reflected_normalize n)) =
    5 * five_reflected_normalize (five_reflected_H n)"
  by (simp only: five_reflected_physical_two_step five_reflected_H_def[symmetric]
      five_reflected_H_normalize_commute)

lemma five_reverse_orbit_two_more:
  "five_reverse_orbit (Suc (Suc k)) seed =
    five_reverse_step (five_reverse_step (five_reverse_orbit k seed))"
  by simp

lemma five_reflected_orbit_from_anchor:
  assumes anchor: "five_reverse_orbit i seed = 5 * five_reflected_normalize source"
  shows "five_reverse_orbit (2*t+i) seed =
    5 * five_reflected_normalize (five_reflected_H_iter t source)"
proof (induction t)
  case 0
  show ?case using anchor
    by (simp only: mult_zero_right add_0_left five_reflected_H_iter.simps)
next
  case (Suc t)
  have count: "2 * Suc t + i = Suc (Suc (2*t+i))" by simp
  have physical:
    "five_reverse_orbit (2 * Suc t + i) seed =
      five_reverse_step (five_reverse_step (five_reverse_orbit (2*t+i) seed))"
    using five_reverse_orbit_two_more[of "2*t+i" seed]
    by (simp only: count)
  have transported:
    "five_reverse_step (five_reverse_step (five_reverse_orbit (2*t+i) seed)) =
      five_reverse_step (five_reverse_step
        (5 * five_reflected_normalize (five_reflected_H_iter t source)))"
    by (rule arg_cong[OF Suc.IH])
  have pair:
    "five_reverse_step (five_reverse_step
        (5 * five_reflected_normalize (five_reflected_H_iter t source))) =
      5 * five_reflected_normalize (five_reflected_H (five_reflected_H_iter t source))"
    by (rule five_reflected_physical_pair_on_normalized)
  show ?case
    using trans[OF physical trans[OF transported pair]]
    by (simp only: five_reflected_H_iter.simps)
qed

theorem five_reflected_orbit_even:
  "five_reverse_orbit (2*t+2) seed =
    5 * five_reflected_normalize (five_reflected_H_iter t (five_reflected_E seed))"
proof -
  have physical: "five_reverse_orbit 2 seed = five_reverse_step (five_reverse_step seed)"
    by (simp only: numeral_2_eq_2 five_reverse_orbit.simps)
  have anchor: "five_reverse_orbit 2 seed = 5 * five_reflected_normalize (five_reflected_E seed)"
    by (rule trans[OF physical five_reflected_physical_two_step])
  show ?thesis by (rule five_reflected_orbit_from_anchor[OF anchor, where t=t])
qed

theorem five_reflected_orbit_odd:
  "five_reverse_orbit (2*t+1) seed =
    5 * five_reflected_normalize (five_reflected_H_iter t (decimal_reverse seed))"
proof -
  have anchor: "five_reverse_orbit 1 seed = 5 * five_reflected_normalize (decimal_reverse seed)"
    by (simp only: One_nat_def five_reverse_orbit.simps five_reverse_step_def
        five_reflected_normalize_decimal_reverse)
  show ?thesis by (rule five_reflected_orbit_from_anchor[OF anchor, where t=t])
qed

ML \<open>
  val checked = @{thms five_fixed_reverse_decimal
    five_reflected_physical_two_step
    five_reflected_orbit_from_anchor five_reflected_orbit_even five_reflected_orbit_odd
    five_reflected_E_digit_equation five_reflected_H_power_ten
    five_reflected_H_iter_truncated_source five_reflected_H_iter_cutoff
    five_reflected_H_moving_cut};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Five-reverse reflected H power depends on an oracle, including skip_proof";
\<close>

end
