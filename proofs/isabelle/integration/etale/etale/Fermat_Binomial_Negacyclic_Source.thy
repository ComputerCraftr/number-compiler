theory Fermat_Binomial_Negacyclic_Source
  imports Main
begin

text \<open>
The exact binomial expansion of 3^k can be folded into signed base-2^w
lanes modulo 2^w+1.  This proves the mathematical source equation used by
the Fermat carry bridge.  It does not yet refine a streamed coefficient
generator to this finite sum; that implementation correspondence is a
separate obligation.
\<close>

definition fermat_alternating_binomial_fold :: "nat \<Rightarrow> nat \<Rightarrow> int" where
  "fermat_alternating_binomial_fold w k =
    (\<Sum>j\<in>{..k}. int (k choose j) * (-1)^(j div w) * (2::int)^(j mod w))"

lemma negacyclic_power_difference_dvd:
  fixes x :: int
  shows "x + 1 dvd x^q - (-1)^q"
proof (induction q)
  case 0
  then show ?case by simp
next
  case (Suc q)
  have step:
    "x ^ Suc q - (-1) ^ Suc q =
      x * (x^q - (-1)^q) + (x+1) * (-1)^q"
    by (simp add: power_Suc algebra_simps)
  have first: "x+1 dvd x * (x^q - (-1)^q)"
    using Suc.IH by (rule dvd_mult)
  have second: "x+1 dvd (x+1) * (-1)^q"
    by (rule dvd_mult2[OF dvd_refl])
  show ?case using first second by (simp only: step, rule dvd_add)
qed

lemma negacyclic_binomial_term:
  fixes w k j :: nat
  shows "((2::int)^w + 1) dvd
    (int (k choose j) * (2::int)^j -
      int (k choose j) * (-1)^(j div w) * (2::int)^(j mod w))"
proof -
  let ?x = "(2::int)^w"
  let ?q = "j div w"
  let ?r = "j mod w"
  let ?c = "int (k choose j)"
  have decomposition: "j = ?q * w + ?r"
    using div_mult_mod_eq[of j w] by (simp add: mult.commute)
  have power_split: "(2::int)^j = (2::int)^?r * ?x^?q"
  proof -
    have "(2::int)^j = (2::int)^(?q*w + ?r)"
      using decomposition by simp
    also have "... = (2::int)^(?q*w) * (2::int)^?r"
      by (simp only: power_add)
    also have "... = ?x^?q * (2::int)^?r"
      by (simp add: power_mult[symmetric] mult.commute)
    finally show ?thesis by (simp add: mult.commute)
  qed
  have base: "?x+1 dvd ?x^?q - (-1)^?q"
    by (rule negacyclic_power_difference_dvd)
  have radix_scaled: "?x+1 dvd (2::int)^?r * (?x^?q - (-1)^?q)"
    using base by (rule dvd_mult)
  have scaled: "?x+1 dvd ?c * ((2::int)^?r * (?x^?q - (-1)^?q))"
    using radix_scaled by (rule dvd_mult)
  have rearranged:
    "?c * ((2::int)^?r * (?x^?q - (-1)^?q)) =
      ?c * (2::int)^j - ?c * (-1)^?q * (2::int)^?r"
    using power_split by (simp add: algebra_simps)
  show ?thesis using scaled by (simp only: rearranged)
qed

theorem fermat_alternating_binomial_fold_divisibility:
  fixes w k :: nat
  shows "((2::int)^w + 1) dvd
    ((3::int)^k - fermat_alternating_binomial_fold w k)"
proof -
  let ?source_term = "\<lambda>j. int (k choose j) * (2::int)^j"
  let ?fold_term = "\<lambda>j. int (k choose j) * (-1)^(j div w) *
      (2::int)^(j mod w)"
  have terms:
    "((2::int)^w + 1) dvd (\<Sum>j\<in>{..k}. ?source_term j - ?fold_term j)"
  proof (rule dvd_sum)
    fix j
    assume jle: "j \<in> {..k}"
    show "((2::int)^w + 1) dvd (?source_term j - ?fold_term j)"
      by (rule negacyclic_binomial_term)
  qed
  have expansion: "(3::int)^k = (\<Sum>j\<le>k. ?source_term j)"
    using binomial_ring[of "(2::int)" "(1::int)" k] by simp
  have difference:
    "(\<Sum>j\<in>{..k}. ?source_term j - ?fold_term j) =
      (3::int)^k - fermat_alternating_binomial_fold w k"
    using expansion by (simp add: fermat_alternating_binomial_fold_def
      sum_subtractf)
  show ?thesis using terms by (simp only: difference)
qed

theorem fermat_alternating_binomial_fold_source:
  fixes w k :: nat
  obtains quotient :: int where
    "int ((3::nat)^k) = int ((2::nat)^w + 1) * quotient +
      fermat_alternating_binomial_fold w k"
proof -
  have divisibility:
    "((2::int)^w + 1) dvd
      (int ((3::nat)^k) - fermat_alternating_binomial_fold w k)"
    using fermat_alternating_binomial_fold_divisibility
    by simp
  then obtain quotient where
    equation:
      "int ((3::nat)^k) - fermat_alternating_binomial_fold w k =
        ((2::int)^w + 1) * quotient"
    unfolding dvd_def by blast
  have modulus:
    "int ((2::nat)^w + 1) = (2::int)^w + 1"
    by simp
  show thesis
    using that[of quotient] equation modulus by (simp add: algebra_simps)
qed

text \<open>The radial/unit pumping step is generic once the exact one-level
source split is supplied. This theorem formalizes that implication without
claiming that a finite streamed implementation constructs or authenticates
the split premise. In particular, it is not a terminal residue publisher.
\<close>

theorem fermat_integral_radial_unit_pump:
  fixes w h :: nat and unit_seed :: int
  assumes source_split:
    "(3::int)^w = (2::int)^w + 1 + 2 * unit_seed"
  shows "(3::int)^(w*h) mod ((2::int)^w + 1) =
    (2^h * unit_seed^h) mod ((2::int)^w + 1)"
proof -
  let ?F = "(2::int)^w + 1"
  have one_level:
    "((3::int)^w) mod ?F = (2 * unit_seed) mod ?F"
    using source_split by simp
  have powered:
    "((3::int)^w)^h mod ?F = (2 * unit_seed)^h mod ?F"
    using arg_cong[OF one_level, of "\<lambda>a. a^h mod ?F"]
    by (simp only: power_mod)
  have exponent:
    "(3::int)^(w*h) = ((3::int)^w)^h"
    by (simp add: power_mult)
  show ?thesis
    using powered exponent by (simp add: power_mult_distrib)
qed

lemma fermat_integral_radial_unit_small_control:
  "(3::int)^(2*3) mod 5 = (2^3 * (2::int)^3) mod 5"
  by (simp add: numeral_eq_Suc)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms negacyclic_power_difference_dvd
      negacyclic_binomial_term fermat_alternating_binomial_fold_divisibility
      fermat_alternating_binomial_fold_source
      fermat_integral_radial_unit_pump
      fermat_integral_radial_unit_small_control}) then ()
    else error "Fermat negacyclic binomial source depends on an oracle";
\<close>

end
