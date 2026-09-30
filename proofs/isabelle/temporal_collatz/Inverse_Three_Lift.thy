theory Inverse_Three_Lift
  imports Main "HOL.Groebner_Basis"
begin

text \<open>The stable six-bit Hensel clock lift, with its exceptional first
radix-64 lift kept separate. These are exact integer identities and congruences;
no Collatz valuation itinerary or source occurrence is inferred from them.\<close>

theorem three_clock_stable_lift_witness:
  "\<exists>w::int. (3::int)^((2::nat)^(n+5)) =
    1 - 3*(2::int)^(n+7) + (2::int)^(n+13)*w"
proof (induction n)
  case 0
  show ?case by (rule exI[of _ 226198753522]) simp
next
  case (Suc n)
  obtain w :: int where prior:
    "(3::int)^((2::nat)^(n+5)) =
      1 - 3*(2::int)^(n+7) + (2::int)^(n+13)*w"
    using Suc.IH by blast
  have exponent: "(2::nat)^(Suc n+5) = (2^(n+5))*2"
    by (simp add: power_add power_Suc mult.commute)
  have squared:
    "(3::int)^((2::nat)^(Suc n+5)) = ((3::int)^((2::nat)^(n+5)))^2"
    by (simp only: exponent power_mult)
  let ?next = "9*(2::int)^n + w*(1-3*(2::int)^(n+7)) +
    32*(2::int)^(n+7)*w^2"
  show ?case
    apply (rule exI[of _ ?next])
    unfolding squared prior
    by (simp only: power_add power_Suc; algebra)
qed

theorem three_clock_stable_lift:
  assumes "7 \<le> q"
  shows "(2::int)^(q+6) dvd
    ((3::int)^((2::nat)^(q-2)) - (1-3*(2::int)^q))"
proof -
  obtain n where q: "q = n+7" using assms by (metis le_iff_add add.commute)
  obtain w :: int where witness:
    "(3::int)^((2::nat)^(n+5)) =
      1-3*(2::int)^(n+7)+(2::int)^(n+13)*w"
    using three_clock_stable_lift_witness[of n] by blast
  have delta: "(3::int)^((2::nat)^(n+5)) -
      (1-3*(2::int)^(n+7)) = (2::int)^(n+13)*w"
    using witness by linarith
  have divides: "(2::int)^(n+13) dvd
      ((3::int)^((2::nat)^(n+5)) - (1-3*(2::int)^(n+7)))"
    by (simp only: delta; simp)
  show ?thesis using divides by (simp add: q add.assoc add.commute)
qed

theorem inverse_three_stable_lift_certificate:
  "(2::int)^(n+13) dvd
    ((3::int)^((2::nat)^(n+5)) * (1+3*(2::int)^(n+7)) - 1)"
proof -
  obtain w :: int where prior:
    "(3::int)^((2::nat)^(n+5)) =
      1-3*(2::int)^(n+7)+(2::int)^(n+13)*w"
    using three_clock_stable_lift_witness[of n] by blast
  let ?witness = "-18*(2::int)^n + w*(1+3*(2::int)^(n+7))"
  show ?thesis
    unfolding prior dvd_def
    apply (rule exI[of _ ?witness])
    by (simp only: power_add; algebra)
qed

lemma inverse_three_bootstrap_lift_certificate:
  "((3::int)^16 * (1+35*64)) mod 4096 = 1"
  by simp

lemma affine_phase_lift_second_difference:
  fixes root scale digit :: int
  shows "(root+scale*(digit+2)) - 2*(root+scale*(digit+1)) +
    (root+scale*digit) = 0"
  by algebra

text \<open>The stable inverse coefficient is 3, whereas the q=6 bootstrap
uses 35. In a root digit the effective slope multiplies this coefficient by
the low root residue; it is not a constant slope across all clock phases.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms three_clock_stable_lift_witness three_clock_stable_lift
      inverse_three_stable_lift_certificate inverse_three_bootstrap_lift_certificate
      affine_phase_lift_second_difference}) then ()
    else error "Inverse-three lift proof depends on an oracle";
\<close>
end
