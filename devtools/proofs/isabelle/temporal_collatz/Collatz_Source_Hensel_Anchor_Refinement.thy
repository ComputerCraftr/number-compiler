theory Collatz_Source_Hensel_Anchor_Refinement
  imports Collatz_Cylinder_Constructor
begin

text \<open>The runtime source publisher accepts a positive odd source and its
transition cache computes the exact split
\<open>3*x+1 = 2^E*y\<close>.  This theory uses that source-derived recurrence to
discharge both nonconstructive premises of the generic odd affine cylinder
pullback: multiplication by three is invertible modulo every demanded power
of two, and the current source is the required pullback anchor.\<close>

lemma three_invertible_on_dyadic_divisibility:
  fixes z :: int
  shows "(2::int)^precision dvd 3*z \<longleftrightarrow>
    (2::int)^precision dvd z"
proof -
  have coprime: "coprime ((2::int)^precision) 3" by simp
  show ?thesis by (rule coprime_dvd_mult_right_iff[OF coprime])
qed

lemma collatz_source_split_is_hensel_anchor:
  fixes x :: nat
  shows "(2::int)^(q + collatz_source_valuation x) dvd
    3 * int x + 1 -
      (2::int)^(collatz_source_valuation x) *
        int (collatz_accelerated_target x)"
proof -
  have exact:
      "3 * int x + 1 =
        (2::int)^(collatz_source_valuation x) *
          int (collatz_accelerated_target x)"
    by (rule collatz_source_split_int)
  show ?thesis using exact by simp
qed

theorem collatz_source_pullback_is_anchored_cylinder:
  fixes x :: nat
  shows "cylinder_pullback 3 1 (collatz_source_valuation x) q
      (int (collatz_accelerated_target x)) =
    cylinder (q + collatz_source_valuation x) (int x)"
proof -
  let ?E = "collatz_source_valuation x"
  let ?target = "collatz_accelerated_target x"
  let ?M = "(2::int)^(q + ?E)"
  have inverse: "\<And>z::int. ?M dvd 3*z \<longleftrightarrow> ?M dvd z"
    by (rule three_invertible_on_dyadic_divisibility)
  have anchor:
      "?M dvd 3 * int x + 1 - (2::int)^?E * int ?target"
    by (rule collatz_source_split_is_hensel_anchor)
  show ?thesis
    by (rule odd_inverse_cylinder_pullback[
          where a=3 and b=1 and rho="int x"
            and r="int ?target" and q=q and E="?E"])
      (use inverse anchor in simp_all)
qed

corollary collatz_publisher_source_step_hensel_bundle:
  fixes x :: nat
  assumes source: "odd x"
  shows "0 < collatz_source_valuation x"
    "odd (collatz_accelerated_target x)"
    "cylinder_pullback 3 1 (collatz_source_valuation x) q
        (int (collatz_accelerated_target x)) =
      cylinder (q + collatz_source_valuation x) (int x)"
  using odd_source_has_positive_valuation[OF source]
    collatz_accelerated_target_odd[of x]
    collatz_source_pullback_is_anchored_cylinder[of x q]
  by blast+

text \<open>The bundle maps one accepted \<open>CollatzSourcePublisher\<close>
source and one \<open>CollatzAffineSuffixGerm.next_step\<close> transition to the
shared Hensel cylinder law.  The source recurrence supplies the valuation,
odd target and pullback anchor; no caller-provided valuation itinerary or
assumed-correct occurrence is used.

The theorem specifies arithmetic semantics.  It does not refine the Python
radix-four word traversal, transition cache identity, source publisher seals,
resource budgets, exception cleanup, or publication of event and physical
support roots.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms three_invertible_on_dyadic_divisibility
      collatz_source_split_is_hensel_anchor
      collatz_source_pullback_is_anchored_cylinder
      collatz_publisher_source_step_hensel_bundle}) then ()
    else error "Collatz source Hensel anchor refinement depends on an oracle";
\<close>

end
