theory Decimal_Repunit_Modular
  imports Main
begin

text \<open>Exact natural-number arithmetic for decimal repunits and contiguous
decimal intervals.  The modular theorem deliberately uses division by nine
after reduction modulo \<open>9 * m\<close>; it does not assume that nine is invertible
modulo \<open>m\<close>.\<close>

fun decimal_repunit :: "nat \<Rightarrow> nat" where
  "decimal_repunit 0 = 0"
| "decimal_repunit (Suc n) = 10 * decimal_repunit n + 1"

lemma decimal_repunit_recurrence:
  "decimal_repunit (Suc n) = 10 * decimal_repunit n + 1"
  by simp

lemma decimal_repunit_power_identity:
  "9 * decimal_repunit n + 1 = 10 ^ n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have "9 * decimal_repunit (Suc n) + 1 =
      10 * (9 * decimal_repunit n + 1)"
    by (simp add: algebra_simps)
  also have "... = 10 * 10 ^ n"
    using Suc.IH by simp
  also have "... = 10 ^ Suc n"
    by (simp add: power_Suc)
  finally show ?case .
qed

lemma decimal_repunit_closed_form:
  "decimal_repunit n = (10 ^ n - 1) div 9"
proof -
  have difference: "10 ^ n - 1 = 9 * decimal_repunit n"
    using decimal_repunit_power_identity[of n] by arith
  show ?thesis
    apply (subst difference)
    by simp
qed

theorem decimal_repunit_mod_reduced_power:
  fixes m n :: nat
  assumes modulus_positive: "0 < m"
  shows
    "((10 ^ n mod (9 * m) - 1) div 9) mod m =
      ((10 ^ n - 1) div 9) mod m"
proof -
  let ?r = "decimal_repunit n"
  have remainder_lt: "?r mod m < m"
    using modulus_positive by simp
  have scaled_remainder_lt: "9 * (?r mod m) + 1 < 9 * m"
    using remainder_lt by arith
  have source: "10 ^ n = 9 * ?r + 1"
    using decimal_repunit_power_identity[of n] by simp
  have quotient_remainder:
    "?r = (?r div m) * m + ?r mod m"
    using div_mult_mod_eq[of ?r m] by simp
  have source_decomposition:
    "10 ^ n = (9 * m) * (?r div m) + (9 * (?r mod m) + 1)"
  proof -
    have "10 ^ n = 9 * ?r + 1"
      by (rule source)
    also have "... = 9 * ((?r div m) * m + ?r mod m) + 1"
      by (subst quotient_remainder) (rule refl)
    also have "... =
        (9 * m) * (?r div m) + (9 * (?r mod m) + 1)"
      by (simp only: algebra_simps)
    finally show ?thesis .
  qed
  have reduced_power:
    "10 ^ n mod (9 * m) = 9 * (?r mod m) + 1"
  proof -
    have "10 ^ n mod (9 * m) =
        ((9 * m) * (?r div m) + (9 * (?r mod m) + 1)) mod (9 * m)"
      by (subst source_decomposition) (rule refl)
    also have "... = (9 * (?r mod m) + 1) mod (9 * m)"
      by (rule mod_mult_self4)
    also have "... = 9 * (?r mod m) + 1"
      by (rule mod_less[OF scaled_remainder_lt])
    finally show ?thesis .
  qed
  show ?thesis
    apply (subst decimal_repunit_closed_form[symmetric])
    apply (subst reduced_power)
    by simp
qed

definition decimal_interval_sum ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decimal_interval_sum width lower upper =
    (\<Sum>i = lower..upper. 10 ^ (width - Suc i))"

lemma decimal_interval_sum_offset:
  fixes width lower k :: nat
  assumes endpoint_inside: "lower + k < width"
  shows
    "(\<Sum>i = lower..lower + k. 10 ^ (width - Suc i)) =
      10 ^ (width - Suc (lower + k)) * decimal_repunit (Suc k)"
  using endpoint_inside
proof (induction k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have earlier_inside: "lower + k < width"
    using Suc.prems by arith
  have exponent_step:
    "width - Suc (lower + k) =
      Suc (width - Suc (lower + Suc k))"
    using Suc.prems by arith
  have interval_split:
    "(\<Sum>i = lower..lower + Suc k. 10 ^ (width - Suc i)) =
      (\<Sum>i = lower..lower + k. 10 ^ (width - Suc i)) +
        10 ^ (width - Suc (lower + Suc k))"
    by (simp add: atLeastAtMostSuc_conv add.commute)
  show ?case
  proof -
    note induction_step = Suc.IH[OF earlier_inside]
    have "(\<Sum>i = lower..lower + Suc k. 10 ^ (width - Suc i)) =
        (\<Sum>i = lower..lower + k. 10 ^ (width - Suc i)) +
          10 ^ (width - Suc (lower + Suc k))"
      by (rule interval_split)
    also have "... = 10 ^ (width - Suc (lower + k)) *
          decimal_repunit (Suc k) +
          10 ^ (width - Suc (lower + Suc k))"
      by (subst induction_step) (rule refl)
    also have "... = 10 ^ Suc (width - Suc (lower + Suc k)) *
          decimal_repunit (Suc k) +
          10 ^ (width - Suc (lower + Suc k))"
      by (subst exponent_step) (rule refl)
    also have "... = 10 ^ (width - Suc (lower + Suc k)) *
          decimal_repunit (Suc (Suc k))"
      by (simp only: power_Suc decimal_repunit.simps algebra_simps)
    finally show ?case .
  qed
qed

theorem decimal_interval_sum_geometric:
  fixes width lower upper :: nat
  assumes ordered: "lower \<le> upper"
    and inside: "upper < width"
  shows
    "decimal_interval_sum width lower upper =
      10 ^ (width - 1 - upper) *
        decimal_repunit (upper - lower + 1)"
proof -
  have endpoint: "lower + (upper - lower) = upper"
    using ordered by arith
  have endpoint_inside: "lower + (upper - lower) < width"
    using endpoint inside by simp
  have exponent: "width - Suc upper = width - 1 - upper"
    using inside by arith
  show ?thesis
  proof (rule trans)
    show "decimal_interval_sum width lower upper =
        10 ^ (width - Suc upper) *
          decimal_repunit (Suc (upper - lower))"
    proof -
      have interval:
        "(\<Sum>i = lower..lower + (upper - lower).
            10 ^ (width - Suc i)) =
          10 ^ (width - Suc (lower + (upper - lower))) *
            decimal_repunit (Suc (upper - lower))"
        by (rule decimal_interval_sum_offset[OF endpoint_inside])
      show ?thesis
        unfolding decimal_interval_sum_def
        using interval by (simp only: endpoint)
    qed
    show "10 ^ (width - Suc upper) *
          decimal_repunit (Suc (upper - lower)) =
        10 ^ (width - 1 - upper) *
          decimal_repunit (upper - lower + 1)"
      apply (subst exponent)
      apply (subst Suc_eq_plus1)
      by (rule refl)
  qed
qed

ML \<open>
  val checked = @{thms decimal_repunit_recurrence
    decimal_repunit_power_identity decimal_repunit_closed_form
    decimal_repunit_mod_reduced_power decimal_interval_sum_offset
    decimal_interval_sum_geometric};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Decimal repunit modular arithmetic depends on an oracle";
\<close>

end
