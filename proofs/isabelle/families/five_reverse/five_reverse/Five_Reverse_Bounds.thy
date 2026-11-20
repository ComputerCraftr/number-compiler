theory Five_Reverse_Bounds
  imports Five_Reverse
begin

text \<open>
The finite seed window uses a six-bit-per-step bound to preserve the exact
state budget while avoiding full integer materialization.  This theory proves
that bound directly from the decimal reversal recurrence; it does not assume
any of the finite window's endpoint values.
\<close>

lemma decimal_digit_count_positive:
  "0 < decimal_digit_count n"
  by (cases "n < 10") (simp_all add: decimal_digit_count.simps)

lemma decimal_reverse_below_digit_power:
  "decimal_reverse n < 10 ^ decimal_digit_count n"
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    then show ?thesis
      by (simp add: decimal_reverse.simps decimal_digit_count.simps)
  next
    case False
    let ?q = "n div 10"
    let ?r = "n mod 10"
    have quotient_less: "?q < n" using False by simp
    have ih: "decimal_reverse ?q < 10 ^ decimal_digit_count ?q"
      by (rule less.IH[OF quotient_less])
    have count_step:
      "decimal_digit_count n = Suc (decimal_digit_count ?q)"
      using False by (simp add: decimal_digit_count.simps)
    have reverse_step:
      "decimal_reverse n = ?r * 10 ^ decimal_digit_count ?q +
        decimal_reverse ?q"
      using False count_step by (simp add: decimal_reverse.simps)
    have digit_bound: "?r + 1 \<le> 10" by simp
    have reverse_bound:
      "decimal_reverse n < (?r + 1) * 10 ^ decimal_digit_count ?q"
    proof -
      have local:
        "?r * 10 ^ decimal_digit_count ?q + decimal_reverse ?q <
          ?r * 10 ^ decimal_digit_count ?q +
            10 ^ decimal_digit_count ?q"
        using ih by simp
      show ?thesis
        using local reverse_step by (simp add: algebra_simps)
    qed
    have scaled_bound:
      "(?r + 1) * 10 ^ decimal_digit_count ?q \<le>
        10 * 10 ^ decimal_digit_count ?q"
      by (rule mult_right_mono[OF digit_bound]) simp
    have power_step:
      "(10::nat) * (10::nat) ^ decimal_digit_count ?q =
        (10::nat) ^ decimal_digit_count n"
      using count_step by (simp add: power_Suc mult.commute)
    show ?thesis
      using reverse_bound scaled_bound power_step by arith
  qed
qed

lemma ten_power_digit_count_predecessor_le:
  assumes positive: "0 < n"
  shows "10 ^ (decimal_digit_count n - 1) \<le> n"
  using positive
proof (induction n rule: less_induct)
  case (less n)
  show ?case
  proof (cases "n < 10")
    case True
    have lower: "1 \<le> n" using less.prems by arith
    show ?thesis using True lower by simp
  next
    case False
    let ?q = "n div 10"
    have quotient_positive: "0 < ?q" using False by simp
    have quotient_less: "?q < n" using False by simp
    have ih: "10 ^ (decimal_digit_count ?q - 1) \<le> ?q"
      by (rule less.IH[OF quotient_less quotient_positive])
    have count_positive: "0 < decimal_digit_count ?q"
      by (rule decimal_digit_count_positive)
    have exponent:
      "decimal_digit_count ?q = Suc (decimal_digit_count ?q - 1)"
      using count_positive by arith
    have power_rewrite:
      "(10::nat) ^ decimal_digit_count ?q =
        (10::nat) * (10::nat) ^ (decimal_digit_count ?q - 1)"
      using exponent by (simp add: power_Suc mult.commute)
    have scaled:
      "10 ^ decimal_digit_count ?q \<le> 10 * ?q"
      using ih power_rewrite by (simp add: mult_left_mono)
    have decomposition: "n = ?q * 10 + n mod 10"
      using div_mult_mod_eq[of n 10] by (simp add: algebra_simps)
    have quotient_bound: "10 * ?q \<le> n"
      using decomposition by arith
    have count_step:
      "decimal_digit_count n = Suc (decimal_digit_count ?q)"
      using False by (simp add: decimal_digit_count.simps)
    have bound: "(10::nat) ^ decimal_digit_count ?q \<le> n"
      using scaled quotient_bound by arith
    show ?thesis
      using bound by (simp only: count_step diff_Suc_1)
  qed
qed

lemma five_reverse_step_six_bit_growth:
  assumes positive: "0 < n"
  shows "five_reverse_step n < 64 * n"
proof -
  have reversed: "decimal_reverse n < 10 ^ decimal_digit_count n"
    by (rule decimal_reverse_below_digit_power)
  have lower: "10 ^ (decimal_digit_count n - 1) \<le> n"
    by (rule ten_power_digit_count_predecessor_le[OF positive])
  have digit_count_positive: "0 < decimal_digit_count n"
    by (rule decimal_digit_count_positive)
  have power_bound:
    "10 ^ decimal_digit_count n \<le> 10 * n"
  proof -
    have exponent:
      "decimal_digit_count n = Suc (decimal_digit_count n - 1)"
      using digit_count_positive by arith
    have power_rewrite:
      "(10::nat) ^ decimal_digit_count n =
        (10::nat) * (10::nat) ^ (decimal_digit_count n - 1)"
      using exponent by (simp add: power_Suc mult.commute)
    show ?thesis using lower power_rewrite by (simp add: mult_left_mono)
  qed
  have "5 * decimal_reverse n < 64 * n"
    using reversed power_bound positive by linarith
  then show ?thesis by (simp add: five_reverse_step_def)
qed

theorem five_reverse_seed196_state_bits_bound:
  "five_reverse_orbit n 196 < 2 ^ (8 + 6 * n)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?state = "five_reverse_orbit n 196"
  have previous: "?state < 2 ^ (8 + 6 * n)" by (rule Suc.IH)
  show ?case
  proof (cases "?state = 0")
    case True
    then show ?thesis
      by (simp add: five_reverse_orbit.simps five_reverse_step_def
          decimal_reverse.simps)
  next
    case False
    have positive: "0 < ?state" using False by simp
    have growth: "five_reverse_step ?state < 64 * ?state"
      by (rule five_reverse_step_six_bit_growth[OF positive])
    have power_step:
      "(2::nat) ^ (8 + 6 * Suc n) =
        (64::nat) * (2::nat) ^ (8 + 6 * n)"
      by (simp add: power_add algebra_simps)
    show ?thesis
      using growth previous power_step
      by (simp only: five_reverse_orbit.simps; linarith)
  qed
qed

ML \<open>
  val checked = @{thms decimal_reverse_below_digit_power
    ten_power_digit_count_predecessor_le five_reverse_step_six_bit_growth
    five_reverse_seed196_state_bits_bound};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Five-reverse state-bit bound depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped five-reverse state-bit bound proof" else ();
\<close>

end
