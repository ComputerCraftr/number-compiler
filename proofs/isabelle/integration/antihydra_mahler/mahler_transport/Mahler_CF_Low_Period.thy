theory Mahler_CF_Low_Period
  imports Mahler_Continued_Fraction_Refinement
    "Shared_Carry_Dynamics.Dyadic_Unit_Carry_Frontier"
begin

text \<open>The decimal low suffix is derived from the same raw power of five.
The settled phase belongs only to this bounded suffix and does not identify
the changing-width upper word.\<close>

lemma mahler_cf_low_dyadic_phase:
  fixes columns exponent :: nat
  assumes "0 < columns"
  shows "(5::nat)^exponent mod 2^columns =
    5^(exponent mod dyadic_unit_phase_period 5 columns) mod 2^columns"
proof -
  let ?period = "dyadic_unit_phase_period 5 columns"
  let ?modulus = "(2::nat)^columns"
  have period_positive: "0 < ?period"
    by (simp add: dyadic_unit_phase_period_def)
  have modulus_gt_one: "1 < ?modulus"
    by (rule one_less_power) (use assms in simp_all)
  have returned: "(5::nat)^?period mod ?modulus = 1"
    by (rule dyadic_five_unit_phase_period_returns[OF assms])
  have repeated: "(5::nat)^(?period * (exponent div ?period)) mod ?modulus = 1"
  proof -
    have "((5::nat)^?period)^(exponent div ?period) mod ?modulus =
        (((5::nat)^?period mod ?modulus)^(exponent div ?period)) mod ?modulus"
      by (rule power_mod[symmetric])
    also have "... = 1"
      using assms by (simp only: returned power_one) simp
    finally show ?thesis by (simp only: power_mult)
  qed
  have decomposition:
    "exponent = exponent mod ?period + ?period * (exponent div ?period)"
    using div_mult_mod_eq[of exponent ?period] by (simp add: mult.commute)
  have "(5::nat)^exponent mod ?modulus =
      (5^(exponent mod ?period) * 5^(?period * (exponent div ?period))) mod ?modulus"
    by (subst (1) decomposition) (simp only: power_add)
  also have "... = 5^(exponent mod ?period) mod ?modulus"
  proof -
    have "((5::nat)^(exponent mod ?period) *
        5^(?period * (exponent div ?period))) mod ?modulus =
      ((5^(exponent mod ?period) mod ?modulus) *
        (5^(?period * (exponent div ?period)) mod ?modulus)) mod ?modulus"
      by (rule mod_mult_eq[symmetric])
    also have "... = 5^(exponent mod ?period) mod ?modulus"
      using modulus_gt_one by (simp add: repeated)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

theorem mahler_cf_settled_low_suffix:
  fixes exponent columns :: nat
  assumes columns: "0 < columns" and settled: "columns \<le> exponent"
  shows "(5::nat)^exponent mod 10^columns =
    5^columns *
      (5^((exponent-columns) mod dyadic_unit_phase_period 5 columns) mod 2^columns)"
proof -
  have decomposition: "exponent = columns + (exponent-columns)"
    using settled by simp
  have decimal: "(10::nat)^columns = 5^columns * 2^columns"
    by (simp add: power_mult_distrib[symmetric] mult.commute)
  have "(5::nat)^exponent mod 10^columns =
      5^columns * (5^(exponent-columns) mod 2^columns)"
    by (subst (1) decomposition)
       (simp only: power_add decimal mod_mult_mult1)
  also have "... =
      5^columns * (5^((exponent-columns) mod
        dyadic_unit_phase_period 5 columns) mod 2^columns)"
    by (rule arg_cong[where f="(\<lambda>x. 5^columns * x)"])
       (rule mahler_cf_low_dyadic_phase[OF columns])
  finally show ?thesis .
qed

theorem mahler_cf_low_suffix_ordered_consumer:
  fixes exponent columns :: nat
  assumes "0 < columns" "columns \<le> exponent"
  shows "mahler_cf_word (mahler_cf_decimal_digits columns (5^exponent mod 10^columns)) =
    mahler_cf_word (mahler_cf_decimal_digits columns
      (5^columns * (5^((exponent-columns) mod
        dyadic_unit_phase_period 5 columns) mod 2^columns)))"
  using mahler_cf_settled_low_suffix[OF assms] by simp


lemma mahler_cf_settled_low_return:
  fixes columns offset :: nat
  assumes columns: "0 < columns"
  shows "(5::nat)^(columns+offset+dyadic_unit_phase_period 5 columns) mod 10^columns =
    5^(columns+offset) mod 10^columns"
proof -
  let ?period = "dyadic_unit_phase_period 5 columns"
  have left: "(5::nat)^(columns+offset+?period) mod 10^columns =
    5^columns * (5^((offset+?period) mod ?period) mod 2^columns)"
    using mahler_cf_settled_low_suffix[OF columns, of "columns+offset+?period"]
    by simp
  have right: "(5::nat)^(columns+offset) mod 10^columns =
    5^columns * (5^(offset mod ?period) mod 2^columns)"
    using mahler_cf_settled_low_suffix[OF columns, of "columns+offset"]
    by simp
  show ?thesis using left right by simp
qed

theorem mahler_cf_low_suffix_ordered_period:
  fixes columns offset rows :: nat
  assumes columns: "0 < columns"
    and fits: "dyadic_unit_phase_period 5 columns \<le> rows"
  defines "period \<equiv> dyadic_unit_phase_period 5 columns"
  shows "mahler_cf_word (concat (map (\<lambda>i.
      mahler_cf_decimal_digits columns (5^(columns+offset+i) mod 10^columns))
        [0..<rows])) =
    ordered_matrix2_multiply
      (ordered_matrix2_power (mahler_cf_word (concat (map (\<lambda>i.
        mahler_cf_decimal_digits columns (5^(columns+offset+i) mod 10^columns))
        [0..<period]))) (rows div period))
      (mahler_cf_word (concat (take (rows mod period) (map (\<lambda>i.
        mahler_cf_decimal_digits columns (5^(columns+offset+i) mod 10^columns))
        [0..<period]))))"
proof -
  let ?row = "\<lambda>i. mahler_cf_decimal_digits columns
    (5^(columns+offset+i) mod 10^columns)"
  have positive: "0 < period"
    by (simp add: period_def dyadic_unit_phase_period_def)
  have periodic: "?row (i+period) = ?row i" if "i+period < rows" for i
    using mahler_cf_settled_low_return[OF columns, of "offset+i"]
    by (simp add: period_def add.assoc)
  have sequence:
    "map ?row [0..<rows] =
      concat (replicate (rows div period) (map ?row [0..<period])) @
      take (rows mod period) (map ?row [0..<period])"
    by (rule mahler_cf_periodic_list[OF positive]) (use fits periodic in \<open>auto simp: period_def\<close>)
  show ?thesis using sequence
    by (simp only: mahler_cf_concat_repeated_rows concat_append
        mahler_cf_word_append mahler_cf_word_repeat)
qed

ML \<open>
  val checked = @{thms mahler_cf_low_dyadic_phase
    mahler_cf_settled_low_suffix mahler_cf_low_suffix_ordered_consumer
    mahler_cf_settled_low_return mahler_cf_low_suffix_ordered_period};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mahler low-column phase depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped Mahler low-column phase proof" else ();
\<close>

end
