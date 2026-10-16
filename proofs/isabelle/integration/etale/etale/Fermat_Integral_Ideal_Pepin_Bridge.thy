theory Fermat_Integral_Ideal_Pepin_Bridge
  imports Etale_Primality_Bridge Special_Factor_Progressions
    Fermat_Binomial_Negacyclic_Source Fermat_Dyadic_Unit_Pivot
    Fermat_Binomial_Unit_Producer
begin

text \<open>
An integer signed-carry cochain is enough to turn an authenticated source
fold into the Pépin divisibility.  The second theorem is the sufficient
Pépin criterion itself: it proves primality from the congruence, without
assuming the converse and without using a factor list.
\<close>

fun signed_weighted_value :: "int list \<Rightarrow> int" where
  "signed_weighted_value [] = 0"
| "signed_weighted_value (a # rest) = a + 2 * signed_weighted_value rest"

fun signed_carry_chain :: "int list \<Rightarrow> int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "signed_carry_chain [] [] incoming outgoing = (incoming = outgoing)"
| "signed_carry_chain (a # rest) (e # digits) incoming outgoing =
     (\<exists>carry_next. a + incoming = e + 2 * carry_next \<and>
       signed_carry_chain rest digits carry_next outgoing)"
| "signed_carry_chain _ _ _ _ = False"

lemma signed_weighted_value_append:
  "signed_weighted_value (low @ high) =
    signed_weighted_value low + 2 ^ length low * signed_weighted_value high"
  by (induction low) (simp_all add: algebra_simps power_Suc)

lemma signed_carry_chain_append:
  assumes low: "signed_carry_chain low low_digits incoming middle"
    and high: "signed_carry_chain high high_digits middle outgoing"
  shows "signed_carry_chain (low @ high) (low_digits @ high_digits)
    incoming outgoing"
  using low high
proof (induction low arbitrary: low_digits incoming middle)
  case Nil
  then show ?case by (cases low_digits) auto
next
  case (Cons coefficient rest)
  show ?case
  proof (cases low_digits)
    case Nil
    with Cons.prems(1) show ?thesis by simp
  next
    case (Cons digit digits)
    have first_shape:
      "signed_carry_chain (coefficient # rest) (digit # digits)
        incoming middle"
      using Cons.prems(1) Cons by simp
    then obtain carry_next where
      step: "coefficient + incoming = digit + 2 * carry_next"
        and tail:
          "signed_carry_chain rest digits carry_next middle"
      by auto
    have joined_tail:
      "signed_carry_chain (rest @ high) (digits @ high_digits)
        carry_next outgoing"
      by (rule Cons.IH[OF tail Cons.prems(2)])
    show ?thesis using step joined_tail Cons by simp
  qed
qed

lemma boolean_counter_column_signed_difference:
  fixes source addend incoming emitted outgoing :: nat
  assumes source_bit: "source \<le> 1"
    and addend_bit: "addend \<le> 1"
    and incoming_bit: "incoming \<le> 1"
    and output_bit: "emitted \<le> 1"
    and column: "source + addend + incoming = emitted + 2 * outgoing"
  shows "outgoing \<le> 1"
    and "int emitted - int source = int addend + int incoming - 2 * int outgoing"
proof -
  show "outgoing \<le> 1"
    using source_bit addend_bit incoming_bit column by presburger
  have column_int:
    "int source + int addend + int incoming = int emitted + 2 * int outgoing"
    using column by simp
  show "int emitted - int source = int addend + int incoming - 2 * int outgoing"
    using column_int by linarith
qed

lemma signed_fold_birth_is_incoming_carry_mod_two:
  fixes coefficient digit incoming outgoing :: int
  assumes normalization: "coefficient + incoming = digit + 2 * outgoing"
  shows "digit - coefficient = incoming - 2 * outgoing"
    and "(digit - coefficient) mod 2 = incoming mod 2"
proof -
  show "digit - coefficient = incoming - 2 * outgoing"
    using normalization by linarith
  then show "(digit - coefficient) mod 2 = incoming mod 2"
    by presburger
qed

lemma signed_carry_chain_weighted_identity:
  assumes chain: "signed_carry_chain coefficients digits incoming outgoing"
  shows "signed_weighted_value coefficients - signed_weighted_value digits =
    2 ^ length coefficients * outgoing - incoming"
  using chain
proof (induction coefficients arbitrary: digits incoming outgoing)
  case Nil
  then show ?case by (cases digits) auto
next
  case (Cons coefficient rest)
  note head_chain = Cons.prems
  note tail_induct = Cons.IH
  show ?case
  proof (cases digits)
    case Nil
    with head_chain show ?thesis by simp
  next
    case (Cons digit digits')
    have chain_shape:
      "signed_carry_chain (coefficient # rest) (digit # digits') incoming outgoing"
      using head_chain Cons by simp
    from chain_shape obtain carry_next where
      step: "coefficient + incoming = digit + 2 * carry_next"
        and tail: "signed_carry_chain rest digits' carry_next outgoing"
      by auto
    have tail_value:
      "signed_weighted_value rest - signed_weighted_value digits' =
        2 ^ length rest * outgoing - carry_next"
      by (rule tail_induct[OF tail])
    show ?thesis
      using step tail_value Cons
      by (simp add: algebra_simps power_Suc)
  qed
qed

lemma signed_carry_chain_composition:
  assumes low: "signed_carry_chain low low_digits incoming middle"
    and high: "signed_carry_chain high high_digits middle outgoing"
  shows "signed_weighted_value (low @ high) -
      signed_weighted_value (low_digits @ high_digits) =
    2 ^ (length low + length high) * outgoing - incoming"
proof -
  have joined:
    "signed_carry_chain (low @ high) (low_digits @ high_digits)
      incoming outgoing"
    by (rule signed_carry_chain_append[OF low high])
  have weighted:
    "signed_weighted_value (low @ high) -
      signed_weighted_value (low_digits @ high_digits) =
        2 ^ length (low @ high) * outgoing - incoming"
    by (rule signed_carry_chain_weighted_identity[OF joined])
  show ?thesis using weighted
    by (simp add: signed_weighted_value_append power_add algebra_simps)
qed

lemma signed_weighted_value_zero_replicate:
  "signed_weighted_value (replicate n 0) = 0"
  by (induction n) simp_all

lemma canonical_fermat_signed_digits_value:
  "signed_weighted_value ((-1) # replicate (2 ^ n - 1) 0) = -1"
  by (simp add: signed_weighted_value_zero_replicate)

theorem signed_carry_terminal_ideal_divisibility:
  fixes n :: nat
    and coefficients digits :: "int list"
    and incoming :: int
  assumes width: "length coefficients = 2 ^ n"
    and terminal: "digits = (-1) # replicate (2 ^ n - 1) 0"
    and chain: "signed_carry_chain coefficients digits incoming (- incoming)"
    and fold_auth:
      "signed_weighted_value coefficients =
        fermat_alternating_binomial_fold ((2::nat)^n)
          ((2::nat)^(2 ^ n - 1))"
  shows "(2::nat) ^ (2 ^ n) + 1 dvd
    (3::nat) ^ (2 ^ (2 ^ n - 1)) + 1"
proof -
  obtain quotient where fold_source:
    "int ((3::nat)^(2 ^ (2 ^ n - 1))) =
      int ((2::nat)^(2 ^ n) + 1) * quotient +
        fermat_alternating_binomial_fold ((2::nat)^n) ((2::nat)^(2 ^ n - 1))"
    by (rule fermat_alternating_binomial_fold_source)
  have source:
    "int ((3::nat)^(2 ^ (2 ^ n - 1))) =
      int ((2::nat)^(2 ^ n) + 1) * quotient +
        signed_weighted_value coefficients"
    using fold_source fold_auth by simp
  have carry_identity:
    "signed_weighted_value coefficients - signed_weighted_value digits =
      2 ^ length coefficients * (- incoming) - incoming"
    by (rule signed_carry_chain_weighted_identity[OF chain])
  have digit_value: "signed_weighted_value digits = -1"
    using terminal
    by (simp only: terminal canonical_fermat_signed_digits_value)
  have ideal_identity:
    "signed_weighted_value coefficients + 1 =
      - incoming * (2 ^ (2 ^ n) + 1)"
    using carry_identity width digit_value
    by (simp add: algebra_simps)
  let ?N = "(2::nat) ^ (2 ^ n) + 1"
  have exact:
    "int (3 ^ (2 ^ (2 ^ n - 1)) + 1) = int ?N * (quotient - incoming)"
    using source ideal_identity
    by (simp add: algebra_simps)
  have "int ?N dvd int (3 ^ (2 ^ (2 ^ n - 1)) + 1)"
    unfolding exact by (simp add: dvd_def)
  then show ?thesis by (rule iffD1[OF int_dvd_int_iff])
qed

theorem pepin_divisibility_implies_fermat_prime:
  fixes n :: nat
  assumes n: "1 \<le> n"
    and pepin:
      "(2::nat) ^ (2 ^ n) + 1 dvd (3::nat) ^ (2 ^ (2 ^ n - 1)) + 1"
  shows "prime ((2::nat) ^ (2 ^ n) + 1)"
proof -
  let ?N = "(2::nat) ^ (2 ^ n) + 1"
  let ?w = "(2::nat) ^ n"
  let ?e = "(2::nat) ^ (?w - 1)"
  have Nlarge: "1 < ?N" by simp
  have wpos: "1 \<le> ?w" using n by simp
  have epos: "0 < ?e" by simp
  have all_factors: "\<forall>q. prime q \<and> q dvd ?N \<longrightarrow> q = ?N"
  proof (intro allI impI)
    fix q
    assume q: "prime q \<and> q dvd ?N"
    then have qprime: "prime q" and qfactor: "q dvd ?N" by auto
    have qgt: "2 < q"
    proof -
      have candidate_odd: "odd ?N" by simp
      have qne2: "q \<noteq> 2" using qfactor candidate_odd by auto
      show ?thesis using qprime qne2 prime_ge_2_nat[OF qprime] by arith
    qed
    have qne3: "q \<noteq> 3"
    proof
      assume qeq: "q = 3"
      have divides_test: "q dvd ((3::nat) ^ ?e + 1)"
        using qfactor pepin by (rule dvd_trans)
      have three_divides_sum: "(3::nat) dvd ((3::nat) ^ ?e + 1)"
        using divides_test qeq by simp
      have three_divides_power: "(3::nat) dvd (3::nat) ^ ?e"
        using epos by (cases ?e) auto
      have three_divides_difference:
        "(3::nat) dvd ((3::nat) ^ ?e + 1 - (3::nat) ^ ?e)"
        by (rule dvd_diff_nat[OF three_divides_sum three_divides_power])
      have difference: "(3::nat) ^ ?e + 1 - (3::nat) ^ ?e = 1"
        by simp
      have "(3::nat) dvd (1::nat)"
        using three_divides_difference by (simp only: difference)
      then show False by simp
    qed
    have coprime: "coprime q (3::nat)"
    proof -
      have three_prime: "prime (3::nat)" by simp
      have "\<not> q dvd (3::nat)"
        using qprime three_prime qne3 by (metis primes_dvd_imp_eq)
      then show ?thesis by (rule prime_imp_coprime[OF qprime])
    qed
    have qtest: "q dvd ((3::nat) ^ ?e + 1)"
      using qfactor pepin by (rule dvd_trans)
    have qsuccessor: "q dvd Suc ((3::nat) ^ ?e)"
      using qtest by simp
    have qpos: "0 < q" using qgt by simp
    have neg: "[(3::nat) ^ ?e = q - 1] (mod q)"
      by (rule dvd_successor_imp_cong_predecessor[OF qpos qsuccessor])
    have twice: "2 * ?e = 2 ^ ?w"
    proof -
      have predecessor: "Suc (?w - 1) = ?w" using wpos by arith
      have "2 * (2::nat) ^ (?w - 1) = (2::nat) ^ Suc (?w - 1)"
        by (simp only: power_Suc)
      also have "... = (2::nat) ^ ?w" using predecessor by simp
      finally show ?thesis by simp
    qed
    have order_power: "[(3::nat) ^ (2 ^ ?w) = 1] (mod q)"
    proof -
      have powered: "[((3::nat) ^ ?e) ^ 2 = (q - 1) ^ 2] (mod q)"
        by (rule cong_pow[OF neg])
      have difference: "(q - 1) ^ 2 - 1 = q * (q - 2)"
      proof -
        have q_repr: "q = (q - 2) + 2" using qgt by simp
        show ?thesis
          using q_repr by (simp add: power2_eq_square algebra_simps)
      qed
      have dvd_difference: "q dvd (q - 1) ^ 2 - 1"
        by (subst difference) simp
      have one_le: "1 \<le> (q - 1) ^ 2" using qgt by simp
      have square_one: "[(q - 1) ^ 2 = 1] (mod q)"
        using dvd_difference one_le by (simp add: cong_altdef_nat)
      have base: "[(3 ^ ?e) ^ 2 = 1] (mod q)"
        by (rule cong_trans[OF powered square_one])
      have exponent: "((3::nat) ^ ?e) ^ 2 = (3::nat) ^ (2 * ?e)"
      proof -
        have "((3::nat) ^ ?e) ^ 2 = (3::nat) ^ (?e * 2)"
          by (simp only: power_mult[symmetric])
        also have "... = (3::nat) ^ (2 * ?e)"
          by (simp add: mult.commute)
        finally show ?thesis .
      qed
      show ?thesis using base exponent twice by simp
    qed
    have order_dvd: "ord q (3::nat) dvd 2 ^ ?w"
      by (rule iffD1[OF ord_divides order_power])
    have two_prime: "prime (2::nat)" by simp
    obtain i where i: "i \<le> ?w" "ord q (3::nat) = 2 ^ i"
      using order_dvd divides_primepow_nat[OF two_prime, of "ord q (3::nat)" ?w]
      by blast
    have not_half: "\<not> ord q 3 dvd 2 ^ (?w - 1)"
    proof
      assume half: "ord q (3::nat) dvd 2 ^ (?w - 1)"
      have half_cong: "[(3::nat) ^ ?e = 1] (mod q)"
        by (rule iffD2[OF ord_divides]) (use half in simp)
      have impossible: "[q - 1 = 1] (mod q)"
        using neg half_cong by (meson cong_sym cong_trans)
      have equal: "q - 1 = 1"
        by (rule cong_less_imp_eq_nat[OF _ _ _ _ impossible])
          (use qgt in simp_all)
      with qgt show False by simp
    qed
    have "\<not> i < ?w"
    proof
      assume "i < ?w"
      then have "i \<le> ?w - 1" by arith
      then have power_dvd: "(2::nat) ^ i dvd (2::nat) ^ (?w - 1)"
        by (intro le_imp_power_dvd) simp
      have "ord q (3::nat) dvd 2 ^ (?w - 1)"
        using power_dvd i(2) by simp
      with not_half show False by blast
    qed
    with i(1) have ieq: "i = ?w" by arith
    have order: "ord q (3::nat) = 2 ^ ?w" using i(2) ieq by simp
    have stride: "2 ^ ?w dvd q - 1"
      using prime_modulus_order_dvd_minus_one[OF qprime coprime] order
      by simp
    have lower: "?N \<le> q"
    proof -
      have "2 ^ ?w \<le> q - 1" using stride qgt by (intro dvd_imp_le) auto
      then show ?thesis using qgt by arith
    qed
    have upper: "q \<le> ?N" using qfactor Nlarge by (intro dvd_imp_le) auto
    show "q = ?N" using lower upper by arith
  qed
  show ?thesis
    by (rule iffD2[OF prime_iff_all_prime_divisors_equal[OF Nlarge] all_factors])
qed

theorem normalized_dyadic_unit_residue_one_implies_pepin:
  fixes n :: nat
  assumes level: "1 \<le> n"
    and unit_residue:
      "fermat_dyadic_unit (2^n - 1) mod ((2::nat)^(2^n) + 1) = 1"
  shows "(2::nat)^(2^n) + 1 dvd (3::nat)^(2^(2^n - 1)) + 1"
proof -
  let ?t = "(2::nat)^n - 1"
  let ?N = "(2::nat)^(2^n) + 1"
  let ?u = "fermat_dyadic_unit ?t"
  have power_lower: "2 \<le> (2::nat)^n"
    using level by (cases n) (auto simp: power_Suc)
  have t_positive: "1 \<le> ?t" using power_lower by arith
  have t_successor: "Suc ?t = 2^n" using level by simp
  have exponent_successor: "?t + 2 = Suc (2^n)"
    using t_successor by presburger
  have source_equation:
    "(3::nat)^(2^?t) = 1 + 2^(?t + 2) * ?u"
    using fermat_dyadic_unit_source_equation[of ?t] t_positive by auto
  have unit_decomposition: "?u = ?N * (?u div ?N) + 1"
  proof -
    have division: "?u div ?N * ?N + ?u mod ?N = ?u"
      by (rule div_mult_mod_eq)
    show ?thesis using division unit_residue by (simp add: mult.commute)
  qed
  have coefficient_identity: "(2::nat)^(?t + 2) + 2 = 2 * ?N"
  proof -
    have exponent:
      "(2::nat)^(?t + 2) = (2::nat)^(Suc (2^n))"
      using exponent_successor by simp
    have power: "(2::nat)^(?t + 2) = 2 * 2^(2^n)"
      using exponent by (simp only: power_Suc; simp add: mult.commute)
    show ?thesis using power by (simp add: algebra_simps)
  qed
  have exact:
    "(3::nat)^(2^?t) + 1 =
      ?N * (2^(?t + 2) * (?u div ?N) + 2)"
  proof -
    have source_step:
      "(3::nat)^(2^?t) + 1 = (1 + 2^(?t + 2) * ?u) + 1"
      by (simp only: source_equation)
    also have unit_step:
      "(1 + 2^(?t + 2) * ?u) + 1 =
        2^(?t + 2) * (?N * (?u div ?N) + 1) + 2"
      by (subst (1) unit_decomposition) (simp add: algebra_simps)
    also have factor_step:
      "2^(?t + 2) * (?N * (?u div ?N) + 1) + 2 =
        ?N * (2^(?t + 2) * (?u div ?N) + 2)"
    proof -
      have expanded:
        "2^(?t + 2) * (?N * (?u div ?N) + 1) + 2 =
          ?N * (2^(?t + 2) * (?u div ?N)) + (2^(?t + 2) + 2)"
        by (simp add: algebra_simps)
      show ?thesis
        by (simp only: expanded coefficient_identity) (simp add: algebra_simps)
    qed
    finally show ?thesis .
  qed
  have pepin: "?N dvd (3::nat)^(2^?t) + 1"
    unfolding dvd_def
    by (rule exI[of _ "2^(?t + 2) * (?u div ?N) + 2"]) (rule exact)
  show ?thesis using pepin by simp
qed

theorem fermat_first_three_indices_prime:
  assumes small_index: "n \<in> {1, 2, 3}"
  shows "prime ((2::nat)^(2^n) + 1)"
proof -
  have level: "1 \<le> n" using small_index by auto
  have index_cases: "n = 1 \<or> n = 2 \<or> n = 3"
    using small_index by auto
  have source_level_two:
    "fermat_binomial_accumulator_stream 2 (fermat_unit_complete_width 2)
       (2 ^ 2) = fermat_dyadic_unit 2 mod 2 ^ fermat_unit_complete_width 2"
    using fermat_bounded_python_source_exact(1)[of 2]
    by (simp add: fermat_unit_complete_width_def)
  have source_level_six:
    "fermat_binomial_accumulator_stream 6 (fermat_unit_complete_width 6)
       (2 ^ 6) = fermat_dyadic_unit 6 mod 2 ^ fermat_unit_complete_width 6"
    using fermat_bounded_python_source_exact(1)[of 6]
    by (simp add: fermat_unit_complete_width_def)
  have source_level_two_exact:
    "fermat_binomial_accumulator_stream 2 (fermat_unit_complete_width 2)
       (2 ^ 2) = fermat_dyadic_unit 2"
    using source_level_two
    by (simp add: fermat_dyadic_unit_initial_values fermat_unit_complete_width_def)
  have source_level_six_exact:
    "fermat_binomial_accumulator_stream 6 (fermat_unit_complete_width 6)
       (2 ^ 6) = fermat_dyadic_unit 6"
    using source_level_six
    by (simp add: fermat_unit_numeral_step fermat_unit_complete_width_def)
  have level_two_transition:
    "fermat_dyadic_unit 3 =
      fermat_binomial_accumulator_stream 2
        (fermat_unit_complete_width 2) (2 ^ 2) +
      2 ^ 3 * (fermat_binomial_accumulator_stream 2
        (fermat_unit_complete_width 2) (2 ^ 2))^2"
    using fermat_dyadic_unit_successor_exact[of 2] source_level_two_exact
    by simp
  have unit_three_from_producer:
    "fermat_dyadic_unit 3 mod 17 = 1"
    using level_two_transition source_level_two_exact
    by (simp add: fermat_dyadic_unit_initial_values fermat_unit_complete_width_def)
  have level_six_transition:
    "fermat_dyadic_unit 7 =
      fermat_binomial_accumulator_stream 6
        (fermat_unit_complete_width 6) (2 ^ 6) +
      2 ^ 7 * (fermat_binomial_accumulator_stream 6
        (fermat_unit_complete_width 6) (2 ^ 6))^2"
    using fermat_dyadic_unit_successor_exact[of 6] source_level_six_exact
    by simp
  have unit_seven_from_producer:
    "fermat_dyadic_unit 7 mod 257 = 1"
    using level_six_transition source_level_six_exact
    by (simp add: fermat_unit_numeral_step fermat_unit_complete_width_def)
  have unit_residue:
    "fermat_dyadic_unit (2^n - 1) mod ((2::nat)^(2^n) + 1) = 1"
    using index_cases
    by (elim disjE; simp add: fermat_dyadic_unit_initial_values
        unit_three_from_producer unit_seven_from_producer)
  have pepin:
    "(2::nat)^(2^n) + 1 dvd (3::nat)^(2^(2^n - 1)) + 1"
    by (rule normalized_dyadic_unit_residue_one_implies_pepin[OF level unit_residue])
  show ?thesis
    by (rule pepin_divisibility_implies_fermat_prime[OF level pepin])
qed

theorem source_integral_witness_implies_fermat_prime:
  fixes n :: nat
    and coefficients digits :: "int list"
    and incoming :: int
  assumes n: "1 \<le> n"
    and width: "length coefficients = 2 ^ n"
    and terminal: "digits = (-1) # replicate (2 ^ n - 1) 0"
    and chain: "signed_carry_chain coefficients digits incoming (- incoming)"
    and fold_auth:
      "signed_weighted_value coefficients =
        fermat_alternating_binomial_fold ((2::nat)^n)
          ((2::nat)^(2 ^ n - 1))"
  shows "prime ((2::nat) ^ (2 ^ n) + 1)"
  by (rule pepin_divisibility_implies_fermat_prime[OF n
      signed_carry_terminal_ideal_divisibility[OF width terminal chain fold_auth]])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms signed_weighted_value_append
      signed_carry_chain_append
      signed_carry_chain_composition
      boolean_counter_column_signed_difference
      signed_fold_birth_is_incoming_carry_mod_two
      signed_carry_chain_weighted_identity
      signed_weighted_value_zero_replicate
      canonical_fermat_signed_digits_value
      negacyclic_power_difference_dvd
      negacyclic_binomial_term
      fermat_alternating_binomial_fold_divisibility
      fermat_alternating_binomial_fold_source
      signed_carry_terminal_ideal_divisibility
      pepin_divisibility_implies_fermat_prime
      normalized_dyadic_unit_residue_one_implies_pepin
      fermat_first_three_indices_prime
      source_integral_witness_implies_fermat_prime}) then ()
    else error "Fermat integral ideal/Pepin bridge depends on an oracle";
\<close>

end
