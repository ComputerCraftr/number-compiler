theory Reverse_196_Residue_Quotient
  imports Reverse_196_Publisher_Refinement "HOL-Number_Theory.Cong"
begin

text \<open>The scalar residue quotient is derived from the completed decimal
producer. The mod-99 statement retains the exact source width phase; it is
not a selector for the pair-field successor's GT/EQ/LT word.\<close>

lemma decimal_ten_power_mod99:
  "((10::nat)^n) mod 99 = (if even n then 1 else 10)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have power: "(10::nat) ^ Suc n = 10^n * 10"
    by (simp add: power_Suc)
  have step:
    "((10::nat) ^ Suc n) mod 99 = ((10^n mod 99) * 10) mod 99"
  proof -
    show ?thesis unfolding power by (rule mod_mult_left_eq[symmetric])
  qed
  show ?case
  proof (cases "even n")
    case True
    with Suc.IH step show ?thesis by simp
  next
    case False
    with Suc.IH step show ?thesis by simp
  qed
qed

lemma decimal_ten_power_mod11:
  "((10::nat)^n) mod 11 = (if even n then 1 else 10)"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have power: "(10::nat) ^ Suc n = 10^n * 10"
    by (simp add: power_Suc)
  have step:
    "((10::nat) ^ Suc n) mod 11 = ((10^n mod 11) * 10) mod 11"
  proof -
    show ?thesis unfolding power by (rule mod_mult_left_eq[symmetric])
  qed
  show ?case
  proof (cases "even n")
    case True
    with Suc.IH step show ?thesis by simp
  next
    case False
    with Suc.IH step show ?thesis by simp
  qed
qed

lemma decimal_list_value_mod9:
  "decimal_list_value ds mod 9 = sum_list ds mod 9"
proof (induction ds)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have ten: "(10::nat) mod 9 = 1" by simp
  have product:
    "(10 * decimal_list_value ds) mod 9 = sum_list ds mod 9"
  proof -
    have factors:
      "(10 * decimal_list_value ds) mod 9 =
        ((10 mod 9) * (decimal_list_value ds mod 9)) mod 9"
      by (rule mod_mult_eq[symmetric])
    show ?thesis using factors ten Cons.IH by simp
  qed
  have decimal:
    "decimal_list_value (d # ds) = d + 10 * decimal_list_value ds"
    by simp
  have digits: "sum_list (d # ds) = d + sum_list ds"
    by (simp only: sum_list.Cons)
  show ?case
    unfolding decimal digits
    by (rule mod_add_cong[OF refl product])
qed

lemma decimal_list_value_reverse_mod9:
  "decimal_list_value (rev ds) mod 9 = decimal_list_value ds mod 9"
  by (simp add: decimal_list_value_mod9)

lemma decimal_list_value_reverse_mod99:
  "decimal_list_value (rev ds) mod 99 =
    ((if even (length ds) then 10 else 1) * decimal_list_value ds) mod 99"
proof (induction ds)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have reverse_value:
    "decimal_list_value (rev (d # ds)) =
      decimal_list_value (rev ds) + d * 10 ^ length ds"
    by (simp add: decimal_list_value_append)
  show ?case
  proof (cases "even (length ds)")
    case even_width: True
    have reverse:
      "decimal_list_value (rev ds) mod 99 =
        (10 * decimal_list_value ds) mod 99"
      using Cons.IH even_width by simp
  have power: "((10::nat) ^ length ds) mod (99::nat) = (1::nat) mod (99::nat)"
      using decimal_ten_power_mod99[of "length ds"] even_width by simp
    have scaled:
      "(d * 10 ^ length ds) mod 99 = d mod 99"
    proof -
      have "(d * 10 ^ length ds) mod 99 = (d * 1) mod 99"
        by (rule mod_mult_cong[OF refl power])
      then show ?thesis by simp
    qed
    have combined:
      "(decimal_list_value (rev ds) + d * 10 ^ length ds) mod 99 =
        (10 * decimal_list_value ds + d) mod 99"
      by (rule mod_add_cong[OF reverse scaled])
    have target:
      "((if even (length (d # ds)) then 10 else 1) *
          decimal_list_value (d # ds)) mod 99 =
        (10 * decimal_list_value ds + d) mod 99"
      using even_width by (simp add: algebra_simps)
    show ?thesis
      unfolding reverse_value using combined target by simp
  next
    case odd_width: False
    have reverse:
      "decimal_list_value (rev ds) mod 99 = decimal_list_value ds mod 99"
      using Cons.IH odd_width by simp
    have power: "((10::nat) ^ length ds) mod (99::nat) = (10::nat) mod (99::nat)"
      using decimal_ten_power_mod99[of "length ds"] odd_width by simp
    have scaled:
      "(d * 10 ^ length ds) mod 99 = (d * 10) mod 99"
      by (rule mod_mult_cong[OF refl power])
    have combined:
      "(decimal_list_value (rev ds) + d * 10 ^ length ds) mod 99 =
        (decimal_list_value ds + d * 10) mod 99"
      by (rule mod_add_cong[OF reverse scaled])
    have hundred: "(100::nat) mod 99 = (1::nat) mod 99" by simp
    have high_scaled:
      "(100 * decimal_list_value ds) mod 99 = decimal_list_value ds mod 99"
    proof -
      have "(100 * decimal_list_value ds) mod 99 =
          (1 * decimal_list_value ds) mod 99"
        by (rule mod_mult_cong[OF hundred refl])
      then show ?thesis by simp
    qed
    have expanded:
      "10 * decimal_list_value (d # ds) =
        10 * d + 100 * decimal_list_value ds"
      by (simp add: algebra_simps)
    have target:
      "((if even (length (d # ds)) then 10 else 1) *
          decimal_list_value (d # ds)) mod 99 =
        (decimal_list_value ds + d * 10) mod 99"
    proof -
      have sum:
        "(10 * d + 100 * decimal_list_value ds) mod 99 =
          (10 * d + decimal_list_value ds) mod 99"
        by (rule mod_add_cong[OF refl high_scaled])
      show ?thesis using odd_width expanded sum
        by (simp add: add.commute mult.commute)
    qed
    show ?thesis
      unfolding reverse_value using combined target by simp
  qed
qed

lemma decimal_list_value_reverse_mod11:
  "decimal_list_value (rev ds) mod 11 =
    ((if even (length ds) then 10 else 1) * decimal_list_value ds) mod 11"
proof (induction ds)
  case Nil
  then show ?case by simp
next
  case (Cons d ds)
  have reverse_value:
    "decimal_list_value (rev (d # ds)) =
      decimal_list_value (rev ds) + d * 10 ^ length ds"
    by (simp add: decimal_list_value_append)
  show ?case
  proof (cases "even (length ds)")
    case even_width: True
    have reverse:
      "decimal_list_value (rev ds) mod 11 =
        (10 * decimal_list_value ds) mod 11"
      using Cons.IH even_width by simp
    have power: "((10::nat) ^ length ds) mod (11::nat) = (1::nat) mod (11::nat)"
      using decimal_ten_power_mod11[of "length ds"] even_width by simp
    have scaled:
      "(d * 10 ^ length ds) mod 11 = d mod 11"
    proof -
      have "(d * 10 ^ length ds) mod 11 = (d * 1) mod 11"
        by (rule mod_mult_cong[OF refl power])
      then show ?thesis by simp
    qed
    have combined:
      "(decimal_list_value (rev ds) + d * 10 ^ length ds) mod 11 =
        (10 * decimal_list_value ds + d) mod 11"
      by (rule mod_add_cong[OF reverse scaled])
    have target:
      "((if even (length (d # ds)) then 10 else 1) *
          decimal_list_value (d # ds)) mod 11 =
        (10 * decimal_list_value ds + d) mod 11"
      using even_width by (simp add: algebra_simps)
    show ?thesis
      unfolding reverse_value using combined target by simp
  next
    case odd_width: False
    have reverse:
      "decimal_list_value (rev ds) mod 11 = decimal_list_value ds mod 11"
      using Cons.IH odd_width by simp
    have power: "((10::nat) ^ length ds) mod (11::nat) = (10::nat) mod (11::nat)"
      using decimal_ten_power_mod11[of "length ds"] odd_width by simp
    have scaled:
      "(d * 10 ^ length ds) mod 11 = (d * 10) mod 11"
      by (rule mod_mult_cong[OF refl power])
    have combined:
      "(decimal_list_value (rev ds) + d * 10 ^ length ds) mod 11 =
        (decimal_list_value ds + d * 10) mod 11"
      by (rule mod_add_cong[OF reverse scaled])
    have eleven: "(100::nat) mod 11 = (1::nat) mod 11" by simp
    have high_scaled:
      "(100 * decimal_list_value ds) mod 11 = decimal_list_value ds mod 11"
    proof -
      have "(100 * decimal_list_value ds) mod 11 =
          (1 * decimal_list_value ds) mod 11"
        by (rule mod_mult_cong[OF eleven refl])
      then show ?thesis by simp
    qed
    have expanded:
      "10 * decimal_list_value (d # ds) =
        10 * d + 100 * decimal_list_value ds"
      by (simp add: algebra_simps)
    have target:
      "((if even (length (d # ds)) then 10 else 1) *
          decimal_list_value (d # ds)) mod 11 =
        (decimal_list_value ds + d * 10) mod 11"
    proof -
      have sum:
        "(10 * d + 100 * decimal_list_value ds) mod 11 =
          (10 * d + decimal_list_value ds) mod 11"
        by (rule mod_add_cong[OF refl high_scaled])
      show ?thesis using odd_width expanded sum
        by (simp add: add.commute mult.commute)
    qed
    show ?thesis
      unfolding reverse_value using combined target by simp
  qed
qed

theorem reverse_add_pair_step_mod9:
  assumes valid: "valid_pair ss"
  shows "reverse_add_pair_term (step ss) mod 9 =
    (2 * reverse_add_pair_term ss) mod 9"
proof -
  have successor:
    "reverse_add_pair_term (step ss) =
      reverse_add_pair_term ss + reverse_add_pair_reverse ss"
    by (rule reverse_add_completed_pair_successor[OF valid])
  let ?x = "decimal_list_value (digits ss)"
  let ?y = "decimal_list_value (rev (digits ss))"
  have next_value:
    "reverse_add_pair_term (step ss) = ?x + ?y"
    using successor by (simp add: reverse_add_pair_term_def
        reverse_add_pair_reverse_def)
  have reverse:
    "?y mod 9 = ?x mod 9"
    by (rule decimal_list_value_reverse_mod9)
  have sum:
    "(?x + ?y) mod 9 = (?x + ?x) mod 9"
    by (rule mod_add_cong[OF refl reverse])
  have doubled: "(2 * ?x) mod 9 = (?x + ?x) mod 9"
    by (simp add: mult_2)
  have transition: "reverse_add_pair_term (step ss) mod 9 = (2 * ?x) mod 9"
    using next_value sum doubled by simp
  have current: "reverse_add_pair_term ss = ?x"
    by (simp add: reverse_add_pair_term_def)
  show ?thesis using transition current by simp
qed

theorem reverse_add_pair_step_mod99:
  assumes valid: "valid_pair ss"
  shows "reverse_add_pair_term (step ss) mod 99 =
    ((if even (length (digits ss)) then 11 else 2) *
      reverse_add_pair_term ss) mod 99"
proof -
  have successor:
    "reverse_add_pair_term (step ss) =
      reverse_add_pair_term ss + reverse_add_pair_reverse ss"
    by (rule reverse_add_completed_pair_successor[OF valid])
  let ?x = "decimal_list_value (digits ss)"
  let ?y = "decimal_list_value (rev (digits ss))"
  let ?even = "even (length (digits ss))"
  have next_value:
    "reverse_add_pair_term (step ss) = ?x + ?y"
    using successor by (simp add: reverse_add_pair_term_def
        reverse_add_pair_reverse_def)
  have reverse:
    "?y mod 99 = ((if ?even then 10 else 1) * ?x) mod 99"
    by (rule decimal_list_value_reverse_mod99)
  have sum:
    "(?x + ?y) mod 99 =
      (?x + (if ?even then 10 else 1) * ?x) mod 99"
    by (rule mod_add_cong[OF refl reverse])
  have scalar:
    "((if ?even then 11 else 2) * ?x) mod 99 =
      (?x + (if ?even then 10 else 1) * ?x) mod 99"
  proof (cases ?even)
    case True
    then show ?thesis by (simp add: algebra_simps mult_2)
  next
    case False
    then show ?thesis by (simp add: algebra_simps mult_2)
  qed
  have transition:
    "reverse_add_pair_term (step ss) mod 99 =
      ((if ?even then 11 else 2) * ?x) mod 99"
    using next_value sum scalar by simp
  have current: "reverse_add_pair_term ss = ?x"
    by (simp add: reverse_add_pair_term_def)
  show ?thesis using transition current by simp
qed

theorem reverse_add_pair_step_mod11:
  assumes valid: "valid_pair ss"
  shows "reverse_add_pair_term (step ss) mod 11 =
    ((if even (length (digits ss)) then 0 else 2) *
      reverse_add_pair_term ss) mod 11"
proof -
  have successor:
    "reverse_add_pair_term (step ss) =
      reverse_add_pair_term ss + reverse_add_pair_reverse ss"
    by (rule reverse_add_completed_pair_successor[OF valid])
  let ?x = "decimal_list_value (digits ss)"
  let ?y = "decimal_list_value (rev (digits ss))"
  let ?even = "even (length (digits ss))"
  have next_value:
    "reverse_add_pair_term (step ss) = ?x + ?y"
    using successor by (simp add: reverse_add_pair_term_def
        reverse_add_pair_reverse_def)
  have reverse:
    "?y mod 11 = ((if ?even then 10 else 1) * ?x) mod 11"
    by (rule decimal_list_value_reverse_mod11)
  have sum:
    "(?x + ?y) mod 11 =
      (?x + (if ?even then 10 else 1) * ?x) mod 11"
    by (rule mod_add_cong[OF refl reverse])
  have scalar:
    "((if ?even then 0 else 2) * ?x) mod 11 =
      (?x + (if ?even then 10 else 1) * ?x) mod 11"
  proof (cases ?even)
    case True
    have multiple: "(?x + 10 * ?x) mod 11 = 0"
      by (simp add: algebra_simps)
    show ?thesis using True multiple by simp
  next
    case False
    then show ?thesis by (simp add: algebra_simps mult_2)
  qed
  have transition:
    "reverse_add_pair_term (step ss) mod 11 =
      ((if ?even then 0 else 2) * ?x) mod 11"
    using next_value sum scalar by simp
  have current: "reverse_add_pair_term ss = ?x"
    by (simp add: reverse_add_pair_term_def)
  show ?thesis using transition current by simp
qed

theorem reverse_add_pair_run_mod11_preserves_zero:
  assumes valid: "valid_pair ss"
      and residue: "reverse_add_pair_term ss mod 11 = 0"
  shows "reverse_add_pair_term (run step n ss) mod 11 = 0"
  using valid residue
proof (induction n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have next_valid: "valid_pair (step ss)"
    by (rule valid_pair_successor[OF Suc.prems(1)])
  let ?current = "reverse_add_pair_term ss"
  let ?factor = "if even (length (digits ss)) then 0 else 2"
  have current_residue: "?current mod 11 = (0::nat) mod 11"
    using Suc.prems(2) by simp
  have scaled_zero: "(?factor * ?current) mod 11 = 0"
  proof (cases "even (length (digits ss))")
    case True
    then show ?thesis by simp
  next
    case False
    have scaled: "(2 * ?current) mod 11 = (2 * 0) mod 11"
      by (rule mod_mult_cong[OF refl current_residue])
    then show ?thesis using False by simp
  qed
  have one: "reverse_add_pair_term (step ss) mod 11 = 0"
    using reverse_add_pair_step_mod11[OF Suc.prems(1)] scaled_zero by simp
  show ?case
    by (simp only: run.simps; rule Suc.IH[OF next_valid one])
qed

lemma reverse_add_pair_term_even_source_width_mod11:
  assumes valid: "valid_pair ss"
      and even_width: "even (length ss)"
  shows "reverse_add_pair_term ss mod 11 = 0"
proof -
  have bounded: "\<forall>s\<in>set ss. s \<le> 18"
    using valid unfolding valid_pair_def by blast
  have represented: "decimal_list_value (digits ss) = decimal_list_value ss"
    by (rule digits_preserve_decimal_value[OF bounded])
  have palindrome: "rev ss = ss"
    using valid unfolding valid_pair_def by blast
  let ?r = "decimal_list_value ss mod 11"
  have reverse_value: "decimal_list_value (rev ss) mod 11 = (10 * decimal_list_value ss) mod 11"
    using decimal_list_value_reverse_mod11[of ss] even_width by simp
  have fixed_raw: "?r = (10 * decimal_list_value ss) mod 11"
    using palindrome reverse_value by simp
  have reduced_product:
    "(10 * decimal_list_value ss) mod 11 =
      (10 * (decimal_list_value ss mod 11)) mod 11"
    by (rule mod_mult_right_eq[symmetric])
  have fixed: "?r = (10 * ?r) mod 11"
    using fixed_raw reduced_product by simp
  have bound: "?r < 11" by simp
  have zero: "?r = 0"
  proof (cases ?r)
    case 0
    then show ?thesis .
  next
    case (Suc k)
    have k_bound: "k < 10" using bound Suc by arith
    have k_cases:
      "k = 0 \<or> k = 1 \<or> k = 2 \<or> k = 3 \<or> k = 4 \<or>
       k = 5 \<or> k = 6 \<or> k = 7 \<or> k = 8 \<or> k = 9"
      using k_bound by arith
    have not_fixed: "Suc k \<noteq> (10 * Suc k) mod 11"
      using k_cases by (elim disjE; simp)
    have fixed_k: "Suc k = (10 * Suc k) mod 11"
      using fixed by (simp only: Suc)
    show ?thesis using fixed_k not_fixed by blast
  qed
  show ?thesis
    unfolding reverse_add_pair_term_def
    using represented zero by simp
qed

theorem reverse_add_run_mod9_doubling:
  assumes valid: "valid_pair ss"
  shows "reverse_add_pair_term (run step n ss) mod 9 =
    (2^n * reverse_add_pair_term ss) mod 9"
  using valid
proof (induction n arbitrary: ss)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have next_valid: "valid_pair (step ss)"
    by (rule valid_pair_successor[OF Suc.prems])
  have ih: "reverse_add_pair_term (run step n (step ss)) mod 9 =
      (2^n * reverse_add_pair_term (step ss)) mod 9"
    by (rule Suc.IH[OF next_valid])
  have one: "reverse_add_pair_term (step ss) mod 9 =
      (2 * reverse_add_pair_term ss) mod 9"
    by (rule reverse_add_pair_step_mod9[OF Suc.prems])
  have recurrence:
    "(2^n * reverse_add_pair_term (step ss)) mod 9 =
      (2^n * (2 * reverse_add_pair_term ss)) mod 9"
    by (rule mod_mult_cong[OF refl one])
  show ?case using ih recurrence
    by (simp add: power_Suc algebra_simps)
qed

lemma reverse_add_formula_mod9:
  assumes positive: "0 < n"
  shows "(55 * ((5 * x) mod 9) * (2::nat)^n) mod 9 =
    ((2::nat)^(n-1) * x) mod 9"
proof -
  obtain m where n: "n = Suc m" using positive by (cases n) auto
  let ?source = "(5 * x) mod 9"
  have pow: "(2::nat)^n = 2 * (2::nat)^m" using n by simp
  have c55: "(55::nat) mod 9 = (1::nat) mod 9" by simp
  have c10: "(5 * 2::nat) mod 9 = (1::nat) mod 9" by simp
  have outer:
    "(55 * ?source * (2::nat)^n) mod 9 =
      (?source * (2::nat)^n) mod 9"
  proof -
    have "(55 * (?source * (2::nat)^n)) mod 9 =
        (1 * (?source * (2::nat)^n)) mod 9"
      by (rule mod_mult_cong[OF c55 refl])
    then show ?thesis by (simp add: mult.assoc)
  qed
  have source_factor: "?source mod 9 = (5 * x) mod 9" by simp
  have power_factor:
    "((2::nat)^n) mod 9 = (2 * (2::nat)^m) mod 9"
    using pow by simp
  have scaled:
    "(?source * (2::nat)^n) mod 9 =
      (5 * x * (2 * (2::nat)^m)) mod 9"
    by (rule mod_mult_cong[OF source_factor power_factor])
  have rearranged:
    "(5 * x * (2 * (2::nat)^m)) mod 9 =
      (5 * 2 * x * (2::nat)^m) mod 9"
    by (simp add: algebra_simps)
  have coefficient:
    "(5 * 2 * x) mod 9 = x mod 9"
  proof -
    have "(5 * 2 * x) mod 9 = (1 * x) mod 9"
      by (rule mod_mult_cong[OF c10 refl])
    then show ?thesis by simp
  qed
  have product:
    "(5 * 2 * x * (2::nat)^m) mod 9 =
      (x * (2::nat)^m) mod 9"
    by (rule mod_mult_cong[OF coefficient refl])
  show ?thesis using outer scaled rearranged product n by (simp add: mult.commute)
qed

lemma mod_9_11_equal_mod99:
  fixes a b :: nat
  assumes "a mod 9 = b mod 9" "a mod 11 = b mod 11"
  shows "a mod 99 = b mod 99"
proof -
  have nine: "[a = b] (mod 9)"
    using assms(1) by (simp add: cong_def)
  have eleven: "[a = b] (mod 11)"
    using assms(2) by (simp add: cong_def)
  have coprime: "coprime (9::nat) 11"
    by (simp add: coprime_iff_gcd_eq_1 gcd_nat.simps)
  have combined: "[a = b] (mod (9 * 11))"
    by (rule coprime_cong_mult_nat[OF nine eleven coprime])
  show ?thesis using combined by (simp add: cong_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms decimal_ten_power_mod99 decimal_ten_power_mod11
      decimal_list_value_reverse_mod9 decimal_list_value_reverse_mod99
      decimal_list_value_reverse_mod11 reverse_add_pair_step_mod9
      reverse_add_pair_step_mod99 reverse_add_pair_step_mod11
      reverse_add_pair_run_mod11_preserves_zero
      reverse_add_pair_term_even_source_width_mod11
      reverse_add_run_mod9_doubling reverse_add_formula_mod9
      mod_9_11_equal_mod99 valid_pair_run}) then ()
    else error "Reverse residue quotient depends on an oracle";
\<close>

end
