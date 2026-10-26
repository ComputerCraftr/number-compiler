theory Padic_Affine_Height_Quotient
  imports Padic_Event_Action "HOL-Number_Theory.Modular_Inverse"
begin

text \<open>
This file is arithmetic transport for an already proved signed affine
height equation.  It does not prove that a comma source has a particular
first event, nor does it construct the height or the width-scale integer.
The exact equation is an explicit premise.  The quotient result works with a
signed constant, including negative offsets.
\<close>

lemma padic_int_power_dvd_iff_valuation:
  fixes p x :: int and k :: nat
  assumes prime_p: "prime p" and positive: "0 < x"
  shows "p ^ k dvd x \<longleftrightarrow> k \<le> multiplicity p x"
proof -
  have p_not_unit: "\<not> is_unit p"
    by (rule prime_elem_not_unit[OF prime_imp_prime_elem[OF prime_p]])
  have x_nonzero: "x \<noteq> 0" using positive by simp
  show ?thesis
    using power_dvd_iff_le_multiplicity[OF x_nonzero p_not_unit, of k] .
qed

lemma padic_int_multiplicity_factor_unit:
  fixes p P :: int and k :: nat
  assumes prime_p: "prime p" and positive: "0 < P"
  shows "P = p ^ multiplicity p P * (P div p ^ multiplicity p P)"
    and "coprime (P div p ^ multiplicity p P) (p ^ k)"
proof -
  have p_not_unit: "\<not> is_unit p"
    by (rule prime_elem_not_unit[OF prime_imp_prime_elem[OF prime_p]])
  have P_nonzero: "P \<noteq> 0" using positive by simp
  have power_divides: "p ^ multiplicity p P dvd P"
    by (rule multiplicity_dvd)
  have power_remainder: "P mod p ^ multiplicity p P = 0"
    using power_divides by (simp add: dvd_eq_mod_eq_0)
  have factor:
    "P = p ^ multiplicity p P * (P div p ^ multiplicity p P)"
    using div_mult_mod_eq[of P "p ^ multiplicity p P"] power_remainder
    by (simp add: mult.commute)
  have no_extra_factor:
    "\<not> p dvd (P div p ^ multiplicity p P)"
    by (rule multiplicity_decompose[OF P_nonzero p_not_unit])
  have coprime:
    "coprime (P div p ^ multiplicity p P) (p ^ k)"
    by (rule prime_imp_power_coprime[OF prime_p no_extra_factor])
  show "P = p ^ multiplicity p P * (P div p ^ multiplicity p P)"
    by (rule factor)
  show "coprime (P div p ^ multiplicity p P) (p ^ k)"
    by (rule coprime)
qed

lemma padic_affine_quotient_threshold:
  fixes p P T A :: int and k :: nat
  assumes prime_p: "prime p" and P_positive: "0 < P" and T_positive: "0 < T"
    and affine: "P * T = A"
  shows "p ^ k dvd T \<longleftrightarrow>
    p ^ (k + multiplicity p P) dvd A"
proof -
  have p_elem: "prime_elem p" by (rule prime_imp_prime_elem[OF prime_p])
  have P_nonzero: "P \<noteq> 0" using P_positive by simp
  have T_nonzero: "T \<noteq> 0" using T_positive by simp
  have product_positive: "0 < P * T"
    by (rule mult_pos_pos[OF P_positive T_positive])
  have A_positive: "0 < A" using product_positive by (simp only: affine)
  have T_threshold:
    "p ^ k dvd T \<longleftrightarrow> k \<le> multiplicity p T"
    by (rule padic_int_power_dvd_iff_valuation[OF prime_p T_positive])
  have A_threshold:
    "p ^ (k + multiplicity p P) dvd A \<longleftrightarrow>
      k + multiplicity p P \<le> multiplicity p A"
    by (rule padic_int_power_dvd_iff_valuation[OF prime_p A_positive])
  have product_valuation:
    "multiplicity p A = multiplicity p P + multiplicity p T"
    using prime_elem_multiplicity_mult_distrib[OF p_elem P_nonzero T_nonzero]
      affine by simp
  have arithmetic:
    "k \<le> multiplicity p T \<longleftrightarrow>
      k + multiplicity p P \<le> multiplicity p P + multiplicity p T"
    by arith
  have A_product_threshold:
    "p ^ (k + multiplicity p P) dvd A \<longleftrightarrow>
      k + multiplicity p P \<le> multiplicity p P + multiplicity p T"
    using A_threshold by (simp only: product_valuation)
  show ?thesis
    using T_threshold A_product_threshold arithmetic by blast
qed

lemma padic_affine_quotient_residue:
  fixes p P T A :: int and k :: nat
  assumes prime_p: "prime p" and P_positive: "0 < P" and T_positive: "0 < T"
    and affine: "P * T = A"
  shows "T mod p ^ k =
    (A div p ^ multiplicity p P *
      modular_inverse (p ^ k) (P div p ^ multiplicity p P)) mod p ^ k"
proof -
  let ?a = "multiplicity p P"
  let ?q = "p ^ ?a"
  let ?u = "P div ?q"
  let ?m = "p ^ k"
  have factor_unit: "P = ?q * ?u \<and> coprime ?u ?m"
    using padic_int_multiplicity_factor_unit[OF prime_p P_positive] by blast
  then have factor: "P = ?q * ?u" and u_coprime: "coprime ?u ?m"
    by auto
  have q_positive: "0 < ?q"
    using prime_gt_0_int[OF prime_p] by simp
  have affine_factor: "A = ?q * (?u * T)"
  proof -
    have "A = P * T" by (rule affine[symmetric])
    also have "... = (?q * ?u) * T" by (rule arg_cong[OF factor])
    also have "... = ?q * (?u * T)" by (rule mult.assoc)
    finally show ?thesis .
  qed
  have exact_quotient: "A div ?q = ?u * T"
    using affine_factor q_positive by simp
  have inverse:
    "[?u * modular_inverse ?m ?u = 1] (mod ?m)"
    by (rule cong_modular_inverse1[OF u_coprime])
  have product_congruence:
    "[ (?u * modular_inverse ?m ?u) * T = 1 * T] (mod ?m)"
    by (rule cong_mult[OF inverse cong_refl])
  have quotient_congruence:
    "[A div ?q * modular_inverse ?m ?u = T] (mod ?m)"
    using product_congruence exact_quotient by (simp add: mult_ac)
  have reduced:
    "(A div ?q * modular_inverse ?m ?u) mod ?m = T mod ?m"
    using quotient_congruence by (simp add: cong_def)
  show ?thesis using reduced by simp
qed

lemma padic_affine_quotient_reduced_residue:
  fixes p P T L C :: int and w k :: nat
  assumes prime_p: "prime p" and P_positive: "0 < P" and T_positive: "0 < T"
    and L_positive: "0 < L" and affine: "P * T = L * 10 ^ w + C"
  shows "p ^ multiplicity p P dvd
      ((L * (10 ^ w mod p ^ (k + multiplicity p P)) + C) mod
        p ^ (k + multiplicity p P))"
    and "T mod p ^ k =
      ((((L * (10 ^ w mod p ^ (k + multiplicity p P)) + C) mod
          p ^ (k + multiplicity p P)) div p ^ multiplicity p P *
        modular_inverse (p ^ k) (P div p ^ multiplicity p P)) mod p ^ k)"
proof -
  let ?a = "multiplicity p P"
  let ?q = "p ^ ?a"
  let ?m = "p ^ k"
  let ?M = "p ^ (k + ?a)"
  let ?A = "L * 10 ^ w + C"
  let ?R = "(L * (10 ^ w mod ?M) + C) mod ?M"
  have base:
    "T mod ?m = (?A div ?q * modular_inverse ?m (P div ?q)) mod ?m"
    by (rule padic_affine_quotient_residue[OF prime_p P_positive T_positive affine])
  have q_positive: "0 < ?q"
    using prime_gt_0_int[OF prime_p] by simp
  have modulus_factor: "?M = ?q * ?m"
    unfolding power_add by (simp add: mult.commute)
  have factorization:
    "?A = ?q * (?A div ?q)"
  proof -
    have factor_unit: "P = ?q * (P div ?q) \<and>
        coprime (P div ?q) (p ^ k)"
      using padic_int_multiplicity_factor_unit[OF prime_p P_positive] by blast
    have P_factor: "P = ?q * (P div ?q)"
      using factor_unit by blast
    have A_factor: "?A = P * T" using affine by simp
    have product_factor: "?A = ?q * ((P div ?q) * T)"
    proof -
      have "?A = P * T" by (rule A_factor)
      also have "... = (?q * (P div ?q)) * T"
        by (rule arg_cong[OF P_factor])
      also have "... = ?q * ((P div ?q) * T)" by (rule mult.assoc)
      finally show ?thesis .
    qed
    have quotient: "?A div ?q = (P div ?q) * T"
      using product_factor q_positive by simp
    show ?thesis using product_factor quotient by simp
  qed
  have power_congruence: "[10 ^ w mod ?M = 10 ^ w] (mod ?M)"
    by simp
  have product_congruence:
    "[L * (10 ^ w mod ?M) = L * 10 ^ w] (mod ?M)"
    by (rule cong_mult[OF cong_refl power_congruence])
  have raw_congruence: "[L * (10 ^ w mod ?M) + C = ?A] (mod ?M)"
    using cong_add[OF product_congruence cong_refl] by simp
  have reduced_equal: "?R = ?A mod ?M"
    using raw_congruence by (simp add: cong_def)
  have reduced_factor: "?R = ?q * ((?A div ?q) mod ?m)"
  proof -
    have "?R = ?A mod (?q * ?m)"
      using reduced_equal by (simp only: modulus_factor)
    also have "... = (?q * (?A div ?q)) mod (?q * ?m)"
      by (rule arg_cong[OF factorization])
    also have "... = ?q * ((?A div ?q) mod ?m)"
      by (rule mod_mult_mult1)
    finally show ?thesis .
  qed
  have exact_reduced_quotient: "?R div ?q = (?A div ?q) mod ?m"
    using reduced_factor q_positive by simp
  have reduced_divisible: "?q dvd ?R"
    using reduced_factor by (auto simp: dvd_def)
  have residue:
    "T mod ?m = (?R div ?q * modular_inverse ?m (P div ?q)) mod ?m"
    using base exact_reduced_quotient
    by (simp add: mod_mult_left_eq)
  show "?q dvd ?R" by (rule reduced_divisible)
  show "T mod ?m =
      (?R div ?q * modular_inverse ?m (P div ?q)) mod ?m"
    by (rule residue)
qed

lemma padic_signed_affine_height_threshold:
  fixes p P T L C :: int and w k :: nat
  assumes prime_p: "prime p" and P_positive: "0 < P" and T_positive: "0 < T"
    and affine: "P * T = L * 10 ^ w + C"
  shows "p ^ k dvd T \<longleftrightarrow>
    p ^ (k + multiplicity p P) dvd (L * 10 ^ w + C)"
  by (rule padic_affine_quotient_threshold[OF prime_p P_positive T_positive affine])

lemma padic_signed_affine_height_residue:
  fixes p P T L C :: int and w k :: nat
  assumes prime_p: "prime p" and P_positive: "0 < P" and T_positive: "0 < T"
    and affine: "P * T = L * 10 ^ w + C"
  shows "T mod p ^ k =
    ((L * 10 ^ w + C) div p ^ multiplicity p P *
      modular_inverse (p ^ k) (P div p ^ multiplicity p P)) mod p ^ k"
  by (rule padic_affine_quotient_residue[OF prime_p P_positive T_positive affine])

lemma padic_int_two_valuation_ten:
  "multiplicity (2::int) 10 = 1"
proof -
  have prime_two: "prime (2::int)" by simp
  have prime_five: "prime (5::int)" by simp
  have elem_two: "prime_elem (2::int)" using prime_two by simp
  have product:
    "multiplicity (2::int) ((2::int) * 5) =
      multiplicity (2::int) 2 + multiplicity (2::int) 5"
    by (rule prime_elem_multiplicity_mult_distrib[OF elem_two]) simp_all
  have other: "multiplicity (2::int) 5 = 0"
    by (rule prime_multiplicity_other[OF prime_two prime_five]) simp
  show ?thesis using product other by simp
qed

lemma padic_int_five_valuation_ten:
  "multiplicity (5::int) 10 = 1"
proof -
  have prime_two: "prime (2::int)" by simp
  have prime_five: "prime (5::int)" by simp
  have elem_five: "prime_elem (5::int)" using prime_five by simp
  have product:
    "multiplicity (5::int) ((5::int) * 2) =
      multiplicity (5::int) 5 + multiplicity (5::int) 2"
    by (rule prime_elem_multiplicity_mult_distrib[OF elem_five]) simp_all
  have other: "multiplicity (5::int) 2 = 0"
    by (rule prime_multiplicity_other[OF prime_five prime_two]) simp
  show ?thesis using product other by simp
qed

lemma padic_two_five_have_unit_ten:
  fixes p :: int
  assumes p_case: "p = 2 \<or> p = 5"
  shows "prime p \<and> multiplicity p 10 = 1"
  using p_case padic_int_two_valuation_ten padic_int_five_valuation_ten by auto

lemma padic_affine_height_nonzero_constant_at_width:
  fixes p P L C T :: int and w :: nat
  assumes prime_p: "prime p" and ten_valuation: "multiplicity p 10 = 1"
    and P_positive: "0 < P" and L_positive: "0 < L" and C_nonzero: "C \<noteq> 0"
    and T_positive: "0 < T"
    and affine: "P * T = L * 10 ^ w + C"
    and width_bound: "multiplicity p (abs C) < w"
  shows "multiplicity p T + multiplicity p P = multiplicity p (abs C)"
proof -
  have p_elem: "prime_elem p" by (rule prime_imp_prime_elem[OF prime_p])
  have P_nonzero: "P \<noteq> 0" using P_positive by simp
  have C_abs_positive: "0 < abs C" using C_nonzero by simp
  have C_abs_nonzero: "abs C \<noteq> 0" using C_abs_positive by simp
  have power_valuation:
    "multiplicity p ((10::int) ^ w) = w"
    using prime_elem_multiplicity_power_distrib[OF p_elem, of "(10::int)"]
      ten_valuation by simp
  have X_positive: "0 < L * 10 ^ w" using L_positive by simp
  have X_valuation:
    "multiplicity p (L * 10 ^ w) = multiplicity p L + w"
    using prime_elem_multiplicity_mult_distrib[OF p_elem] L_positive
      power_valuation by simp
  have X_gt:
    "multiplicity p (abs C) < multiplicity p (L * 10 ^ w)"
    using X_valuation width_bound by arith
  let ?A = "P * T"
  let ?X = "L * 10 ^ w"
  let ?c = "abs C"
  have A_positive: "0 < ?A"
    using P_positive T_positive by simp
  have A_eq: "?A = ?X + C" using affine by simp
  have A_valuation:
    "multiplicity p ?A = multiplicity p ?c"
  proof (cases "0 < C")
    case True
    have C_eq: "C = ?c" using True by simp
    have sum_eq: "?A = ?X + ?c" using A_eq C_eq by simp
    have sum_valuation:
      "multiplicity p (?X + ?c) =
        min (multiplicity p ?X) (multiplicity p ?c)"
      by (rule multiplicity_sum_min)
        (use X_positive C_abs_positive X_gt in auto)
    show ?thesis using sum_eq sum_valuation X_gt by simp
  next
    case False
    have C_negative: "C < 0" using C_nonzero False by linarith
    have C_eq: "C = - ?c" using C_negative by simp
    have X_eq: "?X = ?A + ?c" using A_eq C_eq by arith
    show ?thesis
    proof (rule ccontr)
      assume not_equal: "multiplicity p ?A \<noteq> multiplicity p ?c"
      have sum_valuation:
        "multiplicity p (?A + ?c) =
          min (multiplicity p ?A) (multiplicity p ?c)"
        by (rule multiplicity_sum_min)
          (use A_positive C_abs_positive not_equal in auto)
      have "multiplicity p ?X \<le> multiplicity p ?c"
        using X_eq sum_valuation by simp
      with X_gt show False by arith
    qed
  qed
  have product_valuation:
    "multiplicity p ?A = multiplicity p P + multiplicity p T"
    using prime_elem_multiplicity_mult_distrib[OF p_elem P_nonzero]
      T_positive by simp
  show "multiplicity p T + multiplicity p P = multiplicity p (abs C)"
    using product_valuation A_valuation by (simp add: add.commute)
qed

lemma padic_affine_height_zero_constant_at_width:
  fixes p P L T :: int and w :: nat
  assumes prime_p: "prime p" and ten_valuation: "multiplicity p 10 = 1"
    and P_positive: "0 < P" and L_positive: "0 < L"
    and T_positive: "0 < T"
    and affine: "P * T = L * 10 ^ w"
  shows "multiplicity p T + multiplicity p P = multiplicity p L + w"
proof -
  have p_elem: "prime_elem p" by (rule prime_imp_prime_elem[OF prime_p])
  have P_nonzero: "P \<noteq> 0" using P_positive by simp
  have power_valuation: "multiplicity p ((10::int) ^ w) = w"
    using prime_elem_multiplicity_power_distrib[OF p_elem, of "(10::int)"]
      ten_valuation by simp
  have numerator_valuation:
    "multiplicity p (L * 10 ^ w) = multiplicity p L + w"
    using prime_elem_multiplicity_mult_distrib[OF p_elem] L_positive
      power_valuation by simp
  have product_valuation:
    "multiplicity p (P * T) = multiplicity p P + multiplicity p T"
    using prime_elem_multiplicity_mult_distrib[OF p_elem P_nonzero]
      T_positive by simp
  show "multiplicity p T + multiplicity p P =
      multiplicity p L + w"
    using affine product_valuation numerator_valuation
    by (simp add: add.commute)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms padic_int_power_dvd_iff_valuation padic_int_multiplicity_factor_unit
      padic_affine_quotient_threshold padic_affine_quotient_residue
      padic_affine_quotient_reduced_residue
      padic_signed_affine_height_threshold padic_signed_affine_height_residue
      padic_two_five_have_unit_ten
      padic_affine_height_nonzero_constant_at_width
      padic_affine_height_zero_constant_at_width})
    then () else error "Affine p-adic height transport depends on an oracle";
\<close>
end
