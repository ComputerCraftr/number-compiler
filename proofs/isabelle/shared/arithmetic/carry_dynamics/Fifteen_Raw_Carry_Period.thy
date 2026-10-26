theory Fifteen_Raw_Carry_Period
  imports "HOL-Number_Theory.Pocklington"
begin

text \<open>The raw radix-10 carry stream for multiplication by 15 reduces,
after the 5-primary transient, to the orbit of 15 on a power-of-two residue.
This theory proves the exact multiplicative order; a family occurrence must
still authenticate its source phase and the transition law before using the
period for a production action.\<close>

lemma raw15_dyadic_period_exact_aux:
  fixes q :: nat
  shows "q = 0 \<or>
    (2^(q+4) dvd ((15::nat)^(2^q) - 1) \<and>
      \<not> 2^(q+5) dvd ((15::nat)^(2^q) - 1))"
proof (induction q)
  case 0
  then show ?case by simp
next
  case (Suc q)
  show ?case
  proof (cases "q = 0")
    case True
    then show ?thesis by (simp add: power2_eq_square)
  next
    case False
    then have q_positive: "1 \<le> q" by simp
    have lower_divisor:
      "2^(q+4) dvd ((15::nat)^(2^q) - 1)"
      using Suc.IH False by auto
    have upper_not_divisor:
      "\<not> 2^(q+5) dvd ((15::nat)^(2^q) - 1)"
      using Suc.IH False by auto
    let ?x = "(15::nat)^(2^q)"
    have upper_not_divisor_x: "\<not> 2^(q+5) dvd ?x - 1"
      using upper_not_divisor by simp
    have x_positive: "1 \<le> ?x" by simp
    have x_odd: "odd ?x" by simp
    obtain b where x_repr: "?x = 2*b + 1"
      using x_odd by (rule oddE)
    have x_plus_one: "?x + 1 = 2 * (b + 1)"
      using x_repr by (simp add: algebra_simps)
    have x_minus_one: "?x - 1 = 2 * b"
      using x_repr by simp
    obtain a where x_minus_factor:
      "?x - 1 = 2^(q+4) * a"
      using lower_divisor by (rule dvdE)
    have exponent_step: "(2::nat)^(q+5) = (2::nat)^(q+4) * 2"
    proof -
      have exponent: "q+5 = Suc (q+4)" by simp
      have "(2::nat)^(q+5) = (2::nat)^Suc (q+4)"
        by (simp only: exponent)
      also have "... = (2::nat)^(q+4) * 2"
        by (simp only: power_Suc)
      finally show ?thesis .
    qed
    have a_odd: "odd a"
    proof (rule ccontr)
      assume not_odd: "\<not> odd a"
      have "2 dvd a" using not_odd by simp
      then obtain c where a_factor: "a = 2*c" by (rule dvdE)
      have "2^(q+4) * 2 dvd (2^(q+4) * 2) * c"
        by (rule dvd_mult2) (rule dvd_refl)
      then have factor_divisor: "2^(q+4) * 2 dvd 2^(q+4) * a"
        using a_factor by (simp add: algebra_simps)
      have "2^(q+5) dvd 2^(q+4) * a"
        using factor_divisor exponent_step by simp
      then have factor_divisor_x: "2^(q+5) dvd ?x - 1"
        using x_minus_factor by simp
      from upper_not_divisor_x factor_divisor_x show False by blast
    qed
    have four_divides_x_minus_one: "4 dvd ?x - 1"
    proof -
      have "(2::nat)^2 dvd (2::nat)^(q+4)"
        using q_positive by (intro le_imp_power_dvd) simp
      then have "(2::nat)^2 dvd ?x - 1"
        using lower_divisor by (blast intro: dvd_trans)
      then show ?thesis by simp
    qed
    have two_divides_b: "2 dvd b"
    proof -
      have "(2::nat) * 2 dvd 2 * b"
        using four_divides_x_minus_one x_minus_one by simp
      then show ?thesis
        by (rule dvd_mult_cancel) simp
    qed
    have b_plus_one_odd: "odd (b + 1)"
      using two_divides_b by simp
    have square_minus_one:
      "?x^2 - 1 = (?x - 1) * (?x + 1)"
      using x_repr by (simp add: power2_eq_square algebra_simps)
    have exponent_double:
      "(2::nat)^(Suc q) = (2::nat)^q * 2"
      by (simp only: power_Suc)
    have powered_square:
      "(15::nat)^(2^(Suc q)) = ?x^2"
      by (simp only: exponent_double power_mult[symmetric])
    have successor_factor:
      "(15::nat)^(2^(Suc q)) - 1 = 2^(q+5) * (a * (b+1))"
    proof -
      have "(15::nat)^(2^(Suc q)) - 1 = ?x^2 - 1"
        by (simp only: powered_square)
      also have "... = (?x - 1) * (?x + 1)"
        by (rule square_minus_one)
      also have "... = (2^(q+4) * a) * (2 * (b+1))"
        by (simp only: x_minus_factor x_plus_one)
      also have "... = 2^(q+5) * (a * (b+1))"
        using exponent_step by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have successor_divisor:
      "2^(Suc q+4) dvd (15::nat)^(2^(Suc q)) - 1"
    proof -
      have exponent: "Suc q+4 = q+5" by simp
      have factored:
        "2^(Suc q+4) * (a*(b+1)) = (15::nat)^(2^(Suc q)) - 1"
        using successor_factor
        by (simp only: exponent successor_factor[symmetric])
      show ?thesis
        by (rule dvdI[where k="a*(b+1)"]) (rule factored[symmetric])
    qed
    have successor_not_divisor:
      "\<not> 2^(Suc q+5) dvd (15::nat)^(2^(Suc q)) - 1"
    proof
      assume divides:
        "2^(Suc q+5) dvd (15::nat)^(2^(Suc q)) - 1"
      have successor_exponent:
        "(2::nat)^(Suc q+5) = (2::nat)^(q+5) * 2"
      proof -
        have exponent: "Suc q+5 = Suc (q+5)" by simp
        have "(2::nat)^(Suc q+5) = (2::nat)^Suc (q+5)"
          by (simp only: exponent)
        also have "... = (2::nat)^(q+5) * 2"
          by (simp only: power_Suc)
        finally show ?thesis .
      qed
      have cancel_common:
        "2^(q+5) * 2 dvd 2^(q+5) * (a * (b+1))"
        using divides successor_factor successor_exponent by simp
      have "2 dvd a * (b+1)"
        using cancel_common by (rule dvd_mult_cancel) simp
      then show False using a_odd b_plus_one_odd by simp
    qed
    show ?thesis
      using successor_divisor successor_not_divisor by auto
  qed
qed

theorem raw15_dyadic_power_return:
  assumes "1 \<le> q"
  shows "[(15::nat)^((2::nat)^q) = 1] (mod (2::nat)^(q+4))"
proof -
  have divisor: "(2::nat)^(q+4) dvd (15::nat)^((2::nat)^q) - 1"
    using raw15_dyadic_period_exact_aux[of q] assms by auto
  have positive: "1 \<le> (15::nat)^((2::nat)^q)" by simp
  show ?thesis using divisor positive by (simp add: cong_altdef_nat)
qed

theorem raw15_dyadic_previous_power_not_return:
  assumes "1 \<le> q"
  shows "[(15::nat)^((2::nat)^(q-1)) \<noteq> 1]
    (mod (2::nat)^(q+4))"
proof (cases "q = 1")
  case True
  then show ?thesis by (simp add: cong_altdef_nat)
next
  case False
  then have q_minus_one_positive: "1 \<le> q - 1" using assms by simp
  have no_divisor:
    "\<not> (2::nat)^((q-1)+5) dvd (15::nat)^((2::nat)^(q-1)) - 1"
    using raw15_dyadic_period_exact_aux[of "q-1"] q_minus_one_positive
    by auto
  have positive: "1 \<le> (15::nat)^((2::nat)^(q-1))" by simp
  have q_decomposition: "q = Suc (q-1)" using assms by simp
  have exponent: "(q-1)+5 = q+4"
    using q_decomposition by simp
  have no_divisor_at_modulus:
    "\<not> (2::nat)^(q+4) dvd (15::nat)^((2::nat)^(q-1)) - 1"
    using no_divisor[unfolded exponent] .
  show ?thesis
    using no_divisor_at_modulus positive by (simp add: cong_altdef_nat)
qed

theorem raw15_dyadic_multiplicative_order:
  assumes q_positive: "1 \<le> q"
  shows "ord ((2::nat)^(q+4)) (15::nat) = (2::nat)^q"
proof -
  have return: "[(15::nat)^((2::nat)^q) = 1]
    (mod (2::nat)^(q+4))"
    by (rule raw15_dyadic_power_return[OF q_positive])
  have order_divisor:
    "ord ((2::nat)^(q+4)) (15::nat) dvd (2::nat)^q"
    using return ord_divides by blast
  have prime_two: "prime (2::nat)" by simp
  have order_shape:
    "\<exists>i\<le>q. ord ((2::nat)^(q+4)) (15::nat) = (2::nat)^i"
    using divides_primepow_nat[OF prime_two,
      of "ord ((2::nat)^(q+4)) (15::nat)" q]
      order_divisor by blast
  obtain i where i_bound: "i \<le> q"
      and order_is_power: "ord ((2::nat)^(q+4)) (15::nat) = (2::nat)^i"
    using order_shape by blast
  have i_not_smaller: "\<not> i < q"
  proof
    assume i_lt: "i < q"
    have order_divides_half:
      "ord ((2::nat)^(q+4)) (15::nat) dvd (2::nat)^(q-1)"
    proof -
      have "(2::nat)^i dvd (2::nat)^(q-1)"
        using i_lt q_positive by (intro le_imp_power_dvd) simp
      then show ?thesis using order_is_power by simp
    qed
    have half_return:
      "[(15::nat)^((2::nat)^(q-1)) = 1]
        (mod (2::nat)^(q+4))"
      by (rule iffD2[OF ord_divides]) (rule order_divides_half)
    then show False
      using raw15_dyadic_previous_power_not_return[OF q_positive] by blast
  qed
  show ?thesis using i_bound i_not_smaller order_is_power by simp
qed

text \<open>The family-independent theorem now identifies the minimal eventual
binary residue clock. The 5-primary transient and the family-specific carry
word remain separate source/occurrence obligations.\<close>

theorem raw15_dyadic_minimal_order:
  fixes d :: nat
  assumes depth: "5 \<le> d"
  shows "ord (2^d) (15::nat) = 2^(d-4)"
proof -
  let ?q = "d - 4"
  have q_positive: "1 \<le> ?q" using depth by simp
  have exponent: "?q + 4 = d" using depth by simp
  show ?thesis
    using raw15_dyadic_multiplicative_order[OF q_positive]
    by (simp add: exponent)
qed

ML \<open>
  val checked = @{thms raw15_dyadic_power_return
    raw15_dyadic_previous_power_not_return
    raw15_dyadic_multiplicative_order raw15_dyadic_minimal_order};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Raw radix-15 period theorem depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped raw radix-15 period proof" else ();
\<close>

end
