theory Special_Factor_Progressions
  imports "HOL-Number_Theory.Pocklington"
begin

text \<open>The transverse windows use arithmetic progressions forced by the
order of two modulo each prime divisor.  These lemmas discharge that admission
from the candidate and a prime-divisor hypothesis; no factor list occurs.
\<close>

lemma prime_modulus_order_dvd_minus_one:
  fixes q a :: nat
  assumes q: "prime q" and coprime: "coprime q a"
  shows "ord q a dvd q - 1"
  using order_divides_totient[OF coprime] q by (simp add: totient_prime)

lemma dvd_successor_imp_cong_predecessor:
  fixes q a :: nat
  assumes qpos: "0 < q" and factor: "q dvd Suc a"
  shows "[a = q - 1] (mod q)"
proof -
  have aq: "[Suc a = q] (mod q)"
  proof -
    have "[Suc a = 0] (mod q)" using factor by (simp add: cong_0_iff)
    moreover have "[q = 0] (mod q)" by (simp add: cong_0_iff)
    ultimately show ?thesis by (meson cong_sym cong_trans)
  qed
  have "[a + 1 = (q - 1) + 1] (mod q)" using aq qpos by simp
  then show ?thesis by (simp only: cong_add_rcancel_nat)
qed

lemma cong_predecessor_imp_successor_zero:
  fixes q a :: nat
  assumes qpos: "0 < q" and neg: "[a = q - 1] (mod q)"
  shows "[a + 1 = 0] (mod q)"
proof -
  have added: "[a + 1 = (q - 1) + 1] (mod q)"
    by (rule cong_add[OF neg cong_refl])
  have aq: "[a + 1 = q] (mod q)" using added qpos by simp
  have qzero: "[q = 0] (mod q)" by (simp add: cong_0_iff)
  show ?thesis by (rule cong_trans[OF aq qzero])
qed

lemma mersenne_prime_factor_order:
  fixes p q :: nat
  assumes p: "prime p" and q: "prime q" and factor: "q dvd 2 ^ p - 1"
  shows "ord q 2 = p"
proof -
  have ppos: "0 < p" using p by (simp add: prime_gt_0_nat)
  have qnot2: "q \<noteq> 2"
  proof
    assume "q = 2"
    with factor ppos show False by simp
  qed
  have two_prime: "prime (2::nat)" by simp
  have not_dvd_two: "\<not> q dvd 2"
    using q two_prime qnot2 by (metis primes_dvd_imp_eq)
  have coprime: "coprime q 2"
    by (rule prime_imp_coprime[OF q not_dvd_two])
  have power_one: "[2 ^ p = 1] (mod q)"
    using factor by (simp add: cong_altdef_nat)
  have order_dvd: "ord q 2 dvd p"
    by (rule iffD1[OF ord_divides power_one])
  have order_pos: "0 < ord q 2"
    using coprime by simp
  have order_not_one: "ord q 2 \<noteq> 1"
  proof
    assume one: "ord q 2 = 1"
    have "[2 = 1] (mod q)"
      using ord[of 2 q] one by simp
    then have "q dvd 1" by (simp add: cong_altdef_nat)
    with q show False by (simp add: prime_nat_iff)
  qed
  from p order_dvd have "ord q 2 = 1 \<or> ord q 2 = p"
    by (simp add: prime_nat_iff)
  with order_not_one order_pos show ?thesis by blast
qed

theorem mersenne_prime_factor_progression:
  fixes p q :: nat
  assumes p: "prime p" and podd: "odd p"
    and q: "prime q" and factor: "q dvd 2 ^ p - 1"
  shows "2 * p dvd q - 1"
proof -
  have order: "ord q 2 = p"
    by (rule mersenne_prime_factor_order[OF p q factor])
  have qnot2: "q \<noteq> 2"
  proof
    assume "q = 2"
    moreover have "0 < p" using p by (simp add: prime_gt_0_nat)
    ultimately show False using factor by simp
  qed
  have qgt2: "2 < q"
    using q qnot2 prime_ge_2_nat[OF q] by arith
  have qodd: "odd q" by (rule prime_odd_nat[OF q qgt2])
  have pdvd: "p dvd q - 1"
  proof -
    have two_prime: "prime (2::nat)" by simp
    have not_dvd_two: "\<not> q dvd 2"
      using q two_prime qnot2 by (metis primes_dvd_imp_eq)
    have "coprime q 2" by (rule prime_imp_coprime[OF q not_dvd_two])
    then have "ord q 2 dvd q - 1"
      by (rule prime_modulus_order_dvd_minus_one[OF q])
    with order show ?thesis by simp
  qed
  have twodvd: "2 dvd q - 1" using qodd by simp
  have coprime: "coprime 2 p" using podd by simp
  show ?thesis
    by (rule divides_mult[OF twodvd pdvd coprime])
qed

text \<open>A fourth root of minus one supplies the extra Fermat factor of two
directly.  If @{term "x^4"} is minus one, then
@{term "(x^2+1)^2"} is congruent to @{term "2*x^2"}.  Fermat's theorem for
both nonzero residues at exponent @{term "q-1"} therefore makes two a
half-exponent root of one.  This avoids importing a quadratic-reciprocity
supplement.\<close>

lemma quartic_minus_one_forces_quadratic_two:
  fixes q x :: nat
  assumes q: "prime q" and qgt: "2 < q" and neg: "[x ^ 4 = q - 1] (mod q)"
  shows "[2 ^ ((q - 1) div 2) = 1] (mod q)"
proof -
  have qodd: "odd q" by (rule prime_odd_nat[OF q qgt])
  have xnonzero: "\<not> q dvd x"
  proof
    assume qx: "q dvd x"
    have "x dvd x ^ 4" by simp
    then have "q dvd x ^ 4" by (rule dvd_trans[OF qx])
    then have zero: "[x ^ 4 = 0] (mod q)" by (simp add: cong_0_iff)
    have impossible: "[q - 1 = 0] (mod q)"
      using cong_sym[OF neg] zero by (rule cong_trans)
    have "q - 1 = 0"
      by (rule cong_less_imp_eq_nat[OF _ _ _ _ impossible])
        (use qgt in simp_all)
    with qgt show False by simp
  qed
  let ?y = "x ^ 2 + 1"
  have ynonzero: "\<not> q dvd ?y"
  proof
    assume qy: "q dvd ?y"
    have "?y dvd ?y ^ 2" by simp
    then have "q dvd ?y ^ 2" by (rule dvd_trans[OF qy])
    then have zero: "[?y ^ 2 = 0] (mod q)" by (simp add: cong_0_iff)
    have square_neg: "[x ^ 4 + 1 = 0] (mod q)"
      by (rule cong_predecessor_imp_successor_zero[OF _ neg])
        (use qgt in simp)
    have alg: "?y ^ 2 = 2 * x ^ 2 + (x ^ 4 + 1)"
      by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
    have total: "[2 * x ^ 2 + (x ^ 4 + 1) = 0] (mod q)"
      using zero alg by simp
    have drop: "[2 * x ^ 2 + (x ^ 4 + 1) = 2 * x ^ 2 + 0] (mod q)"
      by (rule cong_add[OF cong_refl square_neg])
    have dropped: "[2 * x ^ 2 = 2 * x ^ 2 + (x ^ 4 + 1)] (mod q)"
      using cong_sym[OF drop] by simp
    have "[2 * x ^ 2 = 0] (mod q)"
      using dropped total by (rule cong_trans)
    then have "q dvd 2 * x ^ 2" by (simp add: cong_0_iff)
    then have "q dvd 2 \<or> q dvd x"
      using prime_dvd_multD[OF q] prime_dvd_power[OF q] by blast
    moreover have "\<not> q dvd 2"
    proof
      assume "q dvd 2"
      then have "q \<le> 2" by (rule dvd_imp_le) simp
      with qgt show False by simp
    qed
    ultimately show False using xnonzero by blast
  qed
  have xf: "[x ^ (q - 1) = 1] (mod q)"
    by (rule fermat_theorem[OF q xnonzero])
  have yf: "[?y ^ (q - 1) = 1] (mod q)"
    by (rule fermat_theorem[OF q ynonzero])
  have square: "[?y ^ 2 = 2 * x ^ 2] (mod q)"
  proof -
    have alg: "?y ^ 2 = 2 * x ^ 2 + (x ^ 4 + 1)"
      by (simp add: power2_eq_square power4_eq_xxxx algebra_simps)
    have square_neg: "[x ^ 4 + 1 = 0] (mod q)"
      by (rule cong_predecessor_imp_successor_zero[OF _ neg])
        (use qgt in simp)
    have drop: "[2 * x ^ 2 + (x ^ 4 + 1) = 2 * x ^ 2 + 0] (mod q)"
      by (rule cong_add[OF cong_refl square_neg])
    have dropped: "[2 * x ^ 2 + (x ^ 4 + 1) = 2 * x ^ 2] (mod q)"
      using drop by simp
    have rewrite: "[?y ^ 2 = 2 * x ^ 2 + (x ^ 4 + 1)] (mod q)"
      using alg by simp
    show ?thesis using rewrite dropped by (rule cong_trans)
  qed
  have twice_half: "2 * ((q - 1) div 2) = q - 1"
    using qodd by simp
  have raw: "[(?y ^ 2) ^ ((q - 1) div 2) =
      (2 * x ^ 2) ^ ((q - 1) div 2)] (mod q)"
    by (rule cong_pow[OF square])
  have left: "(?y ^ 2) ^ ((q - 1) div 2) = ?y ^ (q - 1)"
    using twice_half by (simp only: power_mult[symmetric])
  have right: "(2 * x ^ 2) ^ ((q - 1) div 2) =
      x ^ (q - 1) * 2 ^ ((q - 1) div 2)"
  proof -
    have "(2 * x ^ 2) ^ ((q - 1) div 2) =
        2 ^ ((q - 1) div 2) * (x ^ 2) ^ ((q - 1) div 2)"
      by (simp only: power_mult_distrib)
    also have "\<dots> = 2 ^ ((q - 1) div 2) *
        x ^ (2 * ((q - 1) div 2))"
      by (simp only: power_mult[symmetric])
    also have "\<dots> = 2 ^ ((q - 1) div 2) * x ^ (q - 1)"
      by (simp only: twice_half)
    also have "\<dots> = x ^ (q - 1) * 2 ^ ((q - 1) div 2)"
      by (simp only: mult.commute)
    finally show ?thesis .
  qed
  have powered: "[?y ^ (q - 1) =
      x ^ (q - 1) * 2 ^ ((q - 1) div 2)] (mod q)"
    using raw by (simp only: left right)
  have reduced: "[x ^ (q - 1) * 2 ^ ((q - 1) div 2) =
      2 ^ ((q - 1) div 2)] (mod q)"
    using cong_mult[OF xf cong_refl[of "2 ^ ((q - 1) div 2)" q]]
    by simp
  have "[?y ^ (q - 1) = 2 ^ ((q - 1) div 2)] (mod q)"
    by (rule cong_trans[OF powered reduced])
  with yf show ?thesis by (meson cong_sym cong_trans)
qed

lemma fermat_order_plus_quadratic_two_implies_progression:
  fixes n q :: nat
  assumes order: "ord q 2 = 2 ^ (n + 1)"
    and qodd: "odd q"
    and quadratic_two: "[2 ^ ((q - 1) div 2) = 1] (mod q)"
  shows "2 ^ (n + 2) dvd q - 1"
proof -
  have half: "2 ^ (n + 1) dvd (q - 1) div 2"
  proof -
    have "ord q 2 dvd (q - 1) div 2"
      by (rule iffD1[OF ord_divides quadratic_two])
    with order show ?thesis by simp
  qed
  then obtain k where k: "(q - 1) div 2 = 2 ^ (n + 1) * k" ..
  have even_minus: "even (q - 1)" using qodd by simp
  have "q - 1 = 2 * ((q - 1) div 2)"
    using even_minus by simp
  also have "\<dots> = 2 ^ (n + 2) * k"
    using k by (simp add: power_Suc ac_simps)
  finally have factorization: "q - 1 = 2 ^ (n + 2) * k" .
  show ?thesis unfolding dvd_def
    by (rule exI[of _ k]) (rule factorization)
qed

lemma fermat_prime_factor_order:
  fixes n q :: nat
  assumes n: "2 \<le> n" and q: "prime q"
    and factor: "q dvd 2 ^ (2 ^ n) + 1"
  shows "ord q 2 = 2 ^ (n + 1)"
proof -
  have qgt: "2 < q"
  proof -
    have odd_candidate: "odd (2 ^ (2 ^ n) + 1)" by simp
    have "q \<noteq> 2" using factor odd_candidate by auto
    with q prime_ge_2_nat[OF q] show ?thesis by arith
  qed
  have neg: "[2 ^ (2 ^ n) = q - 1] (mod q)"
    by (rule dvd_successor_imp_cong_predecessor)
      (use factor qgt in simp_all)
  have squared: "[2 ^ (2 ^ (n + 1)) = 1] (mod q)"
  proof -
    have raw: "[(2 ^ (2 ^ n)) ^ 2 = (q - 1) ^ 2] (mod q)"
      by (rule cong_pow[OF neg])
    have exponent: "(2::nat) ^ n * 2 = 2 ^ (n + 1)"
      by (simp add: power_Suc mult.commute)
    have left: "((2::nat) ^ (2 ^ n)) ^ 2 = 2 ^ (2 ^ (n + 1))"
      by (simp only: power_mult[symmetric] exponent)
    let ?k = "q - 2"
    have qeq: "q = ?k + 2" using qgt by simp
    have difference: "(q - 1) ^ 2 - 1 = q * (q - 2)"
      using qeq
      by (simp add: power2_eq_square algebra_simps)
    have dvd_difference: "q dvd (q - 1) ^ 2 - 1"
      using difference by simp
    have one_le: "1 \<le> (q - 1) ^ 2" using qgt by simp
    have right: "[(q - 1) ^ 2 = 1] (mod q)"
      using dvd_difference one_le by (simp add: cong_altdef_nat)
    have "[(2 ^ (2 ^ n)) ^ 2 = 1] (mod q)"
      by (rule cong_trans[OF raw right])
    with left show ?thesis by simp
  qed
  have order_dvd: "ord q 2 dvd 2 ^ (n + 1)"
    by (rule iffD1[OF ord_divides squared])
  have two_prime: "prime (2::nat)" by simp
  obtain i where i: "i \<le> n + 1" "ord q 2 = 2 ^ i"
    using order_dvd
      divides_primepow_nat[OF two_prime, of "ord q 2" "n+1"]
    by blast
  have not_half: "\<not> ord q 2 dvd 2 ^ n"
  proof
    assume "ord q 2 dvd 2 ^ n"
    then have "[2 ^ (2 ^ n) = 1] (mod q)"
      by (rule iffD2[OF ord_divides])
    with neg have impossible: "[q - 1 = 1] (mod q)"
      by (meson cong_sym cong_trans)
    have "q - 1 = 1"
      by (rule cong_less_imp_eq_nat[OF _ _ _ _ impossible])
        (use qgt in simp_all)
    with qgt show False by simp
  qed
  have "\<not> i \<le> n"
    using not_half i by (auto intro: le_imp_power_dvd)
  with i(1) have "i = n + 1" by arith
  with i(2) show ?thesis by simp
qed

theorem fermat_prime_factor_progression:
  fixes n q :: nat
  assumes n: "2 \<le> n" and q: "prime q"
    and factor: "q dvd 2 ^ (2 ^ n) + 1"
  shows "2 ^ (n + 2) dvd q - 1"
proof -
  have qgt: "2 < q"
  proof -
    have odd_candidate: "odd (2 ^ (2 ^ n) + 1)" by simp
    have "q \<noteq> 2" using factor odd_candidate by auto
    with q prime_ge_2_nat[OF q] show ?thesis by arith
  qed
  let ?x = "(2::nat) ^ (2 ^ (n - 2))"
  have nsplit: "n = (n - 2) + 2" using n by arith
  have exponent: "(4::nat) * 2 ^ (n - 2) = 2 ^ n"
  proof -
    have "(4::nat) * 2 ^ (n - 2) = 2 ^ 2 * 2 ^ (n - 2)" by simp
    also have "\<dots> = 2 ^ ((n - 2) + 2)"
      by (simp only: power_add mult.commute)
    also have "\<dots> = 2 ^ n" using nsplit by simp
    finally show ?thesis .
  qed
  have xfour: "?x ^ 4 = 2 ^ (2 ^ n)"
  proof -
    have "?x ^ 4 = 2 ^ (2 ^ (n - 2) * 4)"
      by (simp only: power_mult[symmetric])
    also have "\<dots> = 2 ^ (4 * 2 ^ (n - 2))"
      by (simp only: mult.commute)
    also have "\<dots> = 2 ^ (2 ^ n)" by (simp only: exponent)
    finally show ?thesis .
  qed
  have neg: "[?x ^ 4 = q - 1] (mod q)"
  proof -
    have candidate: "q dvd Suc (?x ^ 4)"
      using factor xfour by simp
    show ?thesis
      by (rule dvd_successor_imp_cong_predecessor[OF _ candidate])
        (use qgt in simp)
  qed
  have quadratic_two: "[2 ^ ((q - 1) div 2) = 1] (mod q)"
    by (rule quartic_minus_one_forces_quadratic_two[OF q qgt neg])
  have order: "ord q 2 = 2 ^ (n + 1)"
    by (rule fermat_prime_factor_order[OF n q factor])
  have qodd: "odd q" by (rule prime_odd_nat[OF q qgt])
  show ?thesis
    by (rule fermat_order_plus_quadratic_two_implies_progression
        [OF order qodd quadratic_two])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms prime_modulus_order_dvd_minus_one
      dvd_successor_imp_cong_predecessor
      cong_predecessor_imp_successor_zero
      mersenne_prime_factor_order mersenne_prime_factor_progression
      quartic_minus_one_forces_quadratic_two
      fermat_order_plus_quadratic_two_implies_progression
      fermat_prime_factor_order fermat_prime_factor_progression}) then ()
    else error "special factor progression proof depends on an oracle";
\<close>

end
