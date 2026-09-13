theory Etale_Primality_Bridge
  imports Primary_Carry_Jet "HOL-Computational_Algebra.Primes"
begin

text \<open>These local-to-global equivalences prove what an all-local bit
means. They do not implement that bit by factoring the input or assume that a
finite carry jet separates it.\<close>

lemma prime_iff_all_prime_divisors_equal:
  fixes N :: nat
  assumes "1 < N"
  shows "prime N \<longleftrightarrow> (\<forall>q. prime q \<and> q dvd N \<longrightarrow> q=N)"
proof
  assume "prime N"
  then show "\<forall>q. prime q \<and> q dvd N \<longrightarrow> q=N"
    by (auto simp: prime_nat_iff)
next
  assume all: "\<forall>q. prime q \<and> q dvd N \<longrightarrow> q=N"
  obtain q where "prime q" "q dvd N"
    using prime_factor_nat[of N] assms by auto
  with all show "prime N" by auto
qed

lemma all_local_maximal_stride_iff_prime:
  fixes N :: nat
  assumes "1 < N"
  shows "prime N \<longleftrightarrow>
    (\<forall>q. prime q \<and> q dvd N \<longrightarrow> N-1 dvd q-1)"
proof
  assume "prime N"
  then show "\<forall>q. prime q \<and> q dvd N \<longrightarrow> N-1 dvd q-1"
    using prime_iff_all_prime_divisors_equal[OF assms] by auto
next
  assume all: "\<forall>q. prime q \<and> q dvd N \<longrightarrow> N-1 dvd q-1"
  have "q=N" if "prime q" "q dvd N" for q
  proof -
    have q: "1 < q" using that(1) by (rule prime_gt_1_nat)
    have upper: "q \<le> N" using that(2) assms by (intro dvd_imp_le) auto
    have lower: "N-1 \<le> q-1"
      using all that q by (intro dvd_imp_le) auto
    show ?thesis using upper lower assms by arith
  qed
  then show "prime N"
    using prime_iff_all_prime_divisors_equal[OF assms] by blast
qed

lemma all_prime_divisors_above_square_root:
  fixes N :: nat
  assumes N: "1 < N"
    and large: "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow> N < q*q"
  shows "prime N"
proof (rule ccontr)
  assume notprime: "\<not> prime N"
  obtain p where p: "prime p" "p dvd N"
    using prime_factor_nat[of N] N by auto
  have pp: "1 < p" using p(1) by (rule prime_gt_1_nat)
  have pne: "p \<noteq> N" using p(1) notprime by auto
  have ple: "p \<le> N" using p(2) N by (intro dvd_imp_le) auto
  have product: "p * (N div p) = N" using p(2) by (rule dvd_mult_div_cancel)
  have cofactor: "1 < N div p"
  proof (rule ccontr)
    assume "\<not> 1 < N div p"
    then have "N div p = 0 \<or> N div p = 1" by arith
    with product N pne show False by auto
  qed
  obtain r where r: "prime r" "r dvd (N div p)"
    using prime_factor_nat[of "N div p"] cofactor by auto
  have rdvd: "r dvd N" using dvd_mult[OF r(2), of p] product
    by (simp add: mult.commute)
  have both_raw: "p*r dvd p*(N div p)"
    by (intro mult_dvd_mono) (simp_all add: r(2))
  have both: "p*r dvd N" using both_raw by (simp only: product)
  have bound: "p*r \<le> N" using both N by (intro dvd_imp_le) auto
  have plarge: "N < p*p" by (rule large[OF p])
  have rlarge: "N < r*r" by (rule large[OF r(1) rdvd])
  show False
  proof (cases "p \<le> r")
    case True
    have "p*p \<le> p*r" using True by (intro mult_left_mono) auto
    with bound plarge show False by arith
  next
    case False
    have "r*r \<le> p*r" using False by (intro mult_right_mono) arith+
    with bound rlarge show False by arith
  qed
qed

theorem fermat_half_threshold_iff_prime:
  fixes B N :: nat
  assumes B: "0 < B" and N: "N = B*B+1"
  shows "prime N \<longleftrightarrow>
    (\<forall>q. prime q \<and> q dvd N \<longrightarrow> B dvd q-1)"
proof
  assume "prime N"
  then have only: "q=N" if "prime q" "q dvd N" for q
    using that prime_nat_iff by blast
  show "\<forall>q. prime q \<and> q dvd N \<longrightarrow> B dvd q-1"
  proof (intro allI impI)
    fix q assume q: "prime q \<and> q dvd N"
    have qN: "q=N" using only q by blast
    show "B dvd q-1" by (simp add: qN N)
  qed
next
  assume all: "\<forall>q. prime q \<and> q dvd N \<longrightarrow> B dvd q-1"
  have big: "1 < N" using B N by simp
  show "prime N"
  proof (rule all_prime_divisors_above_square_root[OF big])
    fix q assume q: "prime q" "q dvd N"
    have qp: "1 < q" using q(1) by (rule prime_gt_1_nat)
    have "B \<le> q-1" using all q qp by (intro dvd_imp_le) auto
    then have bound: "(B+1)*(B+1) \<le> q*q"
      using qp by (intro mult_mono) arith+
    have "N < (B+1)*(B+1)" using N B by (simp add: algebra_simps)
    with bound show "N < q*q" by arith
  qed
qed

theorem mersenne_half_threshold_iff_prime:
  fixes C N :: nat
  assumes C: "1 < C" and N: "N+1 = 2*C*C"
  shows "prime N \<longleftrightarrow>
    (\<forall>q. prime q \<and> q dvd N \<longrightarrow> 2*C dvd q-1 \<or> 2*C dvd q+1)"
proof
  assume "prime N"
  then have only: "q=N" if "prime q" "q dvd N" for q
    using that prime_nat_iff by blast
  show "\<forall>q. prime q \<and> q dvd N \<longrightarrow> 2*C dvd q-1 \<or> 2*C dvd q+1"
  proof (intro allI impI)
    fix q assume q: "prime q \<and> q dvd N"
    have qN: "q=N" using only q by blast
    have "2*C dvd N+1" using N by auto
    then show "2*C dvd q-1 \<or> 2*C dvd q+1" by (simp add: qN)
  qed
next
  assume all: "\<forall>q. prime q \<and> q dvd N \<longrightarrow> 2*C dvd q-1 \<or> 2*C dvd q+1"
  have Csquare: "4 \<le> C*C"
    using C by (intro mult_mono[of "2::nat" C 2 C, simplified]) arith+
  have big: "1 < N" using Csquare N by arith
  show "prime N"
  proof (rule all_prime_divisors_above_square_root[OF big])
    fix q assume q: "prime q" "q dvd N"
    have qp: "1 < q" using q(1) by (rule prime_gt_1_nat)
    have "2*C \<le> q+1"
      using all q qp dvd_imp_le[of "2*C" "q-1"]
        dvd_imp_le[of "2*C" "q+1"] by auto
    then have qbound: "2*(C-1)+1 \<le> q" using C by arith
    have bound: "(2*(C-1)+1)*(2*(C-1)+1) \<le> q*q"
      by (intro mult_mono[OF qbound qbound]) auto
    have cexpand: "C = (C-1)+1" using C by arith
    have positive: "0 < (C-1)*(C-1)" using C by simp
    have identity: "(2*(C-1)+1)*(2*(C-1)+1) + 1 =
        2*C*C + 2*((C-1)*(C-1))"
      proof -
      obtain k where Ck: "C = k+1" using C by (cases C) auto
      show ?thesis by (simp add: Ck algebra_simps)
    qed
    show "N < q*q" using identity positive N bound by arith
  qed
qed

text \<open>A coefficient gcd is a proper factor only on the proper-gcd
branch. Neither gcd=1 nor gcd=N claims successful factor printing.\<close>

theorem coefficient_gcd_prints_exact_factor:
  fixes N a :: nat
  assumes proper: "1 < gcd N a" "gcd N a < N"
  shows "N = gcd N a * (N div gcd N a)"
    and "1 < N div gcd N a"
    and "\<not> prime N"
proof -
  have product: "gcd N a * (N div gcd N a) = N"
    by (rule dvd_mult_div_cancel) simp
  then show "N = gcd N a * (N div gcd N a)" by simp
  show "1 < N div gcd N a"
  proof (rule ccontr)
    assume "\<not> 1 < N div gcd N a"
    then have "N div gcd N a = 0 \<or> N div gcd N a = 1" by arith
    then show False
    proof (elim disjE)
      assume zero: "N div gcd N a = 0"
      have "N=0" using product by (simp only: zero mult_zero_right)
      with proper show False by arith
    next
      assume one: "N div gcd N a = 1"
      have "gcd N a=N" using product by (simp only: one mult_1_right)
      with proper show False by arith
    qed
  qed
  show "\<not> prime N"
  proof
    assume "prime N"
    then have "gcd N a = 1 \<or> gcd N a = N"
      using gcd_dvd1[of N a] by (auto simp: prime_nat_iff)
    with proper show False by arith
  qed
qed

theorem nontrivial_etale_root_has_proper_gcd:
  fixes N D :: nat
  assumes modulus: "2 < N" and canonical: "0 < D" "D < N"
    and nonglobal: "D+2 \<noteq> N"
    and root: "N dvd D*(D+2)"
  shows "1 < gcd N D" "gcd N D < N"
proof -
  have not_one: "gcd N D \<noteq> 1"
  proof
    assume "gcd N D = 1"
    then have coprime: "coprime N D" by (simp add: coprime_iff_gcd_eq_1)
    have divides: "N dvd D+2"
      using root coprime_dvd_mult_left_iff[OF coprime, of "D+2"]
      by (simp add: mult.commute)
    obtain k where product: "D+2 = N*k" using divides by (elim dvdE)
    have nonzero: "k \<noteq> 0"
    proof
      assume "k=0"
      then have "D+2=0" using product by simp
      then show False by arith
    qed
    have small: "D+2 < N*2" using canonical modulus by arith
    have "k < 2"
    proof (rule ccontr)
      assume "\<not> k<2"
      then have "N*2 \<le> N*k" by (intro mult_left_mono) auto
      with small product show False by arith
    qed
    with nonzero have "k=1" by arith
    with product nonglobal show False by simp
  qed
  have nonzero: "gcd N D \<noteq> 0" using modulus by auto
  with not_one show "1 < gcd N D" by arith
  have not_full: "gcd N D \<noteq> N"
  proof
    assume equal: "gcd N D = N"
    have "N dvd D" using gcd_dvd2[of N D] by (simp only: equal)
    then have "N \<le> D" using canonical(1) by (rule dvd_imp_le)
    with canonical show False by arith
  qed
  have "gcd N D \<le> N" using modulus by simp
  with not_full show "gcd N D < N" by arith
qed

corollary nontrivial_etale_root_prints_factor:
  fixes N D :: nat
  assumes "2<N" "0<D" "D<N" "D+2\<noteq>N" "N dvd D*(D+2)"
  shows "N = gcd N D * (N div gcd N D)"
    "1 < gcd N D" "gcd N D < N" "1 < N div gcd N D" "\<not> prime N"
  using nontrivial_etale_root_has_proper_gcd[OF assms]
    coefficient_gcd_prints_exact_factor[of N D] by auto

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms all_local_maximal_stride_iff_prime all_prime_divisors_above_square_root
      fermat_half_threshold_iff_prime mersenne_half_threshold_iff_prime
      coefficient_gcd_prints_exact_factor nontrivial_etale_root_has_proper_gcd
      nontrivial_etale_root_prints_factor}) then ()
    else error "Etale primality bridge depends on an oracle";
\<close>
end
