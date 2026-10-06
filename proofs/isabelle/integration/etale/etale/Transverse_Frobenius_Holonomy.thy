theory Transverse_Frobenius_Holonomy
  imports Special_Frobenius_Defect_Bridge Special_Factor_Progressions
    "HOL-Library.Discrete_Functions"
begin

text \<open>At every interior coordinate 1 \<le> k < N, the transverse
Frobenius difference has coefficient N choose k.  The helper below extends
the binomial residue to the two endpoints only to state the transport
identity uniformly; the difference polynomial itself has zero endpoint
coefficients.  This is the full interior coefficient germ, not the primary
carry jet.\<close>

definition transverse_coefficient :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "transverse_coefficient N k = (N choose k) mod N"

lemma binomial_neighbor_connection:
  fixes N k :: nat
  assumes "k < N"
  shows "Suc k * (N choose Suc k) + k * (N choose k) =
    N * (N choose k)"
proof (cases k)
  case 0
  then show ?thesis by simp
next
  case (Suc j)
  have Npos: "0 < N" using assms by simp
  have left: "Suc k * (N choose Suc k) = N * ((N-1) choose k)"
    by (rule binomial_absorption)
  have right: "k * (N choose k) = N * ((N-1) choose (k-1))"
    by (rule times_binomial_minus1_eq) (simp add: Suc)
  have split: "N choose k = ((N-1) choose (k-1)) + ((N-1) choose k)"
    by (rule choose_reduce_nat[OF Npos]) (simp add: Suc)
  have "Suc k * (N choose Suc k) + k * (N choose k) =
      N * ((N-1) choose k) + N * ((N-1) choose (k-1))"
    by (simp only: left right)
  also have "\<dots> =
      N * (((N-1) choose (k-1)) + ((N-1) choose k))"
    by (simp add: algebra_simps)
  also have "\<dots> = N * (N choose k)" by (simp only: split)
  finally show ?thesis .
qed

lemma transverse_coefficient_connection:
  fixes N k :: nat
  assumes N: "0 < N" and k: "k < N"
  shows "(Suc k * transverse_coefficient N (Suc k) +
      k * transverse_coefficient N k) mod N = 0"
proof -
  have raw: "(Suc k * (N choose Suc k) + k * (N choose k)) mod N = 0"
    using binomial_neighbor_connection[OF k] by simp
  have next_scaled:
      "(Suc k * transverse_coefficient N (Suc k)) mod N =
        (Suc k * (N choose Suc k)) mod N"
    unfolding transverse_coefficient_def by (rule mod_mult_cong) simp_all
  have current_scaled:
      "(k * transverse_coefficient N k) mod N =
        (k * (N choose k)) mod N"
    unfolding transverse_coefficient_def by (rule mod_mult_cong) simp_all
  have total:
      "(Suc k * transverse_coefficient N (Suc k) +
          k * transverse_coefficient N k) mod N =
        (Suc k * (N choose Suc k) + k * (N choose k)) mod N"
    by (rule mod_add_cong[OF next_scaled current_scaled])
  show ?thesis
    using total raw by simp
qed

text \<open>The progression window is represented extensionally.  It is exactly
the atoms 1+C*m above one and at or below the discrete square-root boundary;
no primality test or supplied factor occurs in its definition.\<close>

definition transverse_slots :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "transverse_slots N C =
    {q. 1 < q \<and> q \<le> floor_sqrt N \<and> C dvd q-1}"

definition transverse_holonomy :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "transverse_holonomy N C = (\<Prod>q\<in>transverse_slots N C. q)"

definition transverse_holonomy_residue :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "transverse_holonomy_residue N C = transverse_holonomy N C mod N"

definition transverse_indices :: "nat \<Rightarrow> nat \<Rightarrow> nat set" where
  "transverse_indices N C = {1..(floor_sqrt N - 1) div C}"

definition indexed_transverse_holonomy :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "indexed_transverse_holonomy N C =
    (\<Prod>m\<in>transverse_indices N C. 1 + C*m)"

lemma finite_transverse_slots [simp]: "finite (transverse_slots N C)"
proof -
  have "transverse_slots N C \<subseteq> {..floor_sqrt N}"
    by (auto simp: transverse_slots_def)
  then show ?thesis by (rule finite_subset) simp
qed

lemma transverse_slots_as_index_image:
  fixes N C :: nat
  assumes C: "0 < C"
  shows "transverse_slots N C =
    (\<lambda>m. 1 + C*m) ` transverse_indices N C"
proof
  show "transverse_slots N C \<subseteq>
      (\<lambda>m. 1 + C*m) ` transverse_indices N C"
  proof
    fix q assume slot: "q \<in> transverse_slots N C"
    then have qone: "1 < q" and qbound: "q \<le> floor_sqrt N"
      and dvd: "C dvd q-1"
      by (simp_all add: transverse_slots_def)
    obtain m where qm: "q - 1 = C*m" using dvd by (auto simp: dvd_def)
    have qeq: "q = 1 + C*m" using qone qm by arith
    have mone: "1 \<le> m"
    proof (rule ccontr)
      assume "\<not> 1 \<le> m"
      then have "m = 0" by simp
      with qeq qone show False by simp
    qed
    have product_bound: "m*C \<le> floor_sqrt N - 1"
      using qbound qeq by (simp add: mult.commute)
    have index_bound: "m \<le> (floor_sqrt N - 1) div C"
      using product_bound C
      by (simp add: less_eq_div_iff_mult_less_eq mult.commute)
    have "m \<in> transverse_indices N C"
      using mone index_bound by (simp add: transverse_indices_def)
    with qeq show "q \<in> (\<lambda>m. 1 + C*m) ` transverse_indices N C"
      by blast
  qed
  show "(\<lambda>m. 1 + C*m) ` transverse_indices N C
      \<subseteq> transverse_slots N C"
  proof
    fix q assume image: "q \<in>
      (\<lambda>m. 1 + C*m) ` transverse_indices N C"
    then obtain m where m: "m \<in> transverse_indices N C"
      and qeq: "q = 1 + C*m" by blast
    have mone: "1 \<le> m" and
      mbound: "m \<le> (floor_sqrt N - 1) div C"
      using m by (simp_all add: transverse_indices_def)
    have product_bound: "m*C \<le> floor_sqrt N - 1"
      using mbound C
      by (simp add: less_eq_div_iff_mult_less_eq)
    have product_pos: "0 < m*C" using mone C by simp
    have sqrt_pos: "0 < floor_sqrt N" using product_pos product_bound by arith
    have qone: "1 < q" using C mone qeq by simp
    have ordered_bound: "C*m \<le> floor_sqrt N - 1"
      using product_bound by (simp add: mult.commute)
    have qbound: "q \<le> floor_sqrt N"
      using ordered_bound sqrt_pos qeq by arith
    have "C dvd q-1" using qeq by simp
    with qone qbound show "q \<in> transverse_slots N C"
      by (simp add: transverse_slots_def)
  qed
qed

lemma transverse_holonomy_eq_indexed:
  fixes N C :: nat
  assumes C: "0 < C"
  shows "transverse_holonomy N C = indexed_transverse_holonomy N C"
proof -
  have inj: "inj_on (\<lambda>m. 1 + C*m) (transverse_indices N C)"
    using C by (auto simp: inj_on_def)
  have "(\<Prod>q\<in>(\<lambda>m. 1 + C*m) ` transverse_indices N C. q) =
      (\<Prod>m\<in>transverse_indices N C. 1 + C*m)"
    by (rule prod.image_eq[OF inj])
  then show ?thesis
    by (simp add: transverse_holonomy_def indexed_transverse_holonomy_def
        transverse_slots_as_index_image[OF C])
qed

lemma progression_prime_factor_is_transverse_slot:
  fixes N C q :: nat
  assumes "1 < q" "q^2 \<le> N" "C dvd q-1"
  shows "q \<in> transverse_slots N C"
  using assms by (simp add: transverse_slots_def le_floor_sqrt_iff)

lemma transverse_holonomy_units_iff:
  "coprime N (transverse_holonomy N C) \<longleftrightarrow>
    (\<forall>q\<in>transverse_slots N C. coprime N q)"
proof
  assume unit: "coprime N (transverse_holonomy N C)"
  show "\<forall>q\<in>transverse_slots N C. coprime N q"
  proof (intro ballI)
    fix q assume slot: "q \<in> transverse_slots N C"
    have qH: "q dvd transverse_holonomy N C"
      unfolding transverse_holonomy_def
      by (rule dvd_prodI[OF finite_transverse_slots slot])
    show "coprime N q"
      by (rule coprime_divisors[OF dvd_refl qH unit])
  qed
next
  assume all: "\<forall>q\<in>transverse_slots N C. coprime N q"
  show "coprime N (transverse_holonomy N C)"
    unfolding transverse_holonomy_def
    by (rule prod_coprime_right) (use all in auto)
qed

lemma transverse_residue_unit_iff:
  assumes "0 < N"
  shows "coprime N (transverse_holonomy_residue N C) \<longleftrightarrow>
    coprime N (transverse_holonomy N C)"
  using assms by (simp add: transverse_holonomy_residue_def)

theorem transverse_holonomy_prime_criterion:
  fixes N C :: nat
  assumes N: "1 < N"
    and progression_complete:
      "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow> C dvd q-1"
  shows "prime N \<longleftrightarrow> coprime N (transverse_holonomy N C)"
proof
  assume prime: "prime N"
  show "coprime N (transverse_holonomy N C)"
    unfolding transverse_holonomy_def
  proof (rule prod_coprime_right)
    fix q assume slot: "q \<in> transverse_slots N C"
    then have q: "1 < q" "q^2 \<le> N"
      by (auto simp: transverse_slots_def le_floor_sqrt_iff)
    have "q < q^2"
      unfolding power2_eq_square by (rule n_less_n_mult_m) (use q(1) in auto)
    then have "q < N" using q(2) by arith
    then have "\<not> N dvd q" using N q(1) by (auto dest: dvd_imp_le)
    then show "coprime N q" by (rule prime_imp_coprime_nat[OF prime])
  qed
next
  assume unit: "coprime N (transverse_holonomy N C)"
  show "prime N"
  proof (rule ccontr)
    assume notprime: "\<not> prime N"
    have notlarge: "\<not> (\<forall>q. prime q \<longrightarrow> q dvd N \<longrightarrow> N < q*q)"
      using notprime all_prime_divisors_above_square_root[OF N] by blast
    then obtain q where q: "prime q" "q dvd N" "q*q \<le> N"
      by (auto simp: not_less)
    have qone: "1 < q" using q(1) by (rule prime_gt_1_nat)
    have slot: "q \<in> transverse_slots N C"
      by (rule progression_prime_factor_is_transverse_slot)
        (use q qone progression_complete[OF q(1,2)] in
          \<open>simp_all add: power2_eq_square\<close>)
    have qH: "q dvd transverse_holonomy N C"
      unfolding transverse_holonomy_def
      by (rule dvd_prodI[OF finite_transverse_slots slot])
    have "q=1" by (rule coprime_common_divisor_nat[OF unit q(2) qH])
    with qone show False by simp
  qed
qed

corollary transverse_holonomy_residue_prime_criterion:
  fixes N C :: nat
  assumes N: "1 < N"
    and progression_complete:
      "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow> C dvd q-1"
  shows "prime N \<longleftrightarrow>
    coprime N (transverse_holonomy_residue N C)"
  using transverse_holonomy_prime_criterion[OF assms]
    transverse_residue_unit_iff[of N C] N by simp

corollary transverse_holonomy_gcd_prime_bit:
  fixes N C :: nat
  assumes N: "1 < N"
    and progression_complete:
      "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow> C dvd q-1"
  shows "prime N \<longleftrightarrow>
    gcd N (transverse_holonomy_residue N C) = 1"
  using transverse_holonomy_residue_prime_criterion[OF assms]
  by (simp add: coprime_iff_gcd_eq_1)

theorem fermat_indexed_transverse_holonomy_prime_bit:
  fixes n :: nat
  assumes n: "2 \<le> n"
  defines "N \<equiv> 2 ^ (2 ^ n) + 1"
    and "C \<equiv> 2 ^ (n + 2)"
  shows "prime N \<longleftrightarrow>
    gcd (indexed_transverse_holonomy N C mod N) N = 1"
proof -
  have Nlarge: "1 < N" by (simp add: N_def)
  have Cpos: "0 < C" by (simp add: C_def)
  have progression: "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow> C dvd q-1"
    unfolding N_def C_def
    by (rule fermat_prime_factor_progression[OF n])
  have criterion: "prime N \<longleftrightarrow>
      gcd N (transverse_holonomy_residue N C) = 1"
    by (rule transverse_holonomy_gcd_prime_bit[OF Nlarge progression])
  show ?thesis
    using criterion transverse_holonomy_eq_indexed[OF Cpos, of N]
    by (simp add: transverse_holonomy_residue_def gcd.commute)
qed

theorem mersenne_indexed_transverse_holonomy_prime_bit:
  fixes p :: nat
  assumes p: "prime p" and podd: "odd p"
  defines "N \<equiv> 2 ^ p - 1"
    and "C \<equiv> 2*p"
  shows "prime N \<longleftrightarrow>
    gcd (indexed_transverse_holonomy N C mod N) N = 1"
proof -
  have pge: "2 \<le> p" using prime_ge_2_nat[OF p] .
  have pne: "p \<noteq> 2"
  proof
    assume "p = 2"
    with podd show False by simp
  qed
  have pgt: "2 < p" using pge pne by arith
  obtain k where pk0: "p = Suc (2+k)"
    using pgt by (auto simp: less_iff_Suc_add)
  have pk: "p = 3+k" using pk0 by simp
  have powpos: "0 < (2::nat)^k" by simp
  have bound: "8 \<le> 8 * (2::nat)^k" using powpos by arith
  have Nform: "N = 8 * 2^k - 1" using pk
    by (simp add: N_def power_add)
  have Nlarge: "1 < N" using Nform bound by arith
  have Cpos: "0 < C" using p by (simp add: C_def prime_gt_0_nat)
  have progression: "\<And>q. prime q \<Longrightarrow> q dvd N \<Longrightarrow> C dvd q-1"
    unfolding N_def C_def
    by (rule mersenne_prime_factor_progression[OF p podd])
  have criterion: "prime N \<longleftrightarrow>
      gcd N (transverse_holonomy_residue N C) = 1"
    by (rule transverse_holonomy_gcd_prime_bit[OF Nlarge progression])
  show ?thesis
    using criterion transverse_holonomy_eq_indexed[OF Cpos, of N]
    by (simp add: transverse_holonomy_residue_def gcd.commute)
qed

theorem nonunit_holonomy_has_ring_annihilator:
  fixes N H :: nat
  assumes N: "1 < N" and nonunit: "1 < gcd N H"
  shows "0 < N div gcd N H" "N div gcd N H < N"
    "(H * (N div gcd N H)) mod N = 0"
proof -
  let ?g = "gcd N H"
  let ?a = "N div ?g"
  have gdvdN: "?g dvd N" by simp
  have gdvdH: "?g dvd H" by simp
  have Nfactor: "?g * (N div ?g) = N"
    by (rule dvd_mult_div_cancel[OF gdvdN])
  have ga: "?g * ?a = N" using Nfactor by simp
  have apos: "0 < ?a"
  proof (rule ccontr)
    assume "\<not> 0 < ?a"
    then have "?a = 0" by simp
    with ga N show False by simp
  qed
  show "0 < ?a" by (rule apos)
  have "1*?a < ?g*?a"
    by (rule mult_strict_right_mono) (use nonunit apos in simp_all)
  with ga show "?a < N" by simp
  obtain k where Hfactor: "H = ?g*k" using gdvdH by (auto simp: dvd_def)
  have "H*?a = (?g*k)*?a" using Hfactor by simp
  also have "\<dots> = (?g*?a)*k" by (simp add: mult.assoc mult.commute)
  also have "\<dots> = N*k" using Nfactor by simp
  finally have "H*?a = N*k" .
  then show "(H*?a) mod N = 0" by simp
qed

theorem transverse_nonunit_slot_prints_factor:
  fixes N C q :: nat
  assumes N: "1 < N" and slot: "q \<in> transverse_slots N C"
    and nonunit: "\<not> coprime N q"
  shows "1 < gcd N q" "gcd N q < N"
    "N = gcd N q * (N div gcd N q)" "\<not> prime N"
proof -
  have qone: "1 < q"
    using slot by (simp add: transverse_slots_def)
  have qsq: "q^2 \<le> N"
    using slot by (simp add: transverse_slots_def le_floor_sqrt_iff)
  have qless: "q < N"
  proof -
    have "q < q^2"
      unfolding power2_eq_square by (rule n_less_n_mult_m) (use qone in auto)
    with qsq show ?thesis by arith
  qed
  have gpos: "0 < gcd N q" using N qone by simp
  have gone: "gcd N q \<noteq> 1"
    using nonunit by (simp add: coprime_iff_gcd_eq_1)
  have lower: "1 < gcd N q" using gpos gone by arith
  have "gcd N q \<le> q"
    by (rule dvd_imp_le[OF gcd_dvd2]) (use qone in arith)
  then have upper: "gcd N q < N" using qless by arith
  show proper: "1 < gcd N q" "gcd N q < N"
    using lower upper by simp_all
  show "N = gcd N q * (N div gcd N q)"
    by (rule coefficient_gcd_prints_exact_factor[OF proper])
  show "\<not> prime N"
    by (rule coefficient_gcd_prints_exact_factor[OF proper])
qed

theorem transverse_prime_pole_prints_factor:
  fixes N C q :: nat
  assumes N: "1 < N" and qp: "prime q" and qN: "q dvd N"
    and slot: "q \<in> transverse_slots N C"
  shows "1 < gcd N q" "gcd N q < N"
    "N = gcd N q * (N div gcd N q)" "\<not> prime N"
proof -
  have qone: "1 < q" using qp by (rule prime_gt_1_nat)
  have qsq: "q^2 \<le> N"
    using slot by (simp add: transverse_slots_def le_floor_sqrt_iff)
  have qless: "q < N"
  proof -
    have "q < q^2"
      unfolding power2_eq_square by (rule n_less_n_mult_m) (use qone in auto)
    with qsq show ?thesis by arith
  qed
  have gcd: "gcd N q = q" using qN by simp
  show proper: "1 < gcd N q" "gcd N q < N" using qone qless gcd by simp_all
  show "N = gcd N q * (N div gcd N q)"
    by (rule coefficient_gcd_prints_exact_factor[OF proper])
  show "\<not> prime N"
    by (rule coefficient_gcd_prints_exact_factor[OF proper])
qed

text \<open>The whole-window gcd need not be proper: different slots may cover
all prime components of N.  A SPLIT result therefore descends the product tree
to a nonunit leaf (or subinterval) and applies the theorem above.  The present
definitions enumerate the square-root window.  No theorem here supplies the
remaining compact-shadow-to-transverse-germ construction, and the progression
completeness premise must be discharged by the Fermat or Mersenne factor-order
theorem rather than by factor enumeration.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms binomial_neighbor_connection transverse_coefficient_connection
      progression_prime_factor_is_transverse_slot
      transverse_holonomy_units_iff transverse_residue_unit_iff
      transverse_holonomy_prime_criterion
      transverse_holonomy_residue_prime_criterion
      transverse_holonomy_gcd_prime_bit
      transverse_slots_as_index_image transverse_holonomy_eq_indexed
      fermat_indexed_transverse_holonomy_prime_bit
      mersenne_indexed_transverse_holonomy_prime_bit
      nonunit_holonomy_has_ring_annihilator
      transverse_nonunit_slot_prints_factor
      transverse_prime_pole_prints_factor}) then ()
    else error "transverse Frobenius holonomy proof depends on an oracle";
\<close>

end
