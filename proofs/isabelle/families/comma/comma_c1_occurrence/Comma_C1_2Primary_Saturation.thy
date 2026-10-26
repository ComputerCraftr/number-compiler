theory Comma_C1_2Primary_Saturation
  imports Comma_C1_Entry_Chart_Refinement
begin

text \<open>
The fixed-sector return is evaluated before any occurrence headroom or
source-admission theorem is introduced.  The first lemma identifies the
50-step additive monodromy from the exact physical endpoint and the existing
finite-period displacement.
\<close>

lemma comma_c1_count50_is_half_period:
  fixes f x :: nat and C :: comma_c1_phase
  assumes sector: "1 \<le> f" "f \<le> 9" and suffix: "x \<le> 98"
  defines "C \<equiv> comma_c1_phase_of f x"
  shows "comma_finite_period f (x mod 10) =
      2 * comma_cycle_length f * comma_c1_count C 50"
proof -
  let ?L = "comma_cycle_length f"
  let ?P = "comma_finite_period f (x mod 10)"
  have admitted: "comma_c1_phase_admitted C"
    using comma_c1_phase_of_admitted[OF sector, of x]
    by (simp add: C_def)
  have closes: "10 dvd ?L * f"
    by (rule comma_cycle_length_admitted(2)[OF sector])
  have gpos: "0 < gcd f 10" by simp
  have gdvd: "gcd f 10 dvd 10" by simp
  obtain k where ten: "10 = gcd f 10 * k"
    using gdvd by (auto simp: dvd_def)
  have l_eq: "?L = k"
  proof -
    have divided: "10 div gcd f 10 = k"
      using arg_cong[OF ten, of "\<lambda>u::nat. u div gcd f 10"] gpos by simp
    show ?thesis by (simp only: comma_cycle_length_def divided)
  qed
  have l_dvd_10: "?L dvd 10"
  proof -
    have product: "10 = ?L * gcd f 10"
      using ten by (simp only: l_eq mult.commute)
    show ?thesis by (rule dvdI[OF product])
  qed
  have l_dvd_50: "?L dvd 50"
    using dvd_trans[OF l_dvd_10] by simp
  have block_split: "(50 div ?L) * ?L = 50"
  proof -
    have remainder: "50 mod ?L = 0" using l_dvd_50 by simp
    have balance: "(50 div ?L) * ?L + 50 mod ?L = 50"
      by (rule div_mult_mod_eq)
    show ?thesis using balance by (simp only: remainder add.right_neutral)
  qed
  have period_exact:
    "comma_period_displacement f (x mod 10) ?L = ?P"
    by (rule sym, rule comma_finite_period_refines[OF sector]) simp
  have disp_zero: "comma_period_displacement f (x mod 10) 0 = 0"
    by (simp add: comma_period_displacement_def)
  have disp50:
    "comma_period_displacement f (x mod 10) 50 = (50 div ?L) * ?P"
  proof -
    have repeated:
      "comma_period_displacement f (x mod 10)
          ((50 div ?L) * ?L + 0) =
        (50 div ?L) * comma_period_displacement f (x mod 10) ?L +
          comma_period_displacement f (x mod 10) 0"
      using comma_period_displacement_repeated[OF closes,
        of "x mod 10" "50 div ?L" 0] .
    show ?thesis
      using repeated block_split period_exact disp_zero by simp
  qed
  have iter50: "comma_c1_iter 50 C = C"
    by (rule comma_c1_iter_period50[OF admitted])
  have decode: "comma_c1_decode (c1_mod4 C) (c1_mod25 C) = x"
    using suffix by (simp add: C_def comma_c1_phase_of_def
      comma_c1_decode_residue)
  have sector_eq: "c1_sector C = f"
    by (simp add: C_def comma_c1_phase_of_def)
  have physical:
    "comma_fixed_iter f 50 x = 100 * comma_c1_count C 50 + x"
    using comma_c1_iter_physical[OF admitted, where H=0 and n=50]
      iter50 decode sector_eq
    by (simp del: comma_c1_count.simps)
  have displacement:
    "comma_fixed_iter f 50 x = x +
      comma_period_displacement f (x mod 10) 50"
    by (rule comma_fixed_iter_displacement)
  have count_equation:
    "100 * comma_c1_count C 50 = (50 div ?L) * ?P"
    using physical displacement disp50 by arith
  have multiplied:
    "50 * (2 * ?L * comma_c1_count C 50) = 50 * ?P"
  proof -
    have commuted: "?L * (50 div ?L) = 50"
      using block_split by (simp only: mult.commute)
    have "50 * (2 * ?L * comma_c1_count C 50) =
        ?L * (100 * comma_c1_count C 50)"
      by (simp del: comma_c1_count.simps add: algebra_simps)
    also have "... = ?L * ((50 div ?L) * ?P)"
      by (simp only: count_equation)
    also have "... = (?L * (50 div ?L)) * ?P"
      by (rule mult.assoc[symmetric])
    also have "... = 50 * ?P" by (simp only: commuted)
    finally show ?thesis .
  qed
  have period_equation:
    "2 * ?L * comma_c1_count C 50 = ?P"
    using multiplied by (simp del: comma_c1_count.simps)
  show ?thesis using period_equation by (simp add: mult.commute)
qed

lemma comma_c1_count50_quotient:
  fixes f x :: nat and C :: comma_c1_phase
  assumes sector: "1 \<le> f" "f \<le> 9" and suffix: "x \<le> 98"
  defines "C \<equiv> comma_c1_phase_of f x"
  shows "comma_c1_count C 50 =
    comma_finite_period f (x mod 10) div (2 * comma_cycle_length f)"
proof -
  have exact: "comma_finite_period f (x mod 10) =
      2 * comma_cycle_length f * comma_c1_count C 50"
    using comma_c1_count50_is_half_period[OF sector suffix]
    by (simp only: C_def)
  have positive: "0 < 2 * comma_cycle_length f"
    using comma_cycle_length_admitted(1)[OF sector] by simp
  show ?thesis using exact positive by (simp add: mult.commute)
qed

text \<open>
The count cocycle has a phase-independent 50-block increment along a
50-periodic orbit: shifting the starting phase only cyclically rotates the
same 50 summands.  This yields the exact gcd-selected additive period without
enumerating phases.
\<close>

lemma comma_c1_count_shift_50:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_count C (n + 50 * k) =
    comma_c1_count C n + k * comma_c1_count C 50"
proof -
  let ?D = "comma_c1_iter n C"
  have D_admitted: "comma_c1_phase_admitted ?D"
    by (rule comma_c1_iter_closed[OF admitted])
  have period: "comma_c1_iter 50 C = C"
    by (rule comma_c1_iter_period50[OF admitted])
  have shifted_block:
    "comma_c1_count ?D 50 = comma_c1_count C 50"
  proof -
    have left:
      "comma_c1_count C (n + 50) =
        comma_c1_count C n + comma_c1_count ?D 50"
      by (rule comma_c1_count_add)
    have right:
      "comma_c1_count C (50 + n) =
        comma_c1_count C 50 + comma_c1_count C n"
      using comma_c1_count_add[of C 50 n] period by simp
    have sums: "comma_c1_count C n + comma_c1_count ?D 50 =
        comma_c1_count C 50 + comma_c1_count C n"
    proof -
      have "comma_c1_count C n + comma_c1_count ?D 50 =
          comma_c1_count C (n + 50)" by (rule left[symmetric])
      also have "... = comma_c1_count C (50 + n)"
        by (simp only: add.commute)
      also have "... = comma_c1_count C 50 + comma_c1_count C n"
        by (rule right)
      finally show ?thesis .
    qed
    show ?thesis using sums by arith
  qed
  have cocycle:
    "comma_c1_count C (n + 50 * k) =
      comma_c1_count C n + comma_c1_count ?D (50 * k)"
    by (rule comma_c1_count_add)
  have blocks:
    "comma_c1_count ?D (50 * k) = k * comma_c1_count ?D 50"
    by (rule comma_c1_count_multiple50[OF D_admitted])
  show ?thesis using cocycle blocks shifted_block by simp
qed

lemma comma_c1_iter_shift_50:
  assumes admitted: "comma_c1_phase_admitted C"
  shows "comma_c1_iter (n + 50 * k) C = comma_c1_iter n C"
proof -
  let ?D = "comma_c1_iter n C"
  have D_admitted: "comma_c1_phase_admitted ?D"
    by (rule comma_c1_iter_closed[OF admitted])
  have period: "comma_c1_iter 50 ?D = ?D"
    by (rule comma_c1_iter_period50[OF D_admitted])
  have blocks: "comma_c1_iter (50 * k) ?D = ?D"
    by (rule comma_c1_iter_multiple50[OF period])
  show ?thesis
    using comma_c1_iter_add[of n "50 * k" C] blocks by simp
qed

lemma comma_c1_adaptive_50_period:
  fixes C :: comma_c1_phase and K m n :: nat
  assumes admitted: "comma_c1_phase_admitted C"
  defines "K \<equiv> comma_c1_count C 50"
    and "m \<equiv> 32 div gcd 32 K"
  shows "comma_c1_iter (n + 50 * m) C = comma_c1_iter n C \<and>
    comma_c1_count C (n + 50 * m) mod 32 =
      comma_c1_count C n mod 32"
proof -
  have gpos: "0 < gcd 32 K" by simp
  have gdiv32: "gcd 32 K dvd 32" by simp
  have gdivK: "gcd 32 K dvd K" by simp
  obtain a where a: "32 = gcd 32 K * a"
    using gdiv32 by (auto simp: dvd_def)
  obtain b where b: "K = gcd 32 K * b"
    using gdivK by (auto simp: dvd_def)
  have m_eq: "m = a"
  proof -
    have divided: "32 div gcd 32 K = a"
      using arg_cong[OF a, of "\<lambda>u::nat. u div gcd 32 K"] gpos by simp
    show ?thesis by (simp only: m_def divided)
  qed
  have multiple: "m * K = 32 * b"
  proof -
    have "m * K = m * (gcd 32 K * b)"
      by (rule arg_cong[OF b])
    also have "... = a * (gcd 32 K * b)" by (simp only: m_eq)
    also have "... = (gcd 32 K * a) * b"
      by (simp only: mult.assoc mult.commute mult.left_commute)
    also have "... = 32 * b" by (rule arg_cong[OF a[symmetric]])
    finally show ?thesis .
  qed
  have divisible: "32 dvd (m * K)"
    by (rule dvdI[OF multiple])
  have iter: "comma_c1_iter (n + 50 * m) C = comma_c1_iter n C"
    by (rule comma_c1_iter_shift_50[OF admitted])
  have count:
    "comma_c1_count C (n + 50 * m) = comma_c1_count C n + m * K"
    using comma_c1_count_shift_50[OF admitted, of n m]
    by (simp add: K_def)
  have residue:
    "comma_c1_count C (n + 50 * m) mod 32 =
      comma_c1_count C n mod 32"
  proof -
    have multiple_mod: "(m * K) mod 32 = 0" using divisible by simp
    have "comma_c1_count C (n + 50 * m) mod 32 =
        (comma_c1_count C n + m * K) mod 32" by (simp only: count)
    also have "... =
        (comma_c1_count C n mod 32 + (m * K) mod 32) mod 32"
      by (rule mod_add_eq[symmetric])
    also have "... = comma_c1_count C n mod 32"
      by (simp only: multiple_mod add_0_right mod_mod_trivial)
    finally show ?thesis .
  qed
  show ?thesis using iter residue by blast
qed

text \<open>
This packet-only lemma is the arithmetic bridge used for the concrete
\<open>q \<mapsto> q+924\<close> instance.  Its hypotheses are exactly the Euclidean
packet outputs: no source admission, selected headroom, or literal traversal
is assumed.  The separate Entry packet theorem supplies these equations.
\<close>

lemma comma_c1_entry_packet_shift:
  fixes P Q Q' R R' A A' delta g beta beta' t t' K K' E D :: nat
  assumes P_positive: "0 < P"
    and period_shift: "P dvd delta"
    and endpoint_shift: "A' = A + delta"
    and packet: "P * Q + R = A" "R < P"
    and packet': "P * Q' + R' = A'" "R' < P"
    and beta: "K + beta = E"
    and beta': "K' + beta' = E + D"
    and carry: "100 * beta = t + g + R"
    and carry': "100 * beta' = t' + g + R'"
    and t_bound: "t < 100" and t'_bound: "t' < 100"
  shows "R' = R \<and> beta' = beta \<and> t' = t \<and> K' = K + D"
proof -
  have delta_mod: "delta mod P = 0"
    using period_shift by (simp add: dvd_eq_mod_eq_0)
  have A_mod: "A mod P = R"
  proof -
    have "A mod P = (P * Q + R) mod P"
      by (rule arg_cong[OF packet(1)[symmetric]])
    also have "... = R" using packet(2) by simp
    finally show ?thesis .
  qed
  have A'_mod: "A' mod P = R'"
  proof -
    have "A' mod P = (P * Q' + R') mod P"
      by (rule arg_cong[OF packet'(1)[symmetric]])
    also have "... = R'" using packet'(2) by simp
    finally show ?thesis .
  qed
  have shifted_mod: "A' mod P = A mod P"
  proof -
    have "A' mod P = (A + delta) mod P"
      by (rule arg_cong[OF endpoint_shift])
    also have "... = (A mod P + delta mod P) mod P"
      by (rule mod_add_eq[symmetric])
    also have "... = A mod P" by (simp only: delta_mod add_0_right mod_mod_trivial)
    finally show ?thesis .
  qed
  have r_eq: "R' = R" using A_mod A'_mod shifted_mod by simp
  have t_beta_eq: "beta' = beta \<and> t' = t"
  proof -
    have mixed: "100 * beta + t' = 100 * beta' + t"
      using carry carry' r_eq by arith
    have beta_eq: "beta = beta'"
      using arg_cong[OF mixed, of "\<lambda>u::nat. u div 100"] t_bound t'_bound
      by simp
    have t_eq: "t' = t" using carry carry' r_eq beta_eq by arith
    show ?thesis using beta_eq t_eq by blast
  qed
  have k_eq: "K' = K + D"
    using beta beta' t_beta_eq by arith
  show ?thesis using r_eq t_beta_eq k_eq by blast
qed

lemma comma_nat_positive_product_split:
  fixes X Y :: nat
  assumes positive: "1 \<le> Y"
  shows "X * Y = X + X * (Y - 1)"
proof -
  have split: "Y = (Y - 1) + 1" using positive by arith
  have "X * Y = X * ((Y - 1) + 1)" by (rule arg_cong[OF split])
  also have "... = X * (Y - 1) + X"
    by (simp only: distrib_left mult_1_right)
  also have "... = X + X * (Y - 1)" by (rule add.commute)
  finally show ?thesis .
qed

lemma comma_nat_multiple32_predecessor:
  fixes M :: nat
  assumes positive: "0 < M" and divisible: "32 dvd M"
  shows "(M - 1) mod 32 = 31"
proof -
  obtain c where multiple: "M = 32 * c"
    using divisible by (auto simp only: dvd_def)
  have c_positive: "0 < c" using multiple positive by arith
  have predecessor: "M - 1 = 32 * (c - 1) + 31"
    using multiple c_positive by arith
  show ?thesis using predecessor by simp
qed

lemma comma_c1_entry_924_period_divides_delta:
  fixes f x q :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and width: "5 \<le> q" and suffix: "x \<le> 98"
  shows "comma_finite_period f (x mod 10) dvd
      (10 ^ q * (10 ^ 924 - 1))"
proof -
  let ?P = "comma_finite_period f (x mod 10)"
  have catalog: "?P \<in> comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format,
      of f "x mod 10"] sector
    by (auto simp: comma_cycle_displacements_def)
  have periodic: "(10::nat) ^ (q + 924) mod ?P = 10 ^ q mod ?P"
    by (rule comma_power_period_924[OF catalog width])
  have exponent_order: "q \<le> q + 924" by arith
  have power_order: "(10::nat) ^ q \<le> 10 ^ (q + 924)"
    by (rule power_increasing[OF exponent_order]) simp
  have power_difference:
    "(10::nat) ^ (q + 924) - 10 ^ q = 10 ^ q * (10 ^ 924 - 1)"
    by (simp only: power_add diff_mult_distrib2 mult_1_right)
  have dvd_difference: "?P dvd (10 ^ (q + 924) - 10 ^ q)"
    using periodic power_order by (simp add: mod_eq_dvd_iff_nat)
  show ?thesis using dvd_difference by (simp only: power_difference)
qed

text \<open>
Applying the exact Euclidean packet at widths \<open>q\<close> and \<open>q+924\<close>
reduces saturation to the previous packet-shift lemma.  This statement is
deliberately about the closed Entry driver: its only inputs are the fixed
sector, suffix, and lower width.  It does not require \<open>comma_finite_headroom\<close>
or \<open>comma_c1_source_admitted\<close>.
\<close>

lemma comma_c1_entry_924_return_saturation:
  fixes f x q P L g Q0 Q1 R0 R1 K0 K1 t0 t1 b0 b1 :: nat
    and C :: comma_c1_phase
  assumes sector: "1 \<le> f" "f \<le> 9"
    and width: "5 \<le> q" and suffix: "x \<le> 98"
  defines "C \<equiv> comma_c1_phase_of f x"
    and "P \<equiv> comma_finite_period f (x mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "g \<equiv> 1 + comma_finite_guard_extra f"
    and "Q0 \<equiv> (10 ^ q - x - g) div P"
    and "Q1 \<equiv> (10 ^ (q + 924) - x - g) div P"
    and "R0 \<equiv> (10 ^ q - x - g) mod P"
    and "R1 \<equiv> (10 ^ (q + 924) - x - g) mod P"
    and "K0 \<equiv> comma_c1_count C (Q0 * L)"
    and "K1 \<equiv> comma_c1_count C (Q1 * L)"
    and "t0 \<equiv> comma_c1_decode
      (c1_mod4 (comma_c1_iter (Q0 * L) C))
      (c1_mod25 (comma_c1_iter (Q0 * L) C))"
    and "t1 \<equiv> comma_c1_decode
      (c1_mod4 (comma_c1_iter (Q1 * L) C))
      (c1_mod25 (comma_c1_iter (Q1 * L) C))"
    and "b0 \<equiv> 10 ^ (q - 2) - K0"
    and "b1 \<equiv> 10 ^ (q + 922) - K1"
  shows "c1_target (comma_c1_return C (Q1 * L)) =
      c1_target (comma_c1_return C (Q0 * L))"
    and "K1 = K0 + 10 ^ (q - 2) * (10 ^ 924 - 1)"
    and "7 \<le> q \<Longrightarrow> K1 mod 32 = K0 mod 32"
    and "q = 5 \<Longrightarrow> (K1 - K0) mod 32 = 24"
    and "q = 6 \<Longrightarrow> (K1 - K0) mod 32 = 16"
proof -
  let ?delta = "(10::nat) ^ q * (10 ^ 924 - 1)"
  let ?deltaK = "(10::nat) ^ (q - 2) * (10 ^ 924 - 1)"
  have width1: "5 \<le> q + 924" using width by arith
  have shifted_width: "q + 924 - 2 = q + 922" by arith
  have P_positive: "0 < P"
    using comma_finite_period_in_catalog[rule_format,
      of f "x mod 10"] sector
    by (auto simp: P_def comma_cycle_displacements_def)
  have packet0A: "P * Q0 + R0 = 10 ^ q - x - g"
    using comma_c1_entry_euclidean_packet(1)[OF sector width suffix]
    by (simp add: C_def P_def L_def g_def Q0_def R0_def)
  have packet0R: "R0 < P"
    using comma_c1_entry_euclidean_packet(2)[OF sector width suffix]
    by (simp add: P_def R0_def)
  have packet0K: "K0 + b0 = 10 ^ (q - 2)"
    using comma_c1_entry_euclidean_packet(5)[OF sector width suffix]
    by (simp add: C_def P_def L_def g_def Q0_def K0_def b0_def)
  have packet0B: "100 * b0 - t0 = g + R0"
    using comma_c1_entry_euclidean_packet(6)[OF sector width suffix]
    by (simp add: C_def P_def L_def g_def Q0_def K0_def
      t0_def R0_def b0_def)
  have t0_bound: "t0 < 100" by (simp add: t0_def comma_c1_decode_def)
  have b0_positive: "1 \<le> b0"
    using comma_c1_entry_euclidean_packet(4)[OF sector width suffix]
    by (simp add: C_def P_def L_def g_def Q0_def K0_def b0_def)

  have packet1A: "P * Q1 + R1 = 10 ^ (q + 924) - x - g"
    using comma_c1_entry_euclidean_packet(1)[OF sector width1 suffix]
    by (simp add: C_def P_def L_def g_def Q1_def R1_def)
  have packet1R: "R1 < P"
    using comma_c1_entry_euclidean_packet(2)[OF sector width1 suffix]
    by (simp add: P_def R1_def)
  have packet1K: "K1 + b1 = 10 ^ (q + 922)"
    using comma_c1_entry_euclidean_packet(5)[OF sector width1 suffix]
    by (simp only: C_def P_def L_def g_def Q1_def K1_def b1_def
      shifted_width)
  have packet1B: "100 * b1 - t1 = g + R1"
    using comma_c1_entry_euclidean_packet(6)[OF sector width1 suffix]
    by (simp only: C_def P_def L_def g_def Q1_def K1_def
      t1_def R1_def b1_def shifted_width)
  have t1_bound: "t1 < 100" by (simp add: t1_def comma_c1_decode_def)
  have b1_positive: "1 \<le> b1"
    using comma_c1_entry_euclidean_packet(4)[OF sector width1 suffix]
    by (simp only: C_def P_def L_def g_def Q1_def K1_def b1_def
      shifted_width)

  have delta_divides: "P dvd ?delta"
    using comma_c1_entry_924_period_divides_delta[OF sector width suffix]
    by (simp only: P_def)
  have fit: "x + g \<le> 10 ^ q"
  proof -
    have g_bound: "g \<le> 2"
      by (simp add: g_def comma_finite_guard_extra_def)
    have power_bound: "100000 \<le> (10::nat) ^ q"
      using power_increasing[OF width, of "10::nat"] by simp
    show ?thesis using suffix g_bound power_bound by arith
  qed
  have shifted_power:
    "10 ^ (q + 924) = 10 ^ q + ?delta"
  proof -
    have power: "(10::nat) ^ (q + 924) = 10 ^ q * 10 ^ 924"
      by (rule power_add)
    have large: "1 \<le> (10::nat) ^ 924" by (rule one_le_power) simp
    show ?thesis
      by (rule trans[OF power comma_nat_positive_product_split[OF large]])
  qed
  have endpoints: "10 ^ (q + 924) - x - g =
      (10 ^ q - x - g) + ?delta"
    using fit shifted_power by arith
  have deltaK_power:
    "10 ^ (q + 922) = 10 ^ (q - 2) + ?deltaK"
  proof -
    have exponent: "q + 922 = (q - 2) + 924" using width by arith
    have power: "(10::nat) ^ (q + 922) = 10 ^ (q - 2) * 10 ^ 924"
      by (simp only: exponent power_add)
    have large: "1 \<le> (10::nat) ^ 924" by (rule one_le_power) simp
    show ?thesis
      by (rule trans[OF power comma_nat_positive_product_split[OF large]])
  qed
  have balance0: "100 * b0 = t0 + g + R0"
    using packet0B b0_positive t0_bound by arith
  have balance1: "100 * b1 = t1 + g + R1"
    using packet1B b1_positive t1_bound by arith
  have packet1K_shift: "K1 + b1 = 10 ^ (q - 2) + ?deltaK"
    by (rule trans[OF packet1K deltaK_power])
  have packet_shift:
    "R1 = R0 \<and> b1 = b0 \<and> t1 = t0 \<and>
      K1 = K0 + ?deltaK"
    using comma_c1_entry_packet_shift[OF P_positive delta_divides endpoints
      packet0A packet0R packet1A packet1R packet0K packet1K_shift
      balance0 balance1 t0_bound t1_bound] .
  have admitted: "comma_c1_phase_admitted C"
    using comma_c1_phase_of_admitted[OF sector, of x]
    by (simp add: C_def)
  have iter0_admitted:
    "comma_c1_phase_admitted (comma_c1_iter (Q0 * L) C)"
    by (rule comma_c1_iter_closed[OF admitted])
  have iter1_admitted:
    "comma_c1_phase_admitted (comma_c1_iter (Q1 * L) C)"
    by (rule comma_c1_iter_closed[OF admitted])
  have sector0: "c1_sector (comma_c1_iter (Q0 * L) C) = f"
    by (simp add: C_def comma_c1_phase_of_def comma_c1_iter_sector)
  have sector1: "c1_sector (comma_c1_iter (Q1 * L) C) = f"
    by (simp add: C_def comma_c1_phase_of_def comma_c1_iter_sector)
  have phase0:
    "comma_c1_iter (Q0 * L) C = comma_c1_phase_of f t0"
    using comma_c1_phase_of_decode[OF iter0_admitted]
      sector0 by (simp add: t0_def)
  have phase1:
    "comma_c1_iter (Q1 * L) C = comma_c1_phase_of f t1"
    using comma_c1_phase_of_decode[OF iter1_admitted]
      sector1 by (simp add: t1_def)
  have suffix_eq: "t1 = t0" using packet_shift by blast
  show "c1_target (comma_c1_return C (Q1 * L)) =
      c1_target (comma_c1_return C (Q0 * L))"
    using phase0 phase1 suffix_eq
    by (simp add: comma_c1_return_def)
  show "K1 = K0 + ?deltaK" using packet_shift by blast
  have pow5: "32 dvd (10::nat) ^ 5" by simp
  show "7 \<le> q \<Longrightarrow> K1 mod 32 = K0 mod 32"
  proof -
    assume qbound: "7 \<le> q"
    have high_power_divides: "32 dvd (10::nat) ^ (q - 2)"
    proof -
      have exponent: "q - 2 = 5 + (q - 7)" using qbound by arith
      have split: "(10::nat) ^ (q - 2) = 10 ^ 5 * 10 ^ (q - 7)"
        by (simp only: exponent power_add)
      show ?thesis by (simp only: split) (rule dvd_mult2[OF pow5])
    qed
    have high_delta: "32 dvd ?deltaK"
      by (rule dvd_mult2[OF high_power_divides])
    have count_shift: "K1 = K0 + ?deltaK" using packet_shift by blast
    have delta_mod: "?deltaK mod 32 = 0"
      using high_delta by (simp only: dvd_eq_mod_eq_0)
    have "K1 mod 32 = (K0 + ?deltaK) mod 32"
      by (rule arg_cong[OF count_shift])
    also have "... = (K0 mod 32 + ?deltaK mod 32) mod 32"
      by (rule mod_add_eq[symmetric])
    also have "... = K0 mod 32"
      by (simp only: delta_mod add_0_right mod_mod_trivial)
    finally show "K1 mod 32 = K0 mod 32" .
  qed
  have exponent924: "(924::nat) = 5 + 919" by arith
  have power924: "(10::nat) ^ 924 = 10 ^ 5 * 10 ^ 919"
    by (simp only: exponent924 power_add)
  have pow924_divides: "32 dvd (10::nat) ^ 924"
    by (simp only: power924) (rule dvd_mult2[OF pow5])
  have positive924: "0 < (10::nat) ^ 924" by (rule zero_less_power) simp
  have predecessor_mod: "((10::nat) ^ 924 - 1) mod 32 = 31"
    by (rule comma_nat_multiple32_predecessor[OF positive924 pow924_divides])
  have delta_reduce:
    "?deltaK mod 32 =
      (10 ^ (q - 2) mod 32 * ((10 ^ 924 - 1) mod 32)) mod 32"
    by (rule mod_mult_eq[symmetric])
  show "q = 5 \<Longrightarrow> (K1 - K0) mod 32 = 24"
  proof -
    assume q5: "q = 5"
    have low_power: "(10::nat) ^ (q - 2) mod 32 = 8" using q5 by simp
    have delta_residue: "?deltaK mod 32 = 24"
    proof -
      have "?deltaK mod 32 = (8 * 31) mod 32"
        using delta_reduce by (simp only: low_power predecessor_mod)
      also have "... = 24" by simp
      finally show ?thesis .
    qed
    have count_shift: "K1 = K0 + ?deltaK" using packet_shift by blast
    show "(K1 - K0) mod 32 = 24"
      by (simp only: count_shift add_diff_cancel_left' delta_residue)
  qed
  show "q = 6 \<Longrightarrow> (K1 - K0) mod 32 = 16"
  proof -
    assume q6: "q = 6"
    have low_power: "(10::nat) ^ (q - 2) mod 32 = 16" using q6 by simp
    have delta_residue: "?deltaK mod 32 = 16"
    proof -
      have "?deltaK mod 32 = (16 * 31) mod 32"
        using delta_reduce by (simp only: low_power predecessor_mod)
      also have "... = 16" by simp
      finally show ?thesis .
    qed
    have count_shift: "K1 = K0 + ?deltaK" using packet_shift by blast
    show "(K1 - K0) mod 32 = 16"
      by (simp only: count_shift add_diff_cancel_left' delta_residue)
  qed
qed

ML \<open>
  val checked = @{thms comma_c1_count50_is_half_period comma_c1_count50_quotient
    comma_c1_count_shift_50 comma_c1_iter_shift_50
    comma_c1_adaptive_50_period comma_c1_entry_packet_shift
    comma_nat_positive_product_split comma_nat_multiple32_predecessor
    comma_c1_entry_924_period_divides_delta
    comma_c1_entry_924_return_saturation};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1 2-primary saturation lemmas depend on an oracle";
\<close>

end
