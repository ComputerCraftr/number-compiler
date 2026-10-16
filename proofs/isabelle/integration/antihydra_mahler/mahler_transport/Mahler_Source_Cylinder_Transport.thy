theory Mahler_Source_Cylinder_Transport
  imports "Mahler_Safety_Cylinders.Mahler_Safety_Ledger_Separation"
    "Antihydra.Antihydra_Family_Iteration"
begin

text \<open>Exact source/high-fiber and fractional-interval transport. The source
is the existing mahler_orbit. The guard includes the strict upper endpoint at
every time, rather than just membership in the unrestricted diamond tree.\<close>

definition fractional_endpoint :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> real" where
  "fractional_endpoint D n t = (of_nat D+t)*(3/2)^n - of_nat (mahler_orbit D n)"

definition cylinder_guard :: "nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> bool" where
  "cylinder_guard D n t \<longleftrightarrow>
    0 \<le> t \<and> t < 1/2 \<and> safe_prefix n (of_nat D+t)"

lemma mahler_orbit_add:
  "mahler_orbit D (m+n) = mahler_orbit (mahler_orbit D m) n"
  by (induct n) simp_all

lemma safe_prefix_split:
  "safe_prefix (m+n) x \<longleftrightarrow>
    safe_prefix m x \<and> safe_prefix n (x*(3/2)^m)"
proof
  assume all: "safe_prefix (m+n) x"
  have first: "safe_prefix m x"
    using all by (auto simp: safe_prefix_def)
  have second: "safe_prefix n (x*(3/2)^m)"
    unfolding safe_prefix_def
  proof (intro allI impI)
    fix j assume "j \<le> n"
    then have "frac (x*(3/2)^(m+j)) < 1/2"
      using all by (auto simp: safe_prefix_def)
    then show "frac ((x*(3/2)^m)*(3/2)^j) < 1/2"
      by (simp add: power_add mult.assoc)
  qed
  show "safe_prefix m x \<and> safe_prefix n (x*(3/2)^m)"
    using first second by blast
next
  assume parts: "safe_prefix m x \<and> safe_prefix n (x*(3/2)^m)"
  show "safe_prefix (m+n) x"
    unfolding safe_prefix_def
  proof (intro allI impI)
    fix j assume bound: "j \<le> m+n"
    show "frac (x*(3/2)^j) < 1/2"
    proof (cases "j \<le> m")
      case True
      then show ?thesis using parts by (auto simp: safe_prefix_def)
    next
      case False
      have eq: "j = m+(j-m)" using False by arith
      have "j-m \<le> n" using bound by arith
      then have "frac ((x*(3/2)^m)*(3/2)^(j-m)) < 1/2"
        using parts by (auto simp: safe_prefix_def)
      moreover have powers: "(3/2::real)^j = (3/2)^m*(3/2)^(j-m)"
        using eq power_add[of "3/2::real" m "j-m"] by metis
      ultimately show ?thesis by (simp only: powers mult.assoc)
    qed
  qed
qed

lemma guard_endpoint_bounds:
  assumes "cylinder_guard D n t"
  shows "0 \<le> fractional_endpoint D n t" "fractional_endpoint D n t < 1/2"
proof -
  have safe: "safe_prefix n (of_nat D+t)" and lo: "of_nat D \<le> (of_nat D::real)+t"
    and hi: "(of_nat D::real)+t < of_nat D+1/2"
    using assms by (auto simp: cylinder_guard_def)
  have bounds: "of_nat (mahler_orbit D n) \<le> (of_nat D+t)*(3/2)^n \<and>
      (of_nat D+t)*(3/2)^n < of_nat (mahler_orbit D n)+1/2"
    using safe_prefix_source_bounds[OF safe lo hi, of n] by simp
  then show "0 \<le> fractional_endpoint D n t" "fractional_endpoint D n t < 1/2"
    by (auto simp: fractional_endpoint_def)
qed

theorem source_guard_composition:
  "cylinder_guard D (m+n) t \<longleftrightarrow>
    cylinder_guard D m t \<and>
    cylinder_guard (mahler_orbit D m) n (fractional_endpoint D m t)"
proof -
  have transported: "of_nat (mahler_orbit D m) + fractional_endpoint D m t =
      (of_nat D+t)*(3/2)^m" by (simp add: fractional_endpoint_def)
  show ?thesis
    using guard_endpoint_bounds[of D m t]
    unfolding cylinder_guard_def transported safe_prefix_split by blast
qed

theorem fractional_endpoint_composition:
  "fractional_endpoint D (m+n) t =
    fractional_endpoint (mahler_orbit D m) n (fractional_endpoint D m t)"
  by (simp add: fractional_endpoint_def mahler_orbit_add power_add algebra_simps)

lemma dyadic_scale_transport:
  assumes "n \<le> N"
  shows "(2::real)^N*(3/2)^n = of_nat (2^(N-n)*3^n)"
proof -
  have eq: "N = (N-n)+n" using assms by arith
  have "(2::real)^N = 2^(N-n)*2^n" using eq by (metis power_add)
  then show ?thesis by (simp add: power_divide)
qed

theorem prefix_high_fiber_translation:
  fixes k :: nat
  shows "safe_prefix N (x + of_nat (2^N*k)) \<longleftrightarrow> safe_prefix N x"
proof -
  have exact: "(x + of_nat (2^N*k))*(3/2)^n =
      x*(3/2)^n + of_nat (k*2^(N-n)*3^n)" if "n \<le> N" for n
    using dyadic_scale_transport[OF that]
    by (simp add: of_nat_mult of_nat_power algebra_simps)
  have same: "frac ((x + of_nat (2^N*k))*(3/2)^n) = frac (x*(3/2)^n)"
    if "n \<le> N" for n
    by (simp only: exact[OF that] frac_nat_translate)
  show ?thesis unfolding safe_prefix_def using same by simp
qed

theorem guard_high_fiber_translation:
  "cylinder_guard (r + 2^N*k) N t \<longleftrightarrow> cylinder_guard r N t"
  using prefix_high_fiber_translation[of N "of_nat r+t" k]
  by (simp add: cylinder_guard_def algebra_simps)

theorem endpoint_high_fiber_translation:
  "fractional_endpoint (r + 2^N*k) N t = fractional_endpoint r N t"
proof -
  have orbit: "mahler_orbit (r + 2^N*k) N = mahler_orbit r N + k*3^N"
    using moving_source_cylinder[of N N r k] by (simp add: mult.commute)
  have scale: "(2::real)^N*(3/2)^N = 3^N" by (simp add: power_divide)
  show ?thesis unfolding fractional_endpoint_def orbit
    using scale by (simp add: of_nat_mult of_nat_power algebra_simps)
qed

text \<open>The centered Antihydra coordinate is the exact chart shift
\<open>a=D+1\<close>.  At a finite dyadic cylinder boundary that shift can wrap the
residue, so the carry into the high fiber is part of the chart.  These
definitions retain that carry explicitly; they do not assert an all-time
safety invariant.\<close>

definition centered_source_residue :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "centered_source_residue N r = (r+1) mod 2^N"

definition centered_source_high :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "centered_source_high N r k = k + (r+1) div 2^N"

lemma centered_source_residue_canonical:
  "centered_source_residue N r < 2^N"
  by (simp add: centered_source_residue_def)

lemma centered_source_chart_recombine:
  "centered_source_residue N r + 2^N * centered_source_high N r k =
    (r + 2^N*k) + 1"
proof -
  have decomposition:
    "(r+1) mod 2^N + (r+1) div 2^N * 2^N = r+1"
    by (rule mod_div_mult_eq)
  show ?thesis
    unfolding centered_source_residue_def centered_source_high_def
    using decomposition by (simp add: algebra_simps)
qed

theorem centered_finite_cylinder_conjugacy:
  assumes time: "n \<le> N"
  shows "antihydra_family_orbit
      (centered_source_residue N r + 2^N * centered_source_high N r k) n =
    mahler_orbit r n + 1 + k * 2^(N-n) * 3^n"
proof -
  have transported:
    "mahler_orbit (r + 2^N*k) n =
      mahler_orbit r n + k * 2^(N-n) * 3^n"
    using moving_source_cylinder[OF time, of r k] by (simp add: mult.commute)
  have chart:
    "centered_source_residue N r + 2^N * centered_source_high N r k =
      (r + 2^N*k)+1"
    by (rule centered_source_chart_recombine)
  have centered:
    "antihydra_family_orbit ((r + 2^N*k)+1) n =
      mahler_orbit (r + 2^N*k) n + 1"
    by (rule antihydra_family_centered_orbit)
  show ?thesis
    using chart centered transported by simp
qed

text \<open>This is the complete block bridge for arbitrary natural high fibers
and real fractional coordinates. The next residue is computed from the same
integer endpoint, not selected independently by a prime or carry observer.\<close>

theorem six_step_source_transport:
  "mahler_orbit (r+64*k) 6 = mahler_orbit r 6 + 729*k"
  "fractional_endpoint (r+64*k) 6 t = (729/64)*(of_nat r+t) - of_nat (mahler_orbit r 6)"
  "cylinder_guard (r+64*k) 6 t \<longleftrightarrow> cylinder_guard r 6 t"
  using moving_source_cylinder[of 6 6 r k]
    endpoint_high_fiber_translation[of r 6 k t]
    guard_high_fiber_translation[of r 6 k t]
  by (simp_all add: fractional_endpoint_def power_divide algebra_simps)

theorem fractional_step_diamond_action:
  "4 * fractional_endpoint D 1 t = (3/2)*(4*t) - 2*of_nat (D mod 2)"
  by (cases D rule: nat_mod_two_cases;
      simp add: fractional_endpoint_def mahler_D_step_def algebra_simps mod_Suc)


text \<open>The executable constructor checks the routing equation below after
solving its congruence. These rules preserve endpoint and complete prefix
admission, including empty intervals, for all represented high fibers.\<close>

definition executable_compose_lift ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "executable_compose_lift gain modulus endpoint residue inverse_residue =
    ((residue + modulus - endpoint mod modulus) * inverse_residue) mod modulus"

definition executable_compose_high ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "executable_compose_high gain modulus endpoint residue inverse_residue =
    (endpoint + gain * executable_compose_lift gain modulus endpoint residue inverse_residue
      - residue) div modulus"

definition executable_compose_checked ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "executable_compose_checked gain modulus endpoint residue inverse_residue \<longleftrightarrow>
    0 < modulus \<and> inverse_residue < modulus \<and>
    (gain * inverse_residue) mod modulus = 1 mod modulus \<and>
    residue \<le> endpoint + gain * executable_compose_lift gain modulus endpoint residue inverse_residue \<and>
    (endpoint + gain * executable_compose_lift gain modulus endpoint residue inverse_residue
      - residue) mod modulus = 0"

lemma executable_compose_route:
  assumes checked: "executable_compose_checked gain modulus endpoint residue inverse_residue"
  shows "endpoint + gain * executable_compose_lift gain modulus endpoint residue inverse_residue =
    residue + modulus * executable_compose_high gain modulus endpoint residue inverse_residue"
proof -
  let ?x = "endpoint + gain * executable_compose_lift gain modulus endpoint residue inverse_residue - residue"
  have le: "residue \<le> endpoint + gain * executable_compose_lift gain modulus endpoint residue inverse_residue"
    and zero: "?x mod modulus = 0"
    using checked by (auto simp: executable_compose_checked_def)
  have decomposition: "?x = modulus * (?x div modulus)"
    using mod_div_mult_eq[of ?x modulus] zero by (simp add: mult.commute)
  show ?thesis
    using le decomposition by (simp add: executable_compose_high_def; arith)
qed

definition strict_interval :: "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "strict_interval interval_lower interval_upper x \<longleftrightarrow>
    interval_lower \<le> x \<and> x < interval_upper"

definition executable_affine_pullback ::
    "real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real \<times> real" where
  "executable_affine_pullback pull_scale pull_offset interval_lower interval_upper =
    ((interval_lower-pull_offset)/pull_scale,
      (interval_upper-pull_offset)/pull_scale)"

lemma executable_strict_interval_pullback:
  fixes pull_scale pull_offset interval_lower interval_upper x :: real
  assumes positive: "0 < pull_scale"
  defines "pull_bounds \<equiv>
    executable_affine_pullback pull_scale pull_offset interval_lower interval_upper"
  shows "strict_interval interval_lower interval_upper (pull_scale*x+pull_offset) \<longleftrightarrow>
    strict_interval (fst pull_bounds) (snd pull_bounds) x"
  using positive
  by (auto simp: pull_bounds_def executable_affine_pullback_def strict_interval_def
      divide_le_eq less_divide_eq mult.commute)

theorem composed_source_endpoint:
  assumes route: "mahler_orbit r n + 3^n*l = s + 2^m*h"
  shows "mahler_orbit (r+2^n*l) (n+m) = mahler_orbit s m + 3^m*h"
proof -
  have first: "mahler_orbit (r+2^n*l) n = s+2^m*h"
    using moving_source_cylinder[of n n r l] route
    by (simp add: mult.commute)
  have "mahler_orbit (r+2^n*l) (n+m) = mahler_orbit (s+2^m*h) m"
    by (simp only: mahler_orbit_add first)
  also have "\<dots> = mahler_orbit s m + 3^m*h"
    using moving_source_cylinder[of m m s h] by (simp add: mult.commute)
  finally show ?thesis .
qed

theorem composed_source_guard:
  assumes route: "mahler_orbit r n + 3^n*l = s + 2^m*h"
  shows "cylinder_guard (r+2^n*l) (n+m) t \<longleftrightarrow>
    cylinder_guard r n t \<and> cylinder_guard s m (fractional_endpoint r n t)"
proof -
  have first: "mahler_orbit (r+2^n*l) n = s+2^m*h"
    using moving_source_cylinder[of n n r l] route
    by (simp add: mult.commute)
  show ?thesis
    by (simp only: source_guard_composition first guard_high_fiber_translation
      endpoint_high_fiber_translation)
qed

theorem executable_compose_endpoint:
  assumes checked:
      "executable_compose_checked (3^n) (2^m) (mahler_orbit r n) s inverse_residue"
  shows "mahler_orbit
      (r + 2^n * executable_compose_lift (3^n) (2^m) (mahler_orbit r n) s inverse_residue)
      (n+m) =
    mahler_orbit s m + 3^m *
      executable_compose_high (3^n) (2^m) (mahler_orbit r n) s inverse_residue"
  by (rule composed_source_endpoint)
    (rule executable_compose_route[OF checked])

theorem executable_compose_guard:
  assumes checked:
      "executable_compose_checked (3^n) (2^m) (mahler_orbit r n) s inverse_residue"
  shows "cylinder_guard
      (r + 2^n * executable_compose_lift (3^n) (2^m) (mahler_orbit r n) s inverse_residue)
      (n+m) t \<longleftrightarrow>
    cylinder_guard r n t \<and> cylinder_guard s m (fractional_endpoint r n t)"
  by (rule composed_source_guard)
    (rule executable_compose_route[OF checked])

lemma mahler_zero [simp]: "mahler_orbit 0 n = 0"
  by (induct n) (simp_all add: mahler_D_step_def)

lemma even_source_run:
  assumes "j \<le> k"
  shows "mahler_orbit (2^k*u) j = u*2^(k-j)*3^j"
  using moving_source_cylinder[OF assms, of 0 u]
  by (simp add: mult.commute)

lemma odd_events_append:
  "odd_events D (m+n) = odd_events D m +
    odd_events (mahler_orbit D m) n"
proof (induct n arbitrary: m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have shifted: "mahler_orbit D (m+n) = mahler_orbit (mahler_orbit D m) n"
    by (rule mahler_orbit_add)
  show ?case using Suc.hyps[of m] shifted by (simp add: algebra_simps)
qed

lemma ledger_at_append:
  "ledger_at D (m+n) = ledger_at D m +
    ledger_at (mahler_orbit D m) n"
  by (simp add: ledger_event_accounting odd_events_append algebra_simps)

lemma odd_events_dyadic_block_zero:
  "odd_events (2^k*u) k = 0"
proof (induct k arbitrary: u)
  case 0
  then show ?case by simp
next
  case (Suc k)
  have prefix: "odd_events (2^(Suc k)*u) k = 0"
    using Suc.hyps[of "2*u"] by (simp add: power_Suc algebra_simps)
  have endpoint:
    "mahler_orbit (2^(Suc k)*u) k = u*2^(Suc k-k)*3^k"
    by (rule even_source_run) simp
  have even_endpoint: "even (mahler_orbit (2^(Suc k)*u) k)"
    using endpoint by simp
  show ?case using prefix even_endpoint by simp
qed

text \<open>A source-selected odd event is one exact finite block.  If
3*D+1 = 2^(k+1)*u with odd u, the next odd seam is 3^k*u; the ledger
changes by 3-(k+1).  This bridge preserves the exponent supplied by the
source split and makes no claim that the next source selects the same
exponent.\<close>

theorem mahler_odd_event_block_refines_endpoint_and_ledger:
  assumes odd_source: "odd D"
      and split: "3*D+1 = 2^(Suc k)*u"
      and odd_u: "odd u"
  shows "mahler_orbit D (Suc k) = 3^k*u"
    and "odd (mahler_orbit D (Suc k))"
    and "odd_events D (Suc k) = 1"
    and "ledger_at D (Suc k) = 3 - int (Suc k)"
    and "3*mahler_orbit D (Suc k) =
      3^(Suc k)*(3*D+1) div 2^(Suc k)"
proof -
  have first: "mahler_D_step D = 2^k*u"
    using split by (simp add: mahler_D_step_def power_Suc algebra_simps)
  have tail: "mahler_orbit (2^k*u) k = u*2^(k-k)*3^k"
    by (rule even_source_run) simp
  have shifted: "mahler_orbit D (Suc k) =
      mahler_orbit (mahler_D_step D) k"
    by (rule mahler_orbit_shift)
  have endpoint: "mahler_orbit D (Suc k) = 3^k*u"
    using shifted first tail by (simp add: mult.commute)
  show "mahler_orbit D (Suc k) = 3^k*u" by (rule endpoint)
  have odd_endpoint: "odd (mahler_orbit D (Suc k))"
    using endpoint odd_u by simp
  show "odd (mahler_orbit D (Suc k))" by (rule odd_endpoint)

  have event_head: "odd_events D 1 = 1"
    using odd_source by (simp add: odd_iff_mod_2_eq_one)
  have event_split:
    "odd_events D (Suc k) = odd_events D 1 +
      odd_events (mahler_orbit D 1) k"
    using odd_events_append[of D 1 k] by simp
  have event_tail: "odd_events (mahler_orbit D 1) k = 0"
    using first odd_events_dyadic_block_zero[of k u] by simp
  have events: "odd_events D (Suc k) = 1"
    using event_split event_head event_tail by simp
  show "odd_events D (Suc k) = 1" by (rule events)

  have ledger: "ledger_at D (Suc k) = 3 - int (Suc k)"
    using ledger_event_accounting[of D "Suc k"] events by simp
  show "ledger_at D (Suc k) = 3 - int (Suc k)" by (rule ledger)

  have scaled_split:
    "3^(Suc k)*(3*D+1) = 2^(Suc k)*(3^(Suc k)*u)"
    using split by (simp add: algebra_simps)
  show "3*mahler_orbit D (Suc k) =
      3^(Suc k)*(3*D+1) div 2^(Suc k)"
    using endpoint scaled_split by (simp add: mult.commute)
qed

theorem mahler_odd_event_block_updates_ledger_at_seam:
  assumes odd_seam: "odd (mahler_orbit D m)"
      and split: "3*mahler_orbit D m+1 = 2^(Suc k)*u"
      and odd_u: "odd u"
  shows "ledger_at D (m+Suc k) =
    ledger_at D m + (3 - int (Suc k))"
proof -
  have block:
    "ledger_at (mahler_orbit D m) (Suc k) = 3 - int (Suc k)"
    using mahler_odd_event_block_refines_endpoint_and_ledger[
      OF odd_seam split odd_u] by blast
  show ?thesis
    using ledger_at_append[of D m "Suc k"] block by simp
qed

text \<open>The ledger sign test is the exact integer form of the q-divisibility
barrier.  Here `events` and `elapsed` are the occurrence coordinates before a
source-selected odd block; that block's exponent `a` is supplied by its exact
2-adic split.  The equivalence is arithmetic only and does not select a future
exponent or certify the next source word.\<close>

theorem mahler_ledger_q_divisibility_barrier_iff:
  assumes balance: "ledger = 3 * int events - int elapsed"
  shows "elapsed + exponent \<ge> 3 * events + 4 \<longleftrightarrow>
    ledger + 3 - int exponent < 0"
proof -
  have cast:
    "elapsed + exponent \<ge> 3 * events + 4 \<longleftrightarrow>
      int (3 * events + 4) \<le> int (elapsed + exponent)"
    by (simp only: of_nat_le_iff)
  show ?thesis
    using balance by (simp only: cast; simp; linarith)
qed

text \<open>A mixed odd-event word is a finite, source-selected list of exact
2-adic exponents.  Admission records the split at every successive odd seam;
it does not infer an exponent from a residue, harmonic class, or future
continuation.  The endpoint, elapsed width, event count, and ledger summary
are derived from that one supplied list.\<close>

fun mahler_odd_word_admitted :: "nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "mahler_odd_word_admitted D [] = True"
| "mahler_odd_word_admitted D (a#as) =
    (\<exists>k u. a = Suc k \<and> 3*D+1 = 2^(Suc k)*u \<and> odd u \<and>
      mahler_odd_word_admitted (3^k*u) as)"

fun mahler_odd_word_endpoint :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_odd_word_endpoint [] D = D"
| "mahler_odd_word_endpoint (a#as) D =
    mahler_odd_word_endpoint as (mahler_orbit D a)"

definition mahler_odd_word_span :: "nat list \<Rightarrow> nat" where
  "mahler_odd_word_span as = sum_list as"

definition mahler_odd_word_delta :: "nat list \<Rightarrow> int" where
  "mahler_odd_word_delta as = sum_list (map (\<lambda>a. 3-int a) as)"

fun mahler_odd_word_minimum :: "nat list \<Rightarrow> int" where
  "mahler_odd_word_minimum [] = 0"
| "mahler_odd_word_minimum (a#as) =
    min (min 0 (3-int a)) ((3-int a) + mahler_odd_word_minimum as)"

fun mahler_odd_word_minimum_position :: "nat list \<Rightarrow> nat" where
  "mahler_odd_word_minimum_position [] = 0"
| "mahler_odd_word_minimum_position (a#as) =
    (if min 0 (3-int a) \<le> (3-int a) + mahler_odd_word_minimum as
     then (if 3-int a < 0 then a else 0)
     else a + mahler_odd_word_minimum_position as)"

fun mahler_odd_word_guard :: "nat \<Rightarrow> nat list \<Rightarrow> real \<Rightarrow> bool" where
  "mahler_odd_word_guard D [] t = cylinder_guard D 0 t"
| "mahler_odd_word_guard D (a#as) t =
    (cylinder_guard D a t \<and>
      mahler_odd_word_guard (mahler_orbit D a) as
        (fractional_endpoint D a t))"

lemma mahler_positive_two_power_split_source_odd:
  fixes D k u :: nat
  assumes split: "3*D+1 = 2^(Suc k)*u"
  shows "odd D"
proof -
  have even: "even (3*D+1)"
    using split by (simp add: power_Suc)
  show ?thesis using even by (cases D rule: nat_mod_two_cases; simp)
qed

lemma mahler_odd_run_intermediate_source:
  assumes split: "3*D+1 = 2^(Suc k)*u" and within: "j \<le> k"
  shows "mahler_orbit D (Suc j) = u*2^(k-j)*3^j"
proof -
  have first: "mahler_D_step D = 2^k*u"
    using split by (simp add: mahler_D_step_def power_Suc algebra_simps)
  have shift: "mahler_orbit D (Suc j) = mahler_orbit (mahler_D_step D) j"
    by (rule mahler_orbit_shift)
  show ?thesis
    using even_source_run[OF within, of u] shift first by (simp add: mult.commute)
qed

lemma odd_events_dyadic_block_prefix_zero:
  fixes j k u :: nat
  assumes within: "j \<le> k"
  shows "odd_events (2^k*u) j = 0"
using within
proof (induction j arbitrary: k)
  case 0
  then show ?case by simp
next
  case (Suc j)
  have current_within: "Suc j \<le> k" using Suc.prems .
  have predecessor_within: "j \<le> k" using current_within by arith
  have before: "j < k" using current_within by arith
  have source: "mahler_orbit (2^k*u) j = u*2^(k-j)*3^j"
    using even_source_run[OF predecessor_within, of u] by (simp add: mult.commute)
  have even: "even (mahler_orbit (2^k*u) j)"
    using source before by simp
  have prefix: "odd_events (2^k*u) j = 0"
    using Suc.IH[OF predecessor_within] .
  show ?case using prefix even by simp
qed

lemma mahler_odd_run_event_prefix:
  assumes split: "3*D+1 = 2^(Suc k)*u" and odd_u: "odd u"
      and within: "j \<le> k"
  shows "odd_events D (Suc j) = 1"
proof -
  have first: "mahler_D_step D = 2^k*u"
    using split by (simp add: mahler_D_step_def power_Suc algebra_simps)
  have source_odd: "odd D"
    by (rule mahler_positive_two_power_split_source_odd[OF split])
  have head: "odd_events D 1 = 1"
    using source_odd by (simp add: odd_iff_mod_2_eq_one)
  have append: "odd_events D (Suc j) =
      odd_events D 1 + odd_events (mahler_orbit D 1) j"
    using odd_events_append[of D 1 j] by simp
  have tail: "odd_events (mahler_orbit D 1) j = 0"
    using first odd_events_dyadic_block_prefix_zero[OF within] by simp
  show ?thesis using append head tail by simp
qed

lemma mahler_odd_run_ledger_prefix:
  assumes split: "3*D+1 = 2^(Suc k)*u" and odd_u: "odd u"
      and within: "j \<le> Suc k"
  shows "min 0 (3-int (Suc k)) \<le> ledger_at D j"
proof (cases j)
  case 0
  then show ?thesis by simp
next
  case (Suc n)
  have le: "n \<le> k" using within Suc by arith
  have events: "odd_events D (Suc n) = 1"
    using mahler_odd_run_event_prefix[OF split odd_u le] .
  have exact: "ledger_at D (Suc n) = 3-int (Suc n)"
    using ledger_event_accounting[of D "Suc n"] events by simp
  show ?thesis using exact within Suc by (simp; linarith)
qed

lemma mahler_odd_word_refines_endpoint_events_and_ledger_conj:
  assumes admitted: "mahler_odd_word_admitted D as"
  shows "mahler_orbit D (mahler_odd_word_span as) = mahler_odd_word_endpoint as D
    \<and> odd_events D (mahler_odd_word_span as) = length as
    \<and> ledger_at D (mahler_odd_word_span as) = mahler_odd_word_delta as"
using admitted
proof (induction as arbitrary: D)
  case Nil
  then show ?case
    by (simp add: mahler_odd_word_span_def mahler_odd_word_delta_def)
next
  case (Cons a as)
  obtain k u where a: "a = Suc k" and split: "3*D+1 = 2^(Suc k)*u"
      and odd_u: "odd u" and tail_admitted: "mahler_odd_word_admitted (3^k*u) as"
    using Cons.prems by auto
  have odd_D: "odd D"
    by (rule mahler_positive_two_power_split_source_odd[OF split])
  have block_facts:
      "mahler_orbit D (Suc k) = 3^k*u"
      "odd_events D (Suc k) = 1"
      "ledger_at D (Suc k) = 3-int (Suc k)"
    using mahler_odd_event_block_refines_endpoint_and_ledger[OF odd_D split odd_u]
    by blast+
  have tail_facts:
      "mahler_orbit (3^k*u) (mahler_odd_word_span as) =
          mahler_odd_word_endpoint as (3^k*u)
        \<and> odd_events (3^k*u) (mahler_odd_word_span as) = length as
        \<and> ledger_at (3^k*u) (mahler_odd_word_span as) = mahler_odd_word_delta as"
    using Cons.IH[OF tail_admitted] .
  have tail_endpoint:
      "mahler_orbit (3^k*u) (mahler_odd_word_span as) =
        mahler_odd_word_endpoint as (3^k*u)"
    using tail_facts by blast
  have tail_events:
      "odd_events (3^k*u) (mahler_odd_word_span as) = length as"
    using tail_facts by blast
  have tail_ledger:
      "ledger_at (3^k*u) (mahler_odd_word_span as) = mahler_odd_word_delta as"
    using tail_facts by blast
  show ?case
  proof (intro conjI)
    show "mahler_orbit D (mahler_odd_word_span (a#as)) =
        mahler_odd_word_endpoint (a#as) D"
    proof -
    have "mahler_orbit D (mahler_odd_word_span (a#as)) =
        mahler_orbit D (Suc k + mahler_odd_word_span as)"
      using a by (simp add: mahler_odd_word_span_def)
    also have "... = mahler_orbit (mahler_orbit D (Suc k))
        (mahler_odd_word_span as)"
      by (rule mahler_orbit_add)
    also have "... = mahler_orbit (3^k*u) (mahler_odd_word_span as)"
      using block_facts(1) by simp
    also have "... = mahler_odd_word_endpoint as (3^k*u)"
      by (rule tail_endpoint)
    also have "... = mahler_odd_word_endpoint (a#as) D"
      using a block_facts(1) by simp
    finally show ?thesis .
    qed
    show "odd_events D (mahler_odd_word_span (a#as)) = length (a#as)"
    proof -
      have "odd_events D (mahler_odd_word_span (a#as)) =
          odd_events D (Suc k + mahler_odd_word_span as)"
        using a by (simp add: mahler_odd_word_span_def)
      also have "... = odd_events D (Suc k) +
          odd_events (mahler_orbit D (Suc k)) (mahler_odd_word_span as)"
        by (rule odd_events_append)
      also have "... = 1 + length as"
        using block_facts(1,2) tail_events by simp
      finally show ?thesis using a by simp
    qed
    show "ledger_at D (mahler_odd_word_span (a#as)) = mahler_odd_word_delta (a#as)"
    proof -
      have "ledger_at D (mahler_odd_word_span (a#as)) =
          ledger_at D (Suc k + mahler_odd_word_span as)"
        using a by (simp add: mahler_odd_word_span_def)
      also have "... = ledger_at D (Suc k) +
          ledger_at (mahler_orbit D (Suc k)) (mahler_odd_word_span as)"
        by (rule ledger_at_append)
      also have "... = (3 - int (Suc k)) + mahler_odd_word_delta as"
        using block_facts(1,3) tail_ledger by simp
      finally show ?thesis using a
        by (simp add: mahler_odd_word_delta_def)
    qed
  qed
qed

theorem mahler_odd_word_refines_endpoint_events_and_ledger:
  assumes admitted: "mahler_odd_word_admitted D as"
  shows "mahler_orbit D (mahler_odd_word_span as) = mahler_odd_word_endpoint as D"
    and "odd_events D (mahler_odd_word_span as) = length as"
    and "ledger_at D (mahler_odd_word_span as) = mahler_odd_word_delta as"
  using mahler_odd_word_refines_endpoint_events_and_ledger_conj[OF admitted]
  by blast+

theorem mahler_odd_word_fractional_guard_decomposition:
  "cylinder_guard D (mahler_odd_word_span as) t \<longleftrightarrow>
    mahler_odd_word_guard D as t"
proof (induction as arbitrary: D t)
  case Nil
  show ?case by (simp add: mahler_odd_word_span_def cylinder_guard_def)
next
  case (Cons a as)
  show ?case
    using source_guard_composition[of D a "mahler_odd_word_span as" t]
      Cons.IH[of "mahler_orbit D a" "fractional_endpoint D a t"]
    by (simp add: mahler_odd_word_span_def)
qed

lemma mahler_odd_word_prefix_minimum_exact_conj:
  assumes admitted: "mahler_odd_word_admitted D as"
  shows "(\<forall>j\<le>mahler_odd_word_span as.
      mahler_odd_word_minimum as \<le> ledger_at D j)
    \<and> mahler_odd_word_minimum as =
      ledger_at D (mahler_odd_word_minimum_position as)
    \<and> mahler_odd_word_minimum_position as \<le> mahler_odd_word_span as"
using admitted
proof (induction as arbitrary: D)
  case Nil
  then show ?case by (simp add: mahler_odd_word_span_def)
next
  case (Cons a as)
  obtain k u where a: "a = Suc k" and split: "3*D+1 = 2^(Suc k)*u"
      and odd_u: "odd u" and tail_admitted: "mahler_odd_word_admitted (3^k*u) as"
    using Cons.prems by auto
  have total: "mahler_odd_word_span (a#as) = Suc k + mahler_odd_word_span as"
    using a by (simp add: mahler_odd_word_span_def)
  have odd_D: "odd D"
    by (rule mahler_positive_two_power_split_source_odd[OF split])
  have head_delta: "ledger_at D (Suc k) = 3-int (Suc k)"
    using mahler_odd_event_block_refines_endpoint_and_ledger[OF odd_D split odd_u]
    by blast
  have head_lower:
    "min 0 (3-int (Suc k)) \<le> ledger_at D j" if "j \<le> Suc k" for j
    using mahler_odd_run_ledger_prefix[OF split odd_u that] .
  have tail_lower:
    "mahler_odd_word_minimum as \<le> ledger_at (3^k*u) j"
    if "j \<le> mahler_odd_word_span as" for j
    using Cons.IH[OF tail_admitted] that by blast
  have min_eq:
    "mahler_odd_word_minimum (a#as) =
       min (min 0 (3-int (Suc k)))
         ((3-int (Suc k)) + mahler_odd_word_minimum as)"
    using a by simp
  have all_prefixes:
      "(\<forall>j\<le>mahler_odd_word_span (a#as).
        mahler_odd_word_minimum (a#as) \<le> ledger_at D j)"
  proof (intro allI impI)
    fix j assume bound: "j \<le> mahler_odd_word_span (a#as)"
    show "mahler_odd_word_minimum (a#as) \<le> ledger_at D j"
    proof (cases "j \<le> Suc k")
      case True
      have head: "min 0 (3-int (Suc k)) \<le> ledger_at D j"
        using head_lower[OF True] .
      show ?thesis using min_eq head by simp
    next
      case False
      have after_head: "Suc k < j" using False by simp
      obtain j' where j: "j = Suc k + j'"
      proof -
        have "j = Suc k + (j - Suc k)" using after_head by arith
        then show thesis by (rule that)
      qed
      have jbound: "j' \<le> mahler_odd_word_span as"
        using bound total j by arith
      have append:
        "ledger_at D j = ledger_at D (Suc k) + ledger_at (mahler_orbit D (Suc k)) j'"
        using ledger_at_append[of D "Suc k" j'] j by simp
      have endpoint: "mahler_orbit D (Suc k) = 3^k*u"
        using mahler_odd_event_block_refines_endpoint_and_ledger[OF odd_D split odd_u]
        by blast
      have tail: "mahler_odd_word_minimum as \<le> ledger_at (3^k*u) j'"
        using tail_lower[OF jbound] .
      have selected_tail:
        "(3-int (Suc k)) + mahler_odd_word_minimum as \<le>
          (3-int (Suc k)) + ledger_at (3^k*u) j'"
        using tail by linarith
      have selected_below:
        "min (min 0 (3-int (Suc k)))
            ((3-int (Suc k)) + mahler_odd_word_minimum as)
          \<le> (3-int (Suc k)) + ledger_at (3^k*u) j'"
        using selected_tail by (meson min.cobounded2 order_trans)
      show ?thesis
        using append head_delta endpoint selected_below min_eq
        by (simp only: append head_delta endpoint min_eq; assumption)
    qed
  qed
  have tail_position_bound:
    "mahler_odd_word_minimum_position as \<le> mahler_odd_word_span as"
    using Cons.IH[OF tail_admitted] by blast
  have position_bound:
      "mahler_odd_word_minimum_position (a#as) \<le> mahler_odd_word_span (a#as)"
    using a tail_position_bound total head_delta
    by (auto simp: mahler_odd_word_minimum_position.simps; arith)
  have attained:
      "mahler_odd_word_minimum (a#as) =
      ledger_at D (mahler_odd_word_minimum_position (a#as))"
  proof (cases "min 0 (3-int (Suc k)) \<le>
      (3-int (Suc k)) + mahler_odd_word_minimum as")
    case True
    note choose_head = True
    have selected_minimum:
      "mahler_odd_word_minimum (a#as) = min 0 (3-int (Suc k))"
      using min_eq choose_head by simp
    show ?thesis
    proof (cases "3-int (Suc k) < 0")
      case True
      have position: "mahler_odd_word_minimum_position (a#as) = Suc k"
        using a choose_head True by simp
      have selected: "mahler_odd_word_minimum (a#as) = 3-int (Suc k)"
        using selected_minimum True by simp
      show ?thesis
        by (simp only: position head_delta selected)
    next
      case False
      have position: "mahler_odd_word_minimum_position (a#as) = 0"
        using a choose_head False by simp
      have selected: "mahler_odd_word_minimum (a#as) = 0"
        using selected_minimum False by simp
      show ?thesis using position selected by simp
    qed
  next
    case False
    have position: "mahler_odd_word_minimum_position (a#as) =
        Suc k + mahler_odd_word_minimum_position as"
      using a False by simp
    have append:
      "ledger_at D (Suc k + mahler_odd_word_minimum_position as) =
        ledger_at D (Suc k) + ledger_at (mahler_orbit D (Suc k))
          (mahler_odd_word_minimum_position as)"
      by (rule ledger_at_append)
    have endpoint: "mahler_orbit D (Suc k) = 3^k*u"
      using mahler_odd_event_block_refines_endpoint_and_ledger[OF odd_D split odd_u]
      by blast
    have tail_min:
      "mahler_odd_word_minimum as =
        ledger_at (3^k*u) (mahler_odd_word_minimum_position as)"
      using Cons.IH[OF tail_admitted] by blast
    have selected_minimum:
      "mahler_odd_word_minimum (a#as) =
        (3-int (Suc k)) + mahler_odd_word_minimum as"
      using min_eq False by simp
    show ?thesis using position append endpoint head_delta tail_min selected_minimum
      by (simp only: position append endpoint head_delta tail_min selected_minimum)
  qed
  show ?case using all_prefixes position_bound attained by blast
qed

theorem mahler_odd_word_prefix_minimum_exact:
  assumes admitted: "mahler_odd_word_admitted D as"
  shows "(\<forall>j\<le>mahler_odd_word_span as.
      mahler_odd_word_minimum as \<le> ledger_at D j)"
    and "mahler_odd_word_minimum as =
      ledger_at D (mahler_odd_word_minimum_position as)"
    and "mahler_odd_word_minimum_position as \<le> mahler_odd_word_span as"
  using mahler_odd_word_prefix_minimum_exact_conj[OF admitted]
  by blast+

theorem mahler_odd_word_prefix_safety_iff:
  assumes admitted: "mahler_odd_word_admitted D as"
  shows "(\<forall>j\<le>mahler_odd_word_span as.
      0 \<le> incoming_balance + ledger_at D j) \<longleftrightarrow>
    0 \<le> incoming_balance + mahler_odd_word_minimum as"
proof
  assume safe: "\<forall>j\<le>mahler_odd_word_span as.
      0 \<le> incoming_balance + ledger_at D j"
  have position: "mahler_odd_word_minimum_position as \<le>mahler_odd_word_span as"
    and exact: "mahler_odd_word_minimum as =
      ledger_at D (mahler_odd_word_minimum_position as)"
    using mahler_odd_word_prefix_minimum_exact[OF admitted] by blast+
  show "0 \<le> incoming_balance + mahler_odd_word_minimum as"
    using safe[rule_format, OF position] exact by simp
next
  assume lower: "0 \<le> incoming_balance + mahler_odd_word_minimum as"
  have bound: "mahler_odd_word_minimum as \<le> ledger_at D j"
    if "j \<le>mahler_odd_word_span as" for j
    using mahler_odd_word_prefix_minimum_exact(1)[OF admitted, rule_format, OF that] .
  show "\<forall>j\<le>mahler_odd_word_span as.
      0 \<le> incoming_balance + ledger_at D j"
  proof (intro allI impI)
    fix j
    assume within: "j \<le> mahler_odd_word_span as"
    have minimum: "mahler_odd_word_minimum as \<le> ledger_at D j"
      by (rule bound[OF within])
    show "0 \<le> incoming_balance + ledger_at D j"
      using lower minimum by linarith
  qed
qed

definition mahler_q_at :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "mahler_q_at D n = 2^n * (3*mahler_orbit D n+1)"

theorem mahler_odd_event_q_recurrence:
  assumes seam_odd: "odd (mahler_orbit D n)"
      and split: "3*mahler_orbit D n+1 = 2^(Suc k)*u"
      and odd_u: "odd u"
  shows "mahler_q_at D (n+Suc k) =
    3^(Suc k) * mahler_q_at D n + 2^(n+Suc k)"
proof -
  have endpoint:
    "mahler_orbit D (n+Suc k) = 3^k*u"
    using mahler_orbit_add[of D n "Suc k"]
      mahler_odd_event_block_refines_endpoint_and_ledger[OF seam_odd split odd_u]
    by simp
  have scaled:
    "2^(Suc k) * (3 * (3^k*u) + 1) =
      3^(Suc k) * (3*mahler_orbit D n+1) + 2^(Suc k)"
    using split by (simp add: algebra_simps power_Suc)
  have scaled_at_clock:
    "2^n * (2^(Suc k) * (3 * (3^k*u) + 1)) =
      2^n * (3^(Suc k) * (3*mahler_orbit D n+1) + 2^(Suc k))"
    using arg_cong[where f="\<lambda>x::nat. 2^n*x", OF scaled]
    by (simp add: mult.assoc)
  show ?thesis unfolding mahler_q_at_def endpoint
    using scaled_at_clock by (simp add: power_add algebra_simps)
qed

theorem mahler_odd_event_q_barrier_exact:
  fixes source elapsed exponent events u :: nat
  assumes balance: "ledger = 3 * int events - int elapsed"
      and split: "3*source+1 = 2^exponent*u"
      and odd_u: "odd u"
  shows "2^elapsed*(3*source+1) = 2^(elapsed+exponent)*u"
    and "odd ((2^elapsed*(3*source+1)) div 2^(elapsed+exponent))"
    and "elapsed + exponent \<ge> 3*events+4 \<longleftrightarrow>
      ledger + 3-int exponent < 0"
proof -
  have qfactor: "2^elapsed*(3*source+1) = 2^(elapsed+exponent)*u"
    using split by (simp add: power_add algebra_simps)
  show "2^elapsed*(3*source+1) = 2^(elapsed+exponent)*u"
    by (rule qfactor)
  have quotient:
    "((2::nat)^(elapsed+exponent)*u) div 2^(elapsed+exponent) = u"
  proof -
    have nonzero: "(2::nat)^(elapsed+exponent) \<noteq> 0" by simp
    show ?thesis using nonzero by (simp add: div_mult_self1)
  qed
  show "odd ((2^elapsed*(3*source+1)) div 2^(elapsed+exponent))"
    using qfactor odd_u quotient by simp
  show "elapsed + exponent \<ge> 3*events+4 \<longleftrightarrow>
      ledger + 3-int exponent < 0"
    by (rule mahler_ledger_q_divisibility_barrier_iff[OF balance])
qed

lemma mahler_step_doubled:
  "2*mahler_D_step D = 3*D + D mod 2"
  by (cases D rule: nat_mod_two_cases;
      simp add: mahler_D_step_def algebra_simps mod_Suc)


theorem source_selected_event_endpoint:
  assumes "odd u"
  shows "2*mahler_orbit (2^k*u) (Suc k) = 3^(Suc k)*u + 1"
proof -
  have at_k: "mahler_orbit (2^k*u) k = 3^k*u"
    using even_source_run[of k k u] by (simp add: mult.commute)
  have powmod: "(3::nat)^k mod 2 = 1"
  proof (induct k)
    case 0 then show ?case by simp
  next
    case (Suc k)
    have "(3::nat)^(Suc k) mod 2 = (3*3^k) mod 2" by (simp only: power_Suc)
    also have "\<dots> = ((3 mod 2)*(3^k mod 2)) mod 2"
      by (rule mod_mult_eq[symmetric])
    also have "\<dots> = 1" using Suc.hyps by simp
    finally show ?case .
  qed
  have umod: "u mod 2 = 1" using assms by (simp only: odd_iff_mod_2_eq_one)
  have parity: "(3^k*u) mod 2 = 1"
  proof -
    have "(3^k*u) mod 2 = ((3^k mod 2)*(u mod 2)) mod 2"
      by (rule mod_mult_eq[symmetric])
    also have "\<dots> = 1" by (simp only: powmod umod; simp)
    finally show ?thesis .
  qed
  show ?thesis
    by (simp only: mahler_orbit.simps at_k mahler_step_doubled parity power_Suc mult.assoc)
qed


theorem source_selected_diamond_event:
  assumes "odd u"
  shows "4*fractional_endpoint (2^k*u) (Suc k) t = (3/2)^(Suc k)*(4*t)-2"
proof -
  have endpoint: "2*of_nat (mahler_orbit (2^k*u) (Suc k)) =
      (3::real)^(Suc k)*of_nat u + 1"
    using arg_cong[OF source_selected_event_endpoint[OF assms], of "\<lambda>x. (of_nat x::real)"]
    by simp
  have scale: "(2::real)^k*(3/2)^(Suc k) = 3^(Suc k)/2"
    by (simp add: power_Suc power_divide)
  have scaled: "(of_nat (2^k*u)::real)*(3/2)^(Suc k) = 3^(Suc k)*of_nat u/2"
    using arg_cong[OF scale, of "\<lambda>x. x*of_nat u"]
    by (simp add: algebra_simps)
  show ?thesis unfolding fractional_endpoint_def
    using endpoint by (simp only: distrib_right scaled; simp add: algebra_simps; linarith)
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms source_guard_composition fractional_endpoint_composition
      prefix_high_fiber_translation guard_high_fiber_translation
      endpoint_high_fiber_translation six_step_source_transport
      centered_source_residue_canonical centered_source_chart_recombine
      centered_finite_cylinder_conjugacy
      fractional_step_diamond_action composed_source_endpoint composed_source_guard
      executable_compose_route executable_strict_interval_pullback
      executable_compose_endpoint executable_compose_guard
      source_selected_event_endpoint source_selected_diamond_event
      odd_events_append ledger_at_append odd_events_dyadic_block_zero
      mahler_positive_two_power_split_source_odd
      mahler_odd_run_intermediate_source
      mahler_odd_run_event_prefix
      mahler_odd_run_ledger_prefix
      mahler_odd_event_block_refines_endpoint_and_ledger
      mahler_odd_event_block_updates_ledger_at_seam
      mahler_ledger_q_divisibility_barrier_iff
      mahler_odd_word_refines_endpoint_events_and_ledger
      mahler_odd_word_fractional_guard_decomposition
      mahler_odd_word_prefix_minimum_exact
      mahler_odd_word_prefix_safety_iff
      mahler_odd_event_q_recurrence
      mahler_odd_event_q_barrier_exact})
    then () else error "Source cylinder transport depends on an oracle";
\<close>

end
