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
      source_selected_event_endpoint source_selected_diamond_event})
    then () else error "Source cylinder transport depends on an oracle";
\<close>

end
