theory Radial_Sturmian
  imports Homogeneous_Growth_Scale
begin

text \<open>The Archimedean port observes only the homogeneous multiplier.
The source-dependent affine offset and guarded endpoint remain separate.
Ordinary exponent increments rotate the phase; dyadic sampling doubles it.\<close>

definition radial_alpha :: real where
  "radial_alpha = ln 3 / ln 2 - 1"

definition radial_phase :: "nat \<Rightarrow> real" where
  "radial_phase H = frac (real H * radial_alpha)"

lemma radial_unit_slope:
  "homogeneous_growth_radix_slope mahler_temporal_growth_unit 2 = radial_alpha"
  by (simp add: homogeneous_growth_radix_slope_def
      mahler_temporal_growth_unit_def radial_alpha_def diff_divide_distrib)

lemma radial_log_source:
  "ln ((3::real)^H / 2^D) / ln 2 = real H * (ln 3 / ln 2) - real D"
  by (simp add: ln_div ln_realpow diff_divide_distrib)

lemma radial_order_dyadic_transport:
  "floor (ln ((3::real)^H / 2^D) / ln 2) =
    floor (real H * (ln 3 / ln 2)) - int D"
  using floor_diff_of_int[of "real H * (ln 3 / ln 2)" "int D"]
  by (simp add: radial_log_source)

lemma radial_phase_dyadic_transport:
  "frac (ln ((3::real)^H / 2^D) / ln 2) = radial_phase H"
proof -
  have nf: "frac (real n) = 0" for n by (simp add: frac_def)
  show ?thesis
    by (simp add: radial_log_source radial_phase_def radial_alpha_def
        algebra_simps frac_diff nf)
qed

lemma radial_phase_successor:
  "radial_phase (Suc H) = frac (radial_phase H + radial_alpha)"
  by (simp add: radial_phase_def algebra_simps frac_add)

lemma radial_phase_dyadic_sampling:
  "radial_phase (2*H) = frac (2 * radial_phase H)"
proof -
  have "radial_phase (2*H) = frac (real H * radial_alpha + real H * radial_alpha)"
    unfolding radial_phase_def
    by (rule arg_cong[where f=frac]; simp only: of_nat_mult of_nat_numeral; simp add: algebra_simps)
  also have "... = frac (frac (real H * radial_alpha) + frac (real H * radial_alpha))"
    by (simp only: frac_add_simps)
  also have "... = frac (2 * radial_phase H)"
    unfolding radial_phase_def by (rule arg_cong[where f=frac]; simp add: algebra_simps)
  finally show ?thesis .
qed

lemma radial_alpha_bounds:
  "0 < radial_alpha \<and> radial_alpha < 1"
proof -
  have l2: "0 < ln (2::real)" by simp
  have lower: "ln (2::real) < ln 3" by simp
  have h: "ln (3::real) < ln ((2::real)^2)" by simp
  have e: "ln ((2::real)^2) = 2 * ln 2"
    by (subst ln_realpow; simp)
  have upper: "ln (3::real) < 2 * ln 2" using h e by linarith
  show ?thesis using l2 lower upper
    by (auto simp: radial_alpha_def divide_less_eq less_divide_eq; linarith)
qed

lemma radial_mechanical_bit:
  "homogeneous_growth_point mahler_temporal_growth_unit 2 (int H) \<in> {0,1}"
proof -
  have alpha_floor: "floor radial_alpha = (0::int)"
    using radial_alpha_bounds by (intro floor_unique; simp)
  show ?thesis
    by (simp add: homogeneous_growth_point_def homogeneous_growth_radix_order_def
        radial_unit_slope algebra_simps floor_add alpha_floor)
qed

text \<open>The existing block induction is the implementation's endpoint
subtraction, rather than a replay of individual mechanical symbols.\<close>
lemma radial_block_uses_shared_sum:
  "homogeneous_growth_block mahler_temporal_growth_unit 2 (int H) q =
   homogeneous_growth_points_sum mahler_temporal_growth_unit 2 (int H) q"
  by (rule homogeneous_growth_block_is_point_sum[symmetric])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms radial_log_source
    radial_order_dyadic_transport radial_phase_dyadic_transport
    radial_phase_successor radial_phase_dyadic_sampling radial_alpha_bounds
    radial_mechanical_bit radial_block_uses_shared_sum}) then ()
    else error "Radial Sturmian port depends on an oracle";
\<close>
end
