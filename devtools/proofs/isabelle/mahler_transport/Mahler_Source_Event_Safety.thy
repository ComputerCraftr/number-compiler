theory Mahler_Source_Event_Safety
  imports Mahler_Source_Cylinder_Transport
begin

text \<open>Original fractional safety for a source-selected even run followed
by one odd step. The exact guard is closed at 2 and open at 3 after scaling
w=4t, rather than the unrestricted diamond tree's open interval (2,6).\<close>

lemma even_run_fraction:
  assumes "j \<le> k"
  shows "fractional_endpoint (2^k*u) j t = (3/2)^j*t"
proof -
  have orbit: "mahler_orbit (2^k*u) j = u*2^(k-j)*3^j"
    by (rule even_source_run[OF assms])
  have scale: "(of_nat (2^k*u)::real)*(3/2)^j = of_nat (u*2^(k-j)*3^j)"
    using arg_cong[OF dyadic_scale_transport[OF assms], of "\<lambda>x. of_nat u*x"]
    by (simp add: algebra_simps)
  show ?thesis unfolding fractional_endpoint_def orbit
    by (simp only: distrib_right scale; simp add: mult.commute)
qed

lemma guard_iff_endpoint_bounds:
  assumes "0 \<le> t" "t < 1/2"
  shows "cylinder_guard D n t \<longleftrightarrow>
    (\<forall>j\<le>n. 0 \<le> fractional_endpoint D j t \<and> fractional_endpoint D j t < 1/2)"
proof -
  have lo: "of_nat D \<le> (of_nat D::real)+t" using assms by simp
  have hi: "(of_nat D::real)+t < of_nat D+1/2" using assms by simp
  have point: "(0 \<le> fractional_endpoint D j t \<and> fractional_endpoint D j t < 1/2) \<longleftrightarrow>
      (of_nat (mahler_orbit D j) \<le> (of_nat D+t)*(3/2)^j \<and>
       (of_nat D+t)*(3/2)^j < of_nat (mahler_orbit D j)+1/2)" for j
    unfolding fractional_endpoint_def by linarith
  show ?thesis using safe_prefix_exact[OF lo hi, of n] assms
    by (simp only: cylinder_guard_def point; blast)
qed

theorem source_event_exact_guard:
  assumes odd: "odd u" and t: "0 \<le> t" "t < 1/2"
  shows "cylinder_guard (2^k*u) (Suc k) t \<longleftrightarrow>
    2 \<le> (3/2)^(Suc k)*(4*t) \<and> (3/2)^(Suc k)*(4*t) < 3"
proof
  assume guard: "cylinder_guard (2^k*u) (Suc k) t"
  have bounds: "\<forall>j\<le>Suc k. 0 \<le> fractional_endpoint (2^k*u) j t \<and>
      fractional_endpoint (2^k*u) j t < 1/2"
    using guard guard_iff_endpoint_bounds[OF t] by blast
  have bound_k: "fractional_endpoint (2^k*u) k t < 1/2"
    using bounds[rule_format, of k] by simp
  have before: "(3/2)^k*t < 1/2"
    using bound_k even_run_fraction[of k k u t] by simp
  have after: "0 \<le> fractional_endpoint (2^k*u) (Suc k) t"
    using bounds[rule_format, of "Suc k"] by simp
  show "2 \<le> (3/2)^(Suc k)*(4*t) \<and> (3/2)^(Suc k)*(4*t) < 3"
    using source_selected_diamond_event[OF odd, of k t] before after
    by (simp add: power_Suc algebra_simps; linarith)
next
  assume guard: "2 \<le> (3/2)^(Suc k)*(4*t) \<and> (3/2)^(Suc k)*(4*t) < 3"
  have top: "(3/2)^k*t < 1/2" using guard
    by (simp add: power_Suc algebra_simps; linarith)
  have bounds: "0 \<le> fractional_endpoint (2^k*u) j t \<and>
      fractional_endpoint (2^k*u) j t < 1/2" if "j \<le> Suc k" for j
  proof (cases "j \<le> k")
    case True
    have powers: "(3/2::real)^j \<le> (3/2)^k"
      by (rule power_increasing[OF True]) simp
    have scaled: "(3/2)^j*t \<le> (3/2)^k*t"
      by (rule mult_right_mono[OF powers t(1)])
    have nonnegative: "0 \<le> (3/2)^j*t"
      using mult_nonneg_nonneg[of "(3/2::real)^j" t] t(1) by simp
    have upper: "(3/2)^j*t < 1/2" using top scaled by linarith
    show ?thesis using upper nonnegative
      by (simp only: even_run_fraction[OF True]; blast)
  next
    case False
    then have eq: "j = Suc k" using that by arith
    show ?thesis using source_selected_diamond_event[OF odd, of k t] guard
      unfolding eq by (intro conjI; linarith)
  qed
  show "cylinder_guard (2^k*u) (Suc k) t"
    using bounds guard_iff_endpoint_bounds[OF t] by blast
qed

theorem positive_prefix_at_every_horizon:
  "0 < (of_nat (2^N)::real)" "safe_prefix N (of_nat (2^N))"
proof -
  show "0 < (of_nat (2^N)::real)" by simp
  have safe: "frac ((of_nat (2^N)::real)*(3/2)^n) < 1/2" if "n \<le> N" for n
  proof -
    have eq: "(of_nat (2^N)::real)*(3/2)^n = of_nat (2^(N-n)*3^n)"
      using dyadic_scale_transport[OF that] by simp
    have integral: "frac (of_nat (2^(N-n)*3^n)::real) = 0"
      using frac_nat_translate[of "0::real" "2^(N-n)*3^n"] by simp
    show ?thesis by (simp only: eq integral; simp)
  qed
  show "safe_prefix N (of_nat (2^N))" using safe by (simp add: safe_prefix_def)
qed

text \<open>The positive-prefix witnesses depend on the horizon. They do not
supply one positive real safe at every horizon. They rule out a uniform finite
exhaustion bound over all positive sources.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms even_run_fraction guard_iff_endpoint_bounds source_event_exact_guard
      positive_prefix_at_every_horizon})
    then () else error "Source event safety depends on an oracle";
\<close>

end
