theory Mahler_Reachable_Repetition
  imports Mahler_Source_Event_Safety
begin

text \<open>A repetition of one complete source clause is stronger than a
cycle in its fractional, prime or carry projection. These theorems concern
literal repetition of a fixed finite parity block, not parameter-changing
pumps or arbitrary aperiodic future grammars.\<close>

lemma repeated_affine_obstruction:
  fixes f :: "nat \<Rightarrow> nat"
  assumes step: "\<And>i. i < n \<Longrightarrow> Q*f(Suc i) = (Q+C)*f i+J"
  shows "Q^n * (C*f n+J) = (Q+C)^n * (C*f 0+J)"
using step
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have ih: "Q^n * (C*f n+J) = (Q+C)^n * (C*f 0+J)"
    by (rule Suc.hyps) (use Suc.prems in auto)
  have advance: "Q*(C*f(Suc n)+J) = (Q+C)*(C*f n+J)"
    using arg_cong[OF Suc.prems[of n], of "\<lambda>x. C*x"]
    by (simp add: algebra_simps)
  have "Q^(Suc n)*(C*f(Suc n)+J) = Q^n*(Q*(C*f(Suc n)+J))"
    by (simp add: power_Suc algebra_simps)
  also have "\<dots> = (Q+C)*(Q^n*(C*f n+J))"
    by (simp only: advance; simp add: algebra_simps)
  also have "\<dots> = (Q+C)^(Suc n)*(C*f 0+J)"
    by (simp only: ih power_Suc; simp add: algebra_simps)
  finally show ?case .
qed

lemma repeated_source_divisibility:
  fixes f :: "nat \<Rightarrow> nat"
  assumes co: "coprime Q (Q+C)"
    and step: "\<And>i. i < n \<Longrightarrow> Q*f(Suc i) = (Q+C)*f i+J"
  shows "Q^n dvd C*f 0+J"
proof -
  have equation: "Q^n * (C*f n+J) = (Q+C)^n * (C*f 0+J)"
    by (rule repeated_affine_obstruction) (rule step)
  have divides: "Q^n dvd (Q+C)^n * (C*f 0+J)"
    using equation by (metis dvd_triv_left)
  have copowers: "coprime (Q^n) ((Q+C)^n)" using co by simp
  show ?thesis using divides coprime_dvd_mult_right_iff[OF copowers] by blast
qed

theorem no_positive_periodic_affine_source:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "1 < Q" "0 < C" "0 < f 0" "coprime Q (Q+C)"
    and step: "\<And>i. Q*f(Suc i) = (Q+C)*f i+J"
  shows False
proof -
  let ?H = "C*f 0+J"
  have pos: "0 < ?H" using assms by simp
  have divides: "Q^?H dvd ?H"
    by (rule repeated_source_divisibility[OF assms(4)]) (simp add: step)
  have upper: "Q^?H \<le> ?H" by (rule dvd_imp_le[OF divides pos])
  have lower: "?H < Q^?H" using power_gt_expt[of Q "?H"] assms(1) by simp
  show False using upper lower by simp
qed

lemma source_clause_affine:
  assumes code: "2^L * mahler_orbit r L = 3^L*r+J"
    and residue: "D mod 2^L = r"
  shows "2^L * mahler_orbit D L = 3^L*D+J"
proof -
  have form: "D = r+2^L*(D div 2^L)"
    using residue by (metis div_mult_mod_eq add.commute mult.commute)
  have orbit: "mahler_orbit D L = mahler_orbit r L + 3^L*(D div 2^L)"
    using moving_source_cylinder[of L L r "D div 2^L"] form
    by (simp add: mult.commute)
  show ?thesis
    by (simp only: orbit distrib_left; simp only: code; subst (2) form; simp add: algebra_simps)
qed

theorem no_positive_repeating_source_clause:
  assumes L: "0 < L" and D: "0 < D"
    and code: "2^L * mahler_orbit r L = 3^L*r+J"
  shows "\<not> (\<forall>i. mahler_orbit D (i*L) mod 2^L = r)"
proof
  assume repeating: "\<forall>i. mahler_orbit D (i*L) mod 2^L = r"
  let ?f = "\<lambda>i. mahler_orbit D (i*L)"
  have scale: "(2::nat)^L < 3^L" by (rule power_strict_mono) (use L in auto)
  have big: "1 < (2::nat)^L" by (rule one_less_power) (use L in auto)
  have plus: "2^L+(3^L-2^L) = (3::nat)^L" using scale by arith
  have co: "coprime ((2::nat)^L) (2^L+(3^L-2^L))"
    by (simp only: plus; simp)
  have step: "2^L * ?f(Suc i) = (2^L+(3^L-2^L))*?f i+J" for i
  proof -
    have time: "Suc i*L = i*L+L" by (simp add: algebra_simps)
    show ?thesis
      using source_clause_affine[OF code repeating[rule_format, of i]]
      by (simp only: time mahler_orbit_add plus)
  qed
  show False
    by (rule no_positive_periodic_affine_source[where Q="2^L" and C="3^L-2^L"
      and f="?f" and J=J]) (use L D scale big co step in auto)
qed

text \<open>The executable future grammar retains the parameter relation which
was previously hidden inside congruence composition.  It is a relation, rather
than a total successor on arbitrary high fibers: the next event selects
\<open>a + 2^L*k\<close> and transports it to \<open>b + 3^L*k\<close>.\<close>

lemma affine_fiber_transport:
  fixes d a r b k L :: nat
  assumes route: "d + 3^L*a = r + 2^L*b"
  shows "d + 3^L*(a + 2^L*k) = r + 2^L*(b + 3^L*k)"
proof -
  have extended: "d + 3^L*a + 3^L*2^L*k =
      r + 2^L*b + 3^L*2^L*k"
    by (rule arg_cong[OF route, of "\<lambda>x. x + 3^L*2^L*k"])
  show ?thesis using extended by (simp add: algebra_simps)
qed

theorem source_clause_parameter_transport:
  assumes code: "mahler_orbit r L = d"
    and route: "d + 3^L*a = r + 2^L*b"
  shows "mahler_orbit (r + 2^L*(a + 2^L*k)) L =
      r + 2^L*(b + 3^L*k)"
proof -
  have orbit: "mahler_orbit (r + 2^L*(a + 2^L*k)) L =
      d + 3^L*(a + 2^L*k)"
    using moving_source_cylinder[of L L r "a + 2^L*k"] code
    by (simp add: mult.commute)
  show ?thesis using orbit affine_fiber_transport[OF route] by simp
qed

theorem parameter_transport_preserves_strict_guard:
  "cylinder_guard (r + 2^L*(a + 2^L*k)) L t =
    cylinder_guard r L t"
  using guard_high_fiber_translation[of r L "a + 2^L*k" t] .

lemma positive_mahler_step:
  assumes "0 < D"
  shows "0 < mahler_D_step D"
  using assms by (simp add: mahler_D_step_def)

lemma positive_mahler_orbit:
  assumes "0 < D"
  shows "0 < mahler_orbit D n"
  using assms by (induct n) (simp_all add: positive_mahler_step)

theorem no_positive_eventually_repeating_source_clause:
  assumes L: "0 < L" and D: "0 < D"
    and code: "2^L * mahler_orbit r L = 3^L*r+J"
  shows "\<not> (\<exists>m. \<forall>i. mahler_orbit D (m+i*L) mod 2^L = r)"
proof
  assume eventual: "\<exists>m. \<forall>i. mahler_orbit D (m+i*L) mod 2^L = r"
  then obtain m where tail: "\<forall>i. mahler_orbit D (m+i*L) mod 2^L = r"
    by blast
  have positive: "0 < mahler_orbit D m" by (rule positive_mahler_orbit[OF D])
  have repeating: "\<forall>i. mahler_orbit (mahler_orbit D m) (i*L) mod 2^L = r"
    using tail by (simp add: mahler_orbit_add)
  show False
    using no_positive_repeating_source_clause[OF L positive code] repeating by blast
qed

theorem unsafe_prefix_first_child:
  "\<not> safe_prefix (m+n) x \<longleftrightarrow>
    (\<not> safe_prefix m x \<or>
      (safe_prefix m x \<and> \<not> safe_prefix n (x*(3/2)^m)))"
  using safe_prefix_split[of m n x] by blast

text \<open>The executable audit computes H=(3^L-2^L)D+J and reports
floor(v2(H)/L) as the source repetition limit. The divisibility theorem is
the necessary-condition proof behind that audit. It does not prove the Python
valuation implementation or successful general grammar closure. In particular,
nonperiodic safe sources and changing-parameter pumps are not excluded.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms repeated_affine_obstruction repeated_source_divisibility
      no_positive_periodic_affine_source source_clause_affine
      no_positive_repeating_source_clause affine_fiber_transport
      source_clause_parameter_transport parameter_transport_preserves_strict_guard
      positive_mahler_step positive_mahler_orbit
      no_positive_eventually_repeating_source_clause unsafe_prefix_first_child})
    then () else error "Reachable repetition depends on an oracle";
\<close>

end
