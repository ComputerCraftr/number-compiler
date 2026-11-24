theory Mahler_Finite_Safety_Refinement
  imports Mahler_Exact_Even_Event_Threshold
begin

text \<open>The consumer retains the physical source and its fractional inlet.
  A checked source cylinder covers every earlier tick, and its first
  failing extension identifies the physical failure without a history.\<close>

theorem mahler_finite_safety_first_failed_extension:
  assumes inlet: "0 \<le> t" "t < 1/2"
      and prefix: "cylinder_guard D n t"
      and failed: "\<not> cylinder_guard D (Suc n) t"
  shows "\<forall>j\<le>n. 0 \<le> fractional_endpoint D j t \<and>
             fractional_endpoint D j t < 1/2"
    and "\<not> (0 \<le> fractional_endpoint D (Suc n) t \<and>
                 fractional_endpoint D (Suc n) t < 1/2)"
proof -
  have covered: "\<forall>j\<le>n. 0 \<le> fractional_endpoint D j t \<and>
      fractional_endpoint D j t < 1/2"
    using prefix guard_iff_endpoint_bounds[OF inlet, of D n] by blast
  have failed_bounds: "\<not> (\<forall>j\<le>Suc n.
      0 \<le> fractional_endpoint D j t \<and> fractional_endpoint D j t < 1/2)"
    using failed guard_iff_endpoint_bounds[OF inlet, of D "Suc n"] by blast
  show "\<forall>j\<le>n. 0 \<le> fractional_endpoint D j t \<and>
      fractional_endpoint D j t < 1/2" by (rule covered)
  show "\<not> (0 \<le> fractional_endpoint D (Suc n) t \<and>
      fractional_endpoint D (Suc n) t < 1/2)"
    using covered failed_bounds by (auto simp: le_Suc_eq)
qed

theorem mahler_finite_safety_adjacent_source:
  assumes first: "cylinder_guard D m t"
      and second: "cylinder_guard (mahler_orbit D m) n (fractional_endpoint D m t)"
  shows "cylinder_guard D (m+n) t"
    and "fractional_endpoint D (m+n) t =
      fractional_endpoint (mahler_orbit D m) n (fractional_endpoint D m t)"
  using first second source_guard_composition fractional_endpoint_composition by auto

theorem mahler_finite_safety_even_cut:
  assumes "0 < denominator" "2 * numerator < denominator"
  shows "cylinder_guard (2^ticks * source) ticks
      (of_nat numerator / of_nat denominator) \<longleftrightarrow>
    \<not> mahler_even_event_impossible numerator denominator ticks"
  using mahler_even_event_guard_exact[OF assms] .

ML \<open>
  val checked = @{thms mahler_finite_safety_first_failed_extension
    mahler_finite_safety_adjacent_source mahler_finite_safety_even_cut};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Finite Mahler safety refinement depends on an oracle";
\<close>

end
