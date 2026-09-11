theory Reverse_Observability
  imports Reverse_Two_Cell_Equations
begin

definition four_event_observation where
  "four_event_observation ss =
    map (\<lambda>n. observation (run step n ss)) [0..<5]"

lemma two_cell_observation_table:
  "distinct (map (\<lambda>s. four_event_observation [s,s]) [0..<19])"
  by (simp only: four_event_observation_def observation_intervals list.map
       first_four_runs two_cell_steps;
      simp add: observation_def carry_out_def domain_def)

theorem two_cell_four_event_injective:
  "inj_on (\<lambda>s. four_event_observation [s,s]) {0..<19}"
  using two_cell_observation_table by (simp add: distinct_map)

theorem all_future_two_cell_observations_force_exact_value:
  assumes "s < 19" "t < 19"
    and equal_future: "\<And>n. observation (run step n [s,s]) =
      observation (run step n [t,t])"
  shows "s = t"
proof -
  have same: "four_event_observation [s,s] = four_event_observation [t,t]"
    by (simp add: four_event_observation_def equal_future)
  show ?thesis
    by (rule inj_onD[OF two_cell_four_event_injective same]) (simp_all add: assms)
qed

text \<open>This is an unconditional result for the specified two-cell family.
It does not prove that every possible 196 consumer/context admits only the
identity quotient, and does not authenticate an unbounded 196 context grammar.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms two_cell_four_event_injective
        all_future_two_cell_observations_force_exact_value}) then ()
    else error "Observability proof depends on an oracle";
\<close>

end
