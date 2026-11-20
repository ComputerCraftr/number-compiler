theory Comma_Future_M204_Periodic
  imports Comma_Future_M204_Source_Join Comma_Semantic_B1.Comma_Frontier_M204_Checker
begin

lemma comma_future_m204_mdd_value_periodic:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and divides: "\<And>axis. axis<length radices \<Longrightarrow> radices!axis dvd 924"
  shows "comma_frontier_m204_mdd_value radices nodes roots (phase mod 924) cid =
    comma_frontier_m204_mdd_value radices nodes roots phase cid"
  using comma_crt_mdd_eval_phase_periodic[OF wf divides, where phase=phase and root="roots!cid"]
  by (simp only: comma_frontier_m204_mdd_value_def)

end
