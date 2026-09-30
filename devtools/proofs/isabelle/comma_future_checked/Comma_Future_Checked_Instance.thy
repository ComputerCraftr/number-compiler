theory Comma_Future_Checked_Instance
  imports Comma_Future_Instance
begin

text \<open>This is the concrete release computation. Keep it in a separate
 session so a resource-limited build of the generic checker does not claim
 this theorem. code_simp constructs kernel equations; no oracle or external
 computation result is accepted. A timeout is an unfinished gate.\<close>

theorem comma_future_instance_checked:
  "comma_future_instance_check"
  by code_simp

corollary comma_future_concrete_rank_checked:
  "comma_rank_witness comma_total_children (set comma_boundary_states)
    comma_rank_candidate"
  by (rule comma_future_instance_rank_sound[OF comma_future_instance_checked])

corollary comma_future_concrete_cycle_checked:
  "comma_surviving_delta_path comma_rank_candidate 314
    (Comma_N,2,10) (Comma_N,2,10) 924"
  by (rule comma_future_instance_cycle_sound[OF comma_future_instance_checked])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_future_instance_checked comma_future_concrete_rank_checked
      comma_future_concrete_cycle_checked})
    then () else error "Concrete comma future check depends on an oracle";
\<close>
end
