theory Comma_Round_Phase_Slice
  imports Comma_Round_Witness_Check.Comma_Round_Witness
begin

text \<open>This bounded instance checks every offset 0 through 90 at the
candidate phase against exact, closed control-round equations produced by the
control projection of the checked weighted constructor. Exact control counts,
terminal charts and events are retained. The rank observer does not instantiate
full weighted records or universal occurrence certificates per state; the
generic weighted refinement supplies those semantics. Guard-family size
instrumentation remains unavailable, not zero. This refinement does not establish
the complete 84,084-state decade rank or the boundary future-safety rank.\<close>

ML_file "round_phase_five.ML"
ML_file "round_phase_check.ML"

local_setup \<open>fn lthy => #2 (Local_Theory.note
  ((Binding.name "comma_round_phase_slice", []), comma_round_phase_slice) lthy)\<close>

ML \<open>
  val comma_final_audit_start = Time.now ();
  val _ = if null (Thm_Deps.all_oracles @{thms comma_round_phase_slice}) then ()
    else error "Phase slice export depends on an oracle";
  val _ = comma_export_phase_metrics
    (Time.- (Time.now (), comma_final_audit_start));
\<close>

end
