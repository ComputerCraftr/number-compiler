theory Comma_Frontier24_Exit_Shift_Regression
  imports Comma_Semantic_B1.Comma_Program_Continue_Guard_Exact
begin

text \<open>
An Exit observes the accumulated external offset as well as the source's
internal delta. A phase-coordinate rotation alone cannot replace that offset:
for this admitted source, total offset 1 accepts class 0, while total offset 2
rejects it, independently of the phase coordinate.
\<close>

lemma comma_frontier24_exit_observes_accumulated_offset:
  "\<forall>phase.
    comma_phase_continue_action_observer phase 1 0
      (Comma_Continuation_Exit (Comma_Entry 1 0 0) 1) 0 \<and>
    \<not> comma_phase_continue_action_observer phase 1 1
      (Comma_Continuation_Exit (Comma_Entry 1 0 0) 1) 0"
  by (simp add: comma_phase_continue_action_observer_def
      comma_phase_continue_exit_target_def comma_decade_root_admitted_def
      comma_shift_position.simps comma_offset_orbit_def
      comma_digit_orbit_sum_def)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "frontier24 Exit observes accumulated external offset"
    @{thms comma_frontier24_exit_observes_accumulated_offset}
\<close>

end
