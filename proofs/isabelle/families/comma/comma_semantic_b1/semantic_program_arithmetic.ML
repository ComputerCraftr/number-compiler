(* Closed local arithmetic for normalized semantic programs.  Recursive
   Continue compilation and source/phase occurrences are not evaluated here. *)
structure Comma_Semantic_Program_Arithmetic =
struct
  fun make ctxt =
    let
      val arithmetic = Comma_Entry_Arithmetic.signed_context ctxt
      fun residual_step n = Simplifier.simplify arithmetic
        (Drule.infer_instantiate ctxt
          [(("k",0), Thm.cterm_of ctxt (HOLogic.mk_number @{typ nat} n))]
          @{thm comma_near_residual_count.simps(2)})
      val step_context = arithmetic
        |> fold Simplifier.add_cong @{thms
          comma_finite_position.case_cong_weak
          comma_semantic_port_program.case_cong_weak option.case_cong_weak}
        |> Simplifier.add_simps (@{thms
          comma_phase_program_step_at_selected
          comma_phase_program_structurally_admitted_def
          comma_phase_program_selector_phase.simps
          comma_phase_program_operator_nf.simps
          comma_phase_program_step_of_action.simps
          comma_semantic_port_program.case comma_finite_position.case
          comma_c1_b1_entry_core_port_action_def
          comma_near_symbolic_port_operator_eval comma_near_closed_germ_def
          comma_near_residual_count.simps(1)
          comma_cycle_length_fast_def comma_finite_period_fast_def
          comma_semantic_b1_near_control_port_action_def
          comma_semantic_b1_next_port_action_def comma_round_crossing_def
          comma_source_continuation_base.simps comma_source_continuation_shift.simps
          comma_source_continuation_transport.simps
          comma_semantic_port_program_of_source_def
          comma_canonical_position_admitted_def comma_sector_entry_bound_def
          comma_entry_control_program_def comma_near_control_program_def
          comma_phase_core_modulus.simps comma_phase_core_of_modulus_def
          comma_core_lift_parameters comma_cyclotomic_clock_of_def
          comma_cyclotomic_phase_def comma_cyclotomic_clock.select_convs
          option.map option.case option.sel nth_Cons'} @ map residual_step (0 upto 8))
    in Comma_Decisive_Endpoint_Kernel.make ctxt step_context end
end
