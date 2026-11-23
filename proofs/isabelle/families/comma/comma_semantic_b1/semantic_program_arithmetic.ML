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

  (* A caller retains one normalized program context for its checked points.
     Formatting trace terms belongs to the explicitly requested profile. *)
  fun class_step_tactic ctxt =
    let
      val profiling = Comma_Proof_Profile.enabled ()
      fun report message =
        if profiling then Comma_Proof_Profile.report ("Continue tails stage=" ^ message ()) else ()
      val _ = report (K "setup-start")
      val arithmetic = Comma_Entry_Arithmetic.signed_context ctxt
      val expose = arithmetic |> Simplifier.add_simps @{thms
        comma_semantic_phase_program_class_step_def
        comma_semantic_phase_program_for_class_def
        comma_offset_representatives_def nth_Cons'
        comma_entry_control_program_def comma_finite_period_fast_def
        comma_core_lift_parameters comma_phase_core_of_modulus_def option.case}
      val endpoint = make ctxt
      val step_context = #context endpoint
      val _ = report (K "arithmetic-ready")
      fun lhs cv = Conv.arg_conv (Conv.fun_conv (Conv.arg_conv cv))
      val unfold_round = lhs (Conv.arg_conv (Conv.arg_conv
        (Conv.rewr_conv (mk_meta_eq @{thm comma_semantic_phase_program_round_unfold}))))
      fun selected_step ct =
        let
          val _ = report (fn () => "step-start term=" ^
            Syntax.string_of_term ctxt (Thm.term_of ct))
          val equation = Simplifier.rewrite step_context ct
          val _ = report (fn () => "step-done result=" ^
            Syntax.string_of_term ctxt (Thm.term_of (Thm.rhs_of equation)))
        in equation end
      val evaluate_step = lhs
        (Conv.arg_conv (Conv.arg_conv (Conv.arg_conv selected_step)))
      val finish = ctxt |> Simplifier.add_proc (#simproc endpoint)
      val _ = report (K "finish-ready")
      val layer = ALLGOALS
        (CONVERSION (Conv.try_conv (unfold_round then_conv evaluate_step))
          THEN' simp_tac finish)
      fun traced label tactic =
        if profiling then fn state =>
          (report (fn () => label ^ "-start");
           Seq.map (fn result =>
             (report (fn () => label ^ "-done"); result)) (tactic state))
        else tactic
    in traced "expose" (ALLGOALS (simp_tac expose)) THEN
      REPEAT_DETERM (CHANGED_PROP (traced "layer" layer)) end
end
