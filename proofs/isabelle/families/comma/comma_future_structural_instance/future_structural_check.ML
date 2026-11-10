structure Comma_Future_Structural_Instance_Check =
struct
  fun make ctxt =
    let
      val (certify, _) = Comma_Entry_Arithmetic.make_certifier ctxt
      val summary = Comma_Decade_Summary_Kernel.make ctxt
      val (n_proc, n_stats) = Comma_Future_Rank_Lookup.selected_table ctxt "N" @{thm comma_rank_codes_N_def}
      val (z_proc, z_stats) = Comma_Future_Rank_Lookup.selected_table ctxt "Z" @{thm comma_rank_codes_Z_def}
      val context = (#context summary
        |> Simplifier.add_proc n_proc
        |> Simplifier.add_proc z_proc) |> Simplifier.add_simps
        @{thms comma_future_descent_phase_range_def comma_future_descent_row_def
          comma_summary_boundary_children_def comma_fast_total_boundary_def
          comma_decade_summary_resume.simps comma_boundary_states_def
          comma_boundary_valid_def comma_finite_initial_def
          comma_decade_rank_candidate_on_valid_def
          comma_decade_terminal_candidate_on_valid_def
          comma_rank_candidate_on_valid_def comma_rank_lookup_def
          comma_rank_lookup_result.case comma_rank_code_at_def
          comma_boundary_kind.simps comma_finite_outcome.case
          option.case option.map option.inject option.distinct
          list.distinct list.inject list.map concat.simps append.simps
          list_all_Nil_iff list_all_Cons_iff list_ex_Nil_iff list_ex_Cons_iff}
      fun stats () = #stats summary () ^ " " ^ n_stats () ^ " " ^ z_stats ()
    in {context=context, stats=stats, certify=certify} end

  fun range ctxt (engine: {context: Proof.context, stats: unit -> string,
      certify: thm -> thm}) (lo,hi) =
    let
      val _ = if 0 <= lo andalso lo <= hi andalso hi <= 924 then ()
        else error "Invalid future structural phase range"
      fun nat n = HOLogic.mk_number @{typ nat} n
      val proposition = HOLogic.mk_Trueprop
        (@{term comma_future_descent_phase_range} $
          @{term comma_decade_rank_candidate_on_valid} $
          @{term comma_decade_terminal_candidate_on_valid} $
          @{term comma_rank_candidate_on_valid} $ nat lo $ nat hi)
      val started = Time.now ()
      val theorem = #certify engine (Goal.prove ctxt [] [] proposition
        (fn _ => simp_tac (#context engine) 1))
      val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
      val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
          andalso Thm.prop_of theorem aconv proposition then ()
        else error "Future structural range is not an exact closed theorem"
      val _ = if getenv "COMMA_PROFILE_LOG" = "" then () else
        Comma_Fast_Kernel.report
          ("Future structural range lo=" ^ Int.toString lo ^
           " hi=" ^ Int.toString hi ^
           " evaluation_ms=" ^ LargeInt.toString elapsed ^ " " ^ #stats engine ())
    in theorem end
end
