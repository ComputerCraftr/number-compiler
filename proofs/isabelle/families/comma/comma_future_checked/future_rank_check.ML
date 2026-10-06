(* Legacy exact-rank checker; shared candidate lookup has no transition replay. *)
structure Comma_Future_Rank_Check =
struct
  fun make ctxt =
    let
      val core = Comma_Fast_Kernel.make ctxt
      val (n_procedure, n_stats) = Comma_Future_Rank_Lookup.selected_table ctxt "N" @{thm comma_rank_codes_N_def}
      val (z_procedure, z_stats) = Comma_Future_Rank_Lookup.selected_table ctxt "Z" @{thm comma_rank_codes_Z_def}
      val evaluation = (#context core
        |> Simplifier.add_proc n_procedure
        |> Simplifier.add_proc z_procedure) addsimps
        @{thms comma_boundary_states_def comma_boundary_valid_def
          comma_fast_boundary_children_def comma_fast_boundary_macro_def
          comma_fast_boundary_run_numeral comma_finite_initial_def
          comma_future_rank_row_def comma_future_rank_check_def
          comma_rank_candidate_on_valid_def comma_rank_lookup_def
          comma_rank_lookup_result.case comma_rank_code_at_def
          comma_boundary_kind.simps comma_finite_outcome.case
          option.case option.map option.inject option.distinct
          list.distinct list.inject list.map concat.simps append.simps
          list_ex_Nil_iff list_ex_Cons_iff}
      fun stats () = #stats core () ^ " " ^ n_stats () ^ " " ^ z_stats ()
    in {context = evaluation, stats = stats} end

  fun exact_closed ctxt proposition theorem =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        Thm.prop_of theorem aconv proposition andalso
        null (Thm_Deps.all_oracles [theorem])
    then theorem
    else error "Future rank checker produced a non-closed or inexact theorem"

  fun prove ctxt proposition context label =
    let
      val started = Time.now ()
      val result = Exn.capture (fn () => Goal.prove ctxt [] [] proposition
        (fn _ => simp_tac context 1)) ()
      val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
      val _ = if Exn.is_exn result then
        Comma_Fast_Kernel.report
          (label ^ " status=failed evaluation_ms=" ^ LargeInt.toString elapsed)
        else ()
      val theorem = exact_closed ctxt proposition (Exn.release result)
      val _ = Comma_Fast_Kernel.report
        (label ^ " status=proved evaluation_ms=" ^ LargeInt.toString elapsed)
    in theorem end

  fun tactic ctxt =
    let
      val engine = make ctxt
      val context = #context engine
      val row = HOLogic.mk_Trueprop
        (@{term comma_future_rank_row} $ HOLogic.mk_number @{typ nat} 28 $
          @{term comma_rank_candidate_on_valid} $
          HOLogic.mk_prod (@{term Comma_N},
            HOLogic.mk_prod (HOLogic.mk_number @{typ nat} 2,
              HOLogic.mk_number @{typ nat} 0)))
      val _ = Comma_Fast_Kernel.report
        "Future rank first-row status=started state=(N,2,0)"
      val _ = prove ctxt row context "Future rank first-row"
      val _ = Comma_Fast_Kernel.report
        "Future rank aggregate status=started rows=14784"
      fun aggregate_tactic state =
        let
          val started = Time.now ()
          val result = Exn.capture
            (fn () => Seq.pull (simp_tac context 1 state)) ()
          val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
        in
          (case result of
            Exn.Res NONE =>
              (Comma_Fast_Kernel.report
                ("Future rank aggregate status=failed evaluation_ms=" ^
                  LargeInt.toString elapsed ^ " " ^ #stats engine ());
               Seq.empty)
          | Exn.Res (SOME (proved, remaining)) =>
              let
                val solved = Thm.nprems_of proved = 0
                val status = if solved then "proved" else "incomplete"
                val _ = Comma_Fast_Kernel.report
                  ("Future rank aggregate status=" ^ status ^
                    " evaluation_ms=" ^ LargeInt.toString elapsed ^
                    " unresolved=" ^ Int.toString (Thm.nprems_of proved) ^
                    " " ^ #stats engine ())
              in Seq.cons proved remaining end
          | Exn.Exn failure =>
              (Comma_Fast_Kernel.report
                ("Future rank aggregate status=failed evaluation_ms=" ^
                  LargeInt.toString elapsed ^ " " ^ #stats engine ());
               Exn.reraise failure))
        end
    in aggregate_tactic end
end
