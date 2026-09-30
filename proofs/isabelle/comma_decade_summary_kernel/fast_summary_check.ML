structure Comma_Decade_Summary_Kernel =
struct
  fun make ctxt =
    let
      val (certify, _) = Comma_Entry_Arithmetic.make_certifier ctxt
      (* Preprove the 91 coordinate lenses, leaving decimal phase symbolic.
         The control memo sees only the representative; occurrence labels are
         still checked separately. No candidate transition table is trusted. *)
      val orbit_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms comma_offset_representative_def comma_offset_representatives_def
          comma_offset_orbit_def comma_digit_orbit_sum_def power2_eq_square
          nth_Cons' of_nat_numeral of_nat_0 of_nat_1
          zmod_zminus1_eq_if zmod_zminus2_eq_if}
      fun lens x =
        let
          val rule = Drule.infer_instantiate ctxt
            [(("x",0), Thm.cterm_of ctxt (HOLogic.mk_number @{typ nat} x))]
            @{thm comma_decade_control_orbit_representative}
          val bound = Goal.prove ctxt [] []
            (HOLogic.mk_Trueprop (@{term "(\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool"} $
              HOLogic.mk_number @{typ nat} x $ @{term "90::nat"}))
            (fn _ => simp_tac orbit_context 1)
          val admitted = rule OF [bound]
          val reduced = Conv.fconv_rule
            (Conv.arg_conv (Conv.arg_conv (Simplifier.rewrite orbit_context))) admitted
        in certify reduced end
      val lenses = Vector.fromList (map lens (0 upto 90))
      val transported = Unsynchronized.ref 0
      val transport_time = Unsynchronized.ref Time.zeroTime
      fun transport name key =
        if name <> "decade" then NONE else
        (case key of
          Const (_, _) $ (Const (_, _) $ phase $ offset) =>
            (case try HOLogic.dest_number offset of
              SOME (typ,x) =>
                if typ <> @{typ nat} orelse x<0 orelse x>90 then NONE else
                let
                  val started = Time.now ()
                  val rule = Drule.infer_instantiate ctxt
                    [(("r",0), Thm.cterm_of ctxt phase)] (Vector.sub (lenses,x))
                  val equation = rule RS @{thm eq_reflection}
                  val result = if Thm.is_reflexive equation then NONE
                    else (transported := !transported+1; SOME equation)
                  val _ = transport_time := Time.+
                    (!transport_time, Time.- (Time.now (), started))
                in result end
            | NONE => NONE)
        | _ => NONE)
      val core = Comma_Fast_Kernel.make_with_transport transport ctxt
      val (rank_lookup, rank_stats) = Comma_Decade_Rank_Lookup.make_lookup
        {numeral_context = Comma_Entry_Arithmetic.numeral_context,
         natural_context = Comma_Entry_Arithmetic.natural_context} ctxt
        @{thm comma_decade_rank_codes_def} @{thm comma_decade_rank_candidate_def}
      val (terminal_lookup, terminal_stats) = Comma_Decade_Rank_Lookup.make_lookup
        {numeral_context = Comma_Entry_Arithmetic.numeral_context,
         natural_context = Comma_Entry_Arithmetic.natural_context} ctxt
        @{thm comma_decade_terminal_codes_def}
        @{thm comma_decade_terminal_code_candidate_def}
      fun natural t = (case try HOLogic.dest_number t of
        SOME (typ, n) => typ = @{typ nat} andalso n >= 0
      | NONE => can HOLogic.dest_nat t)
      fun unary_proc proc_name constant pattern lookup =
        let
          fun convert ct = (case Thm.term_of ct of
              Const (name, _) $ (source as Const (constructor, _) $ r $ x) =>
                if name = constant andalso constructor = @{const_name Comma_Decade}
                    andalso natural r andalso natural x
                then SOME (lookup source RS @{thm eq_reflection}) else NONE
            | _ => NONE)
        in Simplifier.make_simproc ctxt
          {name = proc_name, kind = Simplifier.Simproc,
           lhss = [pattern], proc = fn _ => fn _ => convert, identifier = []}
        end
      val rank_proc = unary_proc "comma_summary_rank_lookup"
        @{const_name comma_decade_rank_candidate}
        (@{term comma_decade_rank_candidate} $ Var (("s",0), @{typ comma_decade_state}))
        rank_lookup
      val terminal_proc = unary_proc "comma_summary_terminal_lookup"
        @{const_name comma_decade_terminal_code_candidate}
        (@{term comma_decade_terminal_code_candidate} $ Var (("s",0), @{typ comma_decade_state}))
        terminal_lookup
      val evaluation = (#context core
        |> Simplifier.add_proc rank_proc
        |> Simplifier.add_proc terminal_proc) addsimps
        @{thms comma_fast_decade_summary_step_def comma_fast_decade_summary_range_def
          comma_decade_admitted.simps comma_decade_terminal_candidate_def
          comma_terminal_from_code_eval}
      fun stats () =
        let val r = rank_stats (); val t = terminal_stats () in
          #stats core () ^
          " summary_orbit_transports=" ^ Int.toString (!transported) ^
          " summary_transport_ms=" ^ LargeInt.toString (Time.toMilliseconds (!transport_time)) ^
          " summary_rank_lookups=" ^ Int.toString (#lookups r) ^
          " summary_rank_ms=" ^ LargeInt.toString (#elapsed_ms r) ^
          " summary_terminal_lookups=" ^ Int.toString (#lookups t) ^
          " summary_terminal_ms=" ^ LargeInt.toString (#elapsed_ms t)
        end
    in {context=evaluation, stats=stats, certify=certify} end

  fun range ctxt (engine: {context: Proof.context, stats: unit -> string,
      certify: thm -> thm}) (lo,hi) =
    let
      val _ = if 0 <= lo andalso lo <= hi andalso hi <= 924 then ()
        else error "Invalid summary phase range"
      fun nat n = HOLogic.mk_number @{typ nat} n
      val proposition = HOLogic.mk_Trueprop
        (@{term comma_fast_decade_summary_range} $ @{term comma_decade_rank_candidate} $
          @{term comma_decade_terminal_candidate} $ nat lo $ nat hi)
      val started = Time.now ()
      val theorem = #certify engine (Goal.prove ctxt [] [] proposition
        (fn _ => simp_tac (#context engine) 1))
      val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
          andalso Thm.prop_of theorem aconv proposition then ()
        else error "Decade summary range is not an exact closed theorem"
      val _ = if getenv "COMMA_PROFILE_LOG" = "" then () else
        Comma_Fast_Kernel.report
          ("Decade summary range lo=" ^ Int.toString lo ^
           " hi=" ^ Int.toString hi ^ " evaluation_ms=" ^
           LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started))) ^
           " " ^ #stats engine ())
    in theorem end
end
