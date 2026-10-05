structure Comma_Fast_Rank_Kernel =
struct
  fun make ctxt =
    let
      val core = Comma_Fast_Kernel.make ctxt
      (* One audit authority per immutable engine/context. Dependency serials
         are reused only after a successful complete inspection; no cache is
         shared across make invocations or Isabelle sessions. *)
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      val (lookup, lookup_stats) = Comma_Decade_Rank_Lookup.make_lookup
        {numeral_context = Comma_Entry_Arithmetic.numeral_context,
         natural_context = Comma_Entry_Arithmetic.natural_context} ctxt
        @{thm comma_decade_rank_codes_def} @{thm comma_decade_rank_candidate_on_valid_def}
      fun natural t = (case try HOLogic.dest_number t of
        SOME (typ, n) => typ = @{typ nat} andalso n >= 0
      | NONE => can HOLogic.dest_nat t)
      fun convert ct = (case Thm.term_of ct of
          Const (name, _) $ (source as Const (constructor, _) $ r $ x) =>
            if name = @{const_name comma_decade_rank_candidate_on_valid} andalso
                constructor = @{const_name Comma_Decade} andalso natural r andalso natural x
            then SOME (lookup source RS @{thm eq_reflection}) else NONE
        | _ => NONE)
      val procedure = Simplifier.make_simproc ctxt
        {name = "comma_fast_rank_lookup", kind = Simplifier.Simproc,
         lhss = [@{term comma_decade_rank_candidate_on_valid} $
           Var (("s", 0), @{typ comma_decade_state})],
         proc = fn _ => fn _ => convert, identifier = []}
      val evaluation = (#context core |> Simplifier.add_proc procedure) addsimps
        @{thms comma_fast_decade_rank_step_def comma_fast_decade_bounded_rank_step_def
          comma_fast_decade_bounded_rank_range_def
          comma_decade_admitted.simps}
      fun stats () =
        let val work = lookup_stats ()
          val cert = certification ()
        in #stats core () ^
          " rank_lookup_ms=" ^ LargeInt.toString (#elapsed_ms work) ^
          " rank_lookups=" ^ Int.toString (#lookups work) ^
          " rank_hits=" ^ Int.toString (#hits work) ^
          " rank_leaf_evaluations=" ^ Int.toString (#leaf_evaluations work) ^
          " rank_internal_retained=" ^ Int.toString (#retained_internal work) ^
          " rank_evicted=" ^ Int.toString (#evicted_internal work) ^
          " rank_failed=" ^ Int.toString (#failed_work work) ^
          " rank_cert_calls=" ^ Int.toString (#calls cert) ^
          " rank_cert_nodes=" ^ Int.toString (#nodes cert) ^
          " rank_cert_ms=" ^ LargeInt.toString (#milliseconds cert) ^
          " rank_cert_failed=" ^ Int.toString (#failed_calls cert)
        end
    in {context = evaluation, stats = stats, certify = certify} end

  fun range ctxt (engine: {context: Proof.context, stats: unit -> string, certify: thm -> thm}) (lo, hi) =
    let
      val _ = if 0 <= lo andalso lo <= hi andalso hi <= 924 then ()
        else error "Invalid fast rank phase range"
      fun nat n = HOLogic.mk_number @{typ nat} n
      val proposition = HOLogic.mk_Trueprop
        (@{term comma_fast_decade_bounded_rank_range} $ @{term comma_decade_rank_candidate_on_valid} $
          nat 26 $ nat lo $ nat hi)
      val label = "Fast rank range: lo=" ^ Int.toString lo ^ " hi=" ^ Int.toString hi
      val _ = Comma_Fast_Kernel.report (label ^ " status=started")
      val started = Time.now ()
      val result = Exn.capture (fn () => Goal.prove ctxt [] [] proposition
        (fn _ => simp_tac (#context engine) 1)) ()
      val evaluation_ms = Time.toMilliseconds (Time.- (Time.now (), started))
      val _ = if Exn.is_exn result then
        Comma_Fast_Kernel.report (label ^ " status=failed evaluation_ms=" ^
          LargeInt.toString evaluation_ms) else ()
      val theorem = Exn.release result
      val _ = if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem)
          andalso Thm.prop_of theorem aconv proposition then ()
        else error "Fast rank range is not an exact closed assertion"
      val audit_started = Time.now ()
      val audited = #certify engine theorem
      val audit_ms = Time.toMilliseconds (Time.- (Time.now (), audit_started))
      val _ = Comma_Fast_Kernel.report (label ^ " status=proved evaluation_ms=" ^
        LargeInt.toString evaluation_ms ^ " audit_ms=" ^ LargeInt.toString audit_ms)
      val _ = Comma_Fast_Kernel.report ("Fast rank demand: " ^ #stats engine ())
    in audited end
end
