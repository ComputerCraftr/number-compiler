(* Optional source-level checkpoints for proof-session profiling. *)
structure Comma_Proof_Profile =
struct
  fun enabled () = getenv "COMMA_PROFILE_LOG" <> ""

  fun report line =
    let val destination = getenv "COMMA_PROFILE_LOG" in
      if destination = "" then ()
      else
        let
          val stamped = line ^ " wall_ms=" ^
            LargeInt.toString (Time.toMilliseconds (Time.now ()))
          val _ = Output.physical_stderr (stamped ^ "\n")
        in
          if destination = "1" then ()
          else File.append (Path.explode destination) (stamped ^ "\n")
        end
    end

  fun elapsed_ms started =
    LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started)))

  fun begin_stage is_enabled counter advance limit owner stage =
    if not is_enabled then NONE
    else
      let
        val ordinal = Synchronized.change_result counter (fn state =>
          let
            val (current, next) = advance state
          in (current, if current < limit then next else state) end)
      in
        if ordinal >= limit then NONE
        else
          let
            val started = Time.now ()
            val _ = report (owner ^ " stage=" ^ stage ^ "-start ordinal=" ^
              Int.toString ordinal)
          in SOME (ordinal, started) end
      end

  fun end_stage owner stage trace =
    (case trace of
      NONE => ()
    | SOME (ordinal, started) =>
        report (owner ^ " stage=" ^ stage ^ "-complete ordinal=" ^
          Int.toString ordinal ^ " elapsed_ms=" ^ elapsed_ms started))

  fun trace_stage is_enabled counter advance limit owner stage f =
    let
      val trace = begin_stage is_enabled counter advance limit owner stage
      val result = f ()
      val _ = end_stage owner stage trace
    in result end

  type stage_profile =
   {owner: string, stages: string list, active: bool,
    totals: (int * Time.time) Symtab.table Synchronized.var}

  fun time_stage (profile: stage_profile) stage work =
    let
      val {owner, stages, active, totals} = profile
    in
      if not active then work ()
      else if not (member (op =) stages stage) then
        error ("unknown " ^ owner ^ " profile stage: " ^ stage)
      else
        let
          val started = Time.now ()
          val result = Exn.capture work ()
          val elapsed = Time.- (Time.now (), started)
          val _ = Synchronized.change totals (fn table =>
            let
              val (calls, prior) = (case Symtab.lookup table stage of
                SOME value => value
              | NONE => (0, Time.zeroTime))
            in Symtab.update (stage, (calls + 1, Time.+ (prior, elapsed))) table end)
        in Exn.release result end
    end

  fun stage_profile_stats (profile: stage_profile) =
    let
      val {owner, stages, active, totals} = profile
    in
      if not active then ""
      else
        let
          val table = Synchronized.value totals
          fun fields stage =
            let val (calls, elapsed) = (case Symtab.lookup table stage of
              SOME value => value
            | NONE => (0, Time.zeroTime))
            in owner ^ "_" ^ stage ^ "_calls=" ^ Int.toString calls ^
              " " ^ owner ^ "_" ^ stage ^ "_ms=" ^
              LargeInt.toString (Time.toMilliseconds elapsed) end
        in String.concatWith " " (map fields stages) end
    end

  fun make_stage_totals owner stages: stage_profile =
    {owner = owner, stages = stages, active = enabled (),
     totals = Synchronized.var (owner ^ "_stage_totals")
       (Symtab.empty: (int * Time.time) Symtab.table)}

  fun make_progress owner stats requests recursive fallbacks =
    let
      val emit = report
      val milestones = Synchronized.var (owner ^ "_progress_milestones") (0, 0, 0)
      fun report stage =
        let
          val request_count = requests ()
          val recursive_count = recursive ()
          val fallback_count = fallbacks ()
          val request_bucket = if request_count = 0 then 0
            else 1 + ((request_count - 1) div 128)
          val recursive_bucket = recursive_count div 64
          val fallback_bucket = fallback_count div 32
          val milestone = (request_bucket, recursive_bucket, fallback_bucket)
          val advanced = Synchronized.change_result milestones
            (fn (previous as (requests_seen, recursive_seen, fallbacks_seen)) =>
              let
                val (next_requests, next_recursive, next_fallbacks) = milestone
                val changed = next_requests > requests_seen orelse
                  next_recursive > recursive_seen orelse next_fallbacks > fallbacks_seen
              in (changed, if changed then milestone else previous) end)
        in
          if advanced then emit (owner ^ " stage=" ^ stage ^ " " ^ stats ())
          else ()
        end
    in report end

  fun timer owner =
    let val started = Time.now () in
      fn stage => if getenv "COMMA_PROFILE_LOG" = "" then ()
        else report (owner ^ " stage=" ^ stage ^
          " elapsed_ms=" ^ elapsed_ms started)
    end
end
