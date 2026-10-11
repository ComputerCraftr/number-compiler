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

  fun timer owner =
    let val started = Time.now () in
      fn stage => if getenv "COMMA_PROFILE_LOG" = "" then ()
        else report (owner ^ " stage=" ^ stage ^
          " elapsed_ms=" ^ elapsed_ms started)
    end
end
