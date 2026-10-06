(* Optional source-level checkpoints for proof-session profiling. *)
structure Comma_Proof_Profile =
struct
  fun report line =
    let
      val destination = getenv "COMMA_PROFILE_LOG"
      val _ = if destination = "" then ()
        else Output.physical_stderr (line ^ "\n")
    in
      if destination = "" orelse destination = "1" then ()
      else File.append (Path.explode destination) (line ^ "\n")
    end

  fun elapsed_ms started =
    LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started)))

  fun timer owner =
    let val started = Time.now () in
      fn stage => if getenv "COMMA_PROFILE_LOG" = "" then ()
        else report (owner ^ " stage=" ^ stage ^
          " elapsed_ms=" ^ elapsed_ms started)
    end
end
