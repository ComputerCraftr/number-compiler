(* Optional source-level checkpoints for proof-session profiling. *)
structure Comma_Proof_Profile =
struct
  fun enabled () = getenv "ISABELLE_PROOF_PROFILE_LOG" <> ""

  fun report line =
    let val destination = getenv "ISABELLE_PROOF_PROFILE_LOG" in
      if destination = "" then ()
      else
        let
          val stamped = line ^ " family=comma wall_ms=" ^
            LargeInt.toString (Time.toMilliseconds (Time.now ()))
          val _ = Output.physical_stderr (stamped ^ "\n")
        in
          if destination = "1" then ()
          else File.append (Path.explode destination) (stamped ^ "\n")
        end
    end

  (* Coarse records are a diagnostic sidecar only.  The lock serializes both
     sequence allocation and each complete append within one session process. *)
  val progress_serial = Synchronized.var "isabelle_proof_progress" 0
  fun progress_safe text = text <> "" andalso size text <= 256 andalso
    forall (fn c => Char.isAlphaNum c andalso Char.ord c < 128 orelse
      member (op =) [#"_", #"-", #"."] c) (String.explode text)
  fun progress_mode () = getenv "NUMBER_COMPILER_PROOF_PROGRESS"
  fun progress_enabled () =
    (progress_mode () = "coarse" orelse progress_mode () = "detailed") andalso
    progress_safe (getenv "NUMBER_COMPILER_PROOF_PROGRESS_RUN") andalso
    getenv "NUMBER_COMPILER_PROOF_PROGRESS_PATH" <> ""
  fun progress_event session lane invocation parent stage root event =
    if not (progress_enabled ()) orelse not (forall progress_safe
      ([session,lane,invocation,stage,event] @ the_list parent)) then ()
    else
      let
        val run = getenv "NUMBER_COMPILER_PROOF_PROGRESS_RUN"
        fun quoted text = "\"" ^ text ^ "\""
        val outcome = Exn.capture (fn () => Synchronized.change progress_serial (fn sequence =>
          let
            val destination = Path.explode (getenv "NUMBER_COMPILER_PROOF_PROGRESS_PATH")
            val fields = ["\"run\":" ^ quoted run,
              "\"session\":" ^ quoted session, "\"lane\":" ^ quoted lane,
              "\"invocation\":" ^ quoted invocation,
              "\"parent\":" ^ (case parent of NONE => "null" | SOME value => quoted value),
              "\"stage\":" ^ quoted stage,
              "\"root\":" ^ (case root of NONE => "null" | SOME value => Int.toString value),
              "\"event\":" ^ quoted event, "\"sequence\":" ^ Int.toString sequence]
            val _ = File.append destination ("{" ^ commas fields ^ "}\n")
          in sequence + 1 end)) ()
      in if Exn.is_interrupt_exn outcome then Exn.release outcome else () end

  fun progress_scope session lane root parent stage work =
    if not (progress_enabled ()) then work NONE
    else
      let
        val invocation = Synchronized.change_result progress_serial
          (fn sequence => ("i" ^ Int.toString sequence,sequence+1))
        val _ = progress_event session lane invocation parent stage root "start"
        val result = Exn.capture (fn () => work (SOME invocation)) ()
        val _ = progress_event session lane invocation parent stage root
          (case result of Exn.Res _ => "done" | Exn.Exn _ => "fail")
      in Exn.release result end

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
      fn stage => if getenv "ISABELLE_PROOF_PROFILE_LOG" = "" then ()
        else report (owner ^ " stage=" ^ stage ^
          " elapsed_ms=" ^ elapsed_ms started)
    end
end
