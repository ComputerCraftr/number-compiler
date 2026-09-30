theory Comma_Fast_Totality_Smoke
  imports Comma_Fast_Totality_Check.Comma_Fast_Totality_Check
begin

text \<open>A small resource probe, not an all-phase totality claim. Each
profiled row is a kernel proof reused in the positive first-phase assertion.
Progress is diagnostic output only and is never imported as proof evidence.\<close>

ML \<open>
structure Comma_Fast_Totality_Profile =
struct
  fun progress message =
    let
      val line = message ^ "\n"
      val _ = Output.physical_stderr line
      val destination = getenv "COMMA_PROFILE_LOG"
    in
      if destination = "" then ()
      else File.append (Path.explode destination) line
    end

  fun row_with ctxt evaluation stats r x =
    let
      fun nat n = HOLogic.mk_number @{typ nat} n
      val proposition = HOLogic.mk_Trueprop
        (@{term comma_fast_finishes_within} $ nat 27 $
          (@{term Comma_Decade} $ nat r $ nat x))
      val label = "Fast totality row: phase=" ^ Int.toString r ^
        " offset=" ^ Int.toString x
      val _ = progress (label ^ " status=started")
      val started = Time.now ()
      val result = Exn.capture (fn () => Goal.prove ctxt [] [] proposition
        (fn _ => simp_tac evaluation 1)) ()
      val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
      val _ = progress (label ^ " status=" ^
        (if Exn.is_exn result then "failed" else "proved") ^
        " elapsed_ms=" ^ LargeInt.toString elapsed)
      val _ = progress ("Fast kernel demand: " ^ stats ())
    in Exn.release result end

end
\<close>

text \<open>The command below executes the finite proof construction once.
It publishes exactly the same positive first-state and first-phase assertions;
method elaboration and tactic replay cannot repeat the expensive computation.\<close>

local_setup \<open>fn lthy =>
  let
    val core = Comma_Fast_Kernel.make lthy
    val engine = {context = #context core addsimps
      @{thms comma_fast_finishes_within_eval comma_fast_totality_phase_def
        comma_fast_totality_range_def comma_fast_totality_rectangle_def},
      stats = #stats core}
    val rows = map
      (Comma_Fast_Totality_Profile.row_with lthy (#context engine) (#stats engine) 0)
      (0 upto 90)
    val assembly = Comma_Entry_Arithmetic.natural_context lthy addsimps
      (@{thms comma_fast_totality_phase_def list_all_Nil_iff list_all_Cons_iff
        upt_rec} @ rows)
    val phase = Goal.prove lthy [] [] @{prop "comma_fast_totality_phase 0 27"}
      (fn _ => simp_tac assembly 1)
    val (_, lthy') = Local_Theory.note
      ((Binding.name "comma_fast_totality_first_state", []), [hd rows]) lthy
    val (_, lthy'') = Local_Theory.note
      ((Binding.name "comma_fast_totality_first_phase", []), [phase]) lthy'
  in lthy'' end\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_totality_first_state comma_fast_totality_first_phase})
    then () else error "Fast totality smoke depends on an oracle";
\<close>
end
