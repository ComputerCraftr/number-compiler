theory Comma_Sector_Mask_Smoke
  imports Comma_Sector_Mask_Constructor
begin

ML_file "sector_mask_constructor.ML"

local_setup \<open>
  fn lthy =>
    let
      val engine = Comma_Sector_Mask_Constructor.make lthy
        {max_rows=900, max_clauses=8192, max_guard_nodes=8192, max_operations=100000}
      val crossing = #crossing_probe engine ()
      val first = #word engine 9 0
      val prior = #stats engine ()
      val repeated = #word engine 9 0
      val after = #stats engine ()
      val _ = if #operations prior = #operations after andalso
          #hits after = #hits prior + 1 andalso
          Thm.prop_of (#theorem first) aconv Thm.prop_of (#theorem repeated)
        then () else error "Sector row cache repeated construction or changed its theorem"
      val _ = Comma_Fast_Kernel.report (#report engine ())
      val (_, lthy') = Local_Theory.note
        ((Binding.name "comma_sector_nine_mask_smoke", []), [#theorem first, crossing]) lthy
    in lthy' end
\<close>

local_setup \<open>
  fn lthy =>
    let
      fun check_hint omission_budget =
        let
          val engine = Comma_Sector_Mask_Constructor.make lthy
            {max_rows=32, max_clauses=128, max_guard_nodes=128, max_operations=2048}
      (* A deliberately wrong scheduling hint may cause refusal, but cannot
         manufacture full phase coverage or poison the later exact retry. *)
      val _ = #set_omission_budget engine omission_budget
      val omitted = Exn.capture (fn () => #word engine 8 0) ()
      val _ = if Exn.is_exn omitted then ()
        else error "Omitted nonempty intersections acquired publication authority"
      val _ = if omission_budget = 1 then
          (case omitted of
            Exn.Exn (ERROR message) => if String.isSubstring "full coverage" message then ()
              else error "Selective omission failed before the coverage check"
          | _ => error "Selective omission did not reach the coverage check")
        else ()
      val failed = #stats engine ()
      val _ = #set_omission_budget engine 0
      val recovered = #word engine 8 0
      val after = #stats engine ()
      val _ = if #failures failed > 0 andalso #retained after > #retained failed
        then () else error "Rejected scheduling corrupted the exact retry"
      val _ = Comma_Fast_Kernel.report ("scheduling_retry " ^ #report engine ())
        in #theorem recovered end
      val recovered = map check_hint [~1, 1]
      val (_, lthy') = Local_Theory.note
        ((Binding.name "comma_sector_scheduling_retry", []), recovered) lthy
    in lthy' end
\<close>

local_setup \<open>
  fn lthy =>
    let
      val engine = Comma_Sector_Mask_Constructor.make lthy
        {max_rows=32, max_clauses=128, max_guard_nodes=128, max_operations=2048}
      val forwarded = #word engine 8 0
      val prior = #stats engine ()
      val repeated = #word engine 8 0
      val after = #stats engine ()
      val _ = if #forwarding_aliases prior=1 andalso #transports prior=0
          andalso #operations prior= #operations after
          andalso Thm.prop_of (#theorem forwarded) aconv Thm.prop_of (#theorem repeated)
        then () else error "Period-one forwarding rebuilt masks or lost memo identity"
      val _ = Comma_Fast_Kernel.report ("period_one_forward " ^ #report engine ())
    in #2 (Local_Theory.note
      ((Binding.name "comma_sector_period_one_forward_smoke", []), [#theorem forwarded]) lthy) end
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_sector_nine_mask_smoke comma_sector_scheduling_retry
      comma_sector_period_one_forward_smoke}) then ()
    else error "Sector row smoke depends on an oracle";
\<close>
end
