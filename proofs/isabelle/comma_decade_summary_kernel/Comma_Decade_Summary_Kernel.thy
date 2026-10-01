theory Comma_Decade_Summary_Kernel
  imports Comma_Decade_Orbit.Comma_Decade_Orbit_Quotient
    Comma_Decade_Summary_Transport.Comma_Decade_Summary_Transport
    Comma_Decade_Terminal_Data.Comma_Decade_Terminal_Data
begin

text \<open>The reusable quotient-aware evaluator owns no global certificate.
This focused check evaluates one phase, repeats it through the same engine,
and verifies the restored proposition. Full coverage remains a separate gate.\<close>

ML_file "fast_summary_check.ML"

local_setup \<open>fn lthy =>
  let
    val engine = Comma_Decade_Summary_Kernel.make lthy
    val empty = #lens_stats engine ()
    val _ = if #lookups empty = 0 andalso #hits empty = 0 andalso
        #misses empty = 0 andalso #publications empty = 0 andalso
        #failures empty = 0 andalso #retained empty = 0 then ()
      else error "Summary engine construction eagerly evaluated coordinate lenses"
    val representative = @{term
      "comma_fast_decade_control (Comma_Decade (0::nat) 0)"}
    fun demand request =
      (case #transport engine "decade" request of
        SOME theorem =>
          if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
              Thm.term_of (Thm.rhs_of theorem) aconv representative andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm_Deps.all_oracles [theorem])
          then () else error "Demanded coordinate lens changed its exact source"
      | _ => error "Admitted coordinate offset did not produce a transport theorem")
    val offset1 = @{term "comma_fast_decade_control (Comma_Decade (0::nat) 1)"}
    val offset12 = @{term "comma_fast_decade_control (Comma_Decade (0::nat) 12)"}
    val _ = demand offset1
    val after_first = #lens_stats engine ()
    val _ = if #lookups after_first = 1 andalso #misses after_first = 1 andalso
        #publications after_first = 1 andalso #retained after_first = 1 andalso
        #hits after_first = 0 andalso #failures after_first = 0 then ()
      else error "One coordinate request did not construct exactly one lens"
    val _ = demand offset1
    val after_repeat = #lens_stats engine ()
    val _ = if #lookups after_repeat = 2 andalso #hits after_repeat = 1 andalso
        #misses after_repeat = 1 andalso #publications after_repeat = 1 andalso
        #retained after_repeat = 1 then ()
      else error "Repeated coordinate request did not reuse its exact lens"
    val _ = demand offset12
    val after_second = #lens_stats engine ()
    val _ = if #lookups after_second = 3 andalso #hits after_second = 1 andalso
        #misses after_second = 2 andalso #publications after_second = 2 andalso
        #retained after_second = 2 then ()
      else error "A second offset did not receive its own lens memo entry"
    val first = Comma_Decade_Summary_Kernel.range lthy engine (0,1)
    val repeated = Comma_Decade_Summary_Kernel.range lthy engine (0,1)
    val _ = if Thm.prop_of first aconv Thm.prop_of repeated then ()
      else error "Summary memo changed the receiving proposition"
    (* A closed theorem about a foreign occurrence cannot authorize a key. *)
    val foreign = Thm.reflexive @{cterm "0::nat"}
    val bad = Comma_Fast_Kernel.make_with_transport
      (fn name => fn _ => if name="decade" then SOME foreign else NONE) lthy
    val request = @{cterm "comma_fast_decade_control (Comma_Decade 0 0)"}
    val rejected = Exn.capture (Simplifier.rewrite (#context bad)) request
    val _ = case rejected of Exn.Exn (ERROR message) =>
          if String.isSubstring "Foreign or open fast-kernel transport" message then ()
          else error ("Unexpected transport rejection: " ^ message)
      | _ => error "Foreign transport was accepted"
  in #2 (Local_Theory.note
    ((Binding.name "comma_summary_orbit_phase_zero_checked", []), [first]) lthy) end\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_summary_orbit_phase_zero_checked}) then ()
    else error "Summary smoke depends on an oracle";
\<close>

end
