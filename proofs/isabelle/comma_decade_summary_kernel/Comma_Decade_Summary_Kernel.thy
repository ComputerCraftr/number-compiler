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
