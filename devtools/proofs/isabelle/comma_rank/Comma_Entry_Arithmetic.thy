theory Comma_Entry_Arithmetic
  imports Comma_Short_Phase.Comma_Short_Phase
begin

text \<open>This is a compiled lemma table for the canonical arithmetic. All
periods are obtained from proved finite-period equations; the nine cycle
lengths reuse the same closed gcd certificates, and every modular power is a
closed equation for mod_exp. No table row is assumed.\<close>

ML_file "entry_arithmetic.ML"

ML \<open>
  val _ = let
    val (certify, stats) = Comma_Entry_Arithmetic.make_certifier @{context}
    fun rejects_open theorem =
      let
        val prior = stats ()
        val rejected = (certify theorem; false)
          handle ERROR message => String.isPrefix "Open cached theorem" message
        val after = stats ()
        val _ = if rejected andalso #calls after = #calls prior andalso
            #nodes after = #nodes prior andalso
            #failed_calls after = #failed_calls prior + 1 andalso
            #milliseconds prior <= #milliseconds after then ()
          else error "Certifier lost rejection accounting or changed proof authority"
      in () end
    val _ = rejects_open (Thm.trivial @{cprop True})
    val _ = rejects_open (Thm.assume @{cprop True})
    val _ = certify @{thm TrueI}
    val _ = if #calls (stats ()) = 1 then ()
      else error "Certifier rejected a closed theorem"
  in () end;
  val comma_entry_arithmetic = Comma_Entry_Arithmetic.build @{context};
\<close>

local_setup \<open>fn lthy =>
  let
    fun note name facts context = #2 (Local_Theory.note
      ((Binding.name name, []), facts) context)
  in lthy
    |> note "comma_compiled_cycle_length_facts" (#cycle_lengths comma_entry_arithmetic)
    |> note "comma_compiled_period_facts" (#periods comma_entry_arithmetic)
    |> note "comma_compiled_short_period_facts" (#short_periods comma_entry_arithmetic)
    |> note "comma_compiled_power_facts" (#powers comma_entry_arithmetic)
  end\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_compiled_cycle_length_facts comma_compiled_period_facts
      comma_compiled_short_period_facts
      comma_compiled_power_facts}) then ()
    else error "Compiled Entry arithmetic export depends on an oracle";
\<close>

end
