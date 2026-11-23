(* Checked application bindings for direct semantic rows.  The physical action
   is a transport input, not an expression identity.  This owner never
   discovers or re-proves child expressions while transporting a binding. *)
functor Comma_Direct_Row_Bindings (
  val fixed_entry_port_conversion_plan: Proof.context ->
    {procedure: Simplifier.simproc, plain_procedure: Simplifier.simproc,
     statistics: unit -> string}
  val core_parameter_conversion_plan: Proof.context ->
    {procedure: Simplifier.simproc, plain_procedure: Simplifier.simproc,
     hits: unit -> int, seed_hits: unit -> int}
) =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Row_Plan = Comma_Direct_Entry_Row_Plan (
    val fixed_entry_port_conversion_plan = fixed_entry_port_conversion_plan
    val core_parameter_conversion_plan = core_parameter_conversion_plan)
  val relation = @{term comma_direct_source_relation}

  fun make ctxt (computation: Compiler.computation) (program_bindings: (term * term) list) =
    let
      val proposal_requests = Unsynchronized.ref 0
      val proposal_actions = Unsynchronized.ref 0
      val proposal_action_elapsed = Unsynchronized.ref Time.zeroTime
      val proposal_start = Time.now ()
      val _ = Comma_Proof_Profile.report "Direct Entry proposals start"
      fun proposals (program,_) table =
        (case Compiler.parse_program program of
          Compiler.Entry {sector,residue,core,...} =>
            fold (fn wanted => fn current =>
              let
                val _ = proposal_requests := !proposal_requests + 1
                val key = #entry_action_key computation sector residue core wanted
              in if Termtab.defined current key then current
                else
                  let
                    val action_start = Time.now ()
                    val outcome = Exn.capture
                      (fn () => #entry_action computation sector residue core wanted) ()
                    val _ = proposal_action_elapsed := Time.+ (!proposal_action_elapsed,
                      Time.- (Time.now (),action_start))
                    val action = Exn.release outcome
                    val _ = proposal_actions := !proposal_actions + 1
                    val representative: Compiler.entry_representative =
                      {sector=sector,residue=residue,core=core,wanted=wanted,action=action}
                  in Termtab.update (key,representative) current end
              end)
              (#supported_values computation core) table
        | _ => table)
      val proposal_table = fold proposals program_bindings Termtab.empty
      val proposal_elapsed = Time.- (Time.now (),proposal_start)
      fun proposal_statistics () =
        "entry_row_proposal_requests=" ^ Int.toString (!proposal_requests) ^
        " entry_row_action_calls=" ^ Int.toString (!proposal_actions) ^
        " entry_row_action_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!proposal_action_elapsed)) ^
        " entry_row_proposal_ms=" ^ LargeInt.toString (Time.toMilliseconds proposal_elapsed)
      val _ = Comma_Proof_Profile.report ("Direct Entry proposals " ^ proposal_statistics ())
      val row_plan = Row_Plan.make ctxt computation (Termtab.dest proposal_table)
      val _ = List.app (fn (program,_) => case Compiler.parse_program program of
          Compiler.Entry {sector,residue,core,...} =>
            #prewarm row_plan sector residue core
        | _ => ()) program_bindings
      val representatives = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val registered = Unsynchronized.ref 0
      val transports = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      fun relation_prop action expression = HOLogic.mk_Trueprop (relation $ action $ expression)
      fun key action expression = HOLogic.mk_prod (action,expression)
      fun register action expression theorem =
        let
          val expected = relation_prop action expression
          val checked = Utils.exact_prop ctxt "Direct row representative" expected theorem
          val pair = key action expression
        in case Termtab.lookup (!representatives) pair of
          SOME previous =>
            (hits := !hits+1;
             Utils.exact_prop ctxt "Existing direct row representative" expected previous)
        | NONE =>
            (representatives := Termtab.update (pair,checked) (!representatives);
             registered := !registered+1; checked)
        end
      fun transport target representative expression equality =
        let
          val _ = if forall Utils.closed [target,representative,expression] then ()
            else error "Direct row binding is open"
          val expected_eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (target,representative))
          val equality = Utils.exact_prop ctxt "Direct row action equality" expected_eq equality
          val representative_fact = (case Termtab.lookup (!representatives)
              (key representative expression) of
            SOME theorem => Utils.exact_prop ctxt "Direct row representative lookup"
              (relation_prop representative expression) theorem
          | NONE => error "Direct row representative has not been certified")
          val expected = relation_prop target expression
          val action_eq = equality RS @{thm eq_reflection}
          val relation_eq = Thm.combination
            (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt relation)) action_eq)
            (Thm.reflexive (Thm.cterm_of ctxt expression))
          val proposition_eq = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) relation_eq
          val theorem = Thm.equal_elim (Thm.symmetric proposition_eq) representative_fact
          val theorem = Utils.exact_prop ctxt "Direct row binding transport" expected theorem
          val _ = transports := !transports+1
        in theorem end
      fun entry chart sector residue core wanted expression =
        let
          val key = #entry_action_key computation sector residue core wanted
          val proposed = (case Termtab.lookup proposal_table key of
              SOME item => item | NONE => error "Missing direct row representative proposal")
          val equality = #transport_prepared row_plan chart sector residue core wanted RS @{thm meta_eq_to_obj_eq}
          val target = @{term comma_phase_program_entry_core_value_action} $
            HOLogic.mk_number @{typ nat} sector $ HOLogic.mk_number @{typ nat} residue $
            core $ HOLogic.mk_number @{typ nat} wanted
        in transport target (#action proposed) expression equality end
      fun representative sector residue core wanted =
        (case Termtab.lookup proposal_table (#entry_action_key computation sector residue core wanted) of
          SOME item => #action item | NONE => error "Missing direct row representative proposal")
      fun statistics () = proposal_statistics () ^
        " direct_row_representatives=" ^ Int.toString (!registered) ^
        " direct_row_representative_hits=" ^ Int.toString (!hits) ^
        " direct_row_binding_transports=" ^ Int.toString (!transports) ^ " " ^
        #statistics row_plan ()
    in {register=register,transport=transport,entry=entry,prepare= #prepare row_plan,
      representative=representative,statistics=statistics} end
end
