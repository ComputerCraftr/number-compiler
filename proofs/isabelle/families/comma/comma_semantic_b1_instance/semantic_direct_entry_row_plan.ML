(* Checked factored Entry row equations shared by selector and direct owners. *)
functor Comma_Direct_Entry_Row_Plan (
  val fixed_entry_port_conversion_plan: Proof.context ->
    {procedure: Simplifier.simproc, plain_procedure: Simplifier.simproc,
     statistics: unit -> string}
  val core_parameter_conversion_plan: Proof.context ->
    {procedure: Simplifier.simproc, plain_procedure: Simplifier.simproc,
     hits: unit -> int, seed_hits: unit -> int}
) =
struct
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  val actionT = @{typ comma_source_continuation_action}
  fun nat n = HOLogic.mk_number natT n
  fun const name T args =
    list_comb (Const (name,fold_rev (curry (op -->)) (map fastype_of args) T),args)
  (* Each candidate key is a proposed (sector,digit,port-row) action class.
     Its representative equation is admitted by the kernel before it can be
     transported to another source.  The proposed key itself is not evidence. *)
  fun make ctxt (computation: Compiler.computation)
      (proposed: (term * Compiler.entry_representative) list) =
    let
      val representatives = fold Termtab.update
        proposed Termtab.empty
      val proofs = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val misses = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val key_elapsed = Unsynchronized.ref Time.zeroTime
      val representative_elapsed = Unsynchronized.ref Time.zeroTime
      fun timed elapsed f =
        let val start = Time.now ()
            val outcome = Exn.capture f ()
            val _ = elapsed := Time.+ (!elapsed,Time.- (Time.now (),start))
        in Exn.release outcome end
      val ports = fixed_entry_port_conversion_plan ctxt
      val parameters = core_parameter_conversion_plan ctxt
      val row_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc (#plain_procedure ports)
        |> Simplifier.add_proc (#plain_procedure parameters)
        |> Simplifier.add_simps @{thms comma_entry_row_action_simp_rules}
      val evaluator = Simplifier.rewrite row_context
      val key_context = Comma_Entry_Arithmetic.signed_context ctxt
        |> Simplifier.add_proc (#plain_procedure ports)
        |> Simplifier.add_proc (#plain_procedure parameters)
        |> Simplifier.add_simps (filter_out
          (fn theorem => Thm.eq_thm_prop (theorem,@{thm comma_core_seed_def}))
          @{thms comma_entry_core_key_simp_rules})
        |> Simplifier.add_simps @{thms Num.inc.simps}
      val key_evaluator = Simplifier.rewrite key_context
      val sector_facts = Unsynchronized.ref (Inttab.empty: thm list Inttab.table)
      fun sector f =
        (case Inttab.lookup (!sector_facts) f of
          SOME facts => facts
        | NONE =>
            let
              fun prove proposition = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop proposition)
                (fn {context,...} => simp_tac
                  (Comma_Entry_Arithmetic.natural_context context) 1)
              val facts = [prove (HOLogic.mk_binrel @{const_name less_eq} (nat 1,nat f)),
                prove (HOLogic.mk_binrel @{const_name less_eq} (nat f,nat 9))]
              val _ = sector_facts := Inttab.update (f,facts) (!sector_facts)
            in facts end)
      fun prove key =
        (case Termtab.lookup (!proofs) key of
          SOME theorem => (hits := !hits + 1; theorem)
        | NONE =>
            let
              val _ = if !misses mod 64=0 then Comma_Proof_Profile.report
                ("Frontier24 representative start count=" ^ Int.toString (!misses+1)) else ()
              val rep = (case Termtab.lookup representatives key of
                SOME value => value
              | NONE => error "Missing canonical Entry action representative")
              val (f,rest) = HOLogic.dest_prod key
              val (digit,row) = HOLogic.dest_prod rest
              val request = const @{const_name comma_entry_row_action} actionT [f,digit,row]
              val raw = timed representative_elapsed
                (fn () => evaluator (Thm.cterm_of row_context request))
              val theorem = raw
              val exact = Utils.exact_prop ctxt "Entry action representative"
                (Logic.mk_equals (request,#action rep)) theorem
              val _ = misses := !misses + 1
              val _ = proofs := Termtab.update (key,exact) (!proofs)
              val _ = if !misses mod 64=0 then Comma_Proof_Profile.report
                ("Frontier24 representative complete count=" ^ Int.toString (!misses)) else ()
            in exact end)
      fun statistics () = "entry_representative_proofs=" ^ Int.toString (!misses) ^
        " entry_representative_hits=" ^ Int.toString (!hits) ^
        " entry_representative_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!representative_elapsed)) ^
        " entry_key_ms=" ^ LargeInt.toString (Time.toMilliseconds (!key_elapsed)) ^
        " core_seed_hits=" ^ Int.toString (#seed_hits parameters ())
      val transports = Unsynchronized.ref 0
      fun transport f residue core wanted =
        let
          val key = #entry_action_key computation f residue core wanted
          val rep = (case Termtab.lookup representatives key of
            SOME value => value
          | NONE => error "Missing canonical Entry action transport")
          val request = const @{const_name comma_phase_program_entry_core_value_action}
            actionT [nat f,nat residue,core,nat wanted]
          val key_request = const @{const_name comma_entry_core_action_key}
            (fastype_of key) [nat f,nat residue,core,nat wanted]
          val evaluated = timed key_elapsed
            (fn () => key_evaluator (Thm.cterm_of key_context key_request))
          val key_equation = evaluated
          val _ = Utils.exact_prop ctxt "Entry action key"
            (Logic.mk_equals (key_request,key)) key_equation
          val factor = Drule.infer_instantiate ctxt
            [(("f",0),Thm.cterm_of ctxt (nat f)),
             (("residue",0),Thm.cterm_of ctxt (nat residue)),
             (("core",0),Thm.cterm_of ctxt core),
             (("wanted",0),Thm.cterm_of ctxt (nat wanted))]
            @{thm comma_entry_core_action_row_factor} OF (sector f)
          val factor = factor RS @{thm eq_reflection}
          val rhs = Simplifier.rewrite
            (put_simpset HOL_basic_ss ctxt
              |> Simplifier.add_simp (key_equation RS @{thm meta_eq_to_obj_eq})
              |> Simplifier.add_simps @{thms prod.case}) (Thm.rhs_of factor)
          val factor = Thm.transitive factor rhs
          val (sector,rest) = HOLogic.dest_prod key
          val (digit,row) = HOLogic.dest_prod rest
          val row_action = const @{const_name comma_entry_row_action} actionT
            [sector,digit,row]
          val _ = Utils.exact_prop ctxt "Entry action row factor"
            (Logic.mk_equals (request,row_action)) factor
          val theorem = Thm.transitive factor (prove key)
          val _ = transports := !transports + 1
          val _ = if !transports mod 128=0 then Comma_Proof_Profile.report
            ("Frontier24 row transports=" ^ Int.toString (!transports)) else ()
        in Utils.exact_prop ctxt "Entry action row transport"
          (Logic.mk_equals (request,#action rep)) theorem end
      fun transport_statistics () = statistics () ^
        " entry_row_transports=" ^ Int.toString (!transports)
    in {prove=prove,transport=transport,statistics=transport_statistics} end

end
