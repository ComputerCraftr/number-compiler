(* Direct program and source relation issuer.  Proposal maps are not authority;
   all inserted facts are closed kernel proofs in this receiving context. *)
functor Comma_Direct_Program_Bindings (
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
  structure Entry = Comma_Direct_Entry_Bindings (
    val fixed_entry_port_conversion_plan = fixed_entry_port_conversion_plan
    val core_parameter_conversion_plan = core_parameter_conversion_plan)
  val natT = @{typ nat}
  fun make ctxt (computation:Compiler.computation) program_bindings action_bindings body definition =
    let
      fun proposals label pairs = fold (fn (left,right) => fn table =>
        if not (Utils.closed left andalso Utils.closed right) then error (label ^ " is open")
        else (case Termtab.lookup table left of NONE => Termtab.update (left,right) table
          | SOME old => if old aconv right then table else error (label ^ " is inconsistent")))
        pairs Termtab.empty
      val programs = proposals "Direct program proposal" program_bindings
      val actions = proposals "Direct action proposal" action_bindings
      val entry = Entry.make ctxt computation program_bindings body definition
      val near_owner = Comma_Direct_Entry_Arithmetic.near_operator_plan ctxt
      val program_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val action_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val program_proofs = Unsynchronized.ref 0
      val program_hits = Unsynchronized.ref 0
      val action_proofs = Unsynchronized.ref 0
      val action_hits = Unsynchronized.ref 0
      (* The local relation stores share already checked proof nodes. The
         release consumers still audit their complete theorem for banned paths. *)
      val (certify_native,native_stats) = Comma_Entry_Arithmetic.make_certifier ctxt
      val started = Time.now ()
      fun checkpoint kind count label =
        if count <= 1 orelse count mod 64 = 0 then Comma_Proof_Profile.report
          ("Direct " ^ kind ^ " count=" ^ Int.toString count ^ " kind=" ^ label ^
            " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started) else ()
      val source_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simps @{thms comma_semantic_port_program_of_source_def
          comma_canonical_position_admitted_def comma_round_admitted.simps
          comma_source_continuation_base.simps comma_sector_entry_bound_def
          comma_entry_control_program_def comma_near_control_program_def
          comma_entry_core_common_rules comma_phase_core_of_modulus_def
          comma_finite_position.simps option.simps prod.case}
      fun expression table label key = (case Termtab.lookup table key of
          SOME value => value | NONE => error (label ^ " proposal is missing"))
      fun goal pred left right = HOLogic.mk_Trueprop (pred $ left $ right)
      fun checked label expected theorem = Utils.exact_prop ctxt label expected theorem
      fun prove_source action =
        let
          val expr = expression actions "Direct action" action
          val key = HOLogic.mk_prod (action,expr)
          val expected = goal @{term comma_direct_source_relation} action expr
        in case Termtab.lookup (!action_cache) key of
          SOME theorem => (action_hits := !action_hits+1; checked "Direct source hit" expected theorem)
        | NONE =>
            let
              val action_kind = (case Compiler.parse_action action of
                  Compiler.Goto _ => "goto" | Compiler.Exit _ => "exit"
                | Compiler.Fork _ => "fork" | Compiler.Landmine _ => "landmine"
                | Compiler.Invalid => "invalid")
              val _ = checkpoint "source start" (!action_proofs) action_kind
              val expression_body = body expr
              val expression_definition = definition expr
              val _ = Utils.exact_prop ctxt "Direct action expression definition"
                (Logic.mk_equals (expr,expression_body)) expression_definition
              val shallow_expected = goal @{term comma_direct_source_relation} action expression_body
              val theorem = (case Compiler.parse_action action of
                  Compiler.Goto (source,_) =>
                    let
                      val child = (case #source_program computation source of SOME value => value
                        | NONE => error "Goto source has no proposed program")
                      val child_fact = prove_program child
                      val source_binding = HOLogic.mk_Trueprop (HOLogic.mk_eq
                        (@{term comma_semantic_port_program_of_source} $ source,
                         Const (@{const_name Some},fastype_of child --> @{typ "comma_semantic_port_program option"}) $ child))
                      val source_fact = Utils.prove_exact ctxt "Direct Goto source" source_binding
                        (fn _ => simp_tac source_context 1)
                    in Goal.prove ctxt [] [] shallow_expected (fn {context,...} =>
                      resolve_tac context [@{thm comma_direct_program_relation_comma_direct_source_relation.goto}] 1 THEN
                      resolve_tac context [source_fact] 1 THEN resolve_tac context [child_fact] 1) end
                | Compiler.Exit (source,delta) =>
                    let
                      val admitted_rule = (case strip_comb source of
                          (Const (name,_),[f,source_delta,off]) =>
                            if name = @{const_name Comma_Entry} then
                              let
                                val instance = Drule.infer_instantiate ctxt
                                  (map (fn (key,value) => ((key,0),Thm.cterm_of ctxt value))
                                    [("f",f),("source_delta",source_delta),("off",off),
                                     ("delta",HOLogic.mk_number natT delta)])
                                  @{thm comma_direct_program_relation_comma_direct_source_relation.exit_admitted}
                                val arithmetic = Comma_Entry_Arithmetic.signed_context ctxt
                                  |> Simplifier.add_simps @{thms comma_offset_orbit_def
                                    comma_digit_orbit_sum_def power2_eq_square}
                              in [Simplifier.full_simplify arithmetic instance] end
                            else []
                        | _ => [])
                      val rules = admitted_rule @
                        [@{thm comma_direct_program_relation_comma_direct_source_relation.exit_invalid}]
                    in Goal.prove ctxt [] [] shallow_expected (fn {context,...} =>
                      FIRST' (map (fn theorem => resolve_tac context [theorem]) rules) 1 THEN
                      ALLGOALS (asm_full_simp_tac (source_context |> Simplifier.add_simp
                        @{thm comma_decade_root_admitted_def}))) end
                | _ => Goal.prove ctxt [] [] shallow_expected (fn {context,...} =>
                    FIRST' (map (fn theorem => resolve_tac context [theorem])
                      @{thms comma_direct_program_relation_comma_direct_source_relation.fork comma_direct_program_relation_comma_direct_source_relation.landmine
                        comma_direct_program_relation_comma_direct_source_relation.invalid}) 1 THEN
                    ALLGOALS (asm_full_simp_tac (source_context |> Simplifier.add_simps
                      @{thms comma_decade_root_admitted_def}))))
              val theorem = Entry.fold_expression ctxt "Direct source relation"
                @{term comma_direct_source_relation} action expr expression_definition theorem
                |> certify_native
              val _ = action_cache := Termtab.update (key,theorem) (!action_cache)
              val _ = action_proofs := !action_proofs+1
              val _ = checkpoint "source complete" (!action_proofs) action_kind
            in theorem end
        end
      and prove_program program =
        let
          val expr = expression programs "Direct program" program
          val key = HOLogic.mk_prod (program,expr)
          val expected = goal @{term comma_direct_program_relation} program expr
        in case Termtab.lookup (!program_cache) key of
          SOME theorem => (program_hits := !program_hits+1; checked "Direct program hit" expected theorem)
        | NONE =>
            let
              val program_kind = (case Compiler.parse_program program of
                  Compiler.Entry _ => "entry" | Compiler.Near_Residual _ => "near-residual"
                | Compiler.Near_Boundary _ => "near-boundary")
              val _ = checkpoint "program start" (!program_proofs) program_kind
              val _ = if Termtab.defined (!active) program then error "Cyclic direct program binding" else ()
              val _ = active := Termtab.update (program,()) (!active)
              fun construct () = (case Compiler.parse_program program of
                  Compiler.Entry {sector,residue,core,...} =>
                    let
                      val chart = #prepare entry sector residue core
                      val inputs = map (fn wanted =>
                        let val representative = #representative entry sector residue core wanted
                        in (representative,prove_source representative) end)
                        (#supported_values computation core)
                    in #certify entry chart program expr inputs end
                | _ =>
                    let
                      val action = #operator_action computation program
                      val operator_request = @{term comma_phase_program_operator_nf} $ program $
                        HOLogic.mk_number natT 0
                      val operator_eq = Utils.exact_prop ctxt "Direct Near operator action"
                        (Logic.mk_equals (operator_request,action)) (#equation near_owner program)
                      val admitted_prop = HOLogic.mk_Trueprop
                        (@{term comma_phase_program_structurally_admitted} $ program)
                      val admitted = Utils.prove_exact ctxt "Direct Near program admission" admitted_prop
                        (fn _ => simp_tac (source_context |> Simplifier.add_simps
                          @{thms comma_phase_program_structurally_admitted_def
                            comma_semantic_port_program.simps Let_def}) 1)
                      val relation = prove_source action
                      val rule = Drule.infer_instantiate ctxt
                        [(("action",0),Thm.cterm_of ctxt action)]
                        @{thm comma_direct_program_relation_comma_direct_source_relation.near}
                      val step_context = source_context |> Simplifier.add_simps
                        [admitted,operator_eq RS @{thm meta_eq_to_obj_eq}] |> Simplifier.add_simps
                        @{thms comma_phase_continue_near_residual_step_action
                          comma_phase_continue_near_boundary_step_action
                          comma_semantic_port_program.simps}
                    in Goal.prove ctxt [] [] expected (fn {context,...} =>
                      resolve_tac context [rule] 1 THEN
                      ALLGOALS (FIRST' [resolve_tac context [relation],simp_tac step_context])) end)
              val outcome = Exn.capture construct ()
              val _ = active := Termtab.delete_safe program (!active)
              val theorem = checked "Direct program relation" expected (Exn.release outcome)
                |> certify_native
              val _ = program_cache := Termtab.update (key,theorem) (!program_cache)
              val _ = program_proofs := !program_proofs+1
              val _ = checkpoint "program complete" (!program_proofs) program_kind
            in theorem end
        end
      fun program_action program =
        let
          val relation = prove_program program
          val phase = Free ("direct_program_phase",natT)
          val shift = Free ("direct_program_shift",natT)
          val rule = @{thm comma_direct_relation_sound(1)} OF [relation]
          val point = Drule.infer_instantiate ctxt
            [(("phase",0),Thm.cterm_of ctxt phase),(("shift",0),Thm.cterm_of ctxt shift)] rule
          val universal = point |> Thm.forall_intr (Thm.cterm_of ctxt shift)
            |> Thm.forall_intr (Thm.cterm_of ctxt phase)
        in Utils.ensure_closed_context ctxt "Direct program action" universal end
      fun statistics () =
        let val native = native_stats () in
          "direct_program_binding_proofs=" ^ Int.toString (!program_proofs) ^
          " direct_program_binding_hits=" ^ Int.toString (!program_hits) ^
          " direct_action_binding_proofs=" ^ Int.toString (!action_proofs) ^
          " direct_action_binding_hits=" ^ Int.toString (!action_hits) ^
          " direct_binding_audited_nodes=" ^ Int.toString (#nodes native) ^
          " direct_binding_audit_ms=" ^ LargeInt.toString (#milliseconds native) ^ " " ^
          #statistics entry ()
        end
    in {program_action=program_action,program_relation=prove_program,
      source_relation=prove_source,statistics=statistics} end
end
