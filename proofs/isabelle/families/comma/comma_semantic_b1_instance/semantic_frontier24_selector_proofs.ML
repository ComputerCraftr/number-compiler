(* Kernel checked selector families, parameterized by existing arithmetic owners. *)
functor Comma_Frontier24_Selector_Proofs (
  val fixed_entry_port_conversion_plan: Proof.context ->
    {procedure: Simplifier.simproc, plain_procedure: Simplifier.simproc,
     statistics: unit -> string}
  val core_parameter_conversion_plan: Proof.context ->
    {procedure: Simplifier.simproc, plain_procedure: Simplifier.simproc,
     hits: unit -> int, seed_hits: unit -> int}
) =
struct
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Selected_Table = Comma_Frontier24_Selected_Table_Plan
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  val boolT = HOLogic.boolT
  val actionT = @{typ comma_source_continuation_action}
  fun nat n = HOLogic.mk_number natT n
  fun const name T args =
    list_comb (Const (name,fold_rev (curry (op -->)) (map fastype_of args) T),args)

  structure Entry_Row_Plan = Comma_Direct_Entry_Row_Plan (
    val fixed_entry_port_conversion_plan = fixed_entry_port_conversion_plan
    val core_parameter_conversion_plan = core_parameter_conversion_plan)

  fun entry_representative_plan ctxt result = Entry_Row_Plan.make ctxt
    Runtime.computation (Compiler.entry_representatives result)

  (* A token entry owns its exact selected action and any derived Goto source
     equation. Entries live only for this publisher invocation. *)
  type token_owner = {binding: term -> thm * thm, procedure: Simplifier.simproc,
    statistics: unit -> string}
  fun token_owner ctxt actions (actions_plan: Selected_Table.plan) =
    let
      val basic = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc (#procedure actions_plan)
      val entries = Unsynchronized.ref (Termtab.empty: (thm * thm * thm option Unsynchronized.ref) Termtab.table)
      val source_indices = Unsynchronized.ref (Termtab.empty: term Termtab.table)
      val lookup_elapsed = Unsynchronized.ref Time.zeroTime
      val source_elapsed = Unsynchronized.ref Time.zeroTime
      val source_calls = Unsynchronized.ref 0
      val source_proofs = Unsynchronized.ref 0
      val source_hits = Unsynchronized.ref 0
      fun binding index =
        let
          val _ = if Utils.closed index andalso fastype_of index = natT then ()
            else error "Action token index must be a closed natural"
          val request = const @{const_name nth} actionT [actions,index]
          val extent = const @{const_name size} natT [actions]
          val bound_prop = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less} (index,extent))
          fun validate (lookup,bound) =
            let
              val rhs = Thm.term_of (Thm.rhs_of lookup)
              val _ = Utils.exact_prop ctxt "Action token lookup"
                (Logic.mk_equals (request,rhs)) lookup
              val _ = Utils.exact_prop ctxt "Action token bound" bound_prop bound
            in (lookup,bound) end
        in (case Termtab.lookup (!entries) index of
          SOME (lookup,bound,_) => validate (lookup,bound)
        | NONE =>
            let
              val started = Time.now ()
              val lookup = Simplifier.rewrite basic (Thm.cterm_of ctxt request)
              val action = Thm.term_of (Thm.rhs_of lookup)
              val _ = if action aconv request then error "Selected action token did not resolve" else ()
              val bound = Goal.prove ctxt [] [] bound_prop
                (fn _ => simp_tac basic 1)
              val _ = validate (lookup,bound)
              val _ = lookup_elapsed := Time.+ (!lookup_elapsed,Time.- (Time.now (),started))
              val _ = entries := Termtab.update (index,(lookup,bound,Unsynchronized.ref NONE)) (!entries)
              val _ = (case strip_comb action of
                (Const (name,_),[source,_]) =>
                  if name = @{const_name Comma_Continuation_Goto} then
                    (case Termtab.lookup (!source_indices) source of
                      NONE => source_indices := Termtab.update (source,index) (!source_indices)
                    | SOME _ => ()) else ()
              | _ => ())
            in (lookup,bound) end) end
      val ports = fixed_entry_port_conversion_plan ctxt
      val parameters = core_parameter_conversion_plan ctxt
      val source_context = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc (#plain_procedure ports)
        |> Simplifier.add_proc (#plain_procedure parameters)
        |> Simplifier.add_simps @{thms comma_semantic_port_program_of_source_def
          comma_canonical_position_admitted_def comma_round_admitted.simps
          comma_source_continuation_base.simps comma_sector_entry_bound_def
          comma_entry_control_program_def comma_near_control_program_def
          comma_entry_core_common_rules comma_phase_core_of_modulus_def
          comma_finite_position.simps option.map option.case prod.case}
      fun source_convert active_ctxt ct =
        let
          val request = Thm.term_of ct
          val (head,args) = strip_comb request
          val _ = source_calls := !source_calls + 1
        in if not (Utils.closed request) orelse
          not (head aconv @{term comma_semantic_port_program_of_source}) then NONE else case args of
          [source] => (case Termtab.lookup (!source_indices) source of
            NONE => NONE
          | SOME index =>
              (case Termtab.lookup (!entries) index of
                NONE => error "Missing authenticated Goto token binding"
              | SOME (_,_,cached) => (case !cached of
                  SOME theorem =>
                    let val rhs = Thm.term_of (Thm.rhs_of theorem)
                        val checked = Utils.exact_prop active_ctxt "Cached Goto source program"
                          (Logic.mk_equals (request,rhs)) theorem
                    in source_hits := !source_hits + 1; SOME checked end
                | NONE =>
                    let
                      val started = Time.now ()
                      val theorem = Simplifier.rewrite source_context (Thm.cterm_of ctxt request)
                      val rhs = Thm.term_of (Thm.rhs_of theorem)
                      val proposed = (case #source_program Runtime.computation source of
                          SOME program => Const (@{const_name Some},fastype_of program -->
                            Type (@{type_name option},[fastype_of program])) $ program
                        | NONE => Const (@{const_name None},fastype_of request))
                      val _ = if rhs aconv proposed then ()
                        else error ("Goto source program mismatch: actual " ^
                          Syntax.string_of_term active_ctxt rhs ^ " expected " ^
                          Syntax.string_of_term active_ctxt proposed)
                      val _ = Utils.exact_prop active_ctxt "Goto source program"
                        (Logic.mk_equals (request,rhs)) theorem
                      val _ = source_elapsed := Time.+ (!source_elapsed,Time.- (Time.now (),started))
                      val _ = source_proofs := !source_proofs + 1
                      val _ = cached := SOME theorem
                    in SOME theorem end)))
        | _ => NONE end
      val pattern = Comma_Selected_List_Conversion.schematize
        @{term "comma_semantic_port_program_of_source source"}
      val procedure = Simplifier.make_simproc ctxt
        {name="frontier24_authenticated_goto_source",kind=Simplifier.Congproc true,
         lhss=[pattern],proc=fn _ => source_convert,identifier=[]}
      fun statistics () = " token_lookup_ms=" ^ LargeInt.toString (Time.toMilliseconds (!lookup_elapsed)) ^
        " source_calls=" ^ Int.toString (!source_calls) ^
        " source_proofs=" ^ Int.toString (!source_proofs) ^
        " source_hits=" ^ Int.toString (!source_hits) ^
        " source_ms=" ^ LargeInt.toString (Time.toMilliseconds (!source_elapsed))
    in {binding=binding,procedure=procedure,statistics=statistics} end

  (* Build each selector from bounded, exact action bindings.  The expensive
     Entry action is certified once per proposed port-row class; each later
     binding proves the row equality before using that representative. *)
  fun selector_family_facts ctxt result bundle projections programs selectors
      (actions_plan: Selected_Table.plan) (tokens: token_owner) =
    let
      val (actions,_) = Comma_Frontier24_Selector_Alignment.projection
        ctxt bundle projections @{const_name cf24_action_tokens} actionT
      val entry = entry_representative_plan ctxt result
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=Comma_Selected_List_Conversion.validate_equation}
      val basic = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc (#procedure actions_plan)
        |> Simplifier.add_simps @{thms comma_frontier24_selector_case.select_convs}
      val projection_ctxt = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps @{thms comma_frontier24_selector_case.select_convs}
      fun projected field row =
        Thm.term_of (Thm.rhs_of (Simplifier.rewrite projection_ctxt
          (Thm.cterm_of ctxt (const field natT [row]))))
      val token_binding = #binding tokens
      val support_evaluator = Code_Simp.static_conv
        {ctxt=ctxt,simpset=NONE,
         consts=Code_Thingol.read_const_exprs ctxt
          [@{const_name comma_core_supported_values}]} ctxt
      val support_facts = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      fun support_equation core =
        (case Termtab.lookup (!support_facts) core of
          SOME theorem => theorem
        | NONE =>
            let
              val request = const @{const_name comma_core_supported_values}
                (HOLogic.listT natT) [core]
              val evaluated = support_evaluator (Thm.cterm_of ctxt request)
              val decoded = #decode codec (Thm.rhs_of evaluated)
              val normalized = Simplifier.rewrite
                (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of decoded)
              val theorem = Thm.transitive evaluated (Thm.transitive decoded normalized)
              val _ = Utils.exact_prop ctxt "Supported core values"
                (Logic.mk_equals (request,Thm.term_of (Thm.rhs_of theorem))) theorem
              val _ = support_facts := Termtab.update (core,theorem) (!support_facts)
            in theorem end)
      val near_owner = Comma_Direct_Entry_Arithmetic.near_operator_plan ctxt
      val recipes = Unsynchronized.ref 0
      val case_elapsed = Unsynchronized.ref Time.zeroTime
      val fold_elapsed = Unsynchronized.ref Time.zeroTime
      val support_elapsed = Unsynchronized.ref Time.zeroTime
      fun measured elapsed f =
        let val start = Time.now ()
            val outcome = Exn.capture f ()
            val _ = elapsed := Time.+ (!elapsed,Time.- (Time.now (),start))
        in Exn.release outcome end
      fun prove_case f residue core row =
        let
          val predicate = const @{const_name comma_frontier24_selector_case_action_matches}
            boolT [f,residue,core,row,actions]
          val wanted = projected @{const_name cf24_case_wanted} row
          val index = projected @{const_name cf24_case_action_token} row
          val (lookup,bound) = token_binding index
          val action = #transport entry
            (Utils.dest_nat "Entry sector" natT f)
            (Utils.dest_nat "Entry residue" natT residue) core
            (Utils.dest_nat "Entry wanted value" natT wanted)
          val binding = Thm.transitive lookup (Thm.symmetric action)
            RS @{thm meta_eq_to_obj_eq}
          val intro = Drule.infer_instantiate ctxt
            [(("f",0),Thm.cterm_of ctxt f),(("residue",0),Thm.cterm_of ctxt residue),
             (("core",0),Thm.cterm_of ctxt core),(("row",0),Thm.cterm_of ctxt row),
             (("tokens",0),Thm.cterm_of ctxt actions)]
            @{thm comma_frontier24_selector_case_intro}
          val intro = Simplifier.full_simplify projection_ctxt intro
          val theorem = intro OF [bound,binding]
        in Utils.exact_prop ctxt "Entry selector case"
          (HOLogic.mk_Trueprop predicate) theorem end
      fun prove_near intro program statement =
        let val near = #equation near_owner program RS @{thm meta_eq_to_obj_eq}
            val local_ctxt = basic |> Simplifier.add_simp near
        in Goal.prove ctxt [] [] statement (fn {context,...} =>
          resolve_tac context [intro] 1 THEN ALLGOALS (simp_tac local_ctxt)) end
      fun prove_recipe (program,selector) =
        let
          val _ = recipes := !recipes + 1
          val _ = if !recipes mod 16=1 then Comma_Proof_Profile.report
            ("Frontier24 recipe start count=" ^ Int.toString (!recipes) ^
             " case_ms=" ^ LargeInt.toString (Time.toMilliseconds (!case_elapsed)) ^
             " fold_ms=" ^ LargeInt.toString (Time.toMilliseconds (!fold_elapsed)) ^
             " support_ms=" ^ LargeInt.toString (Time.toMilliseconds (!support_elapsed)) ^
             " " ^ #statistics tokens () ^
             " " ^ #statistics entry ()) else ()
          val predicate = const @{const_name comma_frontier24_selector_recipe_matches}
            boolT [program,selector,actions]
          val statement = HOLogic.mk_Trueprop predicate
        in case (strip_comb program,strip_comb selector) of
          ((Const (p,_),[f,_,residue,core]),(Const (s,_),[_,_,_,_,rows])) =>
            if p = @{const_name Comma_Entry_Core_Program} andalso
                s = @{const_name Comma_Frontier24_Entry_Selector} then
              let
                val cases = HOLogic.dest_list rows
                val facts = measured case_elapsed (fn () => map (prove_case f residue core) cases)
                val all = measured fold_elapsed (fn () =>
                  fold_rev (fn fact => fn tail =>
                    @{thm comma_frontier24_selector_cases_cons} OF [fact,tail]) facts
                    @{thm comma_frontier24_selector_cases_nil})
                val support = support_equation core RS @{thm meta_eq_to_obj_eq}
                val support_ctxt = basic |> Simplifier.add_simp support
                  |> Simplifier.add_simps @{thms list.map}
              in Goal.prove ctxt [] [] statement (fn {context,...} =>
                resolve_tac context [@{thm comma_frontier24_selector_entry_intro}] 1 THEN
                (fn state => Seq.make (fn () =>
                  measured support_elapsed (fn () => Seq.pull (simp_tac support_ctxt 1 state)))) THEN
                resolve_tac context [all] 1) end
            else error "Entry selector constructor mismatch"
        | ((Const (p,_),[_,_,_]),(Const (s,_),[token])) =>
            if p = @{const_name Comma_Near_Residual_Program} andalso
                s = @{const_name Comma_Frontier24_Near_Selector} then
              (token_binding token; prove_near @{thm comma_frontier24_selector_near_residual_intro}
                program statement)
            else error "Near residual selector constructor mismatch"
        | ((Const (p,_),[_]),(Const (s,_),[token])) =>
            if p = @{const_name Comma_Near_Boundary_Program} andalso
                s = @{const_name Comma_Frontier24_Near_Selector} then
              (token_binding token; prove_near @{thm comma_frontier24_selector_near_boundary_intro}
                program statement)
            else error "Near boundary selector constructor mismatch"
        | _ => error "Unknown selector family constructor"
        end
      val _ = if length programs = length selectors then ()
        else error "Selector family has unequal program and selector lengths"
      val outcome = Exn.capture (fn () => map prove_recipe (programs ~~ selectors)) ()
      val _ = Comma_Proof_Profile.report ("Frontier24 " ^ #statistics entry () ^
        " core_support_proofs=" ^ Int.toString (Termtab.size (!support_facts)) ^
        " " ^ #statistics tokens ())
    in Exn.release outcome end

end
