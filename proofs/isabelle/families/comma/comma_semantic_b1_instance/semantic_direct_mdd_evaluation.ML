(* Checked interpretation of one direct expression application.  This owner
   consumes only the frozen Store and its primitive guard/shift/priority
   certificates; compiler closure records are not inputs. *)
structure Comma_Direct_MDD_Evaluation =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Proposal = Comma_Direct_MDD_Proposal
  structure Import = Comma_Frontier24_MDD_Import_Certificates
  structure Operation = Comma_CRT_MDD_Operation_Replay
  structure Multiway = Comma_CRT_MDD_Multiway_Replay
  structure Utils = Comma_CRT_MDD_Proof_Utils
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun tp term = HOLogic.mk_Trueprop term
  fun instantiate ctxt bindings theorem = Drule.infer_instantiate ctxt
    (map (fn (name,term) => ((name,0),Thm.cterm_of ctxt term)) bindings) theorem

  fun make_with ctxt store arena (guards: Proposal.guard list) body definition project terminal fallback_fact_for =
    let
      val _ = Utils.ensure_closed_context ctxt "Direct MDD Store" (Store.wellformed store)
      val phase = Free ("direct_mdd_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val wf = Store.wellformed store
      val shift_replay = Operation.make store
      val priority_replay = Multiway.make store
      val guard_plan = Import.make_guard_plan ctxt
      val cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val guard_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val guard_index = fold (fn (g:Proposal.guard) => fn table =>
        let val key = HOLogic.mk_prod (#core g,nat (#wanted g))
        in case Termtab.lookup table key of
          NONE => Termtab.update (key,g) table
        | SOME _ => error "Duplicate direct semantic guard proposal" end)
        guards Termtab.empty
      val proofs = Unsynchronized.ref 0
      val attempts = Unsynchronized.ref 0
      val entry_attempts = Unsynchronized.ref 0
      val goto_attempts = Unsynchronized.ref 0
      val terminal_attempts = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      fun stage kind ordinal started label =
        if ordinal <= 32 orelse ordinal mod 64 = 0 then
          Comma_Proof_Profile.report ("Direct MDD " ^ kind ^ "=" ^ Int.toString ordinal ^
            " stage=" ^ label ^ " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
        else ()
      fun guarded core wanted =
        let
          val key = HOLogic.mk_prod (core,nat wanted)
        in case Termtab.lookup (!guard_cache) key of
          SOME theorem => theorem
        | NONE =>
            let
              val entry = (case Termtab.lookup guard_index key of
                  SOME g => g | NONE => error "Missing direct semantic guard")
              val imported: Comma_Frontier24_Parametric_Compiler.guard_entry =
                {core=core,wanted=wanted,root=Arena.boolean_index arena (#root entry),
                 source_nodes= #source_nodes entry,source_root= #source_root entry,
                 source_seeds= #source_seeds entry,arena_roots= #arena_roots entry,
                 arena_nodes= #arena_nodes entry}
              val mapping = #certify guard_plan store arena imported
              val theorem = @{thm comma_direct_core_guard_import} OF [wf,mapping]
              val _ = guard_cache := Termtab.update (key,theorem) (!guard_cache)
            in theorem end
        end
      fun eval_term expression shift root =
        let
          val evaluated = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $
            Store.radices store $ Store.table store $ phase $ nat root
          val interpreted = project phase $
            (@{term comma_direct_action_interpret} $ expression $ phase $ nat shift)
          val some = Const (@{const_name Some},natT --> @{typ "nat option"}) $ interpreted
        in tp (HOLogic.mk_eq (evaluated,some)) end
      fun choose variable pairs =
        fold_rev (fn (key,value) => fn tail =>
          Const (@{const_name If},@{typ "bool => nat => nat => nat"}) $
            HOLogic.mk_eq (variable,nat key) $ nat value $ tail) pairs (nat 0)
      fun prove (Proposal.Application {expression,shift,root,step}) =
        let
          val _ = if shift >= 0 andalso Utils.closed expression andalso
              fastype_of expression = @{typ comma_direct_action_expression} then ()
            else error "Direct MDD application requires a closed typed expression and nonnegative shift"
          val root_id = Store.action_index store root
          val key = HOLogic.mk_prod (expression,nat shift)
          val goal = eval_term expression shift root_id
          val expected = Logic.all phase goal
        in case Termtab.lookup (!cache) key of
          SOME theorem => (hits := !hits + 1;
            Utils.exact_prop ctxt "Reused direct MDD application" expected theorem)
        | NONE =>
            let
              val expression_definition = definition expression
              val expression_body = body expression
              val _ = Utils.exact_prop ctxt "Direct expression application definition"
                (Logic.mk_equals (expression,expression_body)) expression_definition
              val proof = (case step of
                  Proposal.Terminal =>
                    let
                      val _ = terminal_attempts := !terminal_attempts + 1
                      val ordinal = !terminal_attempts
                      val started = Time.now ()
                      val _ = stage "Terminal" ordinal started "start"
                      val theorem = Utils.exact_prop ctxt "Direct terminal projection"
                        expected (terminal expression shift root_id)
                      val _ = stage "Terminal" ordinal started "complete"
                    in Thm.forall_elim phase_ct theorem end
                | Proposal.Goto child =>
                    let
                      val _ = goto_attempts := !goto_attempts + 1
                      val ordinal = !goto_attempts
                      val started = Time.now ()
                      val _ = stage "Goto" ordinal started "child-start"
                      val child_fact = Thm.forall_elim phase_ct (prove child)
                      val _ = stage "Goto" ordinal started "child-complete"
                      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
                        |> Simplifier.add_simps [expression_definition,child_fact,@{thm comma_direct_action_interpret.simps(5)}]
                      val theorem = Goal.prove ctxt [] [] goal (fn _ => simp_tac scalar 1)
                      val _ = stage "Goto" ordinal started "complete"
                    in theorem end
                | Proposal.Entry (rows,key) =>
                    let
                      val _ = entry_attempts := !entry_attempts + 1
                      val ordinal = !entry_attempts
                      val started = Time.now ()
                      fun checkpoint stage =
                        if ordinal<=32 orelse ordinal mod 64=0 then
                          Comma_Proof_Profile.report ("Direct MDD Entry=" ^ Int.toString ordinal ^
                            " stage=" ^ stage ^ " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
                        else ()
                      val _ = checkpoint "start"
                      val (_,arguments) = strip_comb expression_body
                      val (core,row_terms) = (case arguments of [c,r] => (c,r)
                        | _ => error "Malformed direct Entry application")
                      val wanted = Free ("direct_wanted",natT)
                      val child_var = Free ("direct_child",@{typ comma_direct_action_expression})
                      val guard_pairs = map (fn (row:Proposal.entry_row) =>
                        (#wanted row,Arena.boolean_index arena (#shifted row))) rows
                      val child_pairs = map (fn (row:Proposal.entry_row) =>
                        (#wanted row,Store.action_index store (Proposal.root (#child row)))) rows
                      val guard_fn = Term.lambda wanted (choose wanted guard_pairs)
                      val child_fn = Term.lambda wanted (Term.lambda child_var (choose wanted child_pairs))
                      val fallback = #2 key
                      val _ = checkpoint "priority-start"
                      val priority = Multiway.certify priority_replay key
                      val _ = checkpoint "priority-complete"
                      val _ = checkpoint "guards-start"
                      val guard_facts = map_index (fn (guard_index,row:Proposal.entry_row) =>
                        let
                          fun guard_checkpoint stage = if ordinal=1 then checkpoint
                            ("guard-" ^ Int.toString guard_index ^ "-" ^ stage) else ()
                          val old = Arena.boolean_index arena (#guard row)
                          val shifted = Arena.boolean_index arena (#shifted row)
                          val _ = guard_checkpoint "shift-start"
                          val transport = Operation.shift_eval_phase shift_replay shift old shifted
                          val transport = instantiate ctxt [("phase",phase)] transport
                          val _ = guard_checkpoint "shift-complete"
                          val _ = guard_checkpoint "import-start"
                          val original = instantiate ctxt [("phase",HOLogic.mk_binop @{const_name Groups.plus} (phase,nat shift))]
                            (guarded core (#wanted row))
                          val _ = guard_checkpoint "import-complete"
                        in @{thm trans} OF [transport,original] end) rows
                      val _ = checkpoint "guards-complete"
                      val _ = checkpoint "children-start"
                      val child_facts = map (fn (row:Proposal.entry_row) =>
                        Thm.forall_elim phase_ct (prove (#child row))) rows
                      val _ = checkpoint "children-complete"
                      val fallback_eval = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $
                        Store.radices store $ Store.table store $ phase $ nat fallback
                      val fallback_value = project phase $ @{term Comma_Phase_Rank_Mask_Invalid}
                      val fallback_goal = Logic.all phase (tp (HOLogic.mk_eq (fallback_eval,
                        Const (@{const_name Some},natT --> @{typ "nat option"}) $ fallback_value)))
                      val fallback_checked = Utils.exact_prop ctxt "Direct projection fallback"
                        fallback_goal (fallback_fact_for fallback)
                      val fallback_fact = Thm.forall_elim phase_ct fallback_checked
                      val rule = instantiate ctxt
                        [("radices",Store.radices store),("nodes",Store.table store),
                         ("phase",phase),("shift",nat shift),("core",core),
                         ("rows",row_terms),("guard",guard_fn),("child_root",child_fn),
                         ("fallback",nat fallback),("root",nat root_id),
                         ("project",project phase)]
                        @{thm comma_direct_expression_entry_projected_rows_mdd}
                      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
                        |> Simplifier.add_simps @{thms list.simps set_simps singleton_iff
                          prod.inject prod.case}
                      val _ = checkpoint "assembly-start"
                      val literal_rows = HOLogic.dest_list row_terms
                      val _ = if length literal_rows = length rows andalso
                          length rows = length guard_facts andalso
                          length rows = length child_facts then ()
                        else error "Direct Entry row and proof extents differ"
                      fun assemble_rows label premise_index row_facts =
                        let
                          val premise = List.nth (Thm.prems_of rule,premise_index)
                          val (application,items) = Term.dest_comb (HOLogic.dest_Trueprop premise)
                          val (head,predicate) = Term.dest_comb application
                          val _ = (case head of Const (name,_) =>
                              if name = @{const_name list_all} then ()
                              else error "Direct Entry premise is not list_all"
                            | _ => error "Direct Entry premise has an invalid head")
                          val _ = if items aconv row_terms then ()
                            else error "Direct Entry premise has different rows"
                          val row_var = Free ("direct_row",Term.domain_type (fastype_of predicate))
                          val universal_predicate = Term.lambda row_var
                            (HOLogic.mk_all ("direct_mdd_phase",natT,
                              Envir.beta_norm (predicate $ row_var)))
                          fun one (row,fact) =
                            let
                              val proposition = tp (Envir.beta_norm (predicate $ row))
                              val theorem = Goal.prove ctxt [] [] proposition (fn _ =>
                                simp_tac (scalar |> Simplifier.add_simp fact) 1)
                              val _ = if Thm.prop_of theorem aconv proposition then ()
                                else error (label ^ " row proves a different proposition")
                              val phase_predicate = Term.lambda phase (HOLogic.dest_Trueprop proposition)
                              val all_rule = Drule.infer_instantiate ctxt
                                [(("P",0),Thm.cterm_of ctxt phase_predicate)] @{thm allI}
                              val normalized_rule = Thm.equal_elim
                                (Thm.beta_conversion true (Thm.cprop_of all_rule)) all_rule
                              val generalized = Thm.forall_intr phase_ct theorem
                              val _ = if hd (Thm.prems_of normalized_rule) aconv
                                  Thm.prop_of generalized then ()
                                else error (label ^ " universal row premise mismatch: " ^
                                  Syntax.string_of_term ctxt (hd (Thm.prems_of normalized_rule)) ^
                                  " versus " ^ Syntax.string_of_term ctxt (Thm.prop_of generalized))
                              val universal = Thm.implies_elim normalized_rule generalized
                              val expected = tp (Envir.beta_norm (universal_predicate $ row))
                            in Utils.exact_prop ctxt (label ^ " universal row") expected universal end
                          val facts = map one (literal_rows ~~ row_facts)
                          val universal = Utils.literal_list_all ctxt label
                            universal_predicate literal_rows facts
                          val specialize = Drule.infer_instantiate ctxt
                            [(("phase",0),phase_ct)] @{thm comma_direct_rows_all_phaseD}
                          val theorem = specialize OF [universal]
                          val actual_conversion = Drule.beta_eta_conversion (Thm.cprop_of theorem)
                          val expected_conversion = Drule.beta_eta_conversion (Thm.cterm_of ctxt premise)
                          val actual = Thm.term_of (Thm.rhs_of actual_conversion)
                          val expected = Thm.term_of (Thm.rhs_of expected_conversion)
                          val _ = if actual aconv expected andalso
                              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
                              null (Thm.tpairs_of theorem) andalso
                              Context.subthy (Thm.theory_of_thm theorem,Proof_Context.theory_of ctxt)
                            then () else error (label ^ " specialized row mismatch: " ^
                              Syntax.string_of_term ctxt actual ^ " versus " ^
                              Syntax.string_of_term ctxt expected)
                        in Thm.equal_elim (Thm.symmetric expected_conversion)
                          (Thm.equal_elim actual_conversion theorem) end
                      val guard_rows = assemble_rows "Direct Entry guard rows" 2 guard_facts
                      val child_rows = assemble_rows "Direct Entry child rows" 3 child_facts
                      val priority_premise = List.nth (Thm.prems_of rule,1)
                      val priority_conversion = Simplifier.rewrite scalar
                        (Thm.cterm_of ctxt priority_premise)
                      val priority_checked = Utils.exact_prop ctxt "Direct Entry priority rows"
                        (Thm.term_of (Thm.rhs_of priority_conversion)) priority
                      val priority_fact = Thm.equal_elim
                        (Thm.symmetric priority_conversion) priority_checked
                      val result = rule OF [wf,priority_fact,guard_rows,child_rows,fallback_fact]
                      val proof = Goal.prove ctxt [] [] goal (fn {context,...} =>
                        simp_tac (put_simpset HOL_basic_ss context
                          |> Simplifier.add_simp expression_definition) 1 THEN
                        resolve_tac context [result] 1)
                      val _ = checkpoint "assembly-complete"
                    in proof end)
              val theorem = Thm.forall_intr phase_ct proof
              val theorem = Utils.exact_prop ctxt "Direct MDD application" expected theorem
              val _ = proofs := !proofs + 1
              val _ = if !proofs mod 64=0 then Comma_Proof_Profile.report
                ("Direct MDD application proofs=" ^ Int.toString (!proofs)) else ()
              val _ = cache := Termtab.update (key,theorem) (!cache)
            in theorem end
        end
      fun statistics () = "direct_mdd_applications=" ^ Int.toString (!proofs) ^
        " direct_mdd_application_hits=" ^ Int.toString (!hits) ^
        " direct_mdd_guard_proofs=" ^ Int.toString (Termtab.size (!guard_cache)) ^
        " " ^ #statistics guard_plan ()
    in {certify=prove,statistics=statistics} end

  fun make store arena guards body definition =
    let
      val ctxt = Store.context store
      val phase = Free ("direct_typed_terminal_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      fun terminal expression shift root =
        let
          val leaf = Thm.forall_elim phase_ct (Store.phase_leaf store root)
          val eval = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $
            Store.radices store $ Store.table store $ phase $ nat root
          val value = @{term comma_parametric_typed_mask_code} $
            (@{term comma_direct_action_interpret} $ expression $ phase $ nat shift)
          val goal = tp (HOLogic.mk_eq (eval,
            Const (@{const_name Some},natT --> @{typ "nat option"}) $ value))
          val scalar = Comma_Entry_Arithmetic.natural_context ctxt
            |> Simplifier.add_simps (definition expression :: leaf :: @{thms comma_direct_expression_terminal_codes})
          val theorem = Goal.prove ctxt [] [] goal (fn _ => simp_tac scalar 1)
        in Thm.forall_intr phase_ct theorem end
      fun fallback root =
        let
          val _ = (case Store.node store root of Store.Leaf 0 => ()
            | _ => error "Direct typed priority fallback is not the checked zero leaf")
          val leaf = Thm.forall_elim phase_ct (Store.phase_leaf store root)
          val eval = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $
            Store.radices store $ Store.table store $ phase $ nat root
          val projected = @{term comma_parametric_typed_mask_code} $ @{term Comma_Phase_Rank_Mask_Invalid}
          val goal = tp (HOLogic.mk_eq (eval,
            Const (@{const_name Some},natT --> @{typ "nat option"}) $ projected))
          val theorem = Goal.prove ctxt [] [] goal (fn _ =>
            simp_tac (put_simpset HOL_basic_ss ctxt
              |> Simplifier.add_simps [leaf,@{thm comma_parametric_typed_mask_code.simps(1)}]) 1)
        in Thm.forall_intr phase_ct theorem end
    in make_with ctxt store arena guards body definition
      (K @{term comma_parametric_typed_mask_code}) terminal fallback end
end
