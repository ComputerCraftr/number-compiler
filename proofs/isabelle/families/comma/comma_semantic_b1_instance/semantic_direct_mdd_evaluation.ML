(* Checked interpretation of one direct expression application.  This owner
   consumes only the frozen Store and its primitive guard/shift/bind
   certificates; compiler closure records are not inputs. *)
structure Comma_Direct_MDD_Evaluation =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Proposal = Comma_Direct_MDD_Proposal
  structure Import = Comma_Frontier24_MDD_Import_Certificates
  structure Operation = Comma_CRT_MDD_Operation_Replay
  structure Bind = Comma_CRT_MDD_Bind_Replay
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
      val bind_replay = Bind.make store
      val phase_replay = Comma_Semantic_Phase_Selector_Replay.make
        ctxt store arena bind_replay shift_replay
      val chart_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val chart_count = Unsynchronized.ref 0
      val chart_hits = Unsynchronized.ref 0
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
      val alias_attempts = Unsynchronized.ref 0
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
      (* The unique-value selector is certified ONCE for each core/shift/
         wanted alphabet. Its construction depends on guard MDDs, not on
         Entry child applications. Each step uses the kernel-checked bind
         certificate, and the selected child mapping is a second bind. *)
      fun close_phase label goal theorem =
        Utils.exact_prop ctxt label (Logic.all phase goal)
          (Thm.forall_intr phase_ct theorem)
      fun check_phase label goal theorem =
        Thm.forall_elim phase_ct (close_phase label goal theorem)
      fun chart_certificate core shift (chart:Proposal.selector_chart) =
        let
          val labels = #wanted chart
          val cache_key = HOLogic.mk_prod (core,HOLogic.mk_prod
            (nat shift,HOLogic.mk_list natT (map nat labels)))
          val chart_id = Store.action_index store (#root chart)
          val evaluated = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $
            Store.radices store $ Store.table store $ phase $ nat chart_id
          val code = @{term comma_direct_entry_selector_code} $ core $
            HOLogic.mk_list natT (map nat labels) $ phase $ nat shift
          val expected = Logic.all phase
            (tp (HOLogic.mk_eq
              (evaluated,Const (@{const_name Some},natT --> @{typ "nat option"}) $ code)))
          fun check theorem = Utils.exact_prop ctxt
            "Direct selector chart exact conclusion" expected theorem
        in case Termtab.lookup (!chart_cache) cache_key of
          SOME theorem => (chart_hits := !chart_hits + 1; check theorem)
        | NONE =>
            (case #phase chart of
              SOME proposal =>
                let
                  val theorem = check (#certify phase_replay core shift labels proposal)
                  val _ = chart_count := !chart_count+1
                  val _ = chart_cache := Termtab.update (cache_key,theorem) (!chart_cache)
                in theorem end
            | NONE =>
            let
              fun eval root = @{term "comma_crt_mdd_eval_phase :: nat list => nat comma_crt_mdd_node list => nat => nat => nat option"} $
                Store.radices store $ Store.table store $ phase $ nat root
              fun some value = Const (@{const_name Some},natT --> @{typ "nat option"}) $ value
              fun guard_condition wanted = @{term "comma_crt_eval :: nat => comma_crt_column => bool"} $
                HOLogic.mk_binop @{const_name Groups.plus} (phase,nat shift) $
                (@{term comma_core_value_guard} $ core $ nat wanted)
              fun if_nat condition then_value else_value =
                Const (@{const_name If},@{typ "bool => nat => nat => nat"}) $
                  condition $ then_value $ else_value
              val steps = #steps chart
              val zero = (case steps of [] => #root chart
                | first :: _ => #prior first)
              val zero_id = Store.action_index store zero
              val zero_fact = Thm.forall_elim phase_ct (Store.phase_leaf store zero_id)
              val zero_goal = tp (HOLogic.mk_eq (eval zero_id,some (nat 0)))
              val _ = check_phase "Direct selector zero" zero_goal zero_fact
              fun one (step:Proposal.selector_step) (previous,code) =
                let
                  val {wanted,shifted,prior,chosen,after,key} = step
                  val old_id = Store.action_index store prior
                  val chosen_id = Store.action_index store chosen
                  val result_id = Store.action_index store after
                  val _ = (case Store.node store chosen_id of
                      Store.Leaf label => if label = wanted + 1 then ()
                        else error "Selector chart has wrong value label"
                    | _ => error "Selector chart wants an exact leaf label")
                  val _ = if old_id = #2 key andalso
                      Arena.boolean_index arena shifted = #1 key andalso
                      #3 key = [(0,old_id),(1,chosen_id)] then ()
                    else error "Selector bind changed its exact two Boolean labels"
                  val _ = check_phase "Direct selector previous"
                    (tp (HOLogic.mk_eq (eval old_id,some code))) previous
                  val shifted_id = Arena.boolean_index arena shifted
                  val shifted_fact = Operation.shift_eval_phase shift_replay shift
                    (Arena.boolean_index arena (#root
                      (case Termtab.lookup guard_index
                        (HOLogic.mk_prod (core,nat wanted)) of
                        SOME source => source
                      | NONE => error "Missing Entry selector guard"))) shifted_id
                    |> instantiate ctxt [ ("phase",phase) ]
                  val original = instantiate ctxt
                    [("phase",HOLogic.mk_binop @{const_name Groups.plus} (phase,nat shift))]
                    (guarded core wanted)
                  val guard_fact = @{thm trans} OF [shifted_fact,original]
                  val selected_leaf = Thm.forall_elim phase_ct
                    (Store.phase_leaf store chosen_id)
                  val combined = instantiate ctxt [("phase",phase)]
                    (Bind.bind_eval_phase bind_replay key)
                  val condition = guard_condition wanted
                  val next_code = if_nat condition (nat (wanted+1)) code
                  val goal = tp (HOLogic.mk_eq (eval result_id,some next_code))
                  val context = Comma_Entry_Arithmetic.natural_context ctxt
                    |> Simplifier.add_simps [previous,guard_fact,selected_leaf]
                    |> Simplifier.add_simps @{thms comma_crt_mdd_bind_target_def
                       map_of_Cons_code option.simps if_True if_False}
                  val cases = Drule.infer_instantiate ctxt
                    [(("P",0),Thm.cterm_of ctxt condition)] @{thm case_split}
                  (* Introduce the bind equation once. Adding it as a rewrite
                     rule can revisit its output when an input shares the root. *)
                  val theorem = Goal.prove ctxt [] [] goal (fn {context=proof,...} =>
                    resolve_tac proof [combined RS @{thm trans}] 1 THEN
                    resolve_tac proof [cases] 1 THEN
                    ALLGOALS (Simplifier.asm_full_simp_tac context))
                    |> check_phase "Direct selector chart step" goal
                in (theorem,next_code) end
              val (computed,_) = fold one steps (zero_fact,nat 0)
              val chart_id = Store.action_index store (#root chart)
              val wanted_term = HOLogic.mk_list natT (map nat labels)
              val code = @{term comma_direct_entry_selector_code} $
                core $ wanted_term $ phase $ nat shift
              val goal = tp (HOLogic.mk_eq (eval chart_id,some code))
              val theorem = Goal.prove ctxt [] [] goal
                (fn _ => simp_tac (Comma_Entry_Arithmetic.natural_context ctxt
                  |> Simplifier.add_simps [computed,
                     @{thm comma_direct_entry_selector_code_def}]
                  |> Simplifier.add_simps @{thms foldr.simps list.simps comp_apply id_apply}) 1)
                |> close_phase "Direct unique-core chart" goal |> check
              val _ = chart_count := !chart_count + 1
              val _ = chart_cache := Termtab.update (cache_key,theorem) (!chart_cache)
            in theorem end)
        end
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
          (* Check semantic identity before the cache lookup: equal outputs do
             not authenticate a changed child, phase, or foreign arena root. *)
          val _ = (case step of Proposal.Entry_One_Goto
              (Proposal.Application {expression=child_expr,shift=child_shift,root=child_root,...}) =>
            let
              val (head,args) = strip_comb (body expression)
              val _ = (case head of Const (name,_) =>
                if name = @{const_name Comma_Direct_Entry} then ()
                else error "Alias parent is not an Entry"
                | _ => error "Alias parent is not an Entry")
              val (core,rows) = (case args of [c,r] => (c,HOLogic.dest_list r)
                | _ => error "Malformed alias Entry")
              val (wanted,goto) = (case rows of [row] => HOLogic.dest_prod row
                | _ => error "Alias support is not a singleton")
              val _ = if (core aconv @{term Comma_Core_1} andalso wanted aconv nat 0) orelse
                  (core aconv @{term Comma_Core_3} andalso wanted aconv nat 1)
                then () else error "Alias core or supported label mismatch"
              val (gh,ga) = strip_comb (body goto)
              val _ = (case (gh,ga) of (Const (name,_),[actual,delta]) =>
                  if name = @{const_name Comma_Direct_Goto} andalso
                    actual aconv child_expr andalso delta aconv nat 0 andalso child_shift = shift
                  then () else error "Alias child or exact shift mismatch"
                | _ => error "Alias row is not a Goto")
              val _ = if Store.action_index store child_root = root_id then ()
                else error "Alias child is not the receiving root"
            in () end
          | _ => ())
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
                | Proposal.Entry_One_Goto child =>
                    let
                      val _ = alias_attempts := !alias_attempts + 1
                      val child_fact = Thm.forall_elim phase_ct (prove child)
                      val (_,arguments) = strip_comb expression_body
                      val (core,rows) = (case arguments of [c,r] => (c,HOLogic.dest_list r)
                        | _ => error "Malformed single Entry alias")
                      val goto = (case rows of [row] => #2 (HOLogic.dest_prod row)
                        | _ => error "Single Entry alias must have one row")
                      val goto_definition = definition goto
                      val (child_expr,wanted,guard_rule) =
                        (case child of Proposal.Application {expression=child_expr,...} =>
                          if core aconv @{term Comma_Core_1} then
                            (child_expr,nat 0,@{thm comma_direct_core_one_guard})
                          else (child_expr,nat 1,@{thm comma_direct_core_three_guard}))
                      val clock = Free ("direct_alias_clock",natT)
                      val guard = instantiate ctxt [("clock",clock)] guard_rule
                        |> Thm.forall_intr (Thm.cterm_of ctxt clock)
                      val rule = instantiate ctxt
                        [("core",core),("wanted",wanted),("child",child_expr),
                         ("phase",phase),("shift",nat shift),("root",nat root_id),
                         ("radices",Store.radices store),("nodes",Store.table store),
                         ("project",project phase)] @{thm comma_direct_single_row_alias_mdd}
                      val proof = Thm.implies_elim (Thm.implies_elim rule guard) child_fact
                      val folded = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt)
                        [Thm.symmetric goto_definition, Thm.symmetric expression_definition] proof
                    in check_phase "Direct Entry alias projection" goal folded end
                | Proposal.Entry (rows,selector) =>
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
                      val child_pairs = map (fn (row:Proposal.entry_row) =>
                        (#wanted row,Store.action_index store (Proposal.root (#child row)))) rows
                      val child_fn = Term.lambda wanted (Term.lambda child_var (choose wanted child_pairs))
                      val selected = #chart selector
                      val chart_id = Store.action_index store (#root selected)
                      val fallback = Arena.action_index arena (#fallback selector)
                      val _ = checkpoint "selector-chart-start"
                      val chart_fact = Thm.forall_elim phase_ct
                        (chart_certificate core shift selected)
                      val _ = checkpoint "selector-chart-complete"
                      val _ = checkpoint "bind-start"
                      val binding = Bind.certify_bind bind_replay (#key selector)
                      val _ = checkpoint "bind-complete"
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
                         ("rows",row_terms),("child_root",child_fn),
                         ("fallback",nat fallback),("chart",nat chart_id),
                         ("root",nat root_id),("project",project phase)]
                        @{thm comma_direct_expression_entry_bind_projected_rows_mdd}
                      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
                        |> Simplifier.add_simps @{thms list.simps set_simps singleton_iff
                          prod.inject prod.case}
                      val _ = checkpoint "assembly-start"
                      val literal_rows = HOLogic.dest_list row_terms
                      val _ = if length literal_rows = length rows andalso
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
                      val child_rows = assemble_rows "Direct Entry child rows" 3 child_facts
                      val bind_premise = List.nth (Thm.prems_of rule,1)
                      val bind_conversion = Simplifier.rewrite scalar
                        (Thm.cterm_of ctxt bind_premise)
                      val bind_checked = Utils.exact_prop ctxt "Direct Entry multi-terminal bind"
                        (Thm.term_of (Thm.rhs_of bind_conversion)) binding
                      val bind_fact = Thm.equal_elim
                        (Thm.symmetric bind_conversion) bind_checked
                      val selector_premise = List.nth (Thm.prems_of rule,2)
                      val selector_conversion = Simplifier.rewrite scalar
                        (Thm.cterm_of ctxt selector_premise)
                      val selector_checked = check_phase "Direct Entry selector"
                        (Thm.term_of (Thm.rhs_of selector_conversion)) chart_fact
                      val selector_fact = Thm.equal_elim
                        (Thm.symmetric selector_conversion) selector_checked
                      val result = rule OF [wf,bind_fact,selector_fact,child_rows,fallback_fact]
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
        " direct_mdd_entry_aliases=" ^ Int.toString (!alias_attempts) ^
        " direct_mdd_guard_proofs=" ^ Int.toString (Termtab.size (!guard_cache)) ^
        " direct_mdd_selector_charts=" ^ Int.toString (!chart_count) ^
        " direct_mdd_chart_hits=" ^ Int.toString (!chart_hits) ^
        " " ^ Bind.statistics bind_replay ^ " " ^ #statistics guard_plan () ^
        " " ^ #statistics phase_replay ()
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
