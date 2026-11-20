(* Construct exact closure-shape proofs in source order from checked selector,
   guard, table and action facts. Candidate indices supply no theorem authority;
   each resulting premise is checked in the receiving context. *)
structure Comma_Frontier24_Structure_Proofs =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Arena = Comma_CRT_MDD_Arena
  val natT = @{typ nat}
  val closureT = @{typ comma_frontier24_closure}
  val bundleT = @{typ comma_frontier24_parametric_bundle}
  fun nat n = HOLogic.mk_number natT n
  type profile = {guards: Time.time Unsynchronized.ref, rows: Time.time Unsynchronized.ref,
    row_lists: Time.time Unsynchronized.ref, constructors: Time.time Unsynchronized.ref}
  fun fresh_profile (): profile = {guards=Unsynchronized.ref Time.zeroTime,
    rows=Unsynchronized.ref Time.zeroTime, row_lists=Unsynchronized.ref Time.zeroTime,
    constructors=Unsynchronized.ref Time.zeroTime}
  fun measure total computation =
    let val started = Time.now ()
        val result = computation ()
        val _ = total := Time.+ (!total,Time.- (Time.now (),started))
    in result end
  fun milliseconds total = LargeInt.toString (Time.toMilliseconds (!total))
  (* Expose scalar projections before the simplifier evaluates a bound child
     record; the theorem is derived once, without inspecting a source row. *)
  fun scalar_definition ctxt =
    let
      val theorem = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt) @{thms Let_def}
        @{thm comma_frontier24_action_output_linked_scalar_def}
      val proposition = Thm.prop_of theorem
      val (_,rhs) = (case try Logic.dest_equals proposition of
          SOME equation => equation
        | NONE => HOLogic.dest_eq (HOLogic.dest_Trueprop proposition))
      val _ = if Term.exists_subterm
        (fn Const (name,_) => name = @{const_name Let} | _ => false) rhs
        then error "Scalar action definition retained a Let expression" else ()
    in theorem end

  fun indexed_closures ctxt bundle (owner: Comma_Frontier24_Parametric_Runtime.named_table) facts =
    let
      val closures = #rows owner
      val table = #table owner
      val _ = if fastype_of bundle = bundleT andalso Utils.closed bundle then ()
        else error "Closure assembly requires a closed typed bundle"
      val _ = if length closures = length facts then ()
        else error "Closure assembly has missing or excess shape facts"
      val _ = if forall (fn closure => fastype_of closure = closureT andalso
          Utils.closed closure) closures then ()
        else error "Closure assembly contains an open or ill-typed closure"
      val shape = @{term comma_frontier24_closure_shape_checked}
      fun validate (index,(closure,fact)) =
        let val proposition = HOLogic.mk_Trueprop
              (shape $ bundle $ HOLogic.mk_prod (nat index,closure))
        in Utils.exact_prop ctxt "Indexed closure shape" proposition fact end
      val checked = map_index validate (closures ~~ facts)
      val count = length closures
      val tableT = HOLogic.listT closureT
      val size = Const (@{const_name size},tableT --> natT) $ table
      val size_fact = Utils.exact_prop ctxt "Named closure table length"
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (size,nat count))) (#size owner)
      val predicate = @{term comma_frontier24_indexed_closure_shape} $ bundle $ table
      val shape_facts = Vector.fromList checked
      fun prove_item index =
        let
          val selected = #lookup owner index
          val theorem = @{thm comma_frontier24_indexed_closure_shape_intro} OF
            [selected RS @{thm meta_eq_to_obj_eq},Vector.sub (shape_facts,index)]
        in Utils.exact_prop ctxt "Named indexed closure shape"
          (HOLogic.mk_Trueprop (predicate $ nat index)) theorem end
      val successor = Comma_Selected_List_Conversion.make_successor_cache ctxt count
      val indexed = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt,predicate=predicate,bound=count,prove_item=prove_item,
         zero_fact= @{thm comma_indexed_all_zero},step_fact= @{thm comma_indexed_all_Suc},
         successor_equation= #equation successor}
      val nat_list = HOLogic.listT natT
      val all = Const (@{const_name list_all},(natT --> HOLogic.boolT) -->
        nat_list --> HOLogic.boolT)
      val upto = Const (@{const_name upt},natT --> natT --> nat_list)
      val target = HOLogic.mk_Trueprop (all $ predicate $ (upto $ nat 0 $ size))
      val conversion = Conv.arg_conv (Conv.arg_conv
        (Conv.arg_conv (Conv.rewr_conv (size_fact RS @{thm eq_reflection}))))
        (Thm.cterm_of ctxt target)
      val indexed = Thm.equal_elim (Thm.symmetric conversion) indexed
      val theorem = @{thm comma_frontier24_indexed_closure_shapes_to_zip} OF [indexed]
      val pairT = HOLogic.mk_prodT (natT,closureT)
      val list_all = Const (@{const_name list_all},
        (pairT --> HOLogic.boolT) --> HOLogic.listT pairT --> HOLogic.boolT)
      val expected_zip = HOLogic.mk_Trueprop
        (list_all $ (@{term comma_frontier24_closure_shape_checked} $ bundle) $
          (Const (@{const_name zip},
            HOLogic.listT natT --> HOLogic.listT closureT -->
              HOLogic.listT (HOLogic.mk_prodT (natT,closureT))) $
            (Const (@{const_name upt}, natT --> natT --> HOLogic.listT natT) $
              nat 0 $ size) $ table))
    in Utils.exact_prop ctxt "Indexed closure list" expected_zip theorem end
  (* A proposed guard index supplies no authority. The kernel verifies the
     index bound and all three projections against the bundle's guard table. *)
  fun guard_witness ctxt bundle
      (guard_plan: Comma_Frontier24_Selected_Table_Plan.plan)
      index core wanted root =
    let
      val proposition = HOLogic.mk_Trueprop
        (@{term comma_frontier24_case_guard_imported} $
          bundle $ core $ wanted $ root)
      val witness = Drule.infer_instantiate ctxt
        [(("index",0),Thm.cterm_of ctxt (nat index))]
        @{thm comma_frontier24_case_guard_imported_witness}
      val basic = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc (#procedure guard_plan)
        |> Simplifier.add_proc (#post_procedure guard_plan)
        |> Simplifier.add_simps @{thms comma_frontier24_guard_entry.select_convs}
      val theorem = Goal.prove ctxt [] [] proposition (fn {context,...} =>
        resolve_tac context [witness] 1 THEN ALLGOALS (simp_tac basic))
    in Utils.exact_prop ctxt "Exact closure guard witness" proposition theorem end

  (* Class-root lookup is an authenticated indexed witness, never a scan
     through the closure list. *)
  fun class_root_witness ctxt scalar_ctxt bundle
      (closure_plan: Comma_Frontier24_Selected_Table_Plan.plan)
      index program_ref root =
    let
      val proposition = HOLogic.mk_Trueprop
        (Envir.beta_norm (@{term "\<lambda>(bundle::comma_frontier24_parametric_bundle)
            program_ref root_id. \<exists>closure\<in>set (cf24_closures bundle).
              cf24_closure_program_ref closure = program_ref \<and>
              cf24_closure_full_shift closure = 0 \<and>
              cf24_closure_output_root closure = root_id"} $ bundle $ program_ref $ root))
      val witness = Drule.infer_instantiate ctxt
        (map (fn (name,value) => ((name,0),Thm.cterm_of ctxt value))
          [("bundle",bundle),("index",nat index),
           ("program_ref",program_ref),("root_id",root)])
        @{thm comma_frontier24_class_root_witness}
      val _ = if Thm.concl_of witness aconv proposition then ()
        else error ("Class root witness conclusion mismatch: " ^
          Syntax.string_of_term ctxt (Thm.concl_of witness) ^ " expected " ^
          Syntax.string_of_term ctxt proposition)
      val basic = scalar_ctxt
        |> Simplifier.add_proc (#procedure closure_plan)
        |> Simplifier.add_proc (#post_procedure closure_plan)
        |> Simplifier.add_simps @{thms comma_frontier24_closure.select_convs}
      fun premise (index,statement) =
        Utils.prove_exact ctxt ("Class root witness premise " ^ Int.toString index)
          statement (fn _ => simp_tac basic 1)
      val facts = map_index premise (Thm.prems_of witness)
      val theorem = witness OF facts
    in Utils.exact_prop ctxt "Exact class-root witness" proposition theorem end

  (* Construct one occurrence's shape from the relevant checked recipe and
     guard facts.  The caller's simplifier contains the authenticated selected
     table procedures; it must also provide the source-program conversion used
     by action-output linkage.  A candidate program or root is only an
     instantiation: all resulting premises are proved in HOL. *)
  fun closure_shape_prepared ctxt scalar_ctxt bundle index closure program selector
      near_root (recipe,normalized_recipe) guards (profile: profile) profile_rows =
    let
      val statement = HOLogic.mk_Trueprop
        (@{term comma_frontier24_closure_shape_checked} $ bundle $
          HOLogic.mk_prod (nat index,closure))
      fun instance fields theorem = Drule.infer_instantiate ctxt
        (map (fn (name,value) => ((name,0),Thm.cterm_of ctxt value))
          (("bundle",bundle)::("closure_index",nat index)::
           ("closure",closure)::fields)) theorem
      val intro =
        (case (strip_comb program,strip_comb selector) of
          ((Const (p,_),[f,d,residue,core]),
           (Const (s,_),[_,_,_,_,cases])) =>
            if p = @{const_name Comma_Entry_Core_Program} andalso
                s = @{const_name Comma_Frontier24_Entry_Selector} then
              instance [("f",f),("d",d),("residue",residue),
                ("core",core),("selector_cases",cases)]
                @{thm comma_frontier24_closure_entry_scalar_intro}
            else error "Entry closure program/selector mismatch"
        | (_, (Const (s,_),[token])) =>
            if s = @{const_name Comma_Frontier24_Near_Selector} then
              (case near_root of
                SOME root => instance [("token",token),("action_root",root)]
                  @{thm comma_frontier24_closure_near_intro}
              | NONE => error "Near closure lacks a proposed action root")
            else error "Unknown closure selector"
        | _ => error "Unknown closure program/selector pair")
      (* First reduce finite row lists while action predicates remain opaque.
         Unfolding them under the row lambda would explore impossible child
         branches before the concrete row has been selected. *)
      val preliminary = scalar_ctxt
        |> Simplifier.add_simps [recipe,normalized_recipe]
        |> Simplifier.add_simps guards
        |> Simplifier.add_simps
          @{thms list_all_Nil_iff list_all_Cons_iff list.map
            comma_frontier24_selector_case.select_convs
            comma_frontier24_closure.select_convs
            comma_frontier24_closure_case.select_convs}
      val final = preliminary |> Simplifier.add_simps
        @{thms comma_frontier24_action_output_linked_def
          comma_source_continuation_action.simps comma_finite_position.simps
          comma_decade_root_admitted_def comma_offset_orbit_def
          comma_digit_orbit_sum_def power2_eq_square
          option.map option.case prod.case}
        |> Simplifier.add_simps Shared_Closed_Arithmetic.signed_scalar_rules
        |> fold Simplifier.add_cong @{thms
          comma_source_continuation_action.case_cong_weak
          comma_finite_position.case_cong_weak option.case_cong_weak}
      (* Derive each Entry row at its concrete record before folding.  The
         premise index is fixed by the checked Entry constructor interface. *)
      val row_facts = (case strip_comb selector of
          (Const (s,_),_) =>
            if s <> @{const_name Comma_Frontier24_Entry_Selector} then NONE
            else
              let
                val premise = List.nth (Thm.prems_of intro,11)
                val (application,cases_term) =
                  Term.dest_comb (HOLogic.dest_Trueprop premise)
                val (head,predicate) = Term.dest_comb application
                val _ = (case head of Const (name,_) =>
                    if name = @{const_name list_all} then ()
                    else error "Entry row premise is not list_all"
                  | _ => error "Entry row premise has an invalid head")
                val projection = Simplifier.rewrite
                  (put_simpset HOL_basic_ss ctxt |>
                    Simplifier.add_simps @{thms comma_frontier24_closure.select_convs})
                  (Thm.cterm_of ctxt cases_term)
                val predicate_equation = Simplifier.rewrite
                  (put_simpset HOL_basic_ss ctxt |>
                    Simplifier.add_simps @{thms comma_frontier24_closure.select_convs})
                  (Thm.cterm_of ctxt predicate)
                val scalar_predicate = Thm.term_of (Thm.rhs_of predicate_equation)
                val rows = HOLogic.dest_list (Thm.term_of (Thm.rhs_of projection))
                fun prove_row row =
                  let
                    val predicate = Envir.beta_norm (scalar_predicate $ row)
                    val _ = if Utils.closed predicate then ()
                      else error "Entry closure row predicate is open"
                    val equation = Simplifier.rewrite final (Thm.cterm_of ctxt predicate)
                    val _ = Utils.exact_prop ctxt "Entry closure row conversion"
                      (Logic.mk_equals (predicate,@{term True})) equation
                    val theorem = equation RS @{thm meta_eq_to_obj_eq} RS @{thm eqTrueE}
                  in Utils.exact_prop ctxt "Entry closure row"
                    (HOLogic.mk_Trueprop predicate) theorem end
                val facts = measure (#rows profile) (fn () => map prove_row rows)
                val _ = if profile_rows andalso not (null rows) then
                  let
                    val predicate = Envir.beta_norm (scalar_predicate $ hd rows)
                    val started = Time.now ()
                    val baseline = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop predicate)
                      (fn _ => simp_tac final 1)
                    val _ = Utils.exact_prop ctxt "Entry row tactic comparison"
                      (Thm.prop_of (hd facts)) baseline
                  in Comma_Proof_Profile.report
                    ("Frontier24 row tactic comparison ms=" ^ LargeInt.toString
                      (Time.toMilliseconds (Time.- (Time.now (),started)))) end
                  else ()
                val literal = measure (#row_lists profile) (fn () =>
                  Utils.literal_list_all ctxt "Entry literal closure rows"
                    scalar_predicate rows facts)
                val predicate_rewrite = Conv.arg_conv (Conv.fun_conv
                  (Conv.arg_conv (Conv.rewr_conv (Thm.symmetric predicate_equation))))
                val literal = Thm.equal_elim
                  (predicate_rewrite (Thm.cprop_of literal)) literal
                val rewrite = Conv.arg_conv
                  (Conv.arg_conv (Conv.rewr_conv (Thm.symmetric projection)))
                val result = Thm.equal_elim (rewrite (Thm.cprop_of literal)) literal
              in SOME (Utils.exact_prop ctxt "Entry closure rows" premise result) end
        | _ => NONE)
      fun finish context = SUBGOAL (fn (goal,index) =>
        if Term.exists_subterm
          (fn Const (name,_) => name = @{const_name list_all} | _ => false) goal
        then no_tac else simp_tac final index)
      val theorem = measure (#constructors profile) (fn () =>
        Goal.prove ctxt [] [] statement (fn {context,...} =>
          resolve_tac context [intro] 1 THEN
          ALLGOALS (FIRST' [resolve_tac context
            (recipe::normalized_recipe::the_list row_facts),
            simp_tac preliminary]) THEN
          ALLGOALS (finish context)))
    in Utils.exact_prop ctxt "Exact individual closure shape" statement theorem end

  fun closure_shape ctxt scalar_ctxt bundle index closure program selector
      near_root recipe guards =
    let val scalar_ctxt = scalar_ctxt |> Simplifier.add_simp (scalar_definition ctxt)
    in closure_shape_prepared ctxt scalar_ctxt bundle index closure program selector
      near_root (recipe,Simplifier.full_simplify scalar_ctxt recipe) guards
        (fresh_profile ()) false end

  fun closure_shapes ctxt scalar_ctxt bundle result
      (selector_owner: Comma_Frontier24_Parametric_Runtime.named_table)
      (closure_owner: Comma_Frontier24_Parametric_Runtime.named_table) recipe_facts
      (guard_plan: Comma_Frontier24_Selected_Table_Plan.plan)
      plan_stats source_statistics =
    let
      val programs = Compiler.programs result
      val selectors = #rows selector_owner
      val program_vector = Vector.fromList programs
      val selector_vector = Vector.fromList selectors
      val recipes = Vector.fromList (map (fn recipe =>
        (recipe,Simplifier.full_simplify scalar_ctxt recipe)) recipe_facts)
      val closures = #rows closure_owner
      val proposals = Compiler.closures result
      val _ = if length closures = length proposals andalso
          length programs = length selectors andalso
          length programs = Vector.length recipes then ()
        else error "Closure source and selector extents differ"
      fun guard_key core wanted root =
        HOLogic.mk_prod (core,HOLogic.mk_prod (nat wanted,nat root))
      fun insert_guard (index,entry: Compiler.guard_entry) table =
        let val key = guard_key (#core entry) (#wanted entry) (#root entry)
        in if Termtab.defined table key then table
          else Termtab.update (key,index) table end
      val guard_indices = fold insert_guard
        (map_index I (Compiler.guard_entries result)) Termtab.empty
      val guard_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val profile = fresh_profile ()
      val sampled_rows = Unsynchronized.ref false
      fun prove_guard core (row: Compiler.closure_case) =
        let
          val key = guard_key core (#wanted row) (#guard_root row)
        in case Termtab.lookup (!guard_cache) key of
          SOME theorem => theorem
        | NONE =>
            let
              val index = (case Termtab.lookup guard_indices key of
                SOME value => value
              | NONE => error "Closure guard lacks a proposed guard entry")
              val theorem = measure (#guards profile) (fn () =>
                guard_witness ctxt bundle guard_plan index core
                  (nat (#wanted row)) (nat (#guard_root row)))
              val _ = guard_cache := Termtab.update (key,theorem) (!guard_cache)
            in theorem end
        end
      fun prove (index,(closure,proposal: Compiler.closure)) =
        let
          val _ = if index mod 32 = 0 then Comma_Proof_Profile.report
            ("Frontier24 closure start index=" ^ Int.toString index) else ()
          val started = Time.now ()
          val program_ref = #program_ref proposal
          val _ = if program_ref >= 0 andalso program_ref < Vector.length program_vector
            then () else error "Closure program proposal is outside the table"
          val program = Vector.sub (program_vector,program_ref)
          val selector = Vector.sub (selector_vector,program_ref)
          val guards = (case strip_comb program of
              (Const (p,_),[_,_,_,core]) =>
                if p = @{const_name Comma_Entry_Core_Program}
                then map (prove_guard core) (#cases proposal) else []
            | _ => [])
          val root = Option.map nat (#near_action_output_root proposal)
          val profile_rows = Comma_Proof_Profile.enabled () andalso not (!sampled_rows) andalso
            exists (fn (row: Compiler.closure_case) => is_some (#child_closure row))
              (#cases proposal)
          val _ = if profile_rows then
              (sampled_rows := true; Comma_Proof_Profile.report
                ("Frontier24 row tactic comparison index=" ^ Int.toString index)) else ()
          val theorem = closure_shape_prepared ctxt scalar_ctxt bundle index closure program selector root
            (Vector.sub (recipes,program_ref)) guards profile profile_rows
          val _ = if index mod 32 = 0 then Comma_Proof_Profile.report
            ("Frontier24 closure complete index=" ^ Int.toString index ^ " ms=" ^
              LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (),started))) ^
              " cumulative_guard_ms=" ^ milliseconds (#guards profile) ^
              " cumulative_rows_ms=" ^ milliseconds (#rows profile) ^
              " cumulative_row_lists_ms=" ^ milliseconds (#row_lists profile) ^
              " cumulative_constructors_ms=" ^ milliseconds (#constructors profile) ^
              " " ^ String.concatWith " " (map Comma_Frontier24_Selected_Table_Plan.statistics
                plan_stats) ^ " " ^ source_statistics ()) else ()
        in theorem end
    in map_index prove (closures ~~ proposals) end

  (* Build the reverse index once. Every selected index is checked by
     class_root_witness against the actual closure table before use. *)
  fun class_root_witnesses ctxt scalar_ctxt bundle result
      (closure_plan: Comma_Frontier24_Selected_Table_Plan.plan) =
    let
      fun key program root = HOLogic.mk_prod (nat program,nat root)
      fun add (index,closure: Compiler.closure) table =
        if #full_shift closure <> 0 then table
        else let val k = key (#program_ref closure) (#output_root closure)
          in if Termtab.defined table k then table
            else Termtab.update (k,index) table end
      val indices = fold add (map_index I (Compiler.closures result)) Termtab.empty
      val arena = Compiler.arena result
      val refs = Compiler.class_program_refs result
      val roots = map (Arena.action_index arena) (Compiler.class_roots result)
      val _ = if length refs = length roots then ()
        else error "Class program and root extents differ"
      fun selected field index =
        Const (@{const_name nth},HOLogic.listT natT --> natT --> natT) $
          (Const (field,bundleT --> HOLogic.listT natT) $ bundle) $ nat index
      fun prove (cid,(program,root)) =
        let
          val index = (case Termtab.lookup indices (key program root) of
            SOME value => value
          | NONE => error "Class has no proposed zero-shift closure")
        in class_root_witness ctxt scalar_ctxt bundle closure_plan index
          (selected @{const_name cf24_class_program_refs} cid)
          (selected @{const_name cf24_class_roots} cid) end
    in map_index prove (refs ~~ roots) end

  fun program_admission ctxt scalar_ctxt bundle field_projections
      (owner: Comma_Frontier24_Parametric_Runtime.named_table) =
    let
      val programT = @{typ comma_semantic_port_program}
      val table = #table owner
      val items = #rows owner
      val count = length items
      val projection = Const (@{const_name cf24_programs},
        bundleT --> HOLogic.listT programT) $ bundle
      val equation = (case AList.lookup (op =) field_projections @{const_name cf24_programs} of
          SOME theorem => Utils.exact_prop ctxt "Program table projection"
            (Logic.mk_equals (projection,table)) theorem
        | NONE => error "Missing program table projection")
      val predicate = @{term comma_phase_program_structurally_admitted}
      val basic = scalar_ctxt
        |> Simplifier.add_simp @{thm comma_phase_program_structurally_admitted_def}
        |> Simplifier.add_simps @{thms comma_entry_core_common_rules
          comma_semantic_port_program.simps}
      fun prove row = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (predicate $ row))
        (fn _ => simp_tac basic 1)
      val facts = Vector.fromList (map prove items)
      val nth = Const (@{const_name nth},HOLogic.listT programT --> natT --> programT)
      val indexed_predicate = Abs ("index",natT,predicate $ (nth $ table $ Bound 0))
      fun prove_item index =
        let
          val target = HOLogic.mk_Trueprop (indexed_predicate $ nat index)
          val normalized = Thm.beta_conversion true (Thm.cterm_of ctxt target)
          val selected = #lookup owner index
          val lifted = Thm.combination (Thm.reflexive (Thm.cterm_of ctxt predicate)) selected
          val theorem = Thm.equal_elim (Thm.symmetric
            (Thm.combination (Thm.reflexive (Thm.cterm_of ctxt
              (Const (@{const_name Trueprop},HOLogic.boolT --> @{typ prop})))) lifted))
            (Vector.sub (facts,index))
          val theorem = Utils.exact_prop ctxt "Indexed program admission"
            (Thm.term_of (Thm.rhs_of normalized)) theorem
        in Thm.equal_elim (Thm.symmetric normalized) theorem end
      val successor = Comma_Selected_List_Conversion.make_successor_cache ctxt count
      val indexed = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt,predicate=indexed_predicate,bound=count,prove_item=prove_item,
         zero_fact= @{thm comma_indexed_all_zero},step_fact= @{thm comma_indexed_all_Suc},
         successor_equation= #equation successor}
      val table_prop = HOLogic.mk_Trueprop
        (Const (@{const_name list_all},(programT --> HOLogic.boolT) -->
          HOLogic.listT programT --> HOLogic.boolT) $ predicate $ table)
      val literal = Goal.prove ctxt [] [] table_prop (fn {context,...} =>
        Method.insert_tac context [indexed,#size owner] 1 THEN
        simp_tac (put_simpset HOL_basic_ss context
          |> Simplifier.add_simp @{thm list_all_length}) 1 THEN
        auto_tac (put_simpset HOL_basic_ss context
          |> Simplifier.add_simps @{thms list_all_iff set_upt atLeastLessThan_iff}))
      val rewrite = Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv (Thm.symmetric equation)))
      val theorem = Thm.equal_elim (rewrite (Thm.cprop_of literal)) literal
      val expected = HOLogic.mk_Trueprop
        (Const (@{const_name list_all},
           (programT --> HOLogic.boolT) --> HOLogic.listT programT --> HOLogic.boolT) $
          predicate $ (Const (@{const_name cf24_programs},
            bundleT --> HOLogic.listT programT) $ bundle))
    in Utils.exact_prop ctxt "Program admissions" expected theorem end

  fun class_roots ctxt scalar_ctxt bundle result closure_plan =
    let
      val programT = @{typ comma_semantic_port_program}
      val optionT = Type (@{type_name option},[programT])
      val programs = Vector.fromList (Compiler.programs result)
      val refs = Compiler.class_program_refs result
      val roots = Compiler.class_roots result
      val witnesses = class_root_witnesses ctxt scalar_ctxt bundle result closure_plan
      val _ = if length refs = 46 andalso length roots = 46 andalso
          length witnesses = 46 then () else error "Class extent is not 46"
      val evaluate = Code_Simp.static_conv
        {ctxt=ctxt,simpset=NONE,
         consts=Code_Thingol.read_const_exprs ctxt
          [@{const_name comma_semantic_phase_program_for_class}]} ctxt
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=Comma_Selected_List_Conversion.validate_equation}
      val predicate = @{term "\<lambda>(bundle::comma_frontier24_parametric_bundle) cid.
        case comma_semantic_phase_program_for_class cid of None \<Rightarrow> False
        | Some program \<Rightarrow>
          cf24_class_program_refs bundle ! cid < length (cf24_programs bundle) \<and>
          cf24_programs bundle ! (cf24_class_program_refs bundle ! cid) = program \<and>
          (\<exists>closure\<in>set (cf24_closures bundle).
            cf24_closure_program_ref closure = cf24_class_program_refs bundle ! cid \<and>
            cf24_closure_full_shift closure = 0 \<and>
            cf24_closure_output_root closure = cf24_class_roots bundle ! cid)"} $ bundle
      fun class_equation cid program =
        let
          val request = Const (@{const_name comma_semantic_phase_program_for_class},
            natT --> optionT) $ nat cid
          val evaluation = evaluate (Thm.cterm_of ctxt request)
          val decoded = #decode codec (Thm.rhs_of evaluation)
          val normalized = Simplifier.rewrite
            (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of decoded)
          val theorem = Thm.transitive evaluation (Thm.transitive decoded normalized)
          val expected = Logic.mk_equals (request,
            Const (@{const_name Some},programT --> optionT) $ program)
        in Utils.exact_prop ctxt "Class program equation" expected theorem end
      fun prove (cid,(program_ref,witness)) =
        let
          val _ = if program_ref >= 0 andalso program_ref < Vector.length programs
            then () else error "Class program reference is out of bounds"
          val program = Vector.sub (programs,program_ref)
          val equation = class_equation cid program RS @{thm meta_eq_to_obj_eq}
          val condition = HOLogic.mk_binrel @{const_name less} (nat cid,nat 46)
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_imp
            (condition,Envir.beta_norm (predicate $ nat cid)))
          val tiny = put_simpset HOL_basic_ss ctxt |> Simplifier.add_simp equation
            |> Simplifier.add_simps @{thms option.case}
        in Goal.prove ctxt [] [] proposition (fn {context,...} =>
          resolve_tac context [@{thm impI}] 1 THEN
          simp_tac tiny 1 THEN
          resolve_tac context [@{thm conjI}] 1 THEN
          simp_tac scalar_ctxt 1 THEN
          resolve_tac context [@{thm conjI}] 1 THEN
          simp_tac scalar_ctxt 1 THEN
          resolve_tac context [witness] 1) end
      val facts = map_index prove (refs ~~ witnesses)
      val guarded = Abs ("cid",natT,HOLogic.mk_imp
        (HOLogic.mk_binrel @{const_name less} (Bound 0,nat 46),
         Term.incr_boundvars 1 predicate $ Bound 0)) |> Envir.beta_norm
      val literal = Utils.literal_list_all ctxt "Literal class bindings" guarded
        (map nat (0 upto 45)) facts
      val range = Const (@{const_name upt},natT --> natT --> HOLogic.listT natT) $
        nat 0 $ nat 46
      val range_ctxt = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simp @{thm upt_rec}
      val range_eq = Simplifier.rewrite range_ctxt
        (Thm.cterm_of ctxt range)
      val literal_range = HOLogic.mk_list natT (map nat (0 upto 45))
      val _ = Utils.exact_prop ctxt "Class index range"
        (Logic.mk_equals (range,literal_range)) range_eq
      val rewrite = Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv (Thm.symmetric range_eq)))
      val list_theorem = Thm.equal_elim (rewrite (Thm.cprop_of literal)) literal
      val index = Free ("frontier24_class_index",natT)
      val universal_prop = HOLogic.mk_Trueprop (HOLogic.mk_all
        ("frontier24_class_index",natT,HOLogic.mk_imp
          (HOLogic.mk_binrel @{const_name less} (index,nat 46),
           Envir.beta_norm (predicate $ index))))
      val universal = Goal.prove ctxt [] [] universal_prop (fn {context,...} =>
        Method.insert_tac context [list_theorem] 1 THEN
        auto_tac (put_simpset HOL_basic_ss context
          |> Simplifier.add_simps @{thms list_all_iff set_upt}))
      val intro = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_class_roots_intro}
      val proposition = HOLogic.mk_Trueprop
        (@{term comma_frontier24_class_roots_checked} $ bundle)
      val basic = scalar_ctxt |> Simplifier.add_simp universal
      val theorem = Goal.prove ctxt [] [] proposition (fn {context,...} =>
        resolve_tac context [intro] 1 THEN ALLGOALS (asm_full_simp_tac basic))
    in Utils.exact_prop ctxt "Class roots" proposition theorem end

  (* The premises are separately proved facts, so this constructor cannot
     certify a bundle by trusting producer-computed shape or cache keys. *)
  fun assemble ctxt bundle field_projections
      {selector, programs, zero_bound, zero_leaf, closures, roots} =
    let
      val (_,closure_equation) = Comma_Frontier24_Selector_Alignment.projection
        ctxt bundle field_projections @{const_name cf24_closures} closureT
      val intro = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_structure_intro}
        |> Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt) [closure_equation]
      val theorem = intro OF
        [selector,programs,zero_bound,zero_leaf,closures,roots]
      val expected = HOLogic.mk_Trueprop
        (@{term comma_frontier24_bundle_semantic_structure_checked} $ bundle)
    in Utils.exact_prop ctxt "Exact bundle structure" expected theorem end

  fun certify_requested include_classes ctxt (candidate: Comma_Frontier24_Parametric_Runtime.candidate)
      {selector,recipe_facts,plans,procedures,bound_facts,lookup_facts,source_statistics} =
    let
      val bundle = #bundle candidate
      val field_projections = #field_projections candidate
      val result = #result candidate
      val closure_plan = (case plans of [_,_,_,plan] => plan
        | _ => error "Structure requires the four existing selected table plans")
      val guard_plan = Comma_Frontier24_Selected_Table_Plan.make ctxt bundle field_projections
        "guards" @{const_name cf24_guard_entries} @{typ comma_frontier24_guard_entry}
        (length (Compiler.guard_entries result)) NONE
      val class_plans = if include_classes then
        [Comma_Frontier24_Selected_Table_Plan.make ctxt bundle field_projections
          "class program refs" @{const_name cf24_class_program_refs} natT
          (length (Compiler.class_program_refs result)) NONE,
         Comma_Frontier24_Selected_Table_Plan.make ctxt bundle field_projections
          "class roots" @{const_name cf24_class_roots} natT
          (length (Compiler.class_roots result)) NONE]
        else []
      val all_plans = plans @ [guard_plan] @ class_plans
      val _ = if null procedures then
          error "Structure requires the checked selector transport" else ()
      fun bundle_projection field T =
        (case AList.lookup (op =) field_projections field of
          SOME theorem => Utils.exact_prop ctxt "Checked bundle projection"
            (Logic.mk_equals (Const (field,bundleT --> T) $ bundle,
              Thm.term_of (Thm.rhs_of theorem))) theorem
        | NONE => error "Structure lacks its checked bundle projection")
      val zero_projection = bundle_projection @{const_name cf24_zero_root} natT
      val nodes_projection = bundle_projection @{const_name cf24_nodes}
        @{typ "nat comma_crt_mdd_node list"}
      val actions_projection = bundle_projection @{const_name cf24_action_tokens}
        @{typ "comma_source_continuation_action list"}
      val closures_projection = bundle_projection @{const_name cf24_closures}
        @{typ "comma_frontier24_closure list"}
      val programs_projection = bundle_projection @{const_name cf24_programs}
        @{typ "comma_semantic_port_program list"}
      val closure_extent = Comma_Frontier24_Selected_Table_Plan.projection_size
        ctxt "Structure closure extent" closures_projection (#named_closures candidate)
      val program_extent = Comma_Frontier24_Selected_Table_Plan.projection_size
        ctxt "Structure program extent" programs_projection (#named_programs candidate)
      fun normal_procedures (plan: Comma_Frontier24_Selected_Table_Plan.plan) =
        [#procedure plan,#post_procedure plan]
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
        (* The caller supplies ordinary, non-Code_Simp procedures only. *)
        |> fold Simplifier.add_proc
          (the_list (#child_fields closure_plan) @ procedures @ maps normal_procedures all_plans)
        |> Simplifier.add_simp (scalar_definition ctxt)
        |> Simplifier.add_simps (bound_facts @ lookup_facts)
        |> Simplifier.add_simps
          [zero_projection,nodes_projection,actions_projection,closure_extent,program_extent]
        |> Simplifier.add_simps @{thms
          comma_phase_program_sector.simps
          comma_entry_core_common_rules comma_phase_core_of_modulus_def
          comma_semantic_port_program_of_source_def
          comma_source_continuation_base.simps
          comma_canonical_position_admitted_def comma_sector_entry_bound_def
          comma_entry_control_program_def comma_near_control_program_def
          comma_parametric_exit_continue_code_def comma_shift_position.simps}
      fun prove label proposition =
        let val theorem = Goal.prove ctxt [] [] proposition (fn _ => simp_tac scalar 1)
        in Utils.exact_prop ctxt label proposition theorem end
      val zero = Const (@{const_name cf24_zero_root},bundleT --> natT) $ bundle
      val nodes = Const (@{const_name cf24_nodes},
        bundleT --> @{typ "nat comma_crt_mdd_node list"}) $ bundle
      val size = Const (@{const_name size},fastype_of nodes --> natT) $ nodes
      val zero_bound = prove "Zero root bound"
        (HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less} (zero,size)))
      val zero_leaf = prove "Zero root leaf"
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (Const (@{const_name nth},fastype_of nodes --> natT -->
              @{typ "nat comma_crt_mdd_node"}) $ nodes $ zero,
           Const (@{const_name Comma_CRT_MDD_Leaf},
              natT --> @{typ "nat comma_crt_mdd_node"}) $ nat 0)))
      val programs = program_admission ctxt scalar bundle field_projections (#named_programs candidate)
      val shapes = closure_shapes ctxt scalar bundle result
        (#named_selectors candidate) (#named_closures candidate) recipe_facts
        guard_plan all_plans source_statistics
      val aggregation_started = Time.now ()
      val closures = indexed_closures ctxt bundle (#named_closures candidate) shapes
      val _ = Comma_Proof_Profile.report ("Frontier24 closure aggregation ms=" ^
        LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (),aggregation_started))))
    in
      if include_classes then
        let
          val started = Time.now ()
          val roots = class_roots ctxt scalar bundle result closure_plan
          val _ = Comma_Proof_Profile.report ("Frontier24 class roots ms=" ^
            LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (),started))))
        in assemble ctxt bundle field_projections
          {selector=selector,programs=programs,zero_bound=zero_bound,
           zero_leaf=zero_leaf,closures=closures,roots=roots} end
      else
        let
          val (_,closure_equation) = Comma_Frontier24_Selector_Alignment.projection
            ctxt bundle field_projections @{const_name cf24_closures} closureT
          val intro = Drule.infer_instantiate ctxt
            [(("bundle",0),Thm.cterm_of ctxt bundle)]
            @{thm comma_frontier24_closure_structure_intro}
            |> Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt) [closure_equation]
          val theorem = intro OF [selector,programs,zero_bound,zero_leaf,closures]
          val expected = HOLogic.mk_Trueprop
            (@{term comma_frontier24_closure_structure_checked} $ bundle)
        in Utils.exact_prop ctxt "Exact closure structure" expected theorem end
    end

  fun certify ctxt candidate inputs = certify_requested true ctxt candidate inputs
  fun certify_closures ctxt candidate inputs = certify_requested false ctxt candidate inputs

end
