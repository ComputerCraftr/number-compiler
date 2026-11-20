(* Checked publisher for Frontier24.  All ML
   values are candidates; only Store/Replay/Import theorems enter the final
   bundle certificate. *)
structure Comma_Frontier24_Bundle_Publisher =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Operation = Comma_CRT_MDD_Operation_Replay
  structure Multiway = Comma_CRT_MDD_Multiway_Replay
  structure Import = Comma_Frontier24_MDD_Import_Certificates
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Selected_Table = Comma_Frontier24_Selected_Table_Plan
  structure Utils = Comma_CRT_MDD_Proof_Utils

  structure Shift_Request_Table = Table(
    type key = int * int * int
    val ord = fn ((a,b,c),(x,y,z)) =>
      prod_ord int_ord (prod_ord int_ord int_ord)
        ((a,(b,c)),(x,(y,z))))
  structure Priority_Key_Table = Table(
    type key = Arena.priority_key
    val ord = prod_ord (list_ord (prod_ord int_ord int_ord)) int_ord)

  val natT = @{typ nat}
  val boolT = HOLogic.boolT
  val programT = @{typ comma_semantic_port_program}
  val selectorT = @{typ comma_frontier24_selector_recipe}
  val actionT = @{typ comma_source_continuation_action}
  val closureT = @{typ comma_frontier24_closure}
  val bundleT = @{typ comma_frontier24_parametric_bundle}
  val nat_listT = HOLogic.listT natT
  val nat_pairT = HOLogic.mk_prodT (natT,natT)
  val nat_pair_listT = HOLogic.listT nat_pairT
  val shift_requestT = HOLogic.mk_prodT
    (natT,HOLogic.mk_prodT (natT,natT))
  val multiway_requestT = HOLogic.mk_prodT
    (nat_pair_listT,HOLogic.mk_prodT (natT,natT))

  fun nat n = HOLogic.mk_number natT n
  fun pair x y = HOLogic.mk_prod (x,y)
  fun list T xs = HOLogic.mk_list T xs
  fun selected_fields projections names =
    map #2 (filter (fn (name,_) => member (op =) names name) projections)
  fun unique_ints xs =
    map #1 (Inttab.dest (fold (fn index => Inttab.update (index,())) xs Inttab.empty))
  fun list_type T = Type (@{type_name list},[T])
  fun const name T args =
    list_comb (Const (name,fold_rev (curry (op -->)) (map fastype_of args) T),args)

  fun bundle_pred name bundle =
    const name boolT [bundle]

  (* `Code_Simp.dynamic_conv` returns a kernel conversion theorem.  This is
     intentionally not `Code_Evaluation.dynamic_value`/`dynamic_holds_conv`. *)
  fun small_product_simpset ctxt projections =
    put_simpset HOL_basic_ss ctxt
    |> Simplifier.add_simps @{thms case_prod_unfold case_prod_beta
      case_prod_beta' prod.collapse
      comma_frontier24_closure.select_convs
      comma_frontier24_closure_case.select_convs
      comma_frontier24_parametric_bundle.select_convs}
    |> Simplifier.add_simps (selected_fields projections
      [@{const_name cf24_radices},@{const_name cf24_nodes}])

  fun normalize_small_products_prop ctxt projections proposition =
    Thm.term_of (Thm.rhs_of (Simplifier.rewrite (small_product_simpset ctxt projections)
      (Thm.cterm_of ctxt proposition)))

  fun normalize_small_products ctxt projections theorem =
    let
      val conversion = Simplifier.rewrite (small_product_simpset ctxt projections)
        (Thm.cterm_of ctxt (Thm.prop_of theorem))
    in Thm.equal_elim conversion theorem end

  (* Transport a checked proposition through one exact equality without
     invoking the ambient theory simpset on its certificate or bundle terms. *)
  fun rewrite_rule_sterile ctxt rules theorem =
    Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt) rules theorem

  fun profiled_stage stage work =
    if not (Comma_Proof_Profile.enabled ()) then work ()
    else
      let
        val owner = "Frontier24 publisher"
        val started = Time.now ()
        val _ = Comma_Proof_Profile.report
          (owner ^ " stage=" ^ stage ^ "-start")
        val result = Exn.capture work ()
        val status = (case result of Exn.Res _ => "ok" | Exn.Exn _ => "failed")
        val _ = Comma_Proof_Profile.report
          (owner ^ " stage=" ^ stage ^ "-complete status=" ^ status ^
            " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
      in Exn.release result end

  fun raw_shift_requests (result: Compiler.result) =
    maps (fn (closure: Compiler.closure) =>
      map (fn (row: Compiler.closure_case) =>
        (#full_shift closure,#guard_root row,#shifted_guard_root row))
        (#cases closure)) (Compiler.closures result)

  fun shift_requests raw =
    let
      val indexed = map_index (fn (index,key) => (index,key)) raw
      val latest = fold (fn (index,key) =>
        Shift_Request_Table.update (key,index)) indexed Shift_Request_Table.empty
    in map_filter (fn (index,key) =>
      if Shift_Request_Table.lookup latest key = SOME index then SOME key else NONE)
      indexed end

  fun raw_multiway_requests (result: Compiler.result) =
    let
      val arena = Compiler.arena result
      val zero = Arena.action_index arena (Arena.action_none arena)
      fun request (closure: Compiler.closure) =
        (map (fn (row:Compiler.closure_case) =>
          (#shifted_guard_root row,#action_output_root row)) (#cases closure),
         zero,#output_root closure)
    in map request (filter (fn (closure:Compiler.closure) =>
      is_none (#near_token closure)) (Compiler.closures result)) end

  fun multiway_requests store (result: Compiler.result) raw =
    let
      val indexed = map_index (fn (index,(rows,fallback,output)) =>
        (index,((rows,fallback),output))) raw
      val latest = fold (fn (index,(key,output)) => fn table =>
        (case Priority_Key_Table.lookup table key of
          SOME (_,prior) => if prior=output then Priority_Key_Table.update (key,(index,output)) table
            else error "One priority key has inconsistent closure roots"
        | NONE => Priority_Key_Table.update (key,(index,output)) table)) indexed Priority_Key_Table.empty
      val keys = Compiler.priority_keys result
      val _ = if length keys = length (Priority_Key_Table.dest latest) then ()
        else error "Priority keys disagree with closure requests"
      val ordered = fold (fn key as (rows,fallback) =>
        let
          val (index,output) = (case Priority_Key_Table.lookup latest key of
            SOME value => value | NONE => error "Priority closure request is missing")
          val witness = Store.priority_witness store key
          val _ = if #result witness = output then ()
            else error "Priority output differs from frozen arena witness"
        in Inttab.update (index,(rows,fallback,output)) end) keys Inttab.empty
      val _ = if length keys = Inttab.size ordered then ()
        else error "Priority requests contain duplicate keys"
    in map #2 (Inttab.dest ordered) end

  fun shift_request_term (amount,source,target) =
    pair (nat amount) (pair (nat source) (nat target))

  fun multiway_request_term (rows,fallback,output) =
    pair (list nat_pairT (map (fn (guard,action) => pair (nat guard) (nat action)) rows))
      (pair (nat fallback) (nat output))

  (* Consume one checked closure at a time.  The generic indexed theorem
     transports coverage to the deduplicated request list without computing
     its flattened representation or unfolding the complete closure table. *)
  fun indexed_requests ctxt projections label predicate unique_facts bundle
      (owner: Runtime.named_table) (plan: Selected_Table.plan) introduction =
    let
      val rule = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle),
         (("P",0),Thm.cterm_of ctxt predicate)] introduction
      val premise = the_single (Thm.prems_of rule)
      val (application,_) = Term.dest_comb (HOLogic.dest_Trueprop premise)
      val (_,indexed_predicate) = Term.dest_comb application
      val projection_eq = (case AList.lookup (op =) projections @{const_name cf24_closures} of
          SOME theorem => theorem
        | NONE => error (label ^ " lacks the checked closure projection"))
      val size_fact = Selected_Table.projection_size ctxt label projection_eq owner
      val basic = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps (unique_facts @
          selected_fields projections [@{const_name cf24_zero_root}])
        |> Simplifier.add_simps @{thms list_all_Cons_iff list_all_Nil_iff list.map
          comma_frontier24_closure.select_convs comma_frontier24_closure_case.select_convs
          option.simps prod.case prod.collapse HOL.simp_thms}
      fun prove_item index =
        let val target = HOLogic.mk_Trueprop (indexed_predicate $ nat index)
            val normalized = Thm.beta_conversion true (Thm.cterm_of ctxt target)
            val selected = #lookup plan index
            val theorem = Utils.prove_exact ctxt (label ^ " selected closure requests")
              (Thm.term_of (Thm.rhs_of normalized))
              (fn _ => simp_tac (basic |> Simplifier.add_simp selected) 1)
        in Thm.equal_elim (Thm.symmetric normalized) theorem end
      val count = length (#rows owner)
      val successor = Comma_Selected_List_Conversion.make_successor_cache ctxt count
      val indexed = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt=ctxt,predicate=indexed_predicate,bound=count,prove_item=prove_item,
         zero_fact= @{thm comma_indexed_all_zero},step_fact= @{thm comma_indexed_all_Suc},
         successor_equation= #equation successor}
      val rewrite = Conv.arg_conv (Conv.arg_conv
        (Conv.arg_conv (Conv.rewr_conv (size_fact RS @{thm eq_reflection}))))
        (Thm.cterm_of ctxt premise)
      val premise_fact = Thm.equal_elim (Thm.symmetric rewrite) indexed
      val premise_fact = Utils.exact_prop ctxt (label ^ " indexed request coverage")
        premise premise_fact
      val theorem = rule OF [premise_fact]
    in Utils.exact_prop ctxt (label ^ " deduplicated request coverage")
      (Thm.concl_of rule) theorem end

  fun shift_predicate store =
    let
      val triple = Free ("cf24_shift_request",shift_requestT)
      val fst_nat = Const (@{const_name fst},shift_requestT --> natT)
      val snd_pair = Const (@{const_name snd},shift_requestT -->
        HOLogic.mk_prodT (natT,natT)) $ triple
      val snd_fst = Const (@{const_name fst},HOLogic.mk_prodT (natT,natT) --> natT) $ snd_pair
      val snd_snd = Const (@{const_name snd},HOLogic.mk_prodT (natT,natT) --> natT) $ snd_pair
      val pred = const @{const_name comma_crt_mdd_root_shift_certificate} boolT
        [Store.radices store,Store.table store,
         fst_nat $ triple,snd_fst,snd_snd]
    in Term.lambda triple pred end

  fun multiway_predicate store =
    Envir.beta_norm (@{term "\<lambda>radices nodes request.
      case request of (rows,fallback,output) =>
        comma_crt_mdd_multiway_certificate radices (nodes::nat comma_crt_mdd_node list)
          rows fallback output"} $ Store.radices store $ Store.table store)

  fun certify_shift_requests ctxt projections store replay requests bundle owner plan =
    let
      val facts = map (fn (amount,source,target) =>
        let
          val theorem = Operation.certify_shift replay amount source target
          val item = shift_request_term (amount,source,target)
          val application = Term.betapply (shift_predicate store,item)
          val actual = HOLogic.dest_Trueprop (Thm.prop_of theorem)
          val conversion = Simplifier.rewrite
            (put_simpset HOL_basic_ss ctxt
              |> Simplifier.add_simps @{thms prod.collapse})
            (Thm.cterm_of ctxt application)
          val _ = Utils.exact_prop ctxt "Frontier24 shift tuple projections"
            (Logic.mk_equals (application,actual)) conversion
          val theorem = rewrite_rule_sterile ctxt [Thm.symmetric conversion] theorem
        in Utils.exact_prop ctxt "Frontier24 shift replay"
          (HOLogic.mk_Trueprop application) theorem end) requests
      val request_function = Const (@{const_name comma_frontier24_shift_requests},
        bundleT --> list_type shift_requestT) $ bundle
      val all_requested = indexed_requests ctxt projections "Frontier24 shift"
        (shift_predicate store) facts bundle owner plan
        @{thm comma_frontier24_shift_requests_from_indexed}
      val definition = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_shifts_certified_def}
      val expected_definition = normalize_small_products_prop ctxt projections
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
        (bundle_pred @{const_name comma_frontier24_shifts_certified} bundle,
         const @{const_name list_all} boolT
           [shift_predicate store,request_function])))
      val definition = normalize_small_products ctxt projections definition
      val definition = Utils.exact_prop ctxt "Frontier24 shifts definition shape"
        expected_definition definition
      val certified = @{thm iffD2} OF [definition,all_requested]
      val expected = HOLogic.mk_Trueprop
        (bundle_pred @{const_name comma_frontier24_shifts_certified} bundle)
    in Utils.exact_prop ctxt "Frontier24 shifts certified" expected certified end

  fun certify_multiway_requests ctxt projections store replay requests bundle owner plan =
    let
      val pred = multiway_predicate store
      val facts = map (fn request as (rows,fallback,_) =>
        let
          val theorem = Multiway.certify replay (rows,fallback)
          val application = Term.betapply (pred,multiway_request_term request)
          val actual = HOLogic.dest_Trueprop (Thm.prop_of theorem)
          val conversion = Simplifier.rewrite
            (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps @{thms prod.case})
            (Thm.cterm_of ctxt application)
          val _ = Utils.exact_prop ctxt "Frontier24 priority tuple projections"
            (Logic.mk_equals (application,actual)) conversion
          val theorem = rewrite_rule_sterile ctxt [Thm.symmetric conversion] theorem
        in Utils.exact_prop ctxt "Frontier24 priority replay"
          (HOLogic.mk_Trueprop application) theorem end) requests
      val request_function = Const (@{const_name comma_frontier24_multiway_requests},
        bundleT --> list_type multiway_requestT) $ bundle
      val all_requested = indexed_requests ctxt projections "Frontier24 priority"
        pred facts bundle owner plan
        @{thm comma_frontier24_multiway_requests_from_indexed}
      val definition = Drule.infer_instantiate ctxt
        [(("bundle",0),Thm.cterm_of ctxt bundle)]
        @{thm comma_frontier24_multiways_certified_def}
      val expected_definition = normalize_small_products_prop ctxt projections
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (bundle_pred @{const_name comma_frontier24_multiways_certified} bundle,
           const @{const_name list_all} boolT [pred,request_function])))
      val definition = normalize_small_products ctxt projections definition
      val definition = Utils.exact_prop ctxt "Frontier24 priority definition shape"
        expected_definition definition
      val certified = @{thm iffD2} OF [definition,all_requested]
      val expected = HOLogic.mk_Trueprop
        (bundle_pred @{const_name comma_frontier24_multiways_certified} bundle)
    in Utils.exact_prop ctxt "Frontier24 multiways certified" expected certified end

  fun certify_guard_imports ctxt projections store arena result bundle =
    let
      val guard_plan = Import.make_guard_plan ctxt
      val facts = map (#certify guard_plan store arena) (Compiler.guard_entries result)
      val predicate = bundle_pred @{const_name comma_frontier24_guard_imports_exact} bundle
      val target = HOLogic.mk_Trueprop predicate
      val ss = put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_simps (@{thms comma_frontier24_guard_imports_exact_def
          comma_frontier24_parametric_bundle.select_convs
          comma_frontier24_guard_entry.select_convs
          list.simps set_simps ball_simps})
        |> Simplifier.add_simps (selected_fields projections [@{const_name cf24_guard_entries}])
        |> Simplifier.add_simps facts
      val theorem = Utils.prove_exact ctxt "Frontier24 guard root maps" target
        (fn _ => Simplifier.asm_full_simp_tac ss 1)
    in Utils.exact_prop ctxt "Frontier24 exact guard import set" target theorem end

  fun referenced_roots (result: Compiler.result) =
    let
      fun case_roots (row: Compiler.closure_case) =
        [#guard_root row,#shifted_guard_root row,#action_output_root row]
      fun closure_roots (closure: Compiler.closure) =
        [#output_root closure] @ maps case_roots (#cases closure) @
        maps the_list
          [#near_action_output_root closure]
      fun selector_roots selector = (case selector of
          Compiler.Near_Selector _ => []
        | Compiler.Entry_Selector {cases,...} => map (fn row =>
            Arena.boolean_index (Compiler.arena result) (#guard_root row)) cases)
      val guard_roots = map #root (Compiler.guard_entries result)
      val class_roots = map (Arena.action_index (Compiler.arena result))
        (Compiler.class_roots result)
      val zero_root = Arena.action_index (Compiler.arena result)
        (Arena.action_none (Compiler.arena result))
    in unique_ints (zero_root::class_roots @ guard_roots @
      maps closure_roots (Compiler.closures result) @
      maps selector_roots (Compiler.selectors result)) end

  fun output_leaf_roots (result: Compiler.result) =
    let
      fun row_roots (row: Compiler.closure_case) = [#action_output_root row]
      fun closure_roots (closure: Compiler.closure) =
        maps row_roots (#cases closure) @
        the_list (#near_action_output_root closure)
      val zero_root = Arena.action_index (Compiler.arena result)
        (Arena.action_none (Compiler.arena result))
    in unique_ints (zero_root::maps closure_roots (Compiler.closures result)) end

  structure Selector_Proofs = Comma_Frontier24_Selector_Proofs (
    val fixed_entry_port_conversion_plan = Comma_Direct_Entry_Arithmetic.fixed_entry_port_conversion_plan
    val core_parameter_conversion_plan = Comma_Direct_Entry_Arithmetic.core_parameter_conversion_plan)

  fun selector_transport ctxt bundle selector
      (programs_plan: Selected_Table.plan) (selectors_plan: Selected_Table.plan)
      (actions_plan: Selected_Table.plan) =
    let
      val expected = HOLogic.mk_Trueprop
        (bundle_pred @{const_name comma_frontier24_selector_rows_checked} bundle)
      val selector = Utils.exact_prop ctxt "Selector transport authority" expected selector
      val raw_rule = (@{thm comma_frontier24_selector_rows_checkedD} OF [selector])
        RS @{thm eqTrueI} RS @{thm eq_reflection}
      val rule = (case #transport_equation actions_plan of
          NONE => raw_rule
        | SOME equation => rewrite_rule_sterile ctxt [equation] raw_rule)
      val pattern = #1 (Logic.dest_equals (Thm.concl_of rule))
      val pattern_ct = Thm.cterm_of ctxt pattern
      val hits = Unsynchronized.ref 0
      fun canonical_argument plan argument =
        #canonicalize (plan: Selected_Table.plan) (Thm.cterm_of ctxt argument)
      fun rewrite request =
        let
          val request_term = Thm.term_of request
          val (head,arguments) = strip_comb request_term
        in if not (Utils.closed request_term) then NONE else
          case (head,arguments) of
            (Const (name,_),[program,recipe,actions]) =>
              if name <> @{const_name comma_frontier24_selector_recipe_matches}
              then NONE else
              (case (canonical_argument programs_plan program,
                     canonical_argument selectors_plan recipe,
                     canonical_argument actions_plan actions) of
                (SOME program_eq,SOME recipe_eq,SOME actions_eq) =>
                  let
                    val canonical = fold (fn argument => fn function =>
                      Thm.combination function argument)
                      [program_eq,recipe_eq,actions_eq]
                      (Thm.reflexive (Thm.cterm_of ctxt head))
                    val equation = Thm.instantiate
                      (Thm.match (pattern_ct,Thm.rhs_of canonical)) rule
                    val index = #2 (dest_comb program)
                    val programs = const @{const_name cf24_programs}
                      (HOLogic.listT programT) [bundle]
                    val bound = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
                      (index,const @{const_name size} natT [programs]))
                    val _ = if Thm.concl_of equation aconv
                          Logic.mk_equals (Thm.term_of (Thm.rhs_of canonical),@{term True})
                        andalso Thm.prems_of equation=[bound]
                        andalso null (Thm.hyps_of equation)
                        andalso null (Thm.tpairs_of equation) then () else
                      error "Selector transport changed its indexed bound or result"
                    val bound_ct = Thm.cterm_of ctxt bound
                    val point = Thm.implies_elim equation (Thm.assume bound_ct)
                    val exact = Thm.implies_intr bound_ct
                      (Thm.transitive canonical point)
                    val _ = if Thm.concl_of exact aconv
                        Logic.mk_equals (request_term,@{term True}) andalso
                        Thm.prems_of exact=[bound] andalso
                        null (Thm.hyps_of exact) andalso
                        null (Thm.tpairs_of exact) then () else
                      error "Selector transport changed the original request"
                    val _ = hits := !hits+1
                  in SOME exact end
              | _ => NONE)
          | _ => NONE
        end
        handle Pattern.MATCH => NONE
      val dispatch = @{term "comma_frontier24_selector_recipe_matches
        selector_program selector_recipe selector_actions"}
      val procedure = Simplifier.make_simproc ctxt
        {name="frontier24_checked_selector_transport",kind=Simplifier.Congproc true,
         lhss=[dispatch],proc=fn _ => fn _ => rewrite,identifier=[]}
    in {procedure=procedure,hits=fn () => !hits} end

  fun certify_requested include_classes ctxt store arena operation_replay multiway_replay
      (candidate: Runtime.candidate) =
    let
      val result = #result candidate
      val bundle = #bundle candidate
      val projections = #field_projections candidate
      val _ = Comma_Proof_Profile.report
        ("Frontier24 publisher candidate " ^ Runtime.statistics candidate)
      val root_indices = referenced_roots result
      val output_indices = output_leaf_roots result
      val bound_facts = map (Store.bound store) root_indices
      val lookup_facts = map (Store.lookup store) output_indices
      val lookup_plans =
        [Selected_Table.make_balanced ctxt bundle projections "programs" @{const_name cf24_programs}
          programT (length (Compiler.programs result)) (#named_programs candidate),
         Selected_Table.make_balanced ctxt bundle projections "selectors" @{const_name cf24_selectors}
          selectorT (length (Compiler.selectors result)) (#named_selectors candidate),
         Selected_Table.make_named ctxt bundle projections "actions" @{const_name cf24_action_tokens}
          actionT (length (Compiler.action_tokens result))
          (#named_actions candidate) (Compiler.action_tokens result),
         Selected_Table.make_balanced ctxt bundle projections "closures" @{const_name cf24_closures}
          closureT (length (Compiler.closures result)) (#named_closures candidate)]
      val actions_plan = (case lookup_plans of
          [_,_,plan,_] => plan | _ => error "Selector family requires the exact action owner")
      val (actions,_) = Comma_Frontier24_Selector_Alignment.projection ctxt bundle projections
        @{const_name cf24_action_tokens} actionT
      val tokens = Selector_Proofs.token_owner ctxt actions actions_plan
      val selector_outcome = Exn.capture (fn () => profiled_stage "selector" (fn () =>
        let
          val programs = Compiler.programs result
          val selectors = #rows (#named_selectors candidate)
          val facts = Selector_Proofs.selector_family_facts ctxt result bundle projections
            programs selectors actions_plan tokens
          val (program_plan,selector_plan) = (case lookup_plans of
              [p,s,_,_] => (p,s) | _ => error "Selector plans are incomplete")
          val checked = Comma_Frontier24_Selector_Alignment.certify_indexed
            ctxt bundle projections programs (#named_programs candidate) (#named_selectors candidate)
            program_plan selector_plan facts
        in (checked,facts) end)) ()
      val _ = Comma_Proof_Profile.report
        ("Frontier24 selector lookups " ^
          String.concatWith " " (map Selected_Table.statistics lookup_plans))
      val (selector,recipe_facts) = Exn.release selector_outcome
      val transport = (case lookup_plans of
          [programs,selectors,actions,_] =>
            selector_transport ctxt bundle selector programs selectors actions
        | _ => error "Selector transport requires its three exact table owners")
      (* Structure proofs use ordinary numeral terms. Their owner installs the
         normal table procedures; code-output procedures belong to Code_Simp. *)
      val structural_procedures = [#procedure transport,#procedure tokens]
      val structural = profiled_stage "structural" (fn () =>
        (if include_classes then Comma_Frontier24_Structure_Proofs.certify
         else Comma_Frontier24_Structure_Proofs.certify_closures) ctxt candidate
          {selector=selector,recipe_facts=recipe_facts,plans=lookup_plans,
           procedures=structural_procedures,source_statistics= #statistics tokens,
           bound_facts=bound_facts,lookup_facts=lookup_facts})
      val _ = Comma_Proof_Profile.report
        ("Frontier24 selector_transports=" ^ Int.toString (#hits transport ()) ^
          " " ^ #statistics tokens ())
      val guard_imports = profiled_stage "guard_imports" (fn () =>
        certify_guard_imports ctxt projections store arena result bundle)
      val closure_plan = (case lookup_plans of
          [_,_,_,plan] => plan | _ => error "Request coverage lacks its closure owner")
      val (shifts_requested,shifts) =
        profiled_stage "shift_requests" (fn () =>
          let
            val raw = raw_shift_requests result
            val requested = shift_requests raw
            val theorem = certify_shift_requests ctxt projections store operation_replay
              requested bundle (#named_closures candidate) closure_plan
          in (requested,theorem) end)
      val (multiways_requested,multiways) =
        profiled_stage "multiway_requests" (fn () =>
          let
            val raw = raw_multiway_requests result
            val requested = multiway_requests store result raw
            val theorem = certify_multiway_requests ctxt projections store multiway_replay
              requested bundle (#named_closures candidate) closure_plan
          in (requested,theorem) end)
      val theorem = profiled_stage "final_assembly" (fn () =>
        let
          val table = Store.wellformed store
          val expected_table = HOLogic.mk_Trueprop
            (const @{const_name comma_crt_mdd_table_wellformed} boolT
              [Store.radices store,Store.table store])
          val table = Utils.exact_prop ctxt "Frontier24 frozen table" expected_table table
          val components = [table,structural,guard_imports,shifts,multiways]
          val (predicate,definition) = if include_classes then
            (@{const_name comma_frontier24_bundle_semantic_certified},
             @{thm comma_frontier24_bundle_semantic_certified_def})
            else (@{const_name comma_frontier24_closure_certified},
              @{thm comma_frontier24_closure_certified_def})
          val expected = HOLogic.mk_Trueprop (bundle_pred predicate bundle)
          val simp = put_simpset HOL_basic_ss ctxt
            |> Simplifier.add_simps [definition]
            |> Simplifier.add_simps
              @{thms comma_frontier24_parametric_bundle.select_convs}
            |> Simplifier.add_simps (selected_fields projections
              [@{const_name cf24_radices},@{const_name cf24_nodes}])
            |> Simplifier.add_simps components
          val theorem = Utils.prove_exact ctxt "Frontier24 certified bundle" expected
            (fn _ => Simplifier.asm_full_simp_tac simp 1)
        in Utils.exact_prop ctxt "Frontier24 certified bundle" expected theorem end)
      val statistics = Store.statistics store ^ " " ^
        Operation.statistics operation_replay ^ " " ^ Multiway.statistics multiway_replay ^
        " guard_root_maps=" ^ Int.toString (length (Compiler.guard_entries result)) ^
        " shift_requests=" ^ Int.toString (length shifts_requested) ^
        " multiway_requests=" ^ Int.toString (length multiways_requested) ^
        " referenced_roots=" ^ Int.toString (length root_indices) ^
        " output_rows=" ^ Int.toString (length output_indices) ^ " " ^
        String.concatWith " " (map Selected_Table.statistics lookup_plans)
    in {theorem=theorem,statistics=statistics,lookup_plans=lookup_plans} end

  fun certify ctxt store arena operation_replay multiway_replay candidate =
    certify_requested true ctxt store arena operation_replay multiway_replay candidate

  fun certify_closures ctxt store arena operation_replay multiway_replay candidate =
    certify_requested false ctxt store arena operation_replay multiway_replay candidate
end
