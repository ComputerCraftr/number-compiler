(* Proof-producing split-control/weight B32 publisher.  The powered action is
   memoized by (depth, root); each successor composes already-certified child
   diagrams and asks the occurrence owner only for depth-zero source rows. *)
signature COMMA_SEMANTIC_B1_CRT_CONVERSION =
sig
  type root_action = Comma_Semantic_B1_B32_Projection.root_action
  type stats =
    {lookups: int, hits: int, misses: int, failures: int,
     root_entries_cached: int, value_nodes: int,
     certification: {calls: int, failed_calls: int, nodes: int,
       milliseconds: LargeInt.int}}
  type engine =
    {power_split: int -> int -> root_action,
     b32: int -> root_action,
     b32_stop242_all: unit -> {certificate: thm, roots: root_action list},
     smoke_split_root: unit -> root_action,
     validate: root_action -> bool,
     stats: unit -> stats,
     report: unit -> string}
  val make: Proof.context -> engine
end

structure Comma_Semantic_B1_CRT_Conversion: COMMA_SEMANTIC_B1_CRT_CONVERSION =
struct
  type root_action = Comma_Semantic_B1_B32_Projection.root_action
  type stats =
    {lookups: int, hits: int, misses: int, failures: int,
     root_entries_cached: int, value_nodes: int,
     certification: {calls: int, failed_calls: int, nodes: int,
       milliseconds: LargeInt.int}}
  type engine =
    {power_split: int -> int -> root_action,
     b32: int -> root_action,
     b32_stop242_all: unit -> {certificate: thm, roots: root_action list},
     smoke_split_root: unit -> root_action,
     validate: root_action -> bool,
     stats: unit -> stats,
     report: unit -> string}

  fun make ctxt : engine =
    let
      val (certify, certification) = Comma_Entry_Arithmetic.make_certifier ctxt
      val occurrence = Comma_Semantic_B1_Occurrence_Check_Cache.make ctxt
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val value_nodes = Unsynchronized.ref 0
      val root_lookups = Unsynchronized.ref 0
      val root_hits = Unsynchronized.ref 0
      val root_misses = Unsynchronized.ref 0
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val split_values = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val root_records = Unsynchronized.ref (Termtab.empty: root_action Termtab.table)
      val compose_conversion = Unsynchronized.ref
        (NONE: (Proof.context -> conv) option)
      val natT = @{typ nat}
      val actionT = @{typ comma_crt_split_action}
      val nat = HOLogic.mk_number natT
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt
      val simpset = Simplifier.simpset_of ctxt
      val stop_conversion = Code_Simp.static_conv
        {ctxt = ctxt, simpset = SOME simpset,
         consts = [@{const_name comma_crt_mdd_stop_weights_bounded242}]}

      fun standalone theorem = Thm.nprems_of theorem = 0 andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)

      fun require_equation request theorem =
        if not (Thm.term_of (Thm.lhs_of theorem) aconv request) then
          error "Split CRT conversion returned an equation for a different request"
        else if not (Comma_Selected_List_Conversion.closed
            (Thm.term_of (Thm.rhs_of theorem))) then
          error "Split CRT conversion returned an open split value"
        else if fastype_of (Thm.term_of (Thm.rhs_of theorem)) <> actionT then
          error "Split CRT conversion returned a value of the wrong type"
        else if not (standalone theorem) then
          error "Split CRT conversion returned an open theorem"
        else theorem

      fun split_request depth root =
        @{term comma_semantic_b1_crt_power_split_action} $ nat depth $ nat root

      fun parse_split_request request =
        (case strip_comb request of
          (Const (name, _), [depth_term, root_term]) =>
            if name = @{const_name comma_semantic_b1_crt_power_split_action} then
              (case (try HOLogic.dest_number depth_term, try HOLogic.dest_number root_term) of
                (SOME (depthT, depth), SOME (rootT, root)) =>
                  if depthT = natT andalso rootT = natT andalso
                      0 <= depth andalso depth <= 5 andalso 0 <= root andalso root < 46
                  then SOME (depth, root) else NONE
              | _ => NONE)
            else NONE
        | _ => NONE)

      fun root_action_equation root =
        let
          val root_occurrence = @{term comma_semantic_b1_crt_root_occurrence} $ nat root
          val occurrence_theorem = #select_root_occurrence occurrence
            (Thm.cterm_of ctxt root_occurrence)
          val root_request = @{term comma_semantic_b1_crt_root_split_action} $ nat root
          val root_definition = @{thm comma_semantic_b1_crt_root_split_action_def}
            RS @{thm eq_reflection}
          val definition_step = Conv.rewr_conv root_definition
            (Thm.cterm_of ctxt root_request)
          val selected_context = put_simpset HOL_basic_ss ctxt addsimps
            [occurrence_theorem, @{thm option.case}]
          val selected_step = Simplifier.rewrite selected_context
            (Thm.rhs_of definition_step)
          val action_request = Thm.term_of (Thm.rhs_of selected_step)
          val action_theorem = #convert_selected occurrence
            (Thm.cterm_of ctxt action_request)
          val equation = Thm.transitive definition_step
            (Thm.transitive selected_step action_theorem)
          val rhs = Thm.term_of (Thm.rhs_of equation)
          val _ = if Thm.term_of (Thm.lhs_of equation) aconv root_request andalso
              fastype_of rhs = actionT andalso standalone equation
            then () else error "Selected B1 occurrence did not produce a closed split action"
        in certify equation end

      fun action_result equation = Thm.term_of (Thm.rhs_of equation)

      fun find_composition term =
        let
          fun seek current =
            let
              val (head, arguments) = strip_comb current
            in
              if head aconv @{term comma_crt_split_compose_from} then SOME current
              else get_first seek arguments
            end
        in
          (case seek term of
            SOME request => request
          | NONE => error "Successor split equation has no matched CRT composition")
        end

      fun shallow_context theorems =
        put_simpset HOL_basic_ss ctxt addsimps
          (@{thms Let_def[abs_def] comma_crt_split_action.select_convs
             fst_conv snd_conv} @ theorems)

      fun successor_equation depth root =
        let
          val predecessor = depth - 1
          val child_equation = split_value predecessor root
          val request = split_request depth root
          val depth_equality = Goal.prove ctxt [] []
            (HOLogic.mk_Trueprop (HOLogic.mk_eq (nat depth,
              HOLogic.mk_Suc (nat predecessor))))
            (fn {context, ...} => simp_tac
              (Comma_Entry_Arithmetic.natural_context context) 1)
            |> (fn theorem => theorem RS @{thm eq_reflection})
          val depth_step = Conv.fun_conv
            (Conv.arg_conv (Conv.rewr_conv depth_equality))
            (Thm.cterm_of ctxt request)
          val instantiated = Drule.infer_instantiate ctxt
            [(("k", 0), Thm.cterm_of ctxt (nat predecessor)),
             (("root", 0), Thm.cterm_of ctxt (nat root))]
            @{thm comma_semantic_b1_crt_power_split_action.simps(2)}
          val recursive_step = Conv.rewr_conv (instantiated RS @{thm eq_reflection})
            (Thm.rhs_of depth_step)
          val one_step = Thm.transitive depth_step recursive_step
          val expanded_lets = Simplifier.rewrite (shallow_context [])
            (Thm.rhs_of one_step)
          val with_left = Simplifier.rewrite (shallow_context [child_equation])
            (Thm.rhs_of expanded_lets)
          val to_compose = Thm.term_of (Thm.rhs_of with_left)
          val compose_request = find_composition to_compose
          val compose =
            (case !compose_conversion of
              SOME convert => convert ctxt (Thm.cterm_of ctxt compose_request)
            | NONE => error "Matched CRT composition conversion is not initialized")
          val _ = if Thm.term_of (Thm.lhs_of compose) aconv compose_request andalso
              standalone compose andalso
              Comma_Selected_List_Conversion.closed (Thm.term_of (Thm.rhs_of compose))
            then () else error "Matched CRT composition returned an invalid equation"
          val finished = Simplifier.rewrite (shallow_context [compose])
            (Thm.rhs_of with_left)
          val equation = Thm.transitive one_step
            (Thm.transitive expanded_lets (Thm.transitive with_left finished))
          val _ = if Thm.term_of (Thm.lhs_of equation) aconv request then ()
            else error "Successor split equation changed its exact request"
        in equation end

      and split_value depth root =
        if depth < 0 orelse depth > 5 orelse root < 0 orelse root >= 46 then
          error "Split B32 value request is outside the finite depth/root domain"
        else
          let
            val request = split_request depth root
            val _ = lookups := !lookups + 1
          in
            (case Termtab.lookup (!split_values) request of
              SOME theorem => (hits := !hits + 1; theorem)
            | NONE =>
                if Termtab.defined (!active) request then
                  error "Recursive split B32 cache re-entered an active depth/root"
                else
                  let
                    val _ = misses := !misses + 1
                    val _ = active := Termtab.update (request, ()) (!active)
                    val attempt = Exn.capture (fn () =>
                      let
                        val equation =
                          if depth = 0 then
                            let
                              val root_equation = root_action_equation root
                              val step = Conv.rewr_conv
                                (@{thm comma_semantic_b1_crt_power_split_action.simps(1)}
                                  RS @{thm eq_reflection})
                                (Thm.cterm_of ctxt request)
                            in Thm.transitive step root_equation end
                          else successor_equation depth root
                          val equation = require_equation request equation |> certify
                          val action = action_result equation
                          val _ = if
                              Comma_Semantic_B1_B32_Projection.action_constructor_normal ctxt action
                            then () else error "Split power cache produced a non-constructor action"
                          val _ = value_nodes := !value_nodes + Term.size action
                      in equation end) ()
                    val _ = active := Termtab.delete request (!active)
                    val _ = if Exn.is_exn attempt then failures := !failures + 1 else ()
                    val theorem = Exn.release attempt
                    val _ = split_values := Termtab.update (request, theorem) (!split_values)
                  in theorem end)
          end

      fun power_value_proc _ cterm =
        let
          val request = Thm.term_of cterm
          fun normalized_request () =
            let
              (* Code_Simp can expose class-overloaded zero/successor forms.
                 Restore typed naturals before the exact depth/root lookup. *)
              val overloaded = Axclass.overload_conv ctxt cterm
              val normalized = Simplifier.rewrite scalar_context (Thm.rhs_of overloaded)
            in Thm.transitive overloaded normalized end
          fun use_equation normalization canonical =
            (case parse_split_request canonical of
              SOME (depth, root) =>
                let
                  val theorem = split_value depth root
                  val _ = if Thm.term_of (Thm.lhs_of theorem) aconv canonical then ()
                    else error "Split B32 cache key did not match normalized request"
                  val result = Thm.transitive normalization theorem
                  val _ = if Thm.term_of (Thm.lhs_of result) aconv request andalso
                      standalone result then ()
                    else error "Split B32 memo returned a theorem for another request"
                in SOME result end
            | NONE => NONE)
        in
          if not (Comma_Selected_List_Conversion.closed request) then NONE
          else
            (case parse_split_request request of
              SOME (depth, root) =>
                let
                  val theorem = split_value depth root
                in if Thm.term_of (Thm.lhs_of theorem) aconv request then SOME theorem
                   else
                     let val normalized = normalized_request ()
                     in use_equation normalized
                       (Thm.term_of (Thm.rhs_of normalized)) end
                end
            | NONE =>
                let val normalized = normalized_request ()
                in use_equation normalized (Thm.term_of (Thm.rhs_of normalized)) end)
        end

      val power_proc = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_split_power_exact_memo",
         kind = Simplifier.Congproc false,
         lhss = [Comma_Selected_List_Conversion.schematize
           @{term "comma_semantic_b1_crt_power_split_action depth root"}],
         proc = fn _ => power_value_proc,
         identifier = []}
      val operation_context =
        Comma_Semantic_B1_CRT_Operation_Conversion.operation_context ctxt
          |> Simplifier.add_proc power_proc
      val _ = compose_conversion := SOME (Code_Simp.static_conv
        {ctxt = ctxt, simpset = SOME (Simplifier.simpset_of operation_context),
         consts = [@{const_name comma_crt_split_compose_from}]})

      fun stop_claim weight_diagram = HOLogic.mk_Trueprop
        (@{term comma_crt_mdd_stop_weights_bounded242} $ weight_diagram)

      fun stop_certificate action =
        let
          val selector = Const (@{const_name comma_crt_split_weight},
            actionT --> @{typ comma_crt_weight_mdd}) $ action
          val selected = Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps
              @{thms comma_crt_split_action.select_convs})
            (Thm.cterm_of ctxt selector)
          val weight_diagram = Thm.term_of (Thm.rhs_of selected)
          val _ = if fastype_of weight_diagram = @{typ comma_crt_weight_mdd} andalso
              Comma_Selected_List_Conversion.closed weight_diagram
            then () else error "B32 weight projection is not a closed MDD"
          val claim = stop_claim weight_diagram
          val proposition = HOLogic.dest_Trueprop claim
          val checked = stop_conversion ctxt (Thm.cterm_of ctxt proposition)
          val rhs = Thm.term_of (Thm.rhs_of checked)
          val _ = if rhs aconv HOLogic.true then ()
            else error "Concrete B32 root has a non-Stop or over-height weight leaf"
          val proposition_eq = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) checked
          val leaf_proof = Thm.equal_elim (Thm.symmetric proposition_eq) @{thm TrueI}
          val predicate_eq = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt
              @{term comma_crt_mdd_stop_weights_bounded242})) selected
          val selected_eq = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) predicate_eq
          val proof = Thm.equal_elim (Thm.symmetric selected_eq) leaf_proof
        in certify proof end

      fun validate (entry: root_action) =
        let
          val root = #root entry
          val request = split_request 5 root
          val action = #action entry
          val equation = #equation entry
          val stop_weights = #stop_weights entry
          val goal = stop_claim
            (@{term comma_crt_split_weight} $ action)
        in root >= 0 andalso root < 46 andalso
          Comma_Selected_List_Conversion.closed action andalso
          fastype_of action = actionT andalso
          Comma_Semantic_B1_B32_Projection.action_constructor_normal ctxt action andalso
          Thm.term_of (Thm.lhs_of equation) aconv request andalso
          Thm.term_of (Thm.rhs_of equation) aconv action andalso standalone equation andalso
          Thm.prop_of stop_weights aconv goal andalso standalone stop_weights
        end

      fun power_split depth root =
        if depth <> 5 then
          error "The production split publisher accepts only powered B32 depth 5"
        else if root < 0 orelse root >= 46 then
          error "CRT split power root must be in 0..45"
        else
          let
            val request = split_request depth root
            val _ = root_lookups := !root_lookups + 1
          in
            (case Termtab.lookup (!root_records) request of
              SOME entry => (root_hits := !root_hits + 1; entry)
            | NONE =>
                let
                  val _ = root_misses := !root_misses + 1
                  val equation = split_value depth root
                  val action = action_result equation
                  val entry = {root = root, action = action, equation = equation,
                    stop_weights = stop_certificate action}: root_action
                  val _ = root_records := Termtab.update (request, entry) (!root_records)
                in entry end)
          end

      fun b32 root = power_split 5 root

      fun smoke_split_root () =
        let
          val first = b32 0
          val root_hits_before = !root_hits
          val repeated_root = b32 0
          val _ = if !root_hits = root_hits_before + 1 andalso
              Thm.prop_of (#equation repeated_root) aconv Thm.prop_of (#equation first)
            then () else error "Repeated B32 root lookup did not reuse the published action"
          val hits_before = !hits
          val repeated = split_value 5 0
          val _ = if !hits = hits_before + 1 andalso
              Thm.prop_of repeated aconv Thm.prop_of (#equation first)
            then () else error "Repeated cold-root split request did not hit the exact cache"
          val foreign = {root = 1, action = #action first,
            equation = #equation first, stop_weights = #stop_weights first}: root_action
          val _ = if validate foreign then
            error "Split B32 publication accepted a mismatched root theorem"
            else ()
        in first end

      fun b32_stop242_all () =
        let
          val roots = 0 upto 45
          val root_entries = map b32 roots
          val predicate = Abs ("root", natT,
            @{term comma_crt_mdd_stop_weights_bounded242} $
              (@{term comma_crt_split_weight} $
                (@{term comma_semantic_b1_crt_power_split_action} $ nat 5 $ Bound 0)))
          val nil_rule = Drule.infer_instantiate ctxt
            [(("P", 0), Thm.cterm_of ctxt predicate)]
            (@{thm list_all_Nil_iff} RS @{thm iffD2})
          val nil_proof = nil_rule OF [@{thm TrueI}]
          fun add (root, entry: root_action) (tail, tail_proof) =
            let
              val root_proof = Simplifier.rewrite_rule ctxt
                [Thm.symmetric (#equation entry)] (#stop_weights entry) |> certify
              val rule = Drule.infer_instantiate ctxt
                [(("P", 0), Thm.cterm_of ctxt predicate),
                 (("x", 0), Thm.cterm_of ctxt (nat root)),
                 (("xs", 0), Thm.cterm_of ctxt tail)]
                (@{thm list_all_Cons_iff} RS @{thm iffD2})
              val proof = rule OF [@{thm conjI} OF [root_proof, tail_proof]]
            in (HOLogic.cons_const natT $ nat root $ tail, proof) end
          val indexed_entries = ListPair.zip (roots, root_entries)
          val (_, literal) = fold_rev add indexed_entries
            (HOLogic.mk_list natT [], nil_proof)
          val domain = @{term "upt :: nat => nat => nat list"} $ nat 0 $ nat 46
          val range_eq = Simplifier.full_rewrite
            (Comma_Entry_Arithmetic.natural_context ctxt addsimps @{thms upt_rec})
            (Thm.cterm_of ctxt domain)
          val list_predicate = @{term "list_all :: (nat => bool) => nat list => bool"} $
            predicate
          val aggregate =
            let
              val application = Thm.combination
                (Thm.reflexive (Thm.cterm_of ctxt list_predicate)) range_eq
              val proposition = Thm.combination
                (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) application
            in Thm.equal_elim (Thm.symmetric proposition) literal |> certify end
          val expected = HOLogic.mk_Trueprop (list_predicate $ domain)
          val _ = if Thm.prop_of aggregate aconv expected andalso standalone aggregate then ()
            else error "B32 split Stop242 certificate changed its aggregate claim"
        in {certificate = aggregate, roots = root_entries} end

      fun stats () : stats =
        {lookups = !lookups, hits = !hits, misses = !misses, failures = !failures,
         root_entries_cached = Termtab.size (!root_records), value_nodes = !value_nodes,
         certification = certification ()}

      fun report () =
        let val measured = stats ()
        in "split_crt_lookups=" ^ Int.toString (#lookups measured) ^
          " split_crt_hits=" ^ Int.toString (#hits measured) ^
          " split_crt_misses=" ^ Int.toString (#misses measured) ^
          " split_crt_failures=" ^ Int.toString (#failures measured) ^
          " split_crt_root_entries_cached=" ^
            Int.toString (#root_entries_cached measured) ^
          " split_crt_root_cache_lookups=" ^ Int.toString (!root_lookups) ^
          " split_crt_root_cache_hits=" ^ Int.toString (!root_hits) ^
          " split_crt_root_cache_misses=" ^ Int.toString (!root_misses) ^
          " split_crt_value_nodes=" ^ Int.toString (#value_nodes measured) ^
          " occurrence_cache={" ^ #report occurrence () ^ "}" ^
          " certification_calls=" ^ Int.toString (#calls (#certification measured)) ^
          " certification_failures=" ^ Int.toString (#failed_calls (#certification measured)) ^
          " certification_nodes=" ^ Int.toString (#nodes (#certification measured)) ^
          " certification_ms=" ^ LargeInt.toString (#milliseconds (#certification measured))
        end
    in
      {power_split = power_split, b32 = b32, b32_stop242_all = b32_stop242_all,
       smoke_split_root = smoke_split_root, validate = validate,
       stats = stats, report = report}
    end
end
