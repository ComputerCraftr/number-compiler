(* Context-local, kernel-checked endpoint evaluation over the published
   continuation graph.  This evaluator consumes the graph owner's exact
   node/root lookup equations; it never reconstructs the source catalogue or
   materializes a second node table. *)
signature COMMA_SEMANTIC_GRAPH_ENDPOINT_EVALUATOR =
sig
  type evaluated = {result: term, equation: thm}
  type evaluator =
    {root: int -> int -> evaluated, stats: unit -> string, clear: unit -> unit}
  val make: Proof.context -> evaluator
end

structure Comma_Semantic_Graph_Endpoint_Evaluator:
    COMMA_SEMANTIC_GRAPH_ENDPOINT_EVALUATOR =
struct
  type evaluated = {result: term, equation: thm}
  type evaluator =
    {root: int -> int -> evaluated, stats: unit -> string, clear: unit -> unit}
  datatype parsed_edge = Parsed_Goto of int | Parsed_Live of int |
    Parsed_Stop of int | Parsed_Invalid

  val natT = @{typ nat}
  val nodeT = @{typ comma_semantic_b1_node}
  val edgeT = @{typ comma_semantic_b1_edge}
  val resultT = @{typ comma_semantic_b1_result}
  val node_of = @{term comma_semantic_b1_node_of}
  val nodes = @{term comma_semantic_graph_nodes}
  val root_ids = @{term comma_semantic_graph_root_ids}

  fun nat n = HOLogic.mk_number natT n

  fun dest_nat ctxt term =
    (case try HOLogic.dest_number term of
      SOME (typ, value) =>
        if typ = natT andalso value >= 0 then value
        else error "Graph endpoint numeral is not a natural"
    | NONE => error ("Graph endpoint equation did not produce a natural numeral: " ^
        Syntax.string_of_term ctxt term))

  fun closed theorem =
    not (Term.is_open (Thm.prop_of theorem)) andalso
      null (Term.add_frees (Thm.prop_of theorem) []) andalso
      null (Term.add_vars (Thm.prop_of theorem) [])

  fun standalone theorem = Thm.nprems_of theorem = 0 andalso
    null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
    closed theorem

  fun checked_object_equation expected theorem message =
    if standalone theorem andalso Thm.prop_of theorem aconv expected then theorem
    else error message

  fun object_equation meta = meta RS @{thm meta_eq_to_obj_eq}

  fun dest_option ctxt term =
    (case strip_comb term of
      (Const (name, _), [value]) =>
        if name = @{const_name Some} then SOME value
        else error "Graph lookup equation did not produce an option constructor"
    | (Const (name, _), []) =>
        if name = @{const_name None} then NONE
        else error "Graph lookup equation did not produce an option constructor"
    | _ => error ("Graph lookup equation left an unreduced option: " ^
        Syntax.string_of_term ctxt term))

  fun dest_edge ctxt term =
    (case strip_comb term of
      (Const (name, _), [value]) =>
        if name = @{const_name Comma_Semantic_B1_Goto} then Parsed_Goto (dest_nat ctxt value)
        else if name = @{const_name Comma_Semantic_B1_Live_Edge} then
          Parsed_Live (dest_nat ctxt value)
        else if name = @{const_name Comma_Semantic_B1_Stop_Edge} then
          Parsed_Stop (dest_nat ctxt value)
        else error "Unknown graph edge constructor"
    | (Const (name, _), []) =>
        if name = @{const_name Comma_Semantic_B1_Invalid_Edge} then Parsed_Invalid
        else error "Unknown nullary graph edge constructor"
    | _ => error "Malformed graph edge in checked lookup equation")

  fun check_result ctxt term =
    (case strip_comb term of
      (Const (name, _), []) =>
        if name = @{const_name Comma_Semantic_B1_Invalid} then ()
        else error "Graph endpoint result is not a B1 result constructor"
    | (Const (name, _), [payload]) =>
        if name = @{const_name Comma_Semantic_B1_Live} then
          if dest_nat ctxt payload < 46 then ()
          else error "Graph endpoint live result is outside the root domain"
        else if name = @{const_name Comma_Semantic_B1_Stop} then
          if dest_nat ctxt payload <= 8 then ()
          else error "Graph endpoint stop result is outside the stop domain"
        else error "Graph endpoint result is not a B1 result constructor"
    | _ => error "Malformed graph endpoint result constructor")

  fun make ctxt : evaluator =
    let
      val node_of_const = Const (@{const_name comma_semantic_b1_node_of},
        @{typ "comma_semantic_b1_node list => nat => comma_semantic_b1_node option"})
      val node_lookup_facts = @{thms comma_semantic_graph_node_lookup_equations}

      fun node_lookup_entry theorem =
        let
          val prop = HOLogic.dest_Trueprop (Thm.prop_of theorem)
          val (lhs, rhs) = HOLogic.dest_eq prop
          val (head, args) = strip_comb lhs
          val _ = if head = node_of_const andalso length args = 2 andalso
              hd args aconv nodes
            then () else error "Published graph node lookup has a foreign table key"
          val cid = dest_nat ctxt (List.nth (args, 1))
          val node = (case dest_option ctxt rhs of
            SOME value => value
          | NONE => error "Published graph node lookup unexpectedly produced None")
          val _ = if fastype_of node = nodeT andalso standalone theorem then ()
            else error "Published graph node lookup is open or has the wrong node type"
          val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (node_of $ nodes $ nat cid,
             Const (@{const_name Some}, nodeT --> Type (@{type_name option}, [nodeT])) $ node))
          val _ = if Thm.prop_of theorem aconv expected then ()
            else error "Published graph node lookup is not an exact closed row equation"
        in (cid, theorem) end

      val node_entries = map node_lookup_entry node_lookup_facts
      val node_table = fold (fn (cid, theorem) => fn table =>
        if Inttab.defined table cid then
          error "Published graph node lookup contains a duplicate CID"
        else Inttab.update (cid, theorem) table) node_entries Inttab.empty
      val node_count = length node_entries
      val expected_cids = 0 upto (node_count - 1)
      val actual_cids = Inttab.keys node_table
      val _ = if node_count > 0 andalso actual_cids = expected_cids then ()
        else error "Published graph node lookup facts are not a complete dense CID range"

      val root_ids_def = @{thm comma_semantic_graph_root_ids_def}
      val _ = if standalone root_ids_def andalso
          Thm.term_of (Thm.lhs_of root_ids_def) aconv root_ids then ()
        else error "Published root ID theorem is not the closed root-list definition"
      val root_id_values =
        map (dest_nat ctxt) (HOLogic.dest_list (Thm.term_of (Thm.rhs_of root_ids_def)))
      val _ = if length root_id_values = 46 andalso
          List.all (fn cid => Inttab.defined node_table cid) root_id_values then ()
        else error "Published root IDs do not resolve to the complete root domain"
      val root_id_context =
        Comma_Entry_Arithmetic.natural_context ctxt addsimps
          (root_ids_def :: @{thms list.map nth_Cons_0 nth_Cons_Suc nth_Cons'})
      val root_id_conversion = Simplifier.rewrite root_id_context

      val apply_context_base =
        Comma_Entry_Arithmetic.natural_context ctxt addsimps
          (@{thms comma_semantic_b1_graph_apply_def
              comma_semantic_b1_node_from_data_def
              comma_semantic_b1_node.select_convs
              option.case list.size(3) list.size(4)
              prod.case fst_conv snd_conv
              nth_Cons_0 nth_Cons_Suc nth_Cons'})
      val node_period_const = Const (@{const_name comma_semantic_b1_node_period},
        nodeT --> natT)
      type node_metadata =
        {period: int, periodic_rule: thm, apply_context: Proof.context}
      val period_metadata_ms = Unsynchronized.ref Time.zeroTime
      fun node_metadata cid lookup =
        let
          val context = apply_context_base addsimps [lookup]
          val prop = HOLogic.dest_Trueprop (Thm.prop_of lookup)
          val (_, lookup_rhs) = HOLogic.dest_eq prop
          val node = (case dest_option ctxt lookup_rhs of
            SOME value => value
          | NONE => error "Graph node metadata unexpectedly resolved to None")
          val query = node_period_const $ node
          val started = Time.now ()
          val attempt = Exn.capture (fn () => Simplifier.rewrite context
            (Thm.cterm_of context query)) ()
          val _ = period_metadata_ms := Time.+ (!period_metadata_ms,
            Time.- (Time.now (), started))
          val equation = Exn.release attempt
          val lhs = Thm.term_of (Thm.lhs_of equation)
          val rhs = Thm.term_of (Thm.rhs_of equation)
          val period = dest_nat ctxt rhs
          val _ = if standalone equation andalso lhs aconv query andalso
              rhs aconv nat period andalso period > 0 andalso period <= 924 andalso
              924 mod period = 0
            then () else error "Authenticated graph node has an invalid local period"
          val period_fact = equation RS @{thm meta_eq_to_obj_eq}
          val periodic_rule = @{thm comma_semantic_graph_apply_local_period}
            OF [lookup, period_fact]
        in {period=period, periodic_rule=periodic_rule,
            apply_context=context}: node_metadata end
      val node_metadata_table = Unsynchronized.ref
        (Inttab.empty: node_metadata Inttab.table)
      fun demanded_node_metadata cid =
        (case Inttab.lookup (!node_metadata_table) cid of
          SOME value => value
        | NONE =>
            let
              val lookup = (case Inttab.lookup node_table cid of
                SOME theorem => theorem
              | NONE => error "Graph apply metadata has no published node row")
              val value = node_metadata cid lookup
              val _ = node_metadata_table :=
                Inttab.update (cid, value) (!node_metadata_table)
            in value end)

      val numeric_fact_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      fun numeric_fact proposition =
        (case Termtab.lookup (!numeric_fact_cache) proposition of
          SOME theorem => theorem
        | NONE =>
            let
              val theorem = Goal.prove ctxt [] [] proposition
                (fn {context, ...} =>
                  simp_tac (Comma_Entry_Arithmetic.natural_context context) 1)
              val _ = checked_object_equation proposition theorem
                "Graph numeric bound is not a closed exact fact"
              val _ = numeric_fact_cache :=
                Termtab.update (proposition, theorem) (!numeric_fact_cache)
            in theorem end)

      val eval_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val apply_cache = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val root_cache = Unsynchronized.ref (Termtab.empty: evaluated Termtab.table)
      val requests = Unsynchronized.ref 0
      val root_hits = Unsynchronized.ref 0
      val root_misses = Unsynchronized.ref 0
      val eval_hits = Unsynchronized.ref 0
      val eval_misses = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val node_steps = Unsynchronized.ref 0
      val rewrite_ms = Unsynchronized.ref Time.zeroTime
      val apply_requests = Unsynchronized.ref 0
      val apply_hits = Unsynchronized.ref 0
      val apply_misses = Unsynchronized.ref 0
      val apply_period_transports = Unsynchronized.ref 0
      val apply_rewrite_ms = Unsynchronized.ref Time.zeroTime
      val apply_transport_ms = Unsynchronized.ref Time.zeroTime

      fun timed f =
        let
          val started = Time.now ()
          val attempt = Exn.capture f ()
          val elapsed = Time.- (Time.now (), started)
          val _ = rewrite_ms := Time.+ (!rewrite_ms, elapsed)
        in Exn.release attempt end

      fun cache_key left right = HOLogic.mk_prod (nat left, nat right)

      type root_metadata = {cid: int, id_equation: thm}
      val root_metadata_cache = Unsynchronized.ref
        (Inttab.empty: root_metadata Inttab.table)

      fun root_metadata root =
        (case Inttab.lookup (!root_metadata_cache) root of
          SOME metadata => metadata
        | NONE =>
            let
              val root_index = nat root
              val root_query = Const (@{const_name nth},
                HOLogic.listT natT --> natT --> natT) $ root_ids $ root_index
              val equation = timed (fn () => root_id_conversion
                (Thm.cterm_of root_id_context root_query))
              val cid_term = Thm.term_of (Thm.rhs_of equation)
              val cid = dest_nat ctxt cid_term
              val expected_rhs = nat cid
              val _ = if Thm.term_of (Thm.lhs_of equation) aconv root_query andalso
                  Thm.term_of (Thm.rhs_of equation) aconv expected_rhs andalso
                  standalone equation andalso Inttab.defined node_table cid
                then () else error "Graph root index has no checked published node ID"
              val metadata = {cid = cid, id_equation = equation}: root_metadata
              val _ = root_metadata_cache :=
                Inttab.update (root, metadata) (!root_metadata_cache)
            in metadata end)

      fun apply_equation cid phase =
        let
          val _ = apply_requests := !apply_requests + 1
          val metadata = demanded_node_metadata cid
          val local_phase = phase mod #period metadata
          val local_query = @{term comma_semantic_b1_graph_apply} $
            nodes $ nat cid $ nat local_phase
          val local_key = cache_key cid local_phase
          val local_equation =
            (case Termtab.lookup (!apply_cache) local_key of
              SOME theorem =>
                let
                  val _ = if standalone theorem andalso
                      Thm.term_of (Thm.lhs_of theorem) aconv local_query
                    then () else error "Cached local graph action has a foreign key"
                  val _ = apply_hits := !apply_hits + 1
                in theorem end
            | NONE =>
                let
                  val _ = apply_misses := !apply_misses + 1
                  val started = Time.now ()
                  val attempt = Exn.capture (fn () => timed (fn () =>
                    Simplifier.rewrite (#apply_context metadata)
                      (Thm.cterm_of (#apply_context metadata) local_query))) ()
                  val elapsed = Time.- (Time.now (), started)
                  val _ = apply_rewrite_ms := Time.+ (!apply_rewrite_ms, elapsed)
                  val theorem = Exn.release attempt
                  val lhs = Thm.term_of (Thm.lhs_of theorem)
                  val rhs = Thm.term_of (Thm.rhs_of theorem)
                  val _ = if standalone theorem andalso lhs aconv local_query andalso
                      fastype_of rhs = Type (@{type_name option}, [edgeT])
                    then () else error "Local graph action reduction changed its exact request"
                  val _ = apply_cache := Termtab.update
                    (local_key, theorem) (!apply_cache)
                in theorem end)
          val query = @{term comma_semantic_b1_graph_apply} $ nodes $ nat cid $ nat phase
          val equation =
            if phase = local_phase then local_equation
            else
              let
                val started = Time.now ()
                val _ = apply_period_transports := !apply_period_transports + 1
                (* Exported theory parameters are schematic variables, not
                   explicit Pure quantifiers. Instantiate the sole remaining
                   clock variable without assuming its generated index. *)
                val template = #periodic_rule metadata
                val clock_variable =
                  (case Term.add_vars (Thm.prop_of template) [] of
                    [key as (("clock", _), typ)] =>
                      if typ = natT then key
                      else error "Local-period clock has the wrong type"
                  | _ => error "Local-period rule has unexpected open parameters")
                val periodic = Thm.instantiate (TVars.empty,
                  Vars.make [(clock_variable, Thm.cterm_of ctxt (nat phase))]) template
                val periodic_prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
                  (query, @{term comma_semantic_b1_graph_apply} $ nodes $ nat cid $
                    HOLogic.mk_binop @{const_name modulo}
                      (nat phase, nat (#period metadata))))
                val _ = if standalone periodic andalso
                    Thm.prop_of periodic aconv periodic_prop
                  then () else error "Local-period theorem changed the full-phase action"
                val periodic_meta = periodic RS @{thm eq_reflection}
                val reduced_rhs = Simplifier.rewrite
                  (Comma_Entry_Arithmetic.natural_context ctxt)
                  (Thm.rhs_of periodic_meta)
                val reduced_query = @{term comma_semantic_b1_graph_apply} $
                  nodes $ nat cid $ nat local_phase
                val _ = if Thm.term_of (Thm.lhs_of reduced_rhs) aconv
                      Thm.term_of (Thm.rhs_of periodic_meta) andalso
                    Thm.term_of (Thm.rhs_of reduced_rhs) aconv reduced_query
                  then () else error "Local-period reduction did not select the cached phase"
                val transport = Thm.transitive periodic_meta reduced_rhs
                val final = Thm.transitive transport local_equation
                val elapsed = Time.- (Time.now (), started)
                val _ = apply_transport_ms := Time.+ (!apply_transport_ms, elapsed)
              in final end
          val lhs = Thm.term_of (Thm.lhs_of equation)
          val final_rhs = Thm.term_of (Thm.rhs_of equation)
          val _ = if standalone equation andalso lhs aconv query andalso
              fastype_of final_rhs = Type (@{type_name option}, [edgeT])
            then () else error "Graph apply reduction changed the requested CID or phase"
        in (equation, final_rhs) end

      fun none_result cid phase applied =
        let
          val query = @{term comma_semantic_b1_graph_eval} $ nodes $ nat cid $ nat phase
          val none = Const (@{const_name None}, Type (@{type_name option}, [resultT]))
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq (query, none))
          val theorem = Goal.prove ctxt [] [] proposition
            (fn {context, ...} =>
              simp_tac (Comma_Entry_Arithmetic.natural_context context addsimps
                (@{thms comma_semantic_b1_graph_eval.simps} @
                  [object_equation applied])) 1)
        in checked_object_equation proposition theorem
          "Graph evaluator None branch did not close exactly" end

      fun eval cid phase =
        let
          val key = cache_key cid phase
        in
          (case Termtab.lookup (!eval_cache) key of
            SOME theorem => (eval_hits := !eval_hits + 1; theorem)
          | NONE =>
              let
                val _ = eval_misses := !eval_misses + 1
                val _ = node_steps := !node_steps + 1
                val (applied_meta, applied_rhs) = apply_equation cid phase
                val applied = object_equation applied_meta
                val result =
                  (case dest_option ctxt applied_rhs of
                    NONE => none_result cid phase applied_meta
                  | SOME edge =>
                      (case dest_edge ctxt edge of
                        Parsed_Goto child =>
                          if child < cid then
                            let
                              val child_eval = eval child phase
                              val lower_prop = HOLogic.mk_Trueprop
                                (@{term "less :: nat => nat => bool"} $
                                  nat child $ nat cid)
                              val lower = numeric_fact lower_prop
                              val step = @{thm comma_semantic_b1_graph_eval_apply_goto}
                                OF [applied, lower]
                              val composed = Thm.transitive
                                (step RS @{thm eq_reflection})
                                (child_eval RS @{thm eq_reflection})
                            in composed RS @{thm meta_eq_to_obj_eq} end
                          else none_result cid phase applied_meta
                      | Parsed_Live root =>
                          if root < 46 then
                            let
                              val bound_prop = HOLogic.mk_Trueprop
                                (@{term "less :: nat => nat => bool"} $
                                  nat root $ nat 46)
                              val bound = numeric_fact bound_prop
                            in @{thm comma_semantic_b1_graph_eval_apply_live}
                              OF [applied, bound] end
                          else none_result cid phase applied_meta
                      | Parsed_Stop height =>
                          if height <= 8 then
                            let
                              val bound_prop = HOLogic.mk_Trueprop
                                (@{term "less_eq :: nat => nat => bool"} $
                                  nat height $ nat 8)
                              val bound = numeric_fact bound_prop
                            in @{thm comma_semantic_b1_graph_eval_apply_stop}
                              OF [applied, bound] end
                          else none_result cid phase applied_meta
                      | Parsed_Invalid =>
                          @{thm comma_semantic_b1_graph_eval_apply_invalid} OF [applied]))
                val expected_query = @{term comma_semantic_b1_graph_eval} $
                  nodes $ nat cid $ nat phase
                val (_, result_rhs) = HOLogic.dest_eq
                  (HOLogic.dest_Trueprop (Thm.prop_of result))
                val expected_prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
                  (expected_query, result_rhs))
                val _ = checked_object_equation expected_prop result
                  "Graph endpoint step produced a foreign or open equation"
                val _ = eval_cache := Termtab.update (key, result) (!eval_cache)
              in result end)
        end

      fun root_equation phase root =
        let
          val query = @{term comma_semantic_graph_root_action} $ nat phase $ nat root
          val key = cache_key root phase
        in
          (case Termtab.lookup (!root_cache) key of
            SOME evaluated => (root_hits := !root_hits + 1; evaluated)
          | NONE =>
              let
                val _ = root_misses := !root_misses + 1
                val {cid, id_equation} = root_metadata root
                val eval_equation = eval cid phase
                val context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
                  ([@{thm comma_semantic_graph_root_action_def}, id_equation,
                   eval_equation] @ @{thms option.case})
                val meta = timed (fn () => Simplifier.rewrite context
                  (Thm.cterm_of context query))
                val result = Thm.term_of (Thm.rhs_of meta)
                val _ = if fastype_of result = resultT then ()
                  else error "Graph root evaluator returned a non-B1 result"
                val theorem = object_equation meta
                val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq (query, result))
                val checked = checked_object_equation expected theorem
                  "Graph root evaluator did not prove its exact closed query"
                val _ = check_result ctxt result
                val evaluated = {result = result, equation = checked}: evaluated
                val _ = root_cache := Termtab.update (key, evaluated) (!root_cache)
              in evaluated end)
        end

      fun root phase root_index =
        let
          val _ = requests := !requests + 1
          val attempt = Exn.capture (fn () =>
            if phase < 0 orelse phase >= 924 then
              error "Graph endpoint phase is outside 0..923"
            else if root_index < 0 orelse root_index >= 46 then
              error "Graph endpoint root is outside 0..45"
            else root_equation phase root_index) ()
          val _ = if Exn.is_exn attempt then failures := !failures + 1 else ()
        in Exn.release attempt end

      fun stats () =
        "graph_endpoint_requests=" ^ Int.toString (!requests) ^
        " graph_endpoint_root_hits=" ^ Int.toString (!root_hits) ^
        " graph_endpoint_root_misses=" ^ Int.toString (!root_misses) ^
        " graph_endpoint_eval_hits=" ^ Int.toString (!eval_hits) ^
        " graph_endpoint_eval_misses=" ^ Int.toString (!eval_misses) ^
        " graph_endpoint_failures=" ^ Int.toString (!failures) ^
        " graph_endpoint_node_steps=" ^ Int.toString (!node_steps) ^
        " graph_endpoint_apply_requests=" ^ Int.toString (!apply_requests) ^
        " graph_endpoint_apply_local_hits=" ^ Int.toString (!apply_hits) ^
        " graph_endpoint_apply_local_misses=" ^ Int.toString (!apply_misses) ^
        " graph_endpoint_apply_phase_reductions_avoided=" ^
          Int.toString (!apply_requests - !apply_misses) ^
        " graph_endpoint_apply_period_transports=" ^
          Int.toString (!apply_period_transports) ^
        " graph_endpoint_apply_entries=" ^ Int.toString (Termtab.size (!apply_cache)) ^
        " graph_endpoint_node_period_entries=" ^ Int.toString (Inttab.size (!node_metadata_table)) ^
        " graph_endpoint_node_period_ms=" ^ LargeInt.toString (Time.toMilliseconds (!period_metadata_ms)) ^
        " graph_endpoint_apply_rewrite_ms=" ^ LargeInt.toString (Time.toMilliseconds (!apply_rewrite_ms)) ^
        " graph_endpoint_apply_transport_ms=" ^ LargeInt.toString (Time.toMilliseconds (!apply_transport_ms)) ^
        " graph_endpoint_node_entries=" ^ Int.toString (Termtab.size (!eval_cache)) ^
        " graph_endpoint_root_metadata_entries=" ^ Int.toString (Inttab.size (!root_metadata_cache)) ^
        " graph_endpoint_numeric_fact_entries=" ^ Int.toString (Termtab.size (!numeric_fact_cache)) ^
        " graph_endpoint_root_entries=" ^ Int.toString (Termtab.size (!root_cache)) ^
        " graph_endpoint_rewrite_ms=" ^ LargeInt.toString (Time.toMilliseconds (!rewrite_ms))

      fun clear () =
        (eval_cache := Termtab.empty;
         apply_cache := Termtab.empty;
         root_cache := Termtab.empty;
         root_metadata_cache := Inttab.empty;
         node_metadata_table := Inttab.empty;
         numeric_fact_cache := Termtab.empty;
         requests := 0; root_hits := 0; root_misses := 0;
         eval_hits := 0; eval_misses := 0; failures := 0;
         node_steps := 0; rewrite_ms := Time.zeroTime;
         apply_requests := 0; apply_hits := 0; apply_misses := 0;
         apply_period_transports := 0; apply_rewrite_ms := Time.zeroTime;
         apply_transport_ms := Time.zeroTime; period_metadata_ms := Time.zeroTime)
    in {root = root, stats = stats, clear = clear} end
end
