(* Context-local, kernel-checked chronological powers over the certified
   continuation graph.  Each recursive state is closed by one instantiated
   successor equation and exact completed child equations; the simplifier
   never replays graph evaluation or recursively expands the power function. *)
signature COMMA_SEMANTIC_GRAPH_POWER_EVALUATOR =
sig
  type evaluated = {result: term, equation: thm}
  type evaluator =
    {evaluate: int -> int -> int -> evaluated,
     stats: unit -> string,
     clear: unit -> unit}
  val make: Proof.context -> evaluator
end

structure Comma_Semantic_Graph_Power_Evaluator:
  COMMA_SEMANTIC_GRAPH_POWER_EVALUATOR =
struct
  type evaluated = {result: term, equation: thm}
  type evaluator =
    {evaluate: int -> int -> int -> evaluated,
     stats: unit -> string,
     clear: unit -> unit}

  val natT = @{typ nat}
  val resultT = @{typ comma_semantic_b1_result}
  fun nat n = HOLogic.mk_number natT n

  fun standalone theorem =
    Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
      null (Thm.tpairs_of theorem) andalso
      not (Term.is_open (Thm.prop_of theorem)) andalso
      null (Term.add_frees (Thm.prop_of theorem) []) andalso
      null (Term.add_vars (Thm.prop_of theorem) [])

  fun object_equation theorem = theorem RS @{thm meta_eq_to_obj_eq}
  fun meta_equation theorem = theorem RS @{thm eq_reflection}

  fun result_of theorem =
    let
      val prop = HOLogic.dest_Trueprop (Thm.prop_of theorem)
      val (_, rhs) = HOLogic.dest_eq prop
    in rhs end

  datatype parsed_result =
      Live_Result of int
    | Stop_Result of int
    | Invalid_Result

  datatype lift_kind = Composed_Live | Absorbed_Stop | Absorbed_Invalid

  fun parse_result result =
    (case strip_comb result of
      (Const (name, _), []) =>
        if name = @{const_name Comma_Semantic_B1_Invalid} then Invalid_Result
        else error "Graph power result has an unknown nullary constructor"
    | (Const (name, _), [payload]) =>
        let
          val (typ, value) =
            (case try HOLogic.dest_number payload of
              SOME pair => pair
            | NONE => error "Graph power result payload is not a numeral")
          val _ = if typ = natT andalso value >= 0 then ()
            else error "Graph power result payload is not a natural"
        in
          if name = @{const_name Comma_Semantic_B1_Live} then
            if value < 46 then Live_Result value
            else error "Graph power Live result is outside the root domain"
          else if name = @{const_name Comma_Semantic_B1_Stop} then
            Stop_Result value
          else error "Graph power result has an unknown unary constructor"
        end
    | _ => error ("Graph power result has a malformed constructor: " ^
        Syntax.string_of_term @{context} result))

  fun check_exact query result theorem =
    let
      val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq (query, result))
      val _ = if standalone theorem andalso Thm.prop_of theorem aconv expected then ()
        else error "Graph power equation is not the exact closed requested state"
      val _ = if fastype_of result = resultT then ()
        else error "Graph power equation has the wrong result type"
      val _ = parse_result result
    in {result = result, equation = theorem}: evaluated end

  fun pow2 n =
    if n < 0 then error "Negative graph power exponent"
    else if n = 0 then 1
    else 2 * pow2 (n - 1)

  fun make ctxt : evaluator =
    let
      val endpoint = Comma_Semantic_Graph_Endpoint_Evaluator.make ctxt
      val graph_power = @{term comma_semantic_graph_action_power}
      val word_then_def = @{thm comma_semantic_word_then_def}
      val stop_lift = @{thm comma_semantic_word_then_stop}
      val invalid_lift = @{thm comma_semantic_word_then_invalid}

      fun apply_lift template arguments premise =
        let
          val variables = Term.add_vars (Thm.prop_of template) []
          fun binding (name, argument) =
            (case filter (fn ((variable_name, _), _) => variable_name = name)
                variables of
              [key as (_, typ)] =>
                if typ = fastype_of argument then (key, Thm.cterm_of ctxt argument)
                else error "Absorbing lift parameter has the wrong type"
            | _ => error "Absorbing lift parameter is missing or ambiguous")
          val instance = Thm.instantiate
            (TVars.empty, Vars.make (map binding arguments)) template
        in Thm.implies_elim instance premise end

      val arithmetic_context = Simplifier.add_simps (@{thms power_0 power_Suc power_one_right
          power_numeral_even power_numeral_odd power2_eq_square}) (Comma_Entry_Arithmetic.natural_context ctxt)
      val step_templates = Vector.tabulate (5, fn previous =>
        Drule.infer_instantiate ctxt
          [(("k", 0), Thm.cterm_of ctxt (nat previous))]
          @{thm comma_semantic_graph_action_power.simps(2)}
        |> Simplifier.full_simplify arithmetic_context)
      val cache = Unsynchronized.ref (Termtab.empty: evaluated Termtab.table)
      val requests = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val equation_steps = Unsynchronized.ref 0
      val stop_lifts = Unsynchronized.ref 0
      val invalid_lifts = Unsynchronized.ref 0
      val rewrite_time = Unsynchronized.ref Time.zeroTime

      fun cache_key k phase root =
        HOLogic.mk_prod (nat k, HOLogic.mk_prod (nat phase, nat root))

      fun graph_query k phase root = graph_power $ nat k $ nat phase $ nat root

      fun timed f =
        let
          val start = Time.now ()
          val result = Exn.capture f ()
          val elapsed = Time.- (Time.now (), start)
          val _ = rewrite_time := Time.+ (!rewrite_time, elapsed)
        in Exn.release result end

      fun instantiate_one_step k phase root =
        if k <= 0 then error "Successor equation requires positive graph power"
        else
          Drule.infer_instantiate ctxt
            [(("phase", 0), Thm.cterm_of ctxt (nat phase)),
             (("root", 0), Thm.cterm_of ctxt (nat root))]
            (Vector.sub (step_templates, k-1))

      fun prove_zero phase root =
        let
          val query = graph_query 0 phase root
          val endpoint_result = #root endpoint phase root
          val rule = Drule.infer_instantiate ctxt
            [(("phase", 0), Thm.cterm_of ctxt (nat phase)),
             (("root", 0), Thm.cterm_of ctxt (nat root))]
            @{thm comma_semantic_graph_action_power.simps(1)}
          val unfold = Conv.rewr_conv (meta_equation rule) (Thm.cterm_of ctxt query)
          val endpoint_meta = meta_equation (#equation endpoint_result)
          val final_meta = Thm.transitive unfold endpoint_meta
          val final = object_equation final_meta
        in check_exact query (#result endpoint_result) final end

      fun prove_successor k phase root =
        let
          val query = graph_query k phase root
          (* Match the single generic Suc equation before simplification.  The
             sterile simplifier below receives only the completed children. *)
          val one_step = instantiate_one_step k phase root
          val unfold = Conv.rewr_conv (meta_equation one_step) (Thm.cterm_of ctxt query)
          val left_result = power (k - 1) phase root
          val left_meta = meta_equation (#equation left_result)
          val left_case = parse_result (#result left_result)
          val previous_function = graph_power $ nat (k - 1)
          val amount = nat (pow2 (k - 1))
          val phase_term = nat phase
          val root_term = nat root
          val (lifted_meta, lift_kind) =
            (case left_case of
              Stop_Result height =>
                let
                  val lifted = apply_lift stop_lift
                    [("amount", amount), ("first", previous_function),
                     ("second", previous_function), ("phase", phase_term),
                     ("root", root_term), ("height", nat height)]
                    (#equation left_result)
                in (meta_equation lifted, Absorbed_Stop) end
            | Invalid_Result =>
                let
                  val lifted = apply_lift invalid_lift
                    [("amount", amount), ("first", previous_function),
                     ("second", previous_function), ("phase", phase_term),
                     ("root", root_term)]
                    (#equation left_result)
                in (meta_equation lifted, Absorbed_Invalid) end
            | Live_Result next_root =>
                let
                  val next_phase = (phase + pow2 (k - 1)) mod 924
                  val right_result = power (k - 1) next_phase next_root
                  val children =
                    [left_meta, meta_equation (#equation right_result)]
                  val rhs_context = Simplifier.add_simps ((word_then_def :: children @
                      @{thms comma_semantic_b1_result.case})) (arithmetic_context)
                  val rhs_step = timed (fn () =>
                    Simplifier.rewrite rhs_context (Thm.rhs_of unfold))
                in (rhs_step, Composed_Live) end)
          val final_meta = Thm.transitive unfold lifted_meta
          val final = object_equation final_meta
          val result = result_of final
          val checked = check_exact query result final
          val _ = (case lift_kind of
              Absorbed_Stop => stop_lifts := !stop_lifts + 1
            | Absorbed_Invalid => invalid_lifts := !invalid_lifts + 1
            | Composed_Live => ())
          val _ = equation_steps := !equation_steps + 1
        in checked end

      and power k phase root =
        let
          val _ = requests := !requests + 1
          val _ =
            if k < 0 orelse k > 5 then
              error "Graph power evaluator supports only exponents 0 through 5"
            else if phase < 0 orelse phase >= 924 then
              error "Graph power phase is outside 0..923"
            else if root < 0 orelse root >= 46 then
              error "Graph power root is outside 0..45"
            else ()
          val key = cache_key k phase root
        in
          (case Termtab.lookup (!cache) key of
            SOME value => (hits := !hits + 1; value)
          | NONE =>
              let
                val _ = misses := !misses + 1
                val result = if k = 0 then prove_zero phase root
                  else prove_successor k phase root
                val checked = check_exact (graph_query k phase root)
                  (#result result) (#equation result)
                val _ = cache := Termtab.update (key, checked) (!cache)
              in checked end)
        end

      fun evaluate k phase root =
        let
          val attempt = Exn.capture (fn () => power k phase root) ()
          val _ = if Exn.is_exn attempt then failures := !failures + 1 else ()
        in Exn.release attempt end

      fun stats () =
        "graph_power_requests=" ^ Int.toString (!requests) ^
        " graph_power_cache_hits=" ^ Int.toString (!hits) ^
        " graph_power_cache_misses=" ^ Int.toString (!misses) ^
        " graph_power_failures=" ^ Int.toString (!failures) ^
        " graph_power_equation_steps=" ^ Int.toString (!equation_steps) ^
        " graph_power_constant_stop_lifts=" ^ Int.toString (!stop_lifts) ^
        " graph_power_invalid_lifts=" ^ Int.toString (!invalid_lifts) ^
        " graph_power_equation_entries=" ^ Int.toString (Termtab.size (!cache)) ^
        " graph_power_rewrite_ms=" ^
          LargeInt.toString (Time.toMilliseconds (!rewrite_time)) ^
        " " ^ #stats endpoint ()

      fun clear () =
        (cache := Termtab.empty;
         requests := 0; hits := 0; misses := 0; failures := 0;
         equation_steps := 0; stop_lifts := 0; invalid_lifts := 0;
         rewrite_time := Time.zeroTime;
         #clear endpoint ())
    in {evaluate = evaluate, stats = stats, clear = clear} end
end

