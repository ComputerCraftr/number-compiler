(* Demand-driven exact B32 point actions from the checked weighted CRT owner.
   Point queries traverse one selected decision-DAG path; they do not rebuild
   the recursive graph power or discover child sources. *)
signature COMMA_SEMANTIC_GRAPH_ACTION_CERTIFICATE =
sig
  type result = {terminal_weight: int, equation: thm}
  type certificate =
    {query: int -> int -> result, convert: cterm -> thm option,
     report: unit -> string, clear: unit -> unit}
  val make: Proof.context -> certificate
end

structure Comma_Semantic_Graph_Action_Certificate:
    COMMA_SEMANTIC_GRAPH_ACTION_CERTIFICATE =
struct
  type result = {terminal_weight: int, equation: thm}
  type certificate =
    {query: int -> int -> result, convert: cterm -> thm option,
     report: unit -> string, clear: unit -> unit}
  val natT = @{typ nat}
  val actionT = @{typ "nat \<times> comma_semantic_b1_crt_dag"}
  val action_listT = HOLogic.listT actionT
  fun nat n = HOLogic.mk_number natT n
  fun closed term = not (Term.is_open term) andalso
    null (Term.add_frees term []) andalso null (Term.add_vars term [])
  fun standalone theorem = Thm.nprems_of theorem = 0 andalso
    null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
    closed (Thm.prop_of theorem)
  fun exact request value theorem =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso closed (Thm.prop_of theorem) andalso
        Thm.prop_of theorem aconv HOLogic.mk_Trueprop (HOLogic.mk_eq (request, value))
    then theorem else error "Weighted B32 point certificate has foreign or open evidence"
  fun number term =
    (case try HOLogic.dest_number term of
      SOME (typ, value) =>
        if typ = natT andalso value >= 0 then IntInf.toInt value
        else error "Weighted B32 point output is not a natural numeral"
    | NONE => error "Weighted B32 point output is not a numeral")

  fun make ctxt : certificate =
    let
      val theory = Proof_Context.theory_of ctxt
      val vector_definition = Thm.transfer theory
        @{thm comma_semantic_graph_b32_weighted_actions_def}
      val vector_refinement = Thm.transfer theory
        @{thm comma_semantic_graph_b32_weighted_actions_refine}
      val vector_length = Thm.transfer theory
        @{thm comma_semantic_graph_b32_weighted_actions_length}
      val vector_shape = Thm.transfer theory
        @{thm comma_semantic_graph_b32_weighted_actions_wellformed}
      val vector_nonterminal = Thm.transfer theory
        @{thm comma_semantic_graph_b32_weighted_actions_nonterminal_zero}
      val stop242 = Thm.transfer theory
        @{thm comma_semantic_graph_predecessor_stop242_checked}
      val authority = [vector_refinement, vector_length, vector_shape,
        vector_nonterminal, stop242]
      val _ = if null (Thm_Deps.all_oracles authority) then ()
        else error "Weighted B32 point owner has an oracle dependency"
      val requests = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val conversions = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      val cache = Unsynchronized.ref (Inttab.empty: result Inttab.table)
      val cache_capacity = 8192
      val cache_order_front = Unsynchronized.ref ([]: int list)
      val cache_order_back = Unsynchronized.ref ([]: int list)
      val evictions = Unsynchronized.ref 0
      fun enqueue key = cache_order_back := key :: !cache_order_back
      fun dequeue () =
        (case !cache_order_front of
          key :: rest => (cache_order_front := rest; key)
        | [] =>
            (case rev (!cache_order_back) of
              key :: rest =>
                (cache_order_front := rest; cache_order_back := []; key)
            | [] => error "Weighted B32 FIFO order lost a cached point key"))
      fun request phase root = @{term comma_semantic_b1_action_power} $
        nat 5 $ nat phase $ nat root
      val selected_action = Const (@{const_name nth},
        action_listT --> natT --> actionT) $
        @{term comma_semantic_graph_b32_weighted_actions}
      val crt_eval = Const (@{const_name comma_semantic_b1_crt_action_eval},
        actionT --> natT --> @{typ comma_semantic_b1_weighted_result})
      val weighted_action_power =
        @{term comma_semantic_b1_weighted_action_power} $ nat 5 $
          @{term comma_semantic_graph_root_weighted_action}
      val graph_power = @{term comma_semantic_graph_action_power} $ nat 5
      val semantic_power = @{term comma_semantic_b1_action_power} $ nat 5
      val list_rules = @{thms nth_Cons_0 nth_Cons_Suc nth_Cons'
        list.map fst_conv snd_conv}
      val point_rules = vector_definition ::
        (@{thms comma_semantic_b1_crt_action_eval_def
          comma_semantic_b1_crt_decode.simps comma_weighted_crt_apply_def
          comma_weighted_crt_eval.simps(1) comma_weighted_crt_eval_selected
          comma_crt_axis_radix_def} @ list_rules)

      fun prove proposition facts tactic =
        let
          val theorem = Goal.prove ctxt [] [] proposition
            (fn {context, ...} => tactic context facts)
        in theorem end

      fun specialize phase root =
        let
          val phase_term = nat phase
          val root_term = nat root
          val selected = selected_action $ root_term
          val evaluated = crt_eval $ selected $ phase_term
          val reduced = Simplifier.rewrite (ctxt addsimps point_rules)
            (Thm.cterm_of ctxt evaluated)
          val result = Thm.term_of (Thm.rhs_of reduced)
          val (terminal, height) =
            (case strip_comb result of
              (Const (name, _), [j, h]) =>
                if name = @{const_name Comma_Semantic_B1_Stop_At}
                then (number j, number h)
                else error "Checked B32 point action did not reach Stop"
            | _ => error "Checked B32 point action returned a malformed result")
          val elapsed_position = 9 * height + terminal
          val _ = if terminal < 9 andalso height <= 26 andalso
              elapsed_position <= 242 then ()
            else error "Checked B32 point result exceeds its certified Stop envelope"
          val point_equation = reduced RS @{thm meta_eq_to_obj_eq}
          val weighted_equation_prop = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (evaluated,
              weighted_action_power $ phase_term $ root_term))
          val weighted_equation = prove weighted_equation_prop
            [vector_refinement]
            (fn context => fn facts =>
              Method.insert_tac context facts 1 THEN
              asm_full_simp_tac (context addsimps list_rules) 1)
          val weighted_point_meta = Thm.transitive
            (Thm.symmetric (weighted_equation RS @{thm eq_reflection}))
            (point_equation RS @{thm eq_reflection})
          val encoded = @{term comma_semantic_b1_weighted_encode} $
            (weighted_action_power $ phase_term $ root_term)
          val stop = @{term Comma_Semantic_B1_Stop} $ nat elapsed_position
          val encoded_equation_prop = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (encoded, stop))
          val weighted_point = weighted_point_meta RS @{thm meta_eq_to_obj_eq}
          val encoded_equation = prove encoded_equation_prop [weighted_point]
            (fn context => fn facts =>
              Method.insert_tac context facts 1 THEN
              asm_full_simp_tac (context addsimps
                @{thms comma_semantic_b1_weighted_encode.simps}) 1)
          val graph_encoding_prop = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (graph_power $ phase_term $ root_term, encoded))
          val graph_encoding = prove graph_encoding_prop
            [@{thm comma_semantic_graph_weighted_power_exact}]
            (fn context => fn facts =>
              resolve_tac context [@{thm sym}] 1 THEN
              resolve_tac context facts 1)
          val graph_equation_meta = Thm.transitive
            (graph_encoding RS @{thm eq_reflection})
            (encoded_equation RS @{thm eq_reflection})
          val graph_equation = graph_equation_meta RS @{thm meta_eq_to_obj_eq}
          val graph_semantic_equation_prop = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (graph_power $ phase_term $ root_term,
              semantic_power $ phase_term $ root_term))
          val graph_semantic_equation = prove graph_semantic_equation_prop
            [@{thm comma_semantic_graph_action_power_refines}]
            (fn context => fn facts =>
              resolve_tac context facts 1 THEN
              simp_tac context 1)
          val semantic_meta = Thm.transitive
            (Thm.symmetric (graph_semantic_equation RS @{thm eq_reflection}))
            (graph_equation RS @{thm eq_reflection})
          val semantic_equation = exact (request phase root) stop
            (semantic_meta RS @{thm meta_eq_to_obj_eq})
          val point_proofs = [point_equation, weighted_equation,
            encoded_equation, graph_equation, graph_semantic_equation,
            semantic_equation]
          val _ = Thm.consolidate point_proofs
          val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
            "Demanded weighted B32 point projection" point_proofs
          val _ = if standalone point_equation andalso
              standalone weighted_equation andalso
              standalone encoded_equation andalso
              standalone graph_equation andalso
              standalone graph_semantic_equation then ()
            else error "Weighted B32 point transport retained assumptions"
        in {terminal_weight=elapsed_position, equation=semantic_equation}: result end

      fun query phase root =
        let
          val _ = requests := !requests + 1
          val started = Time.now ()
          val attempted = Exn.capture (fn () =>
            if phase < 0 orelse 924 <= phase then
              error "B32 point phase is outside 0..923"
            else if root < 0 orelse 46 <= root then
              error "B32 point root is outside 0..45"
            else
              let val key = root * 924 + phase in
                case Inttab.lookup (!cache) key of
                  SOME value =>
                    (ignore (exact (request phase root)
                       (@{term Comma_Semantic_B1_Stop} $ nat (#terminal_weight value))
                       (#equation value));
                     hits := !hits + 1; value)
                | NONE =>
                    let
                      val value = specialize phase root
                      val _ = if Inttab.size (!cache) < cache_capacity then ()
                        else
                          let
                            val expired = dequeue ()
                            val _ = cache := Inttab.delete expired (!cache)
                            val _ = evictions := !evictions + 1
                          in () end
                      val _ = cache := Inttab.update (key, value) (!cache)
                      val _ = enqueue key
                    in value end
              end) ()
          val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), started))
          val _ = if Exn.is_exn attempted then failures := !failures + 1 else ()
        in Exn.release attempted end

      fun parse term =
        if not (closed term) then NONE
        else case strip_comb term of
          (Const (name, _), [power, phase, root]) =>
            if name <> @{const_name comma_semantic_b1_action_power} then NONE
            else (case (try HOLogic.dest_number power, try HOLogic.dest_number phase,
                try HOLogic.dest_number root) of
              (SOME (pT, 5), SOME (rT, r), SOME (iT, i)) =>
                if pT = natT andalso rT = natT andalso iT = natT andalso
                    0 <= r andalso r < 924 andalso 0 <= i andalso i < 46
                then SOME (r, i) else NONE
            | _ => NONE)
        | _ => NONE
      fun convert requested =
        let val _ = conversions := !conversions + 1 in
          if not (Context.subthy (theory, Thm.theory_of_cterm requested)) then NONE
          else (case parse (Thm.term_of requested) of
            NONE => NONE
          | SOME (phase, root) =>
              SOME (#equation (query phase root) RS @{thm eq_reflection}))
        end
      fun report () =
        "weighted_b32_point_requests=" ^ Int.toString (!requests) ^
        " weighted_b32_point_cache_hits=" ^ Int.toString (!hits) ^
        " weighted_b32_point_failures=" ^ Int.toString (!failures) ^
        " weighted_b32_point_conversions=" ^ Int.toString (!conversions) ^
        " weighted_b32_point_entries=" ^ Int.toString (Inttab.size (!cache)) ^
        " weighted_b32_point_cache_evictions=" ^ Int.toString (!evictions) ^
        " weighted_b32_point_query_ms=" ^
          LargeInt.toString (Time.toMilliseconds (!elapsed))
      fun clear () =
        (cache := Inttab.empty; requests := 0; hits := 0; failures := 0;
         conversions := 0; elapsed := Time.zeroTime;
         cache_order_front := []; cache_order_back := []; evictions := 0)
    in {query=query, convert=convert, report=report, clear=clear}: certificate end
end
