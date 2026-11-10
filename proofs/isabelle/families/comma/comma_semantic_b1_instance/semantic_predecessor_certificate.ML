(* Build a compact, source-authenticated predecessor certificate for the concrete
   continuation graph.  No scalar rank or phase table is constructed;
   the checked transfer and bounded-reachability theorems supply authority. *)
signature COMMA_SEMANTIC_PREDECESSOR_CERTIFICATE =
sig
  val publish: local_theory -> local_theory
end

structure Comma_Semantic_Predecessor_Certificate:
  COMMA_SEMANTIC_PREDECESSOR_CERTIFICATE =
struct
  datatype edge = Goto of int | Live of int | Stop of int | Invalid
  type node = {period: int, actions: edge Vector.vector,
    action_terms: term Vector.vector, node_term: term,
    lookup: thm, period_equation: thm, actions_equation: thm}
  val natT = @{typ nat}
  val nodeT = @{typ comma_semantic_b1_node}
  val edgeT = @{typ comma_semantic_b1_edge}
  val node_of = @{term comma_semantic_b1_node_of}
  val nodes = @{term comma_semantic_graph_nodes}
  val root_ids = @{term comma_semantic_graph_root_ids}
  val period_selector = Const (@{const_name comma_semantic_b1_node_period},
    nodeT --> natT)
  val actions_selector = Const (@{const_name comma_semantic_b1_node_actions},
    nodeT --> HOLogic.listT edgeT)

  fun nat n = HOLogic.mk_number natT n

  fun note name theorem lthy =
    snd (Local_Theory.note ((Binding.name name, []), [theorem]) lthy)

  fun closed theorem =
    not (Term.is_open (Thm.prop_of theorem)) andalso
      null (Term.add_frees (Thm.prop_of theorem) []) andalso
      null (Term.add_vars (Thm.prop_of theorem) [])

  fun standalone theorem = Thm.nprems_of theorem = 0 andalso
    null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
    closed theorem

  fun exact_rule proposition theorem =
    if Thm.prop_of theorem aconv proposition andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
        closed theorem andalso null (Thm_Deps.all_oracles [theorem]) then theorem
    else error "Predecessor proof did not produce the exact closed rule"

  fun exact proposition theorem =
    if standalone theorem andalso Thm.concl_of theorem aconv proposition then theorem
    else error "Predecessor proof did not produce the exact closed proposition"

  fun numeral ctxt term =
    (case try HOLogic.dest_number term of
      SOME (typ, value) =>
        if typ = natT andalso value >= 0 then IntInf.toInt value
        else error "Predecessor graph contains a non-natural numeral"
    | NONE => error ("Predecessor graph contains a non-numeral: " ^
        Syntax.string_of_term ctxt term))

  fun dest_some ctxt term =
    (case strip_comb term of
      (Const (name, _), [value]) =>
        if name = @{const_name Some} then value
        else error "Predecessor node lookup produced a non-Some option"
    | _ => error ("Predecessor node lookup is not an option constructor: " ^
        Syntax.string_of_term ctxt term))

  fun dest_edge ctxt term =
    (case strip_comb term of
      (Const (name, _), [value]) =>
        if name = @{const_name Comma_Semantic_B1_Goto} then Goto (numeral ctxt value)
        else if name = @{const_name Comma_Semantic_B1_Live_Edge} then
          Live (numeral ctxt value)
        else if name = @{const_name Comma_Semantic_B1_Stop_Edge} then
          Stop (numeral ctxt value)
        else error "Predecessor graph contains an unknown edge constructor"
    | (Const (name, _), []) =>
        if name = @{const_name Comma_Semantic_B1_Invalid_Edge} then Invalid
        else error "Predecessor graph contains an unknown nullary edge"
    | _ => error "Predecessor graph contains a malformed edge")

  fun validate_node_fact ctxt theorem =
    let
      val proposition = HOLogic.dest_Trueprop (Thm.concl_of theorem)
      val (lhs, rhs) = HOLogic.dest_eq proposition
      val (head, args) = strip_comb lhs
      val _ = if head = node_of andalso length args = 2 andalso
          hd args aconv nodes then ()
        else error "Predecessor node lookup is for a foreign graph table"
      val cid = numeral ctxt (List.nth (args, 1))
      val node = dest_some ctxt rhs
      val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (node_of $ nodes $ nat cid,
          Const (@{const_name Some}, nodeT --> Type (@{type_name option}, [nodeT])) $ node))
      val _ = if standalone theorem andalso Thm.prop_of theorem aconv expected andalso
          fastype_of node = nodeT then ()
        else error "Predecessor node lookup is not a closed exact equation"
    in (cid, node, theorem) end

  fun list_all_term element_type predicate values =
    Const (@{const_name list_all},
      (element_type --> HOLogic.boolT) --> HOLogic.listT element_type --> HOLogic.boolT) $
      predicate $ values

  fun parse_graph ctxt =
    let
      val facts = @{thms comma_semantic_graph_node_lookup_equations}
      val entries = map (validate_node_fact ctxt) facts
      val theorem_table = fold (fn (cid, _, theorem) => fn table =>
        if Inttab.defined table cid then
          error "Predecessor graph node lookups contain a duplicate CID"
        else Inttab.update (cid, theorem) table) entries Inttab.empty
      val count = length entries
      val _ = if count > 0 andalso Inttab.keys theorem_table = (0 upto (count - 1))
        then () else error "Predecessor graph node IDs are not dense"
      val node_context = Simplifier.add_simps ((@{thms comma_semantic_b1_node_from_data_def
            comma_semantic_b1_node.select_convs fst_conv snd_conv
            list.map upt_rec nth_Cons_0 nth_Cons_Suc nth_Cons'})) (Comma_Entry_Arithmetic.natural_context ctxt)
      fun selected selector constant =
        let
          val query = selector $ constant
          val theorem = Simplifier.rewrite node_context (Thm.cterm_of node_context query)
          val _ = if standalone theorem andalso
              Thm.term_of (Thm.lhs_of theorem) aconv query then ()
            else error "Predecessor node selector lost its exact closed request"
        in theorem end
      fun parse_entry (cid, node, lookup) =
        let
          val period_equation = selected period_selector node
          val actions_equation = selected actions_selector node
          val period = numeral ctxt (Thm.term_of (Thm.rhs_of period_equation))
          val actions_term = Thm.term_of (Thm.rhs_of actions_equation)
          val action_terms = Vector.fromList (HOLogic.dest_list actions_term)
          val actions = Vector.map (dest_edge ctxt) action_terms
          val _ = if standalone period_equation andalso
              Thm.term_of (Thm.lhs_of period_equation) aconv (period_selector $ node) andalso
              Thm.term_of (Thm.rhs_of period_equation) aconv (nat period) then ()
            else error "Predecessor period selector equation was not exact"
          val _ = if standalone actions_equation andalso
              Thm.term_of (Thm.lhs_of actions_equation) aconv (actions_selector $ node) andalso
              Thm.term_of (Thm.rhs_of actions_equation) aconv actions_term then ()
            else error "Predecessor action selector equation was not exact"
          val _ = if 0 < period andalso period <= 924 andalso 924 mod period = 0 andalso
              Vector.length actions = period then ()
            else error "Predecessor graph node has an unsupported period or row length"
          val _ = Vector.app (fn action =>
            case action of
              Goto child => if child < cid then ()
                else error "Predecessor graph has a non-decreasing Goto edge"
            | Live root => if root < 46 then ()
                else error "Predecessor graph Live edge is outside the root domain"
            | Stop height => if height <= 8 then ()
                else error "Predecessor graph Stop edge is outside the terminal domain"
            | Invalid => ()) actions
        in (cid, {period=period, actions=actions, action_terms=action_terms,
          node_term=node, lookup=lookup, period_equation=period_equation,
          actions_equation=actions_equation}: node) end
      val node_entries = map parse_entry entries
      val node_table = fold (fn (cid, node) => Inttab.update (cid, node))
        node_entries Inttab.empty
      val root_definition = @{thm comma_semantic_graph_root_ids_def}
      val _ = if standalone root_definition andalso
          Thm.term_of (Thm.lhs_of root_definition) aconv root_ids then ()
        else error "Predecessor root IDs are not the exact published list definition"
      val roots = map (numeral ctxt)
        (HOLogic.dest_list (Thm.term_of (Thm.rhs_of root_definition)))
      val _ = if length roots = 46 andalso
          List.all (fn cid => Inttab.defined node_table cid) roots then ()
        else error "Predecessor root IDs do not cover the 46-root graph domain"
      val _ = if null (Thm_Deps.all_oracles
          ([@{thm comma_semantic_graph_valid_checked}, root_definition] @ facts)) then ()
        else error "Predecessor source graph facts depend on an oracle"
    in (node_table, roots, root_definition) end

  fun parse_initial_source_ids ctxt node_table =
    let
      val source_ids = @{term comma_semantic_graph_initial_source_ids}
      val definition = @{thm comma_semantic_graph_initial_source_ids_def}
      val binding = @{thm comma_semantic_graph_initial_source_binding_exact}
      val _ = if standalone definition andalso
          Thm.term_of (Thm.lhs_of definition) aconv source_ids then ()
        else error "Initial source CID vector is not its closed published definition"
      val ids = map (numeral ctxt) (HOLogic.dest_list (Thm.term_of (Thm.rhs_of definition)))
      val _ = if length ids = 16 andalso
          List.all (fn cid => Inttab.defined node_table cid) ids then ()
        else error "The authenticated initial source vector has an invalid extent or CID"
      val _ = if standalone binding andalso null (Thm_Deps.all_oracles [definition, binding])
        then () else error "Initial source CID bindings are not native closed evidence"
    in (ids, definition, binding) end

  (* An ephemeral, owner-local decision DAG for the complete weighted action.
     Node integers below are temporary arena addresses only: they never leave
     this publication and are not theorem, source, or cache identities.  The
     semantic leaves contain control only; complete-decade height lives on
     normalized edge/root weights. *)

  fun publish lthy =
    let
      val started = Time.now ()
      val profile = Comma_Proof_Profile.make_stage_totals "semantic_predecessor"
        ["source_weighted_crt_data", "source_weighted_crt_proofs"]
      val secondary_checkpoint_failures = Unsynchronized.ref 0
      fun checkpoint stage = Comma_Fast_Kernel.report
        ("semantic-predecessor stage=" ^ stage ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started ^ " " ^
          Comma_Proof_Profile.stage_profile_stats profile ^
          " secondary_checkpoint_failures=" ^
          Int.toString (!secondary_checkpoint_failures))
      fun timed_checkpoint stage work =
        (case Exn.capture (fn () => Comma_Proof_Profile.time_stage profile stage work) () of
          Exn.Res result => result
        | Exn.Exn failure =>
            let
              val report_status = Exn.capture (fn () => checkpoint
                ("weighted-stage=" ^ stage ^ " failed; source counters retained")) ()
              val _ = (case report_status of
                  Exn.Res () => ()
                | Exn.Exn _ => secondary_checkpoint_failures :=
                    !secondary_checkpoint_failures + 1)
            in Exn.reraise failure end)
      val ctxt0 = Local_Theory.target_of lthy
      val (graph, _, _) = parse_graph ctxt0
      val (source_cids, source_ids_definition, source_binding_exact) =
        parse_initial_source_ids ctxt0 graph
      fun weighted_edge action =
        (case action of
          Goto child => Comma_Semantic_Weighted_CRT_DAG.Goto child
        | Live root => Comma_Semantic_Weighted_CRT_DAG.Live root
        | Stop terminal => Comma_Semantic_Weighted_CRT_DAG.Stop terminal
        | Invalid => Comma_Semantic_Weighted_CRT_DAG.Invalid)
      val weighted_graph = fold (fn (cid, node: node) =>
        Inttab.update (cid,
          {period= #period node,
           actions=Vector.map weighted_edge (#actions node)}:
            Comma_Semantic_Weighted_CRT_DAG.graph_node))
        (Inttab.dest graph) Inttab.empty
      val compiler_rewrite_rules = @{thms
        comma_semantic_b1_crt_compile_node_step
        comma_semantic_b1_crt_leaf_def comma_semantic_b1_crt_invalid_action_def
        comma_weighted_crt_selector_def comma_weighted_crt_selector_aux.simps
        comma_weighted_crt_bind.simps comma_semantic_b1_node.select_convs
        fst_conv snd_conv list.map nth_Cons_0 nth_Cons_Suc nth_Cons' upt_rec}
      fun weighted_report stage metrics =
        checkpoint ("weighted-stage=" ^ stage ^ " " ^ metrics)
      val weighted_data = timed_checkpoint "source_weighted_crt_data" (fn () =>
        Comma_Semantic_Weighted_CRT_DAG.compile_sources ctxt0 weighted_report
          weighted_graph source_cids)
      val _ = checkpoint ("weighted-stage=source-data-complete " ^
        #stats weighted_data ())
      val weighted_checked = timed_checkpoint "source_weighted_crt_proofs" (fn () =>
        Comma_Semantic_Weighted_CRT_DAG.compile_sources_checked weighted_report ctxt0
          weighted_data weighted_graph nodes source_cids
          (compiler_rewrite_rules @ map (fn (_, node) => #lookup node)
            (Inttab.dest graph)))
      val compiler_cids = #compiler_cids weighted_checked
      val compiler_equations = #compiler_equations weighted_checked
      val _ = if length compiler_cids = length compiler_equations then ()
        else error "Source weighted compiler CID/equation vectors differ"
      val compiler_by_cid = fold (fn (cid, theorem) => fn table =>
        if Inttab.defined table cid then
          error "Source weighted compiler emitted a duplicate CID equation"
        else Inttab.update (cid, theorem) table)
        (ListPair.zip (compiler_cids, compiler_equations)) Inttab.empty
      val action_terms = map #action (#source_actions weighted_checked)
      val actionT = (case action_terms of
          action :: _ => fastype_of action
        | [] => error "Source weighted compiler published an empty action vector")
      val action_listT = HOLogic.listT actionT
      val natT = @{typ nat}
      val nodes = @{term comma_semantic_graph_nodes}
      val graph_eval = @{term comma_semantic_b1_graph_eval}
      val graph_resultT = @{typ comma_semantic_b1_result}
      val graph_resultT_option = Type (@{type_name option}, [graph_resultT])
      val graph_controlT = @{typ comma_semantic_b1_crt_control}
      val graph_control_heightT = HOLogic.mk_prodT (graph_controlT, natT)
      val graph_result_function = Const (@{const_name comma_semantic_b1_crt_graph_result},
        graph_resultT --> graph_control_heightT)
      val map_option_result = Const (@{const_name map_option},
        (graph_resultT --> graph_control_heightT) --> graph_resultT_option -->
          Type (@{type_name option}, [graph_control_heightT]))
      val weighted_apply = Const (@{const_name comma_weighted_crt_apply},
        actionT --> natT --> Type (@{type_name option},
          [HOLogic.mk_prodT (graph_controlT, natT)]))
      val phase = Free ("phase", natT)
      val list_rules = @{thms nth_Cons_0 nth_Cons_Suc nth_Cons'
        list.map list_all_iff set_upt atLeastLessThan_iff upt_rec}
      fun exact proposition theorem =
        if standalone theorem andalso Thm.prop_of theorem aconv proposition then theorem
        else error "Source weighted proof did not produce its exact closed proposition"
      val compiler_local_by_cid = Inttab.make (#compiler_local_actions weighted_checked)
      val node_action_by_cid = Inttab.make (#node_action_terms weighted_checked)
      val node_build_by_cid = Inttab.make (#node_builds (#publication weighted_checked))
      val invalid_action = @{term comma_semantic_b1_crt_invalid_action}
      fun graph_children cid =
        (case Inttab.lookup graph cid of
          SOME node => Vector.foldr (fn (edge, rest) =>
            (case edge of Goto child => child :: rest | _ => rest)) [] (#actions node)
        | NONE => error "Source refinement graph CID disappeared")
      fun normalized_action cid =
        (case Inttab.lookup node_action_by_cid cid of
          SOME action => action
        | NONE => error "Source refinement lacks a normalized child action")
      fun action_function cid =
        Comma_Semantic_Weighted_CRT_Local_Node_Compiler.action_function
          nat natT invalid_action graph_children
          normalized_action cid
      val goto_const = Const (@{const_name Comma_Semantic_B1_Goto},
        natT --> @{typ comma_semantic_b1_edge})
      val set_edge_list = Const (@{const_name set},
        HOLogic.listT @{typ comma_semantic_b1_edge} -->
          HOLogic.mk_setT @{typ comma_semantic_b1_edge})
      fun prove_child_refinement node child_fn prior_refinements =
        let
          val child = Free ("postorder_child", natT)
          val child_phase = Free ("postorder_phase", natT)
          val actions = actions_selector $ #node_term node
          val goto_member = HOLogic.mk_mem (goto_const $ child, set_edge_list $ actions)
          val expected = map_option_result $ graph_result_function $
            (graph_eval $ nodes $ child $ child_phase)
          val phase_equation = HOLogic.mk_eq
            (weighted_apply $ (child_fn $ child) $ child_phase, expected)
          val proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_all ("postorder_child", natT,
              HOLogic.mk_imp (goto_member,
                HOLogic.mk_all ("postorder_phase", natT, phase_equation))))
          val theorem = Goal.prove ctxt0 [] [] proposition
            (fn {context, ...} =>
              Method.insert_tac context prior_refinements 1 THEN
              auto_tac (Simplifier.add_simps
                ([#actions_equation node] @ @{thms set_simps})
                (Comma_Entry_Arithmetic.natural_context context)))
        in exact proposition theorem end
      fun build_refinements [] _ accumulated = rev accumulated
        | build_refinements (cid :: rest) previous accumulated =
            let
              val node = (case Inttab.lookup graph cid of
                  SOME value => value
                | NONE => error "Postorder source refinement lost a graph node")
              val build = (case Inttab.lookup node_build_by_cid cid of
                  SOME value => value
                | NONE => error "Postorder source refinement lost its normalized action")
              val normalized = normalized_action cid
              val local_term = (case Inttab.lookup compiler_local_by_cid cid of
                  SOME value => value
                | NONE => error "Postorder source refinement lost its local compiler term")
              val child_fn = action_function cid
              val expected_local = @{term comma_semantic_b1_crt_compile_node_from_children} $
                nodes $ HOLogic.mk_number natT cid $ child_fn
              val _ = if local_term aconv expected_local then ()
                else error "Checked source compiler changed the node-action expression"
              val children = distinct (op =) (graph_children cid)
              val _ = if List.all (fn child => child < cid andalso
                    Inttab.defined previous child) children then ()
                else error "Source postorder encountered an uncertified child CID"
              val child_exact = prove_child_refinement node child_fn
                (map (fn child => the (Inttab.lookup previous child)) children)
              val local_proposition = HOLogic.mk_Trueprop
                (HOLogic.mk_all ("phase", natT,
                  HOLogic.mk_eq (weighted_apply $ local_term $ phase,
                    map_option_result $ graph_result_function $
                      (graph_eval $ nodes $ HOLogic.mk_number natT cid $ phase))))
              val local_refinement =
                (@{thm comma_semantic_b1_crt_compile_node_from_children_refines_graph_eval}
                  OF [@{thm comma_semantic_graph_valid_checked}, #lookup node, child_exact])
                |> exact local_proposition
              val compiler_equation = the (Inttab.lookup compiler_by_cid cid)
              val normalization_equation = #normalization_equation build
              val normalized_proposition = HOLogic.mk_Trueprop
                (HOLogic.mk_all ("phase", natT,
                  HOLogic.mk_eq (weighted_apply $ normalized $ phase,
                    map_option_result $ graph_result_function $
                      (graph_eval $ nodes $ HOLogic.mk_number natT cid $ phase))))
              val theorem = Goal.prove ctxt0 [] [] normalized_proposition
                (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps
                  [Comma_Semantic_Weighted_CRT_Data_Transport.object_symmetric
                    ctxt0 normalization_equation, compiler_equation, local_refinement]
                  context) 1)
                |> exact normalized_proposition
              val next = Inttab.update (cid, theorem) previous
            in build_refinements rest next (theorem :: accumulated) end
      val source_node_refinements = build_refinements compiler_cids Inttab.empty []
      val node_refinements_by_cid = Inttab.make
        (ListPair.zip (compiler_cids, source_node_refinements))
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt0
        "Ascending normalized source-reachable graph nodes refine graph evaluation"
        source_node_refinements
      val source_action_equations = map (fn source: Comma_Semantic_Weighted_CRT_DAG.source_action =>
        let
          val cid = #cid source
          val theorem = (case Inttab.lookup node_refinements_by_cid cid of
              SOME value => value
            | NONE => error "Source node refinement omitted an authenticated source CID")
          val expected = map_option_result $ graph_result_function $
            (graph_eval $ nodes $ HOLogic.mk_number natT cid $ phase)
          val proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_all ("phase", natT,
              HOLogic.mk_eq (weighted_apply $ (#action source) $ phase, expected)))
        in exact proposition theorem end) (#source_actions weighted_checked)
      val source_actions_term = HOLogic.mk_list actionT action_terms
      val (source_actions_constant, source_actions_definition, lthy1) =
        let
          val ((constant, (_, definition_local)), lthy') = Local_Theory.define
            ((Binding.name "comma_semantic_graph_initial_source_actions", NoSyn),
              ((Binding.name "comma_semantic_graph_initial_source_actions_def", []),
                source_actions_term)) lthy
          val morphism = Local_Theory.target_morphism lthy'
        in (Morphism.term morphism constant, Morphism.thm morphism definition_local, lthy') end
      val source_slot = Free ("source_slot", natT)
      val source_phase = Free ("source_phase", natT)
      val nth_action = Const (@{const_name nth}, action_listT --> natT --> actionT)
      val source_cid = Const (@{const_name nth}, HOLogic.listT natT --> natT --> natT) $
        @{term comma_semantic_graph_initial_source_ids} $ source_slot
      val source_rhs = map_option_result $ graph_result_function $
        (graph_eval $ nodes $ source_cid $ source_phase)
      val source_rows_prop = HOLogic.mk_Trueprop
        (Const (@{const_name list_all},
          (natT --> HOLogic.boolT) --> HOLogic.listT natT --> HOLogic.boolT) $
          Term.lambda source_slot (HOLogic.mk_all ("source_phase", natT,
            HOLogic.mk_eq (weighted_apply $
              (nth_action $ source_actions_constant $ source_slot) $ source_phase,
              source_rhs))) @{term "[0..<16] :: nat list"})
      val source_rows = Goal.prove (Local_Theory.target_of lthy1) [] [] source_rows_prop
        (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps
          (source_actions_definition :: source_ids_definition :: source_action_equations @
            list_rules @ @{thms list_all_iff set_upt atLeastLessThan_iff
              comma_semantic_graph_initial_source_ids_def}) context) 1)
        |> exact source_rows_prop
      val source_index = Free ("source_index", natT)
      val source_index_phase = Free ("source_phase", natT)
      val source_point = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (weighted_apply $ (nth_action $ source_actions_constant $ source_index) $
          source_index_phase,
         map_option_result $ graph_result_function $
          (graph_eval $ nodes $
            (Const (@{const_name nth}, HOLogic.listT natT --> natT --> natT) $
              @{term comma_semantic_graph_initial_source_ids} $ source_index) $
            source_index_phase)))
      val source_refine_prop = Logic.all source_index (Logic.all source_index_phase
        (Logic.mk_implies (HOLogic.mk_Trueprop
          (HOLogic.mk_binrel @{const_name less} (source_index, HOLogic.mk_number natT 16)),
          source_point)))
      val source_refine = Goal.prove (Local_Theory.target_of lthy1) [] [] source_refine_prop
        (fn {context, ...} => Method.insert_tac context [source_rows] 1 THEN
          auto_tac (Simplifier.add_simps list_rules context))
        |> exact source_refine_prop
      val list_all = Const (@{const_name list_all},
        (actionT --> HOLogic.boolT) --> HOLogic.listT actionT --> HOLogic.boolT)
      val action = Free ("source_action", actionT)
      val length_const = Const (@{const_name size}, action_listT --> natT)
      val source_length_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (length_const $ source_actions_constant,
          HOLogic.mk_number natT 16))
      val source_length = Goal.prove (Local_Theory.target_of lthy1) [] [] source_length_prop
        (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps
          ([source_actions_definition] @ @{thms list.size}) context) 1)
        |> exact source_length_prop
      val source_wellformed_prop = HOLogic.mk_Trueprop
        (list_all $ Term.lambda action
          (@{term comma_weighted_crt_wellformed} $
            (Const (@{const_name snd}, actionT --> @{typ comma_semantic_b1_crt_dag}) $ action)) $
          source_actions_constant)
      val source_wellformed = Goal.prove (Local_Theory.target_of lthy1) [] [] source_wellformed_prop
        (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps
          ([source_actions_definition] @ @{thms comma_weighted_crt_wellformed.simps
            comma_crt_axis_radix_def list_all_iff}) context) 1)
        |> exact source_wellformed_prop
      val source_zero_equations = ListPair.map
        (fn (source: Comma_Semantic_Weighted_CRT_DAG.source_action, refinement) =>
          let
            val proposition = HOLogic.mk_Trueprop
              (@{term comma_semantic_b1_crt_action_nonterminal_zero} $ #action source)
            val theorem = Goal.prove (Local_Theory.target_of lthy1) [] [] proposition
              (fn {context, ...} =>
                Method.insert_tac context [refinement] 1 THEN
                resolve_tac context
                  [@{thm comma_semantic_b1_crt_nonterminal_zero_of_graph_refinement}] 1
                  THEN assume_tac context 1)
          in exact proposition theorem end)
        (#source_actions weighted_checked, source_action_equations)
      val source_zero_prop = HOLogic.mk_Trueprop
        (list_all $ Term.lambda action
          (@{term comma_semantic_b1_crt_action_nonterminal_zero} $ action) $
          source_actions_constant)
      val source_zero = Goal.prove (Local_Theory.target_of lthy1) [] [] source_zero_prop
        (fn {context, ...} => asm_full_simp_tac (Simplifier.add_simps
          ([source_actions_definition] @ source_zero_equations @ @{thms list_all_iff})
          context) 1)
        |> exact source_zero_prop
      val source_proofs = #compiler_equations weighted_checked @
        #normalization_equations weighted_checked @ source_node_refinements @
        source_action_equations @ [source_rows, source_refine, source_length,
          source_wellformed, source_zero, source_binding_exact]
      val _ = Thm.consolidate source_proofs
      val _ = Comma_Proof_Dependency_Audit.require_native_clean
        (Local_Theory.target_of lthy1)
        "Authenticated 16-source weighted CRT action vector" source_proofs
      fun note name theorem lthy = snd (Local_Theory.note
        ((Binding.name name, []), [theorem]) lthy)
      val lthy2 = note "comma_semantic_graph_initial_source_actions_refine"
        source_refine lthy1
      val lthy3 = note "comma_semantic_graph_initial_source_actions_length"
        source_length lthy2
      val lthy4 = note "comma_semantic_graph_initial_source_actions_wellformed"
        source_wellformed lthy3
      val lthy5 = note "comma_semantic_graph_initial_source_actions_nonterminal_zero"
        source_zero lthy4
      val _ = checkpoint ("source action vector certified actions=" ^
        Int.toString (length action_terms) ^ " postorder nodes=" ^
        Int.toString (length source_node_refinements) ^ " " ^ #stats weighted_data ())
    in lthy5 end

end

