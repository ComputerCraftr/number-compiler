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
      val node_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        (@{thms comma_semantic_b1_node_from_data_def
            comma_semantic_b1_node.select_convs fst_conv snd_conv
            list.map upt_rec nth_Cons_0 nth_Cons_Suc nth_Cons'})
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
        ["weighted_crt_data", "weighted_crt_proofs"]
      val secondary_checkpoint_failures = Unsynchronized.ref 0
      fun timed stage work = Comma_Proof_Profile.time_stage profile stage work
      fun checkpoint stage = Comma_Fast_Kernel.report
        ("semantic-predecessor stage=" ^ stage ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started ^ " " ^
          Comma_Proof_Profile.stage_profile_stats profile ^
          " secondary_checkpoint_failures=" ^
          Int.toString (!secondary_checkpoint_failures))
      fun timed_checkpoint stage work =
        (case Exn.capture (fn () => timed stage work) () of
          Exn.Res result => result
        | Exn.Exn failure =>
            let
              val report_status = Exn.capture (fn () => checkpoint
                ("weighted-stage=" ^ stage ^
                  " failed; last completed counters retained")) ()
              val _ = (case report_status of
                  Exn.Res () => ()
                | Exn.Exn _ => secondary_checkpoint_failures :=
                    !secondary_checkpoint_failures + 1)
            in Exn.reraise failure end)
      val ctxt0 = Local_Theory.target_of lthy
      val (graph, roots, root_definition) = parse_graph ctxt0
      val (source_cids, source_ids_definition, source_binding_exact) =
        parse_initial_source_ids ctxt0 graph
      val root_vector = Vector.fromList roots
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
        fst_conv snd_conv list.map nth_Cons_0
        nth_Cons_Suc nth_Cons' upt_rec}
      fun weighted_report stage metrics =
        checkpoint ("weighted-stage=" ^ stage ^ " " ^ metrics)
      val weighted_data = timed_checkpoint "weighted_crt_data" (fn () =>
        Comma_Semantic_Weighted_CRT_DAG.compile ctxt0 weighted_report weighted_graph
          roots source_cids)
      val _ = checkpoint ("weighted-stage=data-complete " ^
        #stats weighted_data ())
      val weighted_checked = timed_checkpoint "weighted_crt_proofs" (fn () =>
        Comma_Semantic_Weighted_CRT_DAG.compile_checked weighted_report ctxt0
          weighted_data weighted_graph nodes source_cids
          (compiler_rewrite_rules @ map (fn (_, node) => #lookup node)
            (Inttab.dest graph)))
      val _ = if length (#compiler_equations weighted_checked) =
          length (#node_actions weighted_data) andalso
          length (#composition_equations weighted_checked) = 46 * 5 then ()
        else error "Checked weighted CRT publication omitted a node compiler or square equation"
      val weighted_proofs = #compiler_equations weighted_checked @
        #composition_equations weighted_checked @
        #normalization_equations weighted_checked @
        (map #compiler_equation (#source_actions weighted_checked) @
          map #normalization_equation (#source_actions weighted_checked)) @
        [#power_equation weighted_checked, #terminal_bound weighted_checked,
         #bounded_stops weighted_checked,
         #source_nf_apply_refinement weighted_checked,
         #source_nf_bounded_stops weighted_checked]
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt0
        "Weighted CRT raw compiler, five chronological squares, and Stop-height bound"
        weighted_proofs
      val _ = checkpoint ("raw checked CRT compiler nodes=" ^
        Int.toString (length (#compiler_equations weighted_checked)) ^
        " root_coverage=" ^ Int.toString (length roots) ^
        " checked compositions=" ^
        Int.toString (length (#composition_equations weighted_checked)) ^
        " checked normalizations=" ^
        Int.toString (length (#normalization_equations weighted_checked)) ^
        " " ^ #stats weighted_data ())
      val compiler_cids = #compiler_cids weighted_checked
      val compiler_equations = #compiler_equations weighted_checked
      val _ = if length compiler_cids = length compiler_equations then ()
        else error "Weighted compiler CID/equation vectors have different lengths"
      val compiler_by_cid = fold (fn (cid, theorem) => fn table =>
        if Inttab.defined table cid then
          error "Weighted compiler emitted duplicate canonical CID equations"
        else Inttab.update (cid, theorem) table)
        (ListPair.zip (compiler_cids, compiler_equations)) Inttab.empty
      val base_actions = #base_actions_term weighted_checked
      val final_actions = #final_actions_term weighted_checked
      val base_action_terms = HOLogic.dest_list base_actions
      val actionT = (case base_action_terms of
          action :: _ => fastype_of action
        | [] => error "Weighted compiler published an empty B1 root vector")
      val action_listT = HOLogic.listT actionT
      val nth_action = Const (@{const_name nth}, action_listT --> natT --> actionT)
      val weighted_apply = Const (@{const_name comma_weighted_crt_apply},
        actionT --> natT --> Type (@{type_name option},
          [HOLogic.mk_prodT (@{typ comma_semantic_b1_crt_control}, natT)]))
      val graph_resultT = @{typ comma_semantic_b1_result}
      val graph_resultT_option = Type (@{type_name option}, [graph_resultT])
      val graph_controlT = @{typ comma_semantic_b1_crt_control}
      val graph_control_heightT = HOLogic.mk_prodT (graph_controlT, natT)
      val graph_control_heightT_option =
        Type (@{type_name option}, [graph_control_heightT])
      val graph_result_function = Const (@{const_name comma_semantic_b1_crt_graph_result},
        graph_resultT --> graph_control_heightT)
      val map_option_result = Const (@{const_name map_option},
        (graph_resultT --> graph_control_heightT) --> graph_resultT_option -->
          graph_control_heightT_option)
      val graph_eval = @{term comma_semantic_b1_graph_eval}
      val roots_action = @{term comma_semantic_b1_crt_roots_action}
      val root_weighted = @{term comma_semantic_graph_root_weighted_action}
      fun less x bound = HOLogic.mk_binrel @{const_name less} (x, nat bound)
      fun less_prop x bound = HOLogic.mk_Trueprop (less x bound)
      val phase = Free ("phase", natT)
      val root = Free ("root", natT)
      val list_rules = @{thms nth_Cons_0 nth_Cons_Suc nth_Cons'
        list.map list_all_iff set_upt atLeastLessThan_iff upt_rec}
      fun exact_object proposition theorem =
        if standalone theorem andalso Thm.prop_of theorem aconv proposition then theorem
        else error "Weighted predecessor proof did not produce its exact closed proposition"
      val compiler_local_by_cid = Inttab.make
        (#compiler_local_actions weighted_checked)
      val node_action_by_cid = Inttab.make
        (#node_action_terms weighted_checked)
      val node_build_by_cid = Inttab.make
        (#node_builds (#publication weighted_checked))
      val invalid_action = @{term comma_semantic_b1_crt_invalid_action}
      fun graph_children cid =
        (case Inttab.lookup graph cid of
          SOME node => Vector.foldr (fn (edge, rest) =>
            (case edge of Goto child => child :: rest | _ => rest)) []
            (#actions node)
        | NONE => error "Postorder refinement graph CID disappeared")
      fun normalized_action cid =
        (case Inttab.lookup node_action_by_cid cid of
          SOME action => action
        | NONE => error "Postorder refinement has no normalized child action")
      fun action_function cid =
        Comma_Semantic_Weighted_CRT_Local_Node_Compiler.action_function
          nat natT invalid_action graph_children normalized_action cid
      val goto_const = Const (@{const_name Comma_Semantic_B1_Goto},
        natT --> edgeT)
      val set_edgeT = HOLogic.mk_setT edgeT
      val set_edge_list = Const (@{const_name set},
        HOLogic.listT edgeT --> set_edgeT)
      fun node_refinement proposition theorem = exact_object proposition theorem
      fun prove_child_refinement cid node child_fn prior_refinements =
        let
          val child = Free ("postorder_child", natT)
          val phase = Free ("postorder_phase", natT)
          val actions = actions_selector $ #node_term node
          val goto_member = HOLogic.mk_mem (goto_const $ child,
            set_edge_list $ actions)
          val action = child_fn $ child
          val expected = map_option_result $ graph_result_function $
            (graph_eval $ nodes $ child $ phase)
          val phase_equation = HOLogic.mk_eq
            (weighted_apply $ action $ phase, expected)
          val proposition = HOLogic.mk_Trueprop
            (HOLogic.mk_all ("postorder_child", natT,
              HOLogic.mk_imp (goto_member,
                HOLogic.mk_all ("postorder_phase", natT, phase_equation))))
          val theorem = Goal.prove ctxt0 [] [] proposition
            (fn {context, ...} =>
              Method.insert_tac context prior_refinements 1 THEN
              auto_tac
                (Comma_Entry_Arithmetic.natural_context context addsimps
                  ([#actions_equation node] @ @{thms set_simps})) )
        in exact_object proposition theorem end
      fun build_node_refinements [] _ accumulated = rev accumulated
        | build_node_refinements (cid :: rest) previous accumulated =
            let
              val node = (case Inttab.lookup graph cid of
                  SOME value => value
                | NONE => error "Ascending postorder refinement lost a graph node")
              val build = (case Inttab.lookup node_build_by_cid cid of
                  SOME value => value
                | NONE => error "Ascending postorder refinement lost its node NF proof")
              val normalized = normalized_action cid
              val local_term = (case Inttab.lookup compiler_local_by_cid cid of
                  SOME value => value
                | NONE => error "Ascending postorder refinement lost its local compiler term")
              val child_fn = action_function cid
              val expected_local =
                @{term comma_semantic_b1_crt_compile_node_from_children} $
                  nodes $ nat cid $ child_fn
              val _ = if local_term aconv expected_local then ()
                else error "Checked local compiler term changed its child-action function"
              val children = distinct (op =) (graph_children cid)
              val _ = if List.all (fn child => child < cid andalso
                    Inttab.defined previous child) children then ()
                else error "Postorder graph refinement encountered an uncertified child CID"
              val child_facts = map (fn child =>
                the (Inttab.lookup previous child)) children
              val child_exact = prove_child_refinement cid node child_fn child_facts
              val local_proposition = HOLogic.mk_Trueprop
                (HOLogic.mk_all ("phase", natT,
                  HOLogic.mk_eq (weighted_apply $ local_term $ phase,
                    map_option_result $ graph_result_function $
                      (graph_eval $ nodes $ nat cid $ phase))))
              val local_refinement =
                (@{thm comma_semantic_b1_crt_compile_node_from_children_refines_graph_eval}
                  OF [@{thm comma_semantic_graph_valid_checked}, #lookup node, child_exact])
                |> node_refinement local_proposition
              val compiler_equation = the (Inttab.lookup compiler_by_cid cid)
              val normalization_equation = #normalization_equation build
              val normalized_proposition = HOLogic.mk_Trueprop
                (HOLogic.mk_all ("phase", natT,
                  HOLogic.mk_eq (weighted_apply $ normalized $ phase,
                    map_option_result $ graph_result_function $
                      (graph_eval $ nodes $ nat cid $ phase))))
              val theorem = Goal.prove ctxt0 [] [] normalized_proposition
                (fn {context, ...} => asm_full_simp_tac (context addsimps
                  [Comma_Semantic_Weighted_CRT_Data_Transport.object_symmetric
                      ctxt0 normalization_equation, compiler_equation,
                   local_refinement]) 1)
                |> node_refinement normalized_proposition
              val next = Inttab.update (cid, theorem) previous
            in build_node_refinements rest next (theorem :: accumulated) end
      val _ = if map #1 (#node_action_terms weighted_checked) = compiler_cids
          andalso map #1 (#compiler_local_actions weighted_checked) = compiler_cids
          andalso map #1 (#node_builds (#publication weighted_checked)) = compiler_cids
        then () else error "Postorder NF/compiler theorem vectors changed ascending CID order"
      val node_refinement_equations = build_node_refinements compiler_cids Inttab.empty []
      val node_refinements_by_cid = Inttab.make
        (ListPair.zip (compiler_cids, node_refinement_equations))
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt0
        "Ascending postorder normalized node actions refine graph evaluation"
        node_refinement_equations
      fun root_action_equation root_index =
        let
          val cid = Vector.sub (root_vector, root_index)
          val refinement = (case Inttab.lookup node_refinements_by_cid cid of
              SOME theorem => theorem
            | NONE => error "Postorder refinement omitted a published root CID")
          val expected_action = List.nth (base_action_terms, root_index)
          val published_action = normalized_action cid
          val _ = if expected_action aconv published_action then ()
            else error "Normalized root vector does not select its authenticated CID action"
          val equation = HOLogic.mk_eq
            (roots_action $ base_actions $ phase $ nat root_index,
             root_weighted $ phase $ nat root_index)
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all ("phase", natT,
            HOLogic.mk_imp (less phase 924, equation)))
          val facts = [refinement, root_definition,
            @{thm comma_semantic_b1_crt_decode_graph_root}] @
            @{thms comma_semantic_b1_crt_roots_action_def
              comma_semantic_b1_crt_action_eval_def
              comma_semantic_b1_crt_decode.simps
              comma_weighted_crt_apply_def
              comma_semantic_graph_root_ids_def}
          val theorem = Goal.prove ctxt0 [] [] proposition
            (fn {context, ...} =>
              asm_full_simp_tac (context addsimps (facts @ list_rules)) 1)
        in exact_object proposition theorem end
      val root_action_equations = Vector.tabulate (46, root_action_equation)
      val root_predicate = Term.lambda root
        (HOLogic.mk_all ("phase", natT,
          HOLogic.mk_imp (less phase 924,
            HOLogic.mk_eq
              (roots_action $ base_actions $ phase $ root,
               root_weighted $ phase $ root))))
      val root_rows_prop = HOLogic.mk_Trueprop
        (list_all_term natT root_predicate @{term "[0..<46] :: nat list"})
      val root_rows = Goal.prove ctxt0 [] [] root_rows_prop
        (fn {context, ...} =>
          asm_full_simp_tac
            (context addsimps
              (Vector.foldr op:: [] root_action_equations @ list_rules)) 1)
        |> exact_object root_rows_prop
      val base_exact_prop = Logic.all phase (Logic.all root
        (Logic.mk_implies (less_prop phase 924,
          Logic.mk_implies (less_prop root 46,
            HOLogic.mk_Trueprop
              (HOLogic.mk_eq
                (roots_action $ base_actions $ phase $ root,
                 root_weighted $ phase $ root))))))
      val base_exact = Goal.prove ctxt0 [] [] base_exact_prop
        (fn {context, ...} =>
          Method.insert_tac context [root_rows] 1 THEN
          auto_tac (context addsimps list_rules))
      val _ = exact_rule base_exact_prop base_exact
      val base_admitted = @{thm comma_semantic_graph_root_weighted_action_admitted}
      val roots_wf_prop = HOLogic.mk_Trueprop
        (@{term comma_semantic_b1_crt_roots_wellformed} $ base_actions)
      val roots_wf = Goal.prove ctxt0 [] [] roots_wf_prop
        (fn {context, ...} =>
          asm_full_simp_tac (context addsimps
            (@{thms comma_semantic_b1_crt_roots_wellformed_def
              comma_weighted_crt_wellformed.simps comma_crt_axis_radix_def
              list.size nth_Cons_0 nth_Cons_Suc nth_Cons'})) 1)
        |> exact_object roots_wf_prop
      val phase_var = Free ("phase", natT)
      val root_var = Free ("root", natT)
      val final_exact_body = HOLogic.mk_eq
        (weighted_apply $ (nth_action $ final_actions $ root_var) $ phase_var,
         weighted_apply $
           (nth_action $
             (@{term comma_semantic_b1_crt_power} $ nat 5 $ base_actions) $
             root_var) $ phase_var)
      val final_exact_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_all ("root", natT,
          HOLogic.mk_imp (less root_var 46,
            HOLogic.mk_all ("phase", natT, final_exact_body))))
      val final_exact = Goal.prove ctxt0 [] [] final_exact_prop
        (fn {context, ...} =>
          asm_full_simp_tac (context addsimps
            (#power_equation weighted_checked :: list_rules)) 1)
        |> exact_object final_exact_prop
      val final_bounded = #bounded_stops weighted_checked
      val predecessor = @{thm comma_semantic_graph_stop242_from_weighted_crt_power_all}
        OF [roots_wf, base_exact, base_admitted, final_exact, final_bounded]
      val proof_facts = weighted_proofs @ node_refinement_equations @
        Vector.foldr op:: [] root_action_equations @
        [root_rows, base_exact, roots_wf, final_exact, predecessor]
      val _ = Thm.consolidate proof_facts
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt0
        "Ascending normalized graph nodes, five-square transport, and Stop242 bound"
        proof_facts
      val _ = if standalone predecessor then ()
        else error "Concrete weighted predecessor closure retained assumptions"
      fun define_action_list name value lthy =
        let
          val binding = Binding.name name
          val ((constant, (_, definition_local)), lthy') = Local_Theory.define
            ((binding, NoSyn),
              ((Binding.name (name ^ "_def"), []), value)) lthy
          val morphism = Local_Theory.target_morphism lthy'
        in (Morphism.term morphism constant,
          Morphism.thm morphism definition_local, lthy') end
      val source_action_terms = map #action (#source_actions weighted_checked)
      val source_actions_term = HOLogic.mk_list actionT source_action_terms
      val (source_actions_constant, source_actions_definition, lthy1) =
        define_action_list "comma_semantic_graph_initial_source_actions"
          source_actions_term lthy
      val final_actions_term = #final_actions_term weighted_checked
      val (final_actions_constant, final_actions_definition, lthy2) =
        define_action_list "comma_semantic_graph_b32_weighted_actions"
          final_actions_term lthy1
      val source_nf_actions_term = #source_nf_actions_term weighted_checked
      val (source_nf_actions_constant, source_nf_actions_definition, lthy3) =
        define_action_list "comma_semantic_graph_initial_nf_actions"
          source_nf_actions_term lthy2
      fun source_action_refinement (source: Comma_Semantic_Weighted_CRT_DAG.source_action) =
        let
          val cid = #cid source
          val expected_action = normalized_action cid
          val _ = if #action source aconv expected_action then ()
            else error "Initial source vector is not the corresponding normalized CID action"
          val theorem = (case Inttab.lookup node_refinements_by_cid cid of
              SOME value => value
            | NONE => error "Ascending postorder refinement omitted an initial source CID")
          val phase = Free ("phase", natT)
          val graph_lookup = graph_eval $ nodes $ nat cid $ phase
          val expected = map_option_result $ graph_result_function $ graph_lookup
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_all ("phase", natT,
            HOLogic.mk_eq
              (weighted_apply $ (#action source) $ phase,
                expected)))
        in exact_object proposition theorem end
      val source_action_equations = map source_action_refinement
        (#source_actions weighted_checked)
      val source_action_indexes = Free ("source_index", natT)
      val source_phase = Free ("source_phase", natT)
      val initial_source_ids_term = @{term comma_semantic_graph_initial_source_ids}
      val source_indexed_action = nth_action $ source_actions_constant $ source_action_indexes
      val source_indexed_cid = Const (@{const_name nth},
        HOLogic.listT natT --> natT --> natT) $ initial_source_ids_term $
          source_action_indexes
      val source_indexed_graph_eval = graph_eval $ nodes $ source_indexed_cid $ source_phase
      val source_indexed_result = map_option_result $ graph_result_function $
        source_indexed_graph_eval
      val source_row_predicate = Term.lambda source_action_indexes
        (HOLogic.mk_all ("source_phase", natT,
          HOLogic.mk_eq
            (weighted_apply $ source_indexed_action $ source_phase,
             source_indexed_result)))
      val source_rows_prop = HOLogic.mk_Trueprop (list_all_term natT
        source_row_predicate @{term "[0..<16] :: nat list"})
      val source_rows = Goal.prove (Local_Theory.target_of lthy2) [] [] source_rows_prop
        (fn {context, ...} => asm_full_simp_tac (context addsimps
          (source_actions_definition :: source_ids_definition ::
            source_action_equations @ list_rules @
            @{thms list_all_iff set_upt atLeastLessThan_iff list.size
              comma_semantic_graph_initial_source_ids_def})) 1)
        |> exact_object source_rows_prop
      val source_index_bound = less_prop source_action_indexes 16
      val source_point_eq = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (weighted_apply $ source_indexed_action $ source_phase,
         source_indexed_result))
      val source_actions_refine_prop = Logic.all source_action_indexes
        (Logic.all source_phase
          (Logic.mk_implies (source_index_bound, source_point_eq)))
      val source_actions_refine = Goal.prove (Local_Theory.target_of lthy2) [] []
        source_actions_refine_prop
        (fn {context, ...} => Method.insert_tac context [source_rows] 1 THEN
          auto_tac (context addsimps
            @{thms list_all_iff set_upt atLeastLessThan_iff nth_Cons_0
              nth_Cons_Suc nth_Cons' list.map}))
      val _ = exact_rule source_actions_refine_prop source_actions_refine
      val final_phase = Free ("final_phase", natT)
      val final_root = Free ("final_root", natT)
      val final_action_eval = @{term comma_semantic_b1_crt_action_eval} $
        (nth_action $ final_actions_constant $ final_root) $ final_phase
      val final_action_refinement_prop = Logic.all final_root
        (Logic.all final_phase
          (Logic.mk_implies (less_prop final_root 46,
            Logic.mk_implies (less_prop final_phase 924,
              HOLogic.mk_Trueprop (HOLogic.mk_eq (final_action_eval,
                @{term comma_semantic_b1_weighted_action_power} $ nat 5 $
                  root_weighted $ final_phase $ final_root))))))
      val power_refinement = @{thm comma_semantic_b1_crt_power_action_eval}
        OF [roots_wf, base_exact, base_admitted]
      val final_action_refinement = Goal.prove (Local_Theory.target_of lthy2) [] []
        final_action_refinement_prop
        (fn {context, ...} => asm_full_simp_tac (context addsimps
          ([final_actions_definition, #power_equation weighted_checked,
            power_refinement, roots_wf, base_exact, base_admitted] @
           @{thms comma_semantic_b1_crt_action_eval_def
             comma_semantic_b1_crt_roots_action_def
             comma_semantic_b1_crt_power_length
             comma_semantic_b1_crt_decode.simps
             comma_weighted_crt_apply_def list.map nth_Cons_0
             nth_Cons_Suc nth_Cons'})) 1)
      val _ = exact_rule final_action_refinement_prop final_action_refinement
      val nf_source_slot = Free ("source_nf_slot", natT)
      val nf_phase = Free ("source_nf_phase", natT)
      val nf_action = nth_action $ source_nf_actions_constant $ nf_source_slot
      val nf_source_action = nth_action $ source_actions_constant $ nf_source_slot
      val nf_compose = Const (@{const_name comma_semantic_b1_crt_compose},
        natT --> actionT --> action_listT --> actionT) $
          nat 1 $ nf_source_action $ final_actions_constant
      val nf_apply_equation = HOLogic.mk_eq
        (weighted_apply $ nf_action $ nf_phase,
         weighted_apply $ nf_compose $ nf_phase)
      val nf_row_predicate = Term.lambda nf_source_slot
        (HOLogic.mk_all ("source_nf_phase", natT,
          HOLogic.mk_imp (less nf_source_slot 16, nf_apply_equation)))
      val nf_refinement_prop = HOLogic.mk_Trueprop
        (list_all_term natT nf_row_predicate @{term "[0..<16] :: nat list"})
      val source_nf_refinement = Goal.prove (Local_Theory.target_of lthy3) [] []
        nf_refinement_prop
        (fn {context, ...} => asm_full_simp_tac (context addsimps
          ([#source_nf_apply_refinement weighted_checked,
            source_nf_actions_definition, source_actions_definition,
            final_actions_definition] @ list_rules)) 1)
      val _ = if standalone source_nf_refinement andalso
          Thm.prop_of source_nf_refinement aconv nf_refinement_prop then ()
        else error "Published source-to-B32 action vector lost its checked refinement"
      fun list_all_of elementT predicate values =
        Const (@{const_name list_all},
          (elementT --> HOLogic.boolT) --> HOLogic.listT elementT -->
            HOLogic.boolT) $ predicate $ values
      val action = Free ("weighted_action", actionT)
      val snd_action = Const (@{const_name snd},
        actionT --> @{typ comma_semantic_b1_crt_dag}) $ action
      val weighted_wellformed = Const (@{const_name comma_weighted_crt_wellformed},
        @{typ comma_semantic_b1_crt_dag} --> HOLogic.boolT)
      val action_nonterminal_zero = Const
        (@{const_name comma_semantic_b1_crt_action_nonterminal_zero},
          actionT --> HOLogic.boolT)
      val list_length = Const (@{const_name size}, action_listT --> natT)
      fun prove_structure_fact proposition simp_rules label =
        let
          val theorem = Goal.prove (Local_Theory.target_of lthy2) [] [] proposition
            (fn {context, ...} => asm_full_simp_tac
              (context addsimps simp_rules) 1)
        in exact_object proposition theorem end
      val source_length_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (list_length $ source_actions_constant, nat 16))
      val source_length = prove_structure_fact source_length_prop
        ([source_actions_definition] @ @{thms list.size}) "source action length"
      val source_wf_prop = HOLogic.mk_Trueprop
        (list_all_of actionT
          (Term.lambda action (weighted_wellformed $ snd_action))
          source_actions_constant)
      val source_wf = prove_structure_fact source_wf_prop
        ([source_actions_definition] @
         @{thms comma_weighted_crt_wellformed.simps comma_crt_axis_radix_def
           list_all_iff}) "source action shape"
      val _ = if length (#source_actions weighted_checked) =
          length source_action_equations then ()
        else error "Source nonterminal proofs do not match the authenticated action vector"
      val source_zero_equations = ListPair.map
        (fn (source, refinement) =>
          let
            val proposition = HOLogic.mk_Trueprop
              (action_nonterminal_zero $ #action source)
            val theorem = Goal.prove (Local_Theory.target_of lthy2) [] []
              proposition
              (fn {context, ...} =>
                Method.insert_tac context [refinement] 1 THEN
                resolve_tac context
                  [@{thm comma_semantic_b1_crt_nonterminal_zero_of_graph_refinement}] 1
                  THEN assume_tac context 1)
          in exact_object proposition theorem end)
        (#source_actions weighted_checked, source_action_equations)
      val source_zero_prop = HOLogic.mk_Trueprop
        (list_all_of actionT (Term.lambda action
          (action_nonterminal_zero $ action)) source_actions_constant)
      val source_zero = prove_structure_fact source_zero_prop
        ([source_actions_definition] @ source_zero_equations @
          @{thms list_all_iff}) "source nonterminal weights"
      val final_length_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (list_length $ final_actions_constant, nat 46))
      val final_length = prove_structure_fact final_length_prop
        ([final_actions_definition] @ @{thms list.size}) "B32 action length"
      val final_wf_prop = HOLogic.mk_Trueprop
        (list_all_of actionT
          (Term.lambda action (weighted_wellformed $ snd_action))
          final_actions_constant)
      val final_wf = prove_structure_fact final_wf_prop
        ([final_actions_definition] @
         @{thms comma_weighted_crt_wellformed.simps comma_crt_axis_radix_def
           list_all_iff}) "B32 action shape"
      val final_root_index = Free ("final_root", natT)
      val final_root_action = nth_action $ final_actions_constant $ final_root_index
      val final_zero_indexed_prop = Logic.all final_root_index
        (Logic.mk_implies (less_prop final_root_index 46,
          HOLogic.mk_Trueprop
            (action_nonterminal_zero $ final_root_action)))
      val final_zero_indexed = Goal.prove (Local_Theory.target_of lthy2) [] []
        final_zero_indexed_prop
        (fn {context, ...} =>
          Method.insert_tac context [final_bounded] 1 THEN
          resolve_tac context
            [@{thm comma_semantic_b1_crt_nonterminal_zero_of_bounded_stops}] 1
          THEN asm_full_simp_tac (context addsimps
            (final_actions_definition :: list_rules)) 1)
      val _ = exact_rule final_zero_indexed_prop final_zero_indexed
      val final_zero_prop = HOLogic.mk_Trueprop
        (list_all_of actionT (Term.lambda action
          (action_nonterminal_zero $ action)) final_actions_constant)
      val final_zero = prove_structure_fact final_zero_prop
        ([final_length, final_zero_indexed] @
         @{thms list_all_iff all_set_conv_all_nth}) "B32 nonterminal weights"
      val source_nf_length_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (list_length $ source_nf_actions_constant, nat 16))
      val source_nf_length = Goal.prove (Local_Theory.target_of lthy3) [] []
        source_nf_length_prop (fn {context, ...} =>
          asm_full_simp_tac (context addsimps
            ([source_nf_actions_definition] @ @{thms list.size})) 1)
        |> exact_object source_nf_length_prop
      val source_nf_wf_prop = HOLogic.mk_Trueprop
        (list_all_of actionT
          (Term.lambda action (weighted_wellformed $ snd_action))
          source_nf_actions_constant)
      val source_nf_wf = Goal.prove (Local_Theory.target_of lthy3) [] []
        source_nf_wf_prop (fn {context, ...} =>
          asm_full_simp_tac (context addsimps
            ([source_nf_actions_definition] @
             @{thms comma_weighted_crt_wellformed.simps
               comma_crt_axis_radix_def list_all_iff})) 1)
        |> exact_object source_nf_wf_prop
      val weighted_shape = Const
        (@{const_name comma_weighted_crt_shape},
          natT --> @{typ comma_semantic_b1_crt_dag} --> HOLogic.boolT)
      val source_nf_shape_prop = HOLogic.mk_Trueprop
        (list_all_of actionT
          (Term.lambda action (weighted_shape $ nat 0 $ snd_action))
          source_nf_actions_constant)
      val source_nf_shape = Goal.prove (Local_Theory.target_of lthy3) [] []
        source_nf_shape_prop (fn {context, ...} =>
          asm_full_simp_tac (context addsimps
            ([source_nf_actions_definition] @
             @{thms comma_weighted_crt_shape.simps
               comma_crt_axis_radix_def list_all_iff})) 1)
        |> exact_object source_nf_shape_prop
      val source_nf_stopped = #source_nf_bounded_stops weighted_checked
      val publication_facts = proof_facts @ source_action_equations @
        [source_binding_exact, source_actions_definition, source_rows,
         source_actions_refine, final_actions_definition, final_action_refinement,
         source_length, source_wf, source_zero, final_length, final_wf, final_zero,
         source_nf_actions_definition, source_nf_refinement,
         source_nf_length, source_nf_wf, source_nf_shape, source_nf_stopped]
      val _ = Thm.consolidate publication_facts
      val _ = Comma_Proof_Dependency_Audit.require_native_clean
        (Local_Theory.target_of lthy3)
        "Weighted source and B32 action vectors" publication_facts
      val (_, lthy4) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_predecessor_stop242_checked", []),
          [predecessor]) lthy3
      val (_, lthy5) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_source_actions_refine", []),
          [source_actions_refine]) lthy4
      val (_, lthy6) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_b32_weighted_actions_refine", []),
          [final_action_refinement]) lthy5
      val (_, lthy7) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_source_actions_length", []),
          [source_length]) lthy6
      val (_, lthy8) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_source_actions_wellformed", []),
          [source_wf]) lthy7
      val (_, lthy9) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_source_actions_nonterminal_zero", []),
          [source_zero]) lthy8
      val (_, lthy10) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_b32_weighted_actions_length", []),
          [final_length]) lthy9
      val (_, lthy11) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_b32_weighted_actions_wellformed", []),
          [final_wf]) lthy10
      val (_, lthy12) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_b32_weighted_actions_nonterminal_zero", []),
          [final_zero]) lthy11
      val (_, lthy13) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_nf_actions_refine", []),
          [source_nf_refinement]) lthy12
      val (_, lthy14) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_nf_actions_length", []),
          [source_nf_length]) lthy13
      val (_, lthy15) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_nf_actions_wellformed", []),
          [source_nf_wf]) lthy14
      val (_, lthy16) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_nf_actions_shape", []),
          [source_nf_shape]) lthy15
      val (_, lthy17) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_nf_actions_stopped", []),
          [source_nf_stopped]) lthy16
      val _ = checkpoint "weighted CRT roots transported; source actions and Stop242 published"
    in lthy17 end
end

