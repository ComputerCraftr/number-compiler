(* Source-selected graph discovery.  Only local period slots are evaluated;
   exact source addresses bind an occurrence to an interned child-CID node. *)
structure Comma_Semantic_Graph_Constructor =
struct
  datatype edge = Goto of int | Live of int | Stop of int
  type node = {period: int, actions: edge list}
  type binding = {source: term, cid: int}
  type source_class = Comma_Semantic_Source_Ports.source_class
  type source_transition = Comma_Semantic_Source_Ports.source_transition
  type source_forward = Comma_Semantic_Source_Ports.source_forward
  type class_row = Comma_Semantic_Source_Ports.class_row
  type engine =
    {root: int -> int, compile: term -> int,
     initial_sources: term list,
     source_class: term -> source_class,
     validate_selection: source_class -> unit,
     class_row: term -> class_row option,
     source_forward: term -> source_forward option,
     nodes: unit -> (int * node) list, bindings: unit -> binding list,
     publish: local_theory -> local_theory * thm * thm * thm,
     stats: unit -> string,
     work: unit -> {transition_evaluations: int, completed_aliases: int,
       near_operator_reuses: int, near_application_transports: int,
       near_application_rows: int, near_application_row_reuses: int,
       near_action_class_reuses: int}}

  fun make_audit ctxt : engine =
    let
      val kernel = Comma_Fast_Kernel.make ctxt
      val endpoint = Comma_Decisive_Endpoint_Kernel.make ctxt (#context kernel)
      val evaluation = #context endpoint addsimps
        @{thms comma_source_continuation_base.simps
          comma_source_continuation_shift.simps comma_round_crossing_def
          comma_round_admitted.simps
          comma_sector_number.simps
          comma_semantic_b1_terminal_action_result.simps
          comma_offset_orbit_def comma_digit_orbit_sum_def
          comma_offset_representatives_def
          comma_semantic_future_initial_sources_def
          comma_c1_b1_entry_core_port_action_def
          comma_semantic_b1_source_port_action_def
          comma_semantic_b1_source_port_actions_def
          comma_semantic_b1_near_control_port_action_def
          comma_semantic_b1_next_port_action_def
          comma_semantic_b1_entry_near_port_action_def
          comma_semantic_b1_entry_near_terminal_def
          comma_finite_headroom_fast_correct[symmetric]
          comma_near_control_formula
          list.map append.simps upt_rec power2_eq_square of_nat_numeral of_nat_0
          of_nat_1 zmod_zminus1_eq_if zmod_zminus2_eq_if Let_def}
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun theorem_closed theorem =
        not (Term.is_open (Thm.prop_of theorem)) andalso
          null (Term.add_frees (Thm.prop_of theorem) []) andalso
          null (Term.add_vars (Thm.prop_of theorem) [])
      fun number term =
        let val (T, n) = HOLogic.dest_number term
        in if T = @{typ nat} andalso n >= 0 then n
          else error "Semantic graph expected a natural literal" end
      fun entry_chart_coordinates source =
        (case strip_comb source of
          (Const (name, _), [f, delta, offset]) =>
            if name = @{const_name Comma_Entry} andalso number delta = 0
            then SOME (number f, number offset) else NONE
        | _ => NONE)
      fun theorem_closed_no_premises theorem =
        Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) andalso theorem_closed theorem
      fun check_object_proof proof_context proposition facts message =
        let
          val theorem = Goal.prove proof_context [] [] proposition
            (fn {context, ...} =>
              HEADGOAL (Simplifier.asm_full_simp_tac (context addsimps facts)))
        in if theorem_closed_no_premises theorem andalso
            Thm.prop_of theorem aconv proposition then theorem
          else error message end
      val checked_object_proof =
        check_object_proof (Comma_Entry_Arithmetic.natural_context ctxt)
      fun equation_with extra expression =
        let
          val _ = if Term.is_open expression then
              error "Semantic graph source action request is not closed" else ()
          val context = evaluation addsimps extra
          val theorem = Simplifier.full_rewrite context (Thm.cterm_of context expression)
        in if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso theorem_closed theorem andalso
            Thm.term_of (Thm.lhs_of theorem) aconv expression then theorem
          else error "Semantic graph local equation lost source authority" end
      fun equation expression = equation_with [] expression
      val initial_sources_equation = equation @{term comma_semantic_future_initial_sources}
      val initial_sources =
        HOLogic.dest_list (Thm.term_of (Thm.rhs_of initial_sources_equation))
      val _ = if length initial_sources = 16 then ()
        else error "The registered initial source catalogue must contain sixteen charts"
      val offset_orbit_certificates = Unsynchronized.ref Inttab.empty
      val offset_orbit_hits = Unsynchronized.ref 0
      val offset_orbit_misses = Unsynchronized.ref 0
      fun value expression =
        (case strip_comb expression of
          (Const (name, _), [offset_term]) =>
            if name = @{const_name comma_offset_orbit} then
              let
                val offset = number offset_term
              in case Inttab.lookup (!offset_orbit_certificates) offset of
                SOME theorem =>
                  (offset_orbit_hits := !offset_orbit_hits + 1;
                   Thm.term_of (Thm.rhs_of theorem))
              | NONE =>
                  let
                    val _ = offset_orbit_misses := !offset_orbit_misses + 1
                    val theorem = equation expression
                    val _ = offset_orbit_certificates :=
                      Inttab.update (offset, theorem) (!offset_orbit_certificates)
                  in Thm.term_of (Thm.rhs_of theorem) end
              end
            else Thm.term_of (Thm.rhs_of (equation expression))
        | _ => Thm.term_of (Thm.rhs_of (equation expression)))
      val source_port_arguments =
        {ctxt=ctxt, equation=equation, equation_with=equation_with,
         checked_object_proof=checked_object_proof,
         entry_chart_coordinates=entry_chart_coordinates, number=number, nat=nat}
      val _ = Comma_Semantic_Near_Operator_Fixture.run source_port_arguments
      val source_ports = Comma_Semantic_Source_Ports.make source_port_arguments
      val classified_sources = Unsynchronized.ref
        (Termtab.empty: source_class Termtab.table)
      val class_rows = Unsynchronized.ref (Termtab.empty: class_row Termtab.table)
      val source_forwards = Unsynchronized.ref
        (Termtab.empty: source_forward option Termtab.table)
      fun source_shape source =
        (case strip_comb source of
          (Const (name, _), [f, delta, coordinate]) =>
            if (name = @{const_name Comma_Entry} orelse name = @{const_name Comma_Near})
                andalso number delta = 0 then (name, number f, number coordinate)
            else error "Semantic source is not in its normalized chart"
        | _ => error "Semantic graph source is not a literal chart")
      val bindings = Unsynchronized.ref (Termtab.empty: binding Termtab.table)
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val nodes = Unsynchronized.ref (Inttab.empty: node Inttab.table)
      val signatures = Unsynchronized.ref (Termtab.empty: int Termtab.table)
      val local_slots = Unsynchronized.ref 0
      val reused = Unsynchronized.ref 0
      val completed_aliases = Unsynchronized.ref 0
      val near_application_rows = Unsynchronized.ref 0
      val near_application_row_reuses = Unsynchronized.ref 0
      val near_action_class_reuses = Unsynchronized.ref 0
      (* Entry rows use their proved finite-period class key. Near rows use a
         separate exact ordered one-step action key; source applications and
         cycle markers remain keyed by the exact occurrence. *)
      fun row_key (source_class: source_class) =
        (case #kind (#shape source_class) of
          Comma_Semantic_Source_Ports.EntryClass => #application_key source_class
        | Comma_Semantic_Source_Ports.NearClass => #action_key source_class)
      fun minimum_period actions =
        let val n = length actions
          fun matches p = n mod p = 0 andalso
            List.all (fn j => nth actions j = nth actions (j mod p)) (0 upto (n-1))
        in the (find_first matches (1 upto n)) end
      fun intern actions =
        let val p = minimum_period actions
          val node = {period = p, actions = take p actions}
          fun edge_key (Goto cid) = HOLogic.mk_prod (nat 0, nat cid)
            | edge_key (Live root) = HOLogic.mk_prod (nat 1, nat root)
            | edge_key (Stop j) = HOLogic.mk_prod (nat 2, nat j)
          val key = HOLogic.mk_list (HOLogic.mk_prodT (@{typ nat}, @{typ nat}))
            (map edge_key (#actions node))
        in case Termtab.lookup (!signatures) key of
          SOME cid => (reused := !reused + 1; cid)
        | NONE => let val cid = Inttab.size (!nodes)
            val _ = nodes := Inttab.update (cid, node) (!nodes)
            val _ = signatures := Termtab.update (key, cid) (!signatures)
          in cid end end
      fun edge_of_action source phase action =
        let
          val (_, sector, _) = source_shape source
        in case strip_comb action of
          (Const (name, _), [next, shift]) =>
            if name = @{const_name Comma_Continuation_Goto} then
              let val (_, next_sector, _) = source_shape next
                val _ = if number shift = 0 andalso sector < next_sector
                  then () else error "Goto fails strict sector progress"
              in Goto (compile next) end
            else if name = @{const_name Comma_Continuation_Exit} then
              let val (kind, next_sector, offset) = source_shape next
                val _ = if kind = @{const_name Comma_Entry} andalso
                  next_sector = 1 andalso number shift = 1 andalso offset <= 90
                  then () else error "Live result lost its root binding"
                val root = number (value (@{term comma_offset_orbit} $ nat offset))
              in if root < 46 then Live root else error "Live root out of range" end
            else if name = @{const_name Comma_Continuation_Fork} then
              let val a = number next
              in if number shift = 0 andalso 2 <= a andalso a <= 9
                then Stop (a-2) else error "Fork is outside its exact local band" end
            else error "Unrecognized semantic continuation action"
        | (Const (name, _), [shift]) =>
            if name = @{const_name Comma_Continuation_Landmine} andalso
              number shift = 0 then Stop 8
            else error ("Unreduced local continuation: " ^
              Syntax.string_of_term ctxt action ^ " from " ^
              Syntax.string_of_term ctxt source ^ " phase=" ^ Int.toString phase)
        | _ => error "Invalid or unevaluated semantic continuation action"
        end
      and compile source =
        (case Termtab.lookup (!bindings) source of
          SOME item => #cid item
        | NONE =>
          let
            val source_class = #classify source_ports source
            val _ = classified_sources :=
              Termtab.update (source, source_class) (!classified_sources)
            val shape = #shape source_class
            val class_key = #key shape
            val application_key = #application_key source_class
            val reusable_row_key = row_key source_class
            val _ = if Termtab.defined (!active) application_key then
              error "Semantic source class graph contains a cycle" else ()
            val _ = active := Termtab.update (application_key, ()) (!active)
            fun bind_source cid =
              let
                val _ = bindings := Termtab.update
                  (source, {source=source, cid=cid}) (!bindings)
                val _ = if Termtab.size (!bindings) mod 32 = 0 then
                  Comma_Fast_Kernel.report ("semantic_sources=" ^
                    Int.toString (Termtab.size (!bindings)) ^ " class_slots=" ^
                    Int.toString (!local_slots) ^ " " ^ #stats endpoint ()) else ()
              in cid end
            fun build_from_class () =
              (case Termtab.lookup (!class_rows) reusable_row_key of
                SOME row =>
                  (if #kind shape = Comma_Semantic_Source_Ports.NearClass then
                     near_application_row_reuses :=
                       !near_application_row_reuses + 1
                   else ();
                   if #kind shape = Comma_Semantic_Source_Ports.NearClass then
                     near_action_class_reuses := !near_action_class_reuses + 1
                   else ();
                   bind_source (#cid row))
              | NONE =>
                  let
                    val period = #period shape
                    val _ = if period > 0 andalso 924 mod period = 0 then ()
                      else error "Semantic source class period is not an admitted divisor"
                    val (row_source, row_class) =
                      (case #kind shape of
                        Comma_Semantic_Source_Ports.NearClass => (source, source_class)
                      | Comma_Semantic_Source_Ports.EntryClass =>
                          let
                            val representative = #representative shape
                            val representative_class = #classify source_ports representative
                            val representative_shape = #shape representative_class
                            val _ = if Term.aconv (#key representative_shape, class_key) then ()
                              else error "Canonical representative did not resolve to its source class"
                          in (representative, representative_class) end)
                    val _ = if Term.aconv (row_key row_class, reusable_row_key) then ()
                      else error "Selected source row does not match its reusable action key"
                    val transitions = map (#transition source_ports row_class)
                      (0 upto (period - 1))
                    val actions = map #action transitions
                    val _ = if length actions = period then ()
                      else error "Semantic source class produced an incomplete transition row"
                    val slots = map_index (fn (phase, action) =>
                      (local_slots := !local_slots + 1;
                       edge_of_action row_source phase action)) actions
                    val cid = intern slots
                    val row : class_row =
                      {class_source=row_class, transitions=transitions,
                       application_key=application_key,
                       action_key= #action_key row_class,
                       actions=actions, cid=cid}
                    val _ = if #kind shape = Comma_Semantic_Source_Ports.NearClass then
                        near_application_rows := !near_application_rows + 1 else ()
                    val _ = class_rows := Termtab.update
                      (reusable_row_key, row) (!class_rows)
                  in bind_source cid end)
            fun build () =
              let val forward = #forward source_ports source
                  val _ = source_forwards :=
                    Termtab.update (source, forward) (!source_forwards)
              in (case forward of
                SOME {child, ...} =>
                  let
                    val cid = compile child
                    val result = bind_source cid
                    val _ = completed_aliases := !completed_aliases + 1
                  in result end
              | NONE =>
                  (case #kind shape of
                    Comma_Semantic_Source_Ports.EntryClass => build_from_class ()
                  | Comma_Semantic_Source_Ports.NearClass =>
                      (* Validate exact occurrence authority before looking up
                         a representative row under its action class. *)
                      (#validate_selection source_ports source_class;
                       build_from_class ())))
              end
            val attempt = Exn.capture build ()
            val _ = active := Termtab.delete application_key (!active)
          in Exn.release attempt end)
      val representatives_certificate = equation @{term comma_offset_representatives}
      val reps = HOLogic.dest_list
        (Thm.term_of (Thm.rhs_of representatives_certificate))
      fun classified_source source =
        (case Termtab.lookup (!classified_sources) source of
          SOME result => result
        | NONE => error "Published source has no pre-transition class certificate")
      fun class_row_for_source source =
        let val class_source = classified_source source
            val application_key = row_key class_source
        in Termtab.lookup (!class_rows) application_key
        end
      fun forward_for_source source =
        (case Termtab.lookup (!source_forwards) source of
          SOME result => result
        | NONE => NONE)
      fun root i =
        if 0 <= i andalso i < length reps then
          compile (@{term Comma_Entry} $ nat 1 $ nat 0 $ nth reps i)
        else error "Semantic root outside representative domain"
      fun root_ids () = map root (0 upto (length reps - 1))
      fun edge_term (Goto cid) =
            Const (@{const_name Comma_Semantic_B1_Goto},
              @{typ nat} --> @{typ comma_semantic_b1_edge}) $ nat cid
        | edge_term (Live root_id) =
            Const (@{const_name Comma_Semantic_B1_Live_Edge},
              @{typ nat} --> @{typ comma_semantic_b1_edge}) $ nat root_id
        | edge_term (Stop position) =
            Const (@{const_name Comma_Semantic_B1_Stop_Edge},
              @{typ nat} --> @{typ comma_semantic_b1_edge}) $ nat position
      fun mapped_list function_name inputT outputT function input =
        let
          val mapT = (inputT --> outputT) --> HOLogic.listT inputT -->
            HOLogic.listT outputT
        in Const (function_name, mapT) $ function $ input end
      fun publish lthy =
        let
          val started = Time.now ()
          fun report_checkpoint stage details =
            Comma_Fast_Kernel.report
              ("semantic graph publication stage=" ^ stage ^
                " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started ^
                (if details = "" then "" else " " ^ details))
          val _ = report_checkpoint "publish-enter"
            ("sources=" ^ Int.toString (Termtab.size (!bindings)) ^
              " nodes=" ^ Int.toString (Inttab.size (!nodes)) ^
              " slots=" ^ Int.toString (!local_slots))
          val bindingT = @{typ comma_semantic_b1_binding}
          val nodeT = @{typ comma_semantic_b1_node}
          val edgeT = @{typ comma_semantic_b1_edge}
          val positionT = @{typ comma_finite_position}
          val natT = @{typ nat}
          val binding_pairT = HOLogic.mk_prodT (positionT, natT)
          val binding_entries = map #2 (Termtab.dest (!bindings))
          val binding_pair_values = HOLogic.mk_list binding_pairT
            (map (fn ({source, cid}: binding) => HOLogic.mk_prod (source, nat cid))
              binding_entries)
          val binding_pairs_define_started = Time.now ()
          val ((binding_pairs_local, (_, binding_pairs_definition_local)),
              binding_pairs_lthy) =
            Local_Theory.define
              ((Binding.name "comma_semantic_graph_binding_pairs", NoSyn),
                ((Binding.name "comma_semantic_graph_binding_pairs_def", []),
                  binding_pair_values))
              lthy
          val binding_pairs_morphism = Local_Theory.target_morphism binding_pairs_lthy
          val binding_pairs = Morphism.term binding_pairs_morphism binding_pairs_local
          val binding_pairs_definition =
            Morphism.thm binding_pairs_morphism binding_pairs_definition_local
          val _ = report_checkpoint "binding-pairs-defined"
            ("count=" ^ Int.toString (length binding_entries) ^
              " stage_ms=" ^ Comma_Proof_Profile.elapsed_ms binding_pairs_define_started)
          val binding_from_pair =
            @{term comma_semantic_b1_binding_from_pair}
          val binding_list = mapped_list @{const_name map} binding_pairT bindingT
            binding_from_pair binding_pairs
          val bindings_define_started = Time.now ()
          val ((bindings_local, (_, bindings_definition_local)), bindings_lthy) =
            Local_Theory.define
              ((Binding.name "comma_semantic_graph_bindings", NoSyn),
                ((Binding.name "comma_semantic_graph_bindings_def", []), binding_list))
              binding_pairs_lthy
          val _ = report_checkpoint "bindings-defined"
            ("stage_ms=" ^ Comma_Proof_Profile.elapsed_ms bindings_define_started)
          val bindings_morphism = Local_Theory.target_morphism bindings_lthy
          val bindings_constant = Morphism.term bindings_morphism bindings_local
          val bindings_definition = Morphism.thm bindings_morphism bindings_definition_local
          val node_entries = Inttab.dest (!nodes)
          val node_ids = map #1 node_entries
          val expected_node_ids = 0 upto (length node_entries - 1)
          val _ = if node_ids = expected_node_ids then ()
            else error "Semantic graph node IDs are not dense in publication order"
          val node_from_data = @{term comma_semantic_b1_node_from_data}
          (* Keep one literal list of checked node rows.  A mapped data table
             makes every selected lookup reopen the full map over all nodes;
             constructor heads let the selected-list conversion certify just
             the requested row without creating a second published table. *)
          fun node_value (cid, {period, actions}: node) =
            let
              val action_list = HOLogic.mk_list edgeT (map edge_term actions)
              val row_data = HOLogic.mk_prod
                (HOLogic.mk_prod (nat cid, nat period), action_list)
            in node_from_data $ row_data end
          val node_values = map node_value node_entries
          val node_list = HOLogic.mk_list nodeT node_values
          val nodes_define_started = Time.now ()
          val ((nodes_local, (_, nodes_definition_local)), nodes_lthy) =
            Local_Theory.define
              ((Binding.name "comma_semantic_graph_nodes", NoSyn),
                ((Binding.name "comma_semantic_graph_nodes_def", []), node_list))
              bindings_lthy
          val _ = report_checkpoint "nodes-defined"
            ("stage_ms=" ^ Comma_Proof_Profile.elapsed_ms nodes_define_started)
          val nodes_morphism = Local_Theory.target_morphism nodes_lthy
          val nodes_constant = Morphism.term nodes_morphism nodes_local
          val nodes_definition = Morphism.thm nodes_morphism nodes_definition_local
          val node_extent = length node_entries
          val node_row_certificates = Comma_Semantic_Graph_Publication.certify_node_rows
            {ctxt=Local_Theory.target_of nodes_lthy,
             nodes_constant=nodes_constant, nodes_definition=nodes_definition,
             nodeT=nodeT, natT=natT, node_values=node_values,
             node_extent=node_extent}
          val node_size_prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (HOLogic.size_const (HOLogic.listT nodeT) $ nodes_constant,
              nat node_extent))
          val node_size_started = Time.now ()
          val node_size_context = Local_Theory.target_of nodes_lthy addsimps
            (nodes_definition :: @{thms comma_semantic_b1_node_from_data_def
              comma_semantic_b1_node.select_convs list.map})
          val node_size = Goal.prove (Local_Theory.target_of nodes_lthy) [] []
            node_size_prop
            (fn _ => HEADGOAL (Simplifier.asm_full_simp_tac node_size_context))
          val _ = report_checkpoint "node-extent-finished"
            ("count=" ^ Int.toString node_extent ^
              " stage_ms=" ^ Comma_Proof_Profile.elapsed_ms node_size_started)
          val _ = if Thm.nprems_of node_size = 0 andalso
              null (Thm.hyps_of node_size) andalso null (Thm.tpairs_of node_size) andalso
              theorem_closed node_size andalso Thm.prop_of node_size aconv node_size_prop
            then () else error "Semantic graph node table extent did not check"
          val node_ids_explicit = HOLogic.mk_list natT (map nat expected_node_ids)
          val node_ids_explicit_expression =
            let
              val selector = Const (@{const_name comma_semantic_b1_node_cid},
                nodeT --> natT)
              val mapped = Const (@{const_name map},
                (nodeT --> natT) --> HOLogic.listT nodeT --> HOLogic.listT natT) $
                selector $ nodes_constant
            in HOLogic.mk_Trueprop (HOLogic.mk_eq (mapped, node_ids_explicit)) end
          val dense_nodes_started = Time.now ()
          val _ = report_checkpoint "dense-nodes-start" ""
          val dense_nodes_explicit = Goal.prove (Local_Theory.target_of nodes_lthy) [] []
            node_ids_explicit_expression
            (fn {context, ...} =>
              HEADGOAL (Simplifier.asm_full_simp_tac (context addsimps
                ([nodes_definition] @ @{thms comma_semantic_b1_node_from_data_def
                  comma_semantic_b1_node.select_convs list.map}))))
          val _ = if Thm.nprems_of dense_nodes_explicit = 0 andalso
              null (Thm.hyps_of dense_nodes_explicit) andalso
              null (Thm.tpairs_of dense_nodes_explicit) andalso
              theorem_closed dense_nodes_explicit andalso
              Thm.prop_of dense_nodes_explicit aconv node_ids_explicit_expression
            then () else error "Semantic graph node IDs failed their dense-index proof"
          val _ = report_checkpoint "dense-node-explicit-finished"
            ("stage_ms=" ^ Comma_Proof_Profile.elapsed_ms dense_nodes_started)
          val node_range = Const (@{const_name upt}, natT --> natT -->
            HOLogic.listT natT) $ nat 0 $
            (HOLogic.size_const (HOLogic.listT nodeT) $ nodes_constant)
          val range_bridge_prop = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (node_ids_explicit, node_range))
          val range_bridge_started = Time.now ()
          val range_bridge = Goal.prove (Local_Theory.target_of nodes_lthy) [] []
            range_bridge_prop
            (fn {context, ...} =>
              HEADGOAL (Simplifier.asm_full_simp_tac
                (context addsimps [node_size, @{thm upt_rec}])))
          val _ = if Thm.nprems_of range_bridge = 0 andalso
              null (Thm.hyps_of range_bridge) andalso
              null (Thm.tpairs_of range_bridge) andalso theorem_closed range_bridge andalso
              Thm.prop_of range_bridge aconv range_bridge_prop
            then () else error "Semantic graph explicit IDs did not match the canonical range"
          val dense_nodes_prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (Const (@{const_name map},
              (nodeT --> natT) --> HOLogic.listT nodeT --> HOLogic.listT natT) $
              Const (@{const_name comma_semantic_b1_node_cid}, nodeT --> natT) $
              nodes_constant, node_range))
          val dense_nodes_meta = Thm.transitive
            (dense_nodes_explicit RS @{thm eq_reflection})
            (range_bridge RS @{thm eq_reflection})
          val dense_nodes = dense_nodes_meta RS @{thm meta_eq_to_obj_eq}
          val _ = if Thm.nprems_of dense_nodes = 0 andalso
              null (Thm.hyps_of dense_nodes) andalso
              null (Thm.tpairs_of dense_nodes) andalso theorem_closed dense_nodes andalso
              Thm.prop_of dense_nodes aconv dense_nodes_prop
            then () else error "Semantic graph node IDs failed their upt-density bridge"
          val _ = report_checkpoint "dense-nodes-finished"
            ("explicit_ms=" ^ Comma_Proof_Profile.elapsed_ms dense_nodes_started ^
              " range_ms=" ^ Comma_Proof_Profile.elapsed_ms range_bridge_started)
          val (_, dense_lthy) = Local_Theory.note
            ((Binding.name "comma_semantic_graph_node_ids_dense", []), [dense_nodes])
            nodes_lthy
          val root_id_list = HOLogic.mk_list natT (root_ids () |> map nat)
          val root_ids_define_started = Time.now ()
          val ((root_ids_local, (_, root_ids_definition_local)), root_ids_lthy) =
            Local_Theory.define
              ((Binding.name "comma_semantic_graph_root_ids", NoSyn),
                ((Binding.name "comma_semantic_graph_root_ids_def", []), root_id_list))
              dense_lthy
          val _ = report_checkpoint "root-ids-defined"
            ("stage_ms=" ^ Comma_Proof_Profile.elapsed_ms root_ids_define_started)
          val root_ids_morphism = Local_Theory.target_morphism root_ids_lthy
          val root_ids_constant = Morphism.term root_ids_morphism root_ids_local
          val root_ids_definition = Morphism.thm root_ids_morphism root_ids_definition_local
          val graph_request = @{term comma_semantic_b1_graph_completed_valid} $
            bindings_constant $ nodes_constant
          val proposition = HOLogic.mk_Trueprop graph_request
          val source_value = Free ("source", positionT)
          val cid_value = Free ("cid", natT)
          val binding_value = Free ("binding", bindingT)
          val setT = HOLogic.mk_setT bindingT
          val bindings_set = Const (@{const_name set},
            HOLogic.listT bindingT --> setT) $ bindings_constant
          val field_source = Const (@{const_name comma_semantic_b1_binding_source},
            bindingT --> positionT) $ binding_value
          val field_cid = Const (@{const_name comma_semantic_b1_binding_cid},
            bindingT --> natT) $ binding_value
          val root_binding_body =
            Const (@{const_name Bex}, setT -->
              (bindingT --> HOLogic.boolT) --> HOLogic.boolT) $ bindings_set $
              Term.lambda binding_value
                (HOLogic.mk_conj (HOLogic.mk_eq (field_source, source_value),
                  HOLogic.mk_eq (field_cid, cid_value)))
          val root_binding_predicate =
            Term.lambda source_value (Term.lambda cid_value root_binding_body)
          val root_index = Free ("root_index", natT)
          val representative_at = Const (@{const_name nth},
            HOLogic.listT natT --> natT --> natT) $
            @{term comma_offset_representatives} $ root_index
          val root_source = Term.lambda root_index
            (@{term Comma_Entry} $ nat 1 $ nat 0 $ representative_at)
          val root_range = Const (@{const_name upt}, natT --> natT -->
            HOLogic.listT natT) $ nat 0 $ nat 46
          val source_roots = Const (@{const_name map},
            (natT --> positionT) --> HOLogic.listT natT --> HOLogic.listT positionT) $
            root_source $ root_range
          val root_list_relation = Const (@{const_name list_all2},
            (positionT --> natT --> HOLogic.boolT) -->
              HOLogic.listT positionT --> HOLogic.listT natT --> HOLogic.boolT) $
              root_binding_predicate $ source_roots $ root_ids_constant
          val root_exact_prop = HOLogic.mk_Trueprop root_list_relation
          val root_started = Time.now ()
          val root_values = root_ids ()
          fun prove_closed_in context proposition =
            check_object_proof context proposition []
              "Semantic graph publisher fact is not closed"
          fun prove_closed proposition =
            prove_closed_in (Local_Theory.target_of root_ids_lthy) proposition
          fun root_source_value i =
            @{term Comma_Entry} $ nat 1 $ nat 0 $ nth reps i
          fun binding_position source =
            let
              fun locate _ [] = error "Semantic root has no published binding"
                | locate index ((item: binding) :: rest) =
                    if #source item aconv source then index else locate (index + 1) rest
            in locate 0 binding_entries end
          val binding_pair_index = Free ("binding_pair_index", natT)
          val binding_pair_selection_pattern = Const (@{const_name nth},
            HOLogic.listT binding_pairT --> natT --> binding_pairT) $
              binding_pairs $ binding_pair_index
          val {procedure = binding_pair_procedure,
              stats = binding_pair_selection_stats, ...} =
            Comma_Selected_List_Conversion.make
              {ctxt = Local_Theory.target_of root_ids_lthy,
               name = "semantic_graph_bindings",
               root_definition = binding_pairs_definition,
               table_pattern = binding_pair_selection_pattern,
               extents = [length binding_entries]}
          val pair_context = Local_Theory.target_of root_ids_lthy
            addsimps [binding_pairs_definition]
            |> Simplifier.add_proc binding_pair_procedure
          val _ = report_checkpoint "binding-pair-selection-installed"
            (binding_pair_selection_stats ())
          val binding_pairs_size_prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (HOLogic.size_const (HOLogic.listT binding_pairT) $ binding_pairs,
              nat (length binding_entries)))
          val binding_pairs_size_started = Time.now ()
          val binding_pairs_size = prove_closed_in pair_context binding_pairs_size_prop
          val _ = report_checkpoint "binding-pair-extent-finished"
            ("count=" ^ Int.toString (length binding_entries) ^
              " stage_ms=" ^ Comma_Proof_Profile.elapsed_ms binding_pairs_size_started)
          fun prove_pair position source cid =
            let
              val position_term = nat position
              val pair_at = Const (@{const_name nth},
                HOLogic.listT binding_pairT --> natT --> binding_pairT) $
                binding_pairs $ position_term
              val pair_value = HOLogic.mk_prod (source, nat cid)
            in prove_closed_in pair_context (HOLogic.mk_Trueprop
              (HOLogic.mk_eq (pair_at, pair_value))) end
          fun prove_pair_bound position =
            let
              val position_term = nat position
              val index_prop = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less}
                (position_term, HOLogic.size_const (HOLogic.listT binding_pairT) $
                  binding_pairs))
            in prove_closed_in (pair_context addsimps [binding_pairs_size])
              index_prop end
          val pair_first = Const (@{const_name fst}, binding_pairT --> positionT)
          val pair_sources = mapped_list @{const_name map} binding_pairT positionT
            pair_first binding_pairs
          val distinct_pairs_prop = HOLogic.mk_Trueprop
            (Const (@{const_name distinct}, HOLogic.listT positionT --> HOLogic.boolT) $
              pair_sources)
          val distinct_started = Time.now ()
          val _ = report_checkpoint "distinct-source-keys-start" ""
          val distinct_pairs = prove_closed_in pair_context distinct_pairs_prop
          val _ = report_checkpoint "distinct-source-keys-finished"
            ("stage_ms=" ^ Comma_Proof_Profile.elapsed_ms distinct_started)
          val pair_bound_elapsed = Unsynchronized.ref Time.zeroTime
          val pair_equality_elapsed = Unsynchronized.ref Time.zeroTime
          val binding_pair_certificates = map_index
            (fn (index, (item: binding)) =>
              let
                val bound_started = Time.now ()
                val position_bound = prove_pair_bound index
                val _ = pair_bound_elapsed := Time.+ (!pair_bound_elapsed,
                  Time.- (Time.now (), bound_started))
                val equality_started = Time.now ()
                val selected_pair = prove_pair index (#source item) (#cid item)
                val _ = pair_equality_elapsed := Time.+ (!pair_equality_elapsed,
                  Time.- (Time.now (), equality_started))
                val completed = index + 1
                val _ = if completed mod 32 = 0 orelse
                    completed = length binding_entries then
                  report_checkpoint "binding-pairs-progress"
                    ("rows=" ^ Int.toString completed ^
                      " total=" ^ Int.toString (length binding_entries) ^
                      " bound_cumulative_ms=" ^
                        LargeInt.toString (Time.toMilliseconds (!pair_bound_elapsed)) ^
                      " equality_cumulative_ms=" ^
                        LargeInt.toString (Time.toMilliseconds (!pair_equality_elapsed)))
                  else ()
              in (position_bound, selected_pair) end)
            binding_entries
          val _ = report_checkpoint "binding-pairs-finished"
            ("rows=" ^ Int.toString (length binding_entries) ^
              " bound_cumulative_ms=" ^
                LargeInt.toString (Time.toMilliseconds (!pair_bound_elapsed)) ^
              " equality_cumulative_ms=" ^
                LargeInt.toString (Time.toMilliseconds (!pair_equality_elapsed)) ^
              " " ^ binding_pair_selection_stats ())
          val lookup_equations_started = Time.now ()
          val binding_lookup_equations = map_index
            (fn (index, _) =>
              let val (position_bound, selected_pair) =
                    nth binding_pair_certificates index
              in @{thm comma_semantic_graph_binding_lookup_at_index}
                OF [distinct_pairs, position_bound, selected_pair] end)
            binding_entries
          val _ = report_checkpoint "binding-lookups-finished"
            ("count=" ^ Int.toString (length binding_lookup_equations) ^
              " stage_ms=" ^ Comma_Proof_Profile.elapsed_ms lookup_equations_started)
          val cid_witnesses_started = Time.now ()
          val binding_cid_witnesses = map_index
            (fn (index, _) =>
              let val (position_bound, selected_pair) =
                    nth binding_pair_certificates index
              in @{thm comma_semantic_graph_binding_cid_at_index}
                OF [position_bound, selected_pair] end)
            binding_entries
          val _ = report_checkpoint "binding-cid-witnesses-finished"
            ("count=" ^ Int.toString (length binding_cid_witnesses) ^
              " stage_ms=" ^ Comma_Proof_Profile.elapsed_ms cid_witnesses_started)
          val node_ids_list = Const (@{const_name upt}, natT --> natT -->
            HOLogic.listT natT) $ nat 0 $
            (HOLogic.size_const (HOLogic.listT nodeT) $ nodes_constant)
          val node_distinct_started = Time.now ()
          val node_ids_distinct_prop = HOLogic.mk_Trueprop
            (Const (@{const_name distinct}, HOLogic.listT natT --> HOLogic.boolT) $
              node_ids_list)
          val node_ids_distinct = prove_closed_in
            (Local_Theory.target_of root_ids_lthy addsimps
              [@{thm distinct_upt}, node_size]) node_ids_distinct_prop
          val node_distinct = @{thm comma_semantic_graph_node_ids_dense_distinct}
            OF [dense_nodes, node_ids_distinct]
          val _ = report_checkpoint "node-distinct-finished"
            ("stage_ms=" ^ Comma_Proof_Profile.elapsed_ms node_distinct_started)
          val node_bound_elapsed = Unsynchronized.ref Time.zeroTime
          val node_selected_elapsed = Unsynchronized.ref Time.zeroTime
          val node_index_elapsed = Unsynchronized.ref Time.zeroTime
          val node_index_started = Time.now ()
          val _ = report_checkpoint "node-index-certificates-start"
            ("count=" ^ Int.toString (length node_entries))
          fun node_index_facts (index, _) =
            let
              val row_started = Time.now ()
              val index_term = nat index
              val node_length = HOLogic.size_const (HOLogic.listT nodeT) $ nodes_constant
              val bound_started = Time.now ()
              val index_bound = prove_closed_in
                (Local_Theory.target_of root_ids_lthy addsimps [node_size])
                (HOLogic.mk_Trueprop
                  (HOLogic.mk_binrel @{const_name less} (index_term, node_length)))
              val _ = node_bound_elapsed := Time.+ (!node_bound_elapsed,
                Time.- (Time.now (), bound_started))
              val selected_started = Time.now ()
              val selected = prove_closed_in
                (Local_Theory.target_of root_ids_lthy addsimps [node_size, index_bound])
                (HOLogic.mk_Trueprop
                (HOLogic.mk_eq (Const (@{const_name nth},
                  HOLogic.listT natT --> natT --> natT) $ node_ids_list $ index_term,
                  index_term)))
              val _ = node_selected_elapsed := Time.+ (!node_selected_elapsed,
                Time.- (Time.now (), selected_started))
              val node_id = @{thm comma_semantic_graph_node_id_at_index}
                OF [dense_nodes, index_bound, selected]
              val node_lookup = @{thm comma_semantic_graph_node_lookup_at_index}
                OF [node_distinct, index_bound, node_id]
              val _ = node_index_elapsed := Time.+ (!node_index_elapsed,
                Time.- (Time.now (), row_started))
              val completed = index + 1
              val _ = if completed mod 32 = 0 orelse completed = length node_entries then
                report_checkpoint "node-index-certificates-progress"
                  ("rows=" ^ Int.toString completed ^
                    " total=" ^ Int.toString (length node_entries) ^
                    " bound_cumulative_ms=" ^
                      LargeInt.toString (Time.toMilliseconds (!node_bound_elapsed)) ^
                    " selected_cumulative_ms=" ^
                      LargeInt.toString (Time.toMilliseconds (!node_selected_elapsed)) ^
                    " all_cumulative_ms=" ^
                      LargeInt.toString (Time.toMilliseconds (!node_index_elapsed)))
                else ()
            in (index_bound, node_id, node_lookup) end
          val node_index_certificates = map_index node_index_facts node_entries
          val _ = report_checkpoint "node-index-certificates-finished"
            ("rows=" ^ Int.toString (length node_index_certificates) ^
              " bound_cumulative_ms=" ^
                LargeInt.toString (Time.toMilliseconds (!node_bound_elapsed)) ^
              " selected_cumulative_ms=" ^
                LargeInt.toString (Time.toMilliseconds (!node_selected_elapsed)) ^
              " all_cumulative_ms=" ^
                LargeInt.toString (Time.toMilliseconds (!node_index_elapsed)) ^
              " stage_ms=" ^ Comma_Proof_Profile.elapsed_ms node_index_started)
          val indexed_node_lookups = map #3 node_index_certificates
          val node_lookup_equations =
            Comma_Semantic_Graph_Publication.concretize_node_lookups
              {ctxt=Local_Theory.target_of root_ids_lthy,
               nodes_constant=nodes_constant, nodeT=nodeT, natT=natT,
               node_values=node_values, node_rows=node_row_certificates,
               indexed_lookups=indexed_node_lookups}
          fun root_binding_witness (root, cid) =
            let
              val source = root_source_value root
              val position = binding_position source
              val (position_bound, selected_pair) =
                nth binding_pair_certificates position
              val entry = nth binding_entries position
              val _ = if #source entry aconv source andalso #cid entry = cid then ()
                else error "Root binding differs from its certified table row"
              val indexed_binding = @{thm comma_semantic_graph_binding_at_index}
                OF [position_bound, selected_pair]
              val point_body = Term.subst_free
                [(source_value, source), (cid_value, nat cid)] root_binding_body
              val point_prop = HOLogic.mk_Trueprop point_body
              val witness = Goal.prove (Local_Theory.target_of root_ids_lthy) [] []
                point_prop
                (fn {context, ...} =>
                  HEADGOAL (Simplifier.asm_full_simp_tac
                    (put_simpset HOL_basic_ss context addsimps
                      [bindings_definition, indexed_binding])))
              val _ = if Thm.nprems_of witness = 0 andalso
                  null (Thm.hyps_of witness) andalso null (Thm.tpairs_of witness) andalso
                  theorem_closed witness andalso Thm.prop_of witness aconv point_prop
                then () else error "Root binding is not proved by its indexed source row"
            in witness end
          val root_witnesses_started = Time.now ()
          val _ = report_checkpoint "root-witnesses-start" ""
          val root_binding_witnesses =
            map root_binding_witness (map_index I root_values)
          val _ = report_checkpoint "root-witnesses-finished"
            ("count=" ^ Int.toString (length root_binding_witnesses) ^
              " stage_ms=" ^ Comma_Proof_Profile.elapsed_ms root_witnesses_started)
          val root_exact_started = Time.now ()
          val root_exact = Goal.prove (Local_Theory.target_of root_ids_lthy) [] []
            root_exact_prop
            (fn {context, ...} =>
              let
                (* Use the existing bounded natural-arithmetic context: it
                   decides the upt bounds while preserving canonical literal
                   roots, so the indexed witnesses retain their exact source
                   terms.  Avoid the ambient graph simplifier here. *)
                val root_context = Comma_Entry_Arithmetic.natural_context context
                  addsimps (root_ids_definition ::
                    @{thms list_all2_Cons list_all2_Nil list.map upt_rec
                      nth_Cons'} @
                    representatives_certificate :: root_binding_witnesses)
              in ALLGOALS (asm_full_simp_tac root_context) end)
          val _ = if Thm.nprems_of root_exact = 0 andalso
              null (Thm.hyps_of root_exact) andalso
              null (Thm.tpairs_of root_exact) andalso theorem_closed root_exact andalso
              Thm.prop_of root_exact aconv root_exact_prop then ()
            else error "Semantic graph root IDs are not bound to their exact sources"
          val _ = report_checkpoint "root-exact-finished"
            ("stage_ms=" ^ Comma_Proof_Profile.elapsed_ms root_exact_started)
          val _ = Comma_Fast_Kernel.report
            ("semantic graph publication component=root-bindings elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms root_started ^ " checked=true")
          val root_coverage = @{thm comma_semantic_graph_root_coverage_from_list_all2}
            OF [root_exact]
          val root_coverage_checked = Thm.nprems_of root_coverage = 0 andalso
            null (Thm.hyps_of root_coverage) andalso
            null (Thm.tpairs_of root_coverage) andalso theorem_closed root_coverage
          val _ = if root_coverage_checked then ()
            else error "Semantic graph root coverage did not follow from exact root bindings"
          val graph_definition_context = put_simpset HOL_basic_ss
            (Local_Theory.target_of root_ids_lthy) addsimps
              @{thms comma_semantic_b1_graph_completed_valid_def}
          val graph_definition_equation = Simplifier.rewrite graph_definition_context
            (Thm.cterm_of graph_definition_context proposition)
          val graph_definition_checked = Thm.nprems_of graph_definition_equation = 0 andalso
            null (Thm.hyps_of graph_definition_equation) andalso
            null (Thm.tpairs_of graph_definition_equation) andalso
            theorem_closed graph_definition_equation andalso
            Thm.term_of (Thm.lhs_of graph_definition_equation) aconv proposition
          val _ = if graph_definition_checked then ()
            else error "Semantic graph definition did not preserve its closed request"
          val expanded_graph = Thm.term_of (Thm.rhs_of graph_definition_equation)
            |> HOLogic.dest_Trueprop
          val graph_components = HOLogic.dest_conj expanded_graph
          val _ = if length graph_components = 5 then ()
            else error "Semantic graph validity no longer has five checked components"
          val root_component = HOLogic.mk_Trueprop (List.nth (graph_components, 4))
          val _ = if Thm.prop_of root_coverage aconv root_component then ()
            else error "Exact root bindings do not match the graph root-coverage contract"
          fun source_distinct_component term =
            let
              val proposition = HOLogic.mk_Trueprop term
              val source_context = put_simpset HOL_basic_ss
                (Local_Theory.target_of root_ids_lthy) addsimps
                  [bindings_definition,
                   @{thm comma_semantic_graph_binding_sources_from_pairs}]
              val equation = Simplifier.rewrite source_context
                (Thm.cterm_of source_context proposition)
              val expected = Thm.prop_of distinct_pairs
              val reduced = Thm.term_of (Thm.rhs_of equation)
              val _ = if Thm.term_of (Thm.lhs_of equation) aconv proposition andalso
                  reduced aconv expected then ()
                else error ("Source distinctness does not reduce to its checked pair table; " ^
                  XML.content_of (YXML.parse_body
                    (Syntax.string_of_term source_context reduced)))
            in Thm.equal_elim (Thm.symmetric equation) distinct_pairs end
          val _ = Comma_Fast_Kernel.report
            ("semantic graph publication stage=components-start bindings=" ^
              Int.toString (Termtab.size (!bindings)) ^ " nodes=" ^
              Int.toString (Inttab.size (!nodes)) ^ " port_slots=" ^
              Int.toString (!local_slots))
          val binding_rows = map (fn ({source, cid}: binding) => (source, cid))
            binding_entries
          val binding_component = List.nth (graph_components, 2)
          val binding_rows_theorem =
            Comma_Semantic_Graph_Publication.certify_binding_rows
              {ctxt=Local_Theory.target_of root_ids_lthy,
               component=binding_component, bindingT=bindingT, natT=natT,
               bindings_constant=bindings_constant, nodes_constant=nodes_constant,
               bindings_definition=bindings_definition,
               binding_pairs_definition=binding_pairs_definition,
               rows=binding_rows, source_class=classified_source,
               class_row=class_row_for_source,
               source_forward=forward_for_source,
               binding_lookup_equations=binding_lookup_equations,
               node_lookup_equations=node_lookup_equations,
               orbit_equations=map #2 (Inttab.dest (!offset_orbit_certificates))}
          val node_cids = map #1 node_entries
          val node_children = map (fn (_, ({actions, ...}: node)) =>
            List.mapPartial (fn Goto child => SOME child | _ => NONE) actions)
            node_entries
          val node_coverage_component = List.nth (graph_components, 3)
          val node_coverage_theorem =
            Comma_Semantic_Graph_Publication.certify_node_coverage
              {ctxt=Local_Theory.target_of root_ids_lthy,
               component=node_coverage_component, nodeT=nodeT,
               bindingT=bindingT, natT=natT,
               bindings_constant=bindings_constant,
               bindings_definition=bindings_definition,
               nodes_constant=nodes_constant, nodes_definition=nodes_definition,
               node_values=node_values, node_cids=node_cids,
               node_children=node_children, rows=binding_rows,
               binding_cid_witnesses=binding_cid_witnesses,
               node_lookup_equations=node_lookup_equations}
          val checked_components =
            map_index (fn (index, term) =>
              if index = 0 then source_distinct_component term
              else if index = 1 then
                let
                  val proposition = HOLogic.mk_Trueprop term
                  val _ = if Thm.prop_of node_distinct aconv proposition then ()
                    else error "Node distinctness differs from the checked dense-ID certificate"
                in node_distinct end
              else if index = 2 then
                let
                  val proposition = HOLogic.mk_Trueprop term
                  val _ = if Thm.prop_of binding_rows_theorem aconv proposition then ()
                    else error "Binding-row certificates changed the graph-valid component"
                in binding_rows_theorem end
              else if index = 3 then
                let
                  val proposition = HOLogic.mk_Trueprop term
                  val _ = if Thm.prop_of node_coverage_theorem aconv proposition then ()
                    else error "Node-coverage certificates changed the graph-valid component"
                in node_coverage_theorem end
              else if index = 4 then root_coverage
              else error "Unexpected semantic graph validity component")
              graph_components
          fun conjoin [theorem] = theorem
            | conjoin (head :: tail) = @{thm conjI} OF [head, conjoin tail]
            | conjoin [] = error "Semantic graph has no validity components"
          val component_theorem = conjoin checked_components
          val expanded_component_prop = HOLogic.mk_Trueprop expanded_graph
          val _ = if Thm.prop_of component_theorem aconv expanded_component_prop then ()
            else error "Checked semantic graph components have unexpected conjunction shape"
          val graph_theorem = Thm.equal_elim
            (Thm.symmetric graph_definition_equation) component_theorem
          val _ = if Thm.nprems_of graph_theorem = 0 andalso
              null (Thm.hyps_of graph_theorem) andalso
              null (Thm.tpairs_of graph_theorem) andalso theorem_closed graph_theorem andalso
              Thm.prop_of graph_theorem aconv proposition then ()
            else error "Semantic graph validity theorem is not the exact closed graph contract"
          val _ = Comma_Fast_Kernel.report
            "semantic graph publication stage=graph-note-start"
          val graph_note = Local_Theory.note
            ((Binding.name "comma_semantic_graph_valid_checked", []), [graph_theorem])
            root_ids_lthy
          val (_, checked_lthy) = graph_note
          val _ = Comma_Fast_Kernel.report
            "semantic graph publication stage=graph-note-finished"
          val node_lookup_note_started = Time.now ()
          val (_, node_lookup_lthy) = Local_Theory.note
            ((Binding.name "comma_semantic_graph_node_lookup_equations", []),
              node_lookup_equations) checked_lthy
          val _ = Comma_Fast_Kernel.report
            ("semantic graph publication stage=node-lookup-note-finished elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms node_lookup_note_started)
          val root_note_started = Time.now ()
          val (_, final_lthy) = Local_Theory.note
            ((Binding.name "comma_semantic_graph_root_binding_exact", []), [root_exact])
            node_lookup_lthy
          val _ = Comma_Fast_Kernel.report
            ("semantic graph publication stage=root-note-finished elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms root_note_started)
          val initial_source_publish_started = Time.now ()
          val initial_source_ids_published_lthy =
            Comma_Semantic_Graph_Publication.publish_initial_source_ids
              {lthy=final_lthy,
               source_list = @{term comma_semantic_future_initial_sources},
               source_list_equation=initial_sources_equation,
               sources=initial_sources,
               bindings_constant=bindings_constant,
               bindings_definition=bindings_definition,
               binding_rows=binding_rows,
               binding_lookup_equations=binding_lookup_equations,
               positionT=positionT, natT=natT}
          val _ = Comma_Fast_Kernel.report
            ("semantic graph publication stage=initial-source-ids-finished elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms initial_source_publish_started)
          val _ = Comma_Fast_Kernel.report
            ("semantic graph publication stage=components-complete elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms started)
        in (initial_source_ids_published_lthy, graph_theorem, root_exact, dense_nodes) end
      fun stats () = "semantic_sources=" ^ Int.toString (Termtab.size (!bindings)) ^
        " semantic_nodes=" ^ Int.toString (Inttab.size (!nodes)) ^
        " semantic_local_slots=" ^ Int.toString (!local_slots) ^
        " semantic_intern_hits=" ^ Int.toString (!reused) ^
        " " ^ #stats source_ports () ^
        " semantic_near_application_rows=" ^
          Int.toString (!near_application_rows) ^
        " semantic_near_application_row_reuses=" ^
          Int.toString (!near_application_row_reuses) ^
        " semantic_near_action_class_reuses=" ^
          Int.toString (!near_action_class_reuses) ^
        " semantic_completed_action_aliases=" ^
          Int.toString (!completed_aliases) ^
        " semantic_offset_orbit_hits=" ^ Int.toString (!offset_orbit_hits) ^
        " semantic_offset_orbit_misses=" ^ Int.toString (!offset_orbit_misses) ^
        " semantic_offset_orbit_certificates=" ^
          Int.toString (Inttab.size (!offset_orbit_certificates)) ^
        " " ^ #stats endpoint ()
    in {root=root, compile=compile, initial_sources=initial_sources,
      nodes=fn () => Inttab.dest (!nodes),
      bindings=fn () => map #2 (Termtab.dest (!bindings)),
      source_class=classified_source, class_row=class_row_for_source,
      source_forward=forward_for_source,
      publish=publish,
      stats=stats,
      validate_selection= #validate_selection source_ports,
      work=fn () =>
        {transition_evaluations= #transition_evaluations (#work source_ports ()),
         completed_aliases= !completed_aliases,
         near_operator_reuses= #near_operator_reuses (#work source_ports ()),
         near_application_transports=
           #near_application_transports (#work source_ports ()),
         near_application_rows= !near_application_rows,
         near_application_row_reuses= !near_application_row_reuses,
         near_action_class_reuses= !near_action_class_reuses}} end

end
