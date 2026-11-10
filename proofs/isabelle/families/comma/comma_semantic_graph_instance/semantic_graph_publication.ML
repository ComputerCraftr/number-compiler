(* Exact staged publication of the discovered graph rows.  The publisher keeps
   table selection, source arithmetic, and graph-wide coverage as separate
   checked steps so a local row proof never expands every table lookup. *)
structure Comma_Semantic_Graph_Publication =
struct
  fun closed theorem =
    not (Term.is_open (Thm.prop_of theorem)) andalso
      null (Term.add_frees (Thm.prop_of theorem) []) andalso
      null (Term.add_vars (Thm.prop_of theorem) [])

  fun checked expected theorem message =
    if Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso closed theorem andalso
        Thm.prop_of theorem aconv expected then theorem
    else error message

  fun nat n = HOLogic.mk_number @{typ nat} n

  fun publish_initial_source_ids
      {lthy, source_list, source_list_equation, sources,
       bindings_constant, bindings_definition, binding_rows: (term * int) list,
       binding_lookup_equations, positionT, natT} =
    let
      val publication_started = Time.now ()
      val _ = Comma_Fast_Kernel.report
        "semantic graph initial-source stage=started"
      val _ = if length sources = 16 then ()
        else error "Initial source catalogue must contain sixteen charts"
      fun binding_index source =
        let
          fun seek _ [] = error "Compiled initial source has no binding row"
            | seek index ((candidate, _) :: rest) =
                if candidate aconv source then index else seek (index + 1) rest
        in seek 0 binding_rows end
      val lookup_data = map_index
        (fn (index, source) =>
          let
            val binding_position = binding_index source
            val (_, cid) = List.nth (binding_rows, binding_position)
            val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
              (@{term comma_semantic_b1_binding_cid_of} $
                bindings_constant $ source,
               Const (@{const_name Some}, natT -->
                 Type (@{type_name option}, [natT])) $ nat cid))
            val context = Simplifier.add_simps ([bindings_definition]) (put_simpset HOL_basic_ss
              (Local_Theory.target_of lthy))
            val equation = Simplifier.rewrite context
              (Thm.cterm_of context expected)
            val indexed = List.nth (binding_lookup_equations, binding_position)
            val _ = if Thm.term_of (Thm.rhs_of equation) aconv Thm.prop_of indexed
                then ()
              else error "Initial-source lookup does not match its exact indexed row"
            val theorem = Thm.equal_elim (Thm.symmetric equation) indexed
              |> (fn result => checked expected result
                "Initial-source lookup theorem is not closed and exact")
          in (source, cid, theorem) end)
        sources
      val _ = Comma_Fast_Kernel.report
        ("semantic graph initial-source stage=lookups-finished count=" ^
          Int.toString (length lookup_data) ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms publication_started)
      val source_ids = map #2 lookup_data
      val source_id_values = HOLogic.mk_list natT (map nat source_ids)
      val ((source_ids_local, (_, source_ids_definition_local)), source_ids_lthy) =
        Local_Theory.define
          ((Binding.name "comma_semantic_graph_initial_source_ids", NoSyn),
            ((Binding.name "comma_semantic_graph_initial_source_ids_def", []),
              source_id_values)) lthy
      val source_ids_morphism = Local_Theory.target_morphism source_ids_lthy
      val source_ids_constant = Morphism.term source_ids_morphism source_ids_local
      val source_ids_definition =
        Morphism.thm source_ids_morphism source_ids_definition_local
      fun note_lookup (index, (_, _, theorem)) context =
        #2 (Local_Theory.note
          ((Binding.name ("comma_semantic_graph_initial_source_lookup_slot_" ^
              Int.toString index), []), [theorem]) context)
      val lookup_lthy = fold note_lookup (map_index I lookup_data) source_ids_lthy
      val source = Free ("initial_source", positionT)
      val cid = Free ("initial_source_cid", natT)
      val lookup = Const (@{const_name comma_semantic_b1_binding_cid_of},
        HOLogic.listT @{typ comma_semantic_b1_binding} --> positionT -->
          Type (@{type_name option}, [natT])) $ bindings_constant $ source
      val lookup_predicate = Term.lambda source (Term.lambda cid
        (HOLogic.mk_eq (lookup,
          Const (@{const_name Some}, natT --> Type (@{type_name option}, [natT])) $ cid)))
      val exact_relation = Const (@{const_name list_all2},
        (positionT --> natT --> HOLogic.boolT) -->
          HOLogic.listT positionT --> HOLogic.listT natT --> HOLogic.boolT) $
        lookup_predicate $ source_list $ source_ids_constant
      val exact_proposition = HOLogic.mk_Trueprop exact_relation
      val lookup_facts = map #3 lookup_data
      val exact_started = Time.now ()
      val exact = Goal.prove (Local_Theory.target_of lookup_lthy) [] []
        exact_proposition
        (fn {context, ...} => HEADGOAL
          (Simplifier.asm_full_simp_tac
            (Simplifier.add_simps (([source_ids_definition, source_list_equation] @
                @{thms list_all2_Cons list_all2_Nil} @ lookup_facts)) (put_simpset HOL_basic_ss context))))
        |> (fn result => checked exact_proposition result
          "Initial source IDs are not tied to their exact source lookups")
      val _ = Comma_Fast_Kernel.report
        ("semantic graph initial-source stage=exact-relation-finished elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms exact_started)
      val (_, exact_lthy) = Local_Theory.note
        ((Binding.name "comma_semantic_graph_initial_source_binding_exact", []),
          [exact]) lookup_lthy
      val _ = Comma_Fast_Kernel.report
        ("semantic graph initial-source publication slots=" ^
          Int.toString (length source_ids) ^ " exact=true")
      val _ = Comma_Fast_Kernel.report
        ("semantic graph initial-source stage=publication-finished elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms publication_started)
    in exact_lthy end

  fun certify_node_rows
      {ctxt, nodes_constant, nodes_definition, nodeT, natT,
       node_values: term list, node_extent: int} =
    let
      val index = Free ("semantic_publication_node_index", natT)
      val selected = Const (@{const_name nth},
        HOLogic.listT nodeT --> natT --> nodeT) $ nodes_constant $ index
      val {procedure, stats, ...} = Comma_Selected_List_Conversion.make
        {ctxt=ctxt, name="semantic_graph_nodes",
         root_definition=nodes_definition, table_pattern=selected,
         extents=[node_extent]}
      val selection_context = Simplifier.add_simps ([nodes_definition]) (ctxt)
        |> Simplifier.add_proc procedure
      val started = Time.now ()
      val row_time = Unsynchronized.ref Time.zeroTime
      fun certify (i, _) =
        let
          val row_started = Time.now ()
          val nth = Const (@{const_name nth},
            HOLogic.listT nodeT --> natT --> nodeT) $ nodes_constant $ nat i
          val expected = List.nth (node_values, i)
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq (nth, expected))
          val theorem = Goal.prove ctxt [] [] proposition
            (fn {context, ...} =>
              HEADGOAL (Simplifier.asm_full_simp_tac selection_context))
            |> (fn result => checked proposition result
              "Semantic graph selected node row did not check")
          val _ = row_time := Time.+ (!row_time, Time.- (Time.now (), row_started))
          val done = i + 1
          val _ = if done mod 32 = 0 orelse done = node_extent then
            Comma_Fast_Kernel.report
              ("semantic graph publication stage=node-rows rows=" ^
                Int.toString done ^ "/" ^ Int.toString node_extent ^
                " row_cumulative_ms=" ^
                  LargeInt.toString (Time.toMilliseconds (!row_time)))
            else ()
        in theorem end
      val rows = map_index certify (0 upto (node_extent - 1))
      val _ = Comma_Fast_Kernel.report
        ("semantic graph publication stage=node-rows-finished elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started ^ " " ^ stats ())
    in rows end

  fun concretize_node_lookups
      {ctxt, nodes_constant, nodeT, natT, node_values: term list,
       node_rows: thm list, indexed_lookups: thm list} =
    let
      fun concrete (i, indexed) =
        let
          val row = List.nth (node_rows, i)
          val rewrite_context = Simplifier.add_simps ([row]) (put_simpset HOL_basic_ss ctxt)
          val equation = Simplifier.rewrite rewrite_context
            (Thm.cterm_of rewrite_context (Thm.prop_of indexed))
          val value = List.nth (node_values, i)
          val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (@{term comma_semantic_b1_node_of} $ nodes_constant $ nat i,
              Const (@{const_name Some},
                nodeT --> Type (@{type_name option}, [nodeT])) $ value))
          val _ = if Thm.term_of (Thm.rhs_of equation) aconv expected then ()
            else error "Selected node row did not normalize its indexed lookup"
          val theorem = Thm.equal_elim equation indexed
        in checked expected theorem
          "Concrete node lookup is not a closed checked equation" end
    in map_index concrete indexed_lookups end

  fun certify_binding_rows
      {ctxt, component, bindingT, natT, bindings_constant, nodes_constant,
       bindings_definition, binding_pairs_definition,
       rows: (term * int) list,
       source_class: term -> Comma_Semantic_Source_Ports.source_class,
       class_row: term -> Comma_Semantic_Source_Ports.class_row option,
       source_forward: term -> Comma_Semantic_Source_Ports.source_forward option,
       binding_lookup_equations: thm list, node_lookup_equations: thm list,
       orbit_equations: thm list} =
    let
      val started = Time.now ()
      val _ = Comma_Fast_Kernel.report
        ("semantic graph publication stage=binding-rows-start count=" ^
          Int.toString (length rows))
      val binding_from_pair = @{term comma_semantic_b1_binding_from_pair}
      val row_terms = map (fn (source, cid) =>
        binding_from_pair $ HOLogic.mk_prod (source, nat cid)) rows
      val literal_bindings = HOLogic.mk_list bindingT row_terms
      val literal_prop = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (bindings_constant, literal_bindings))
      val literal_started = Time.now ()
      val _ = Comma_Fast_Kernel.report
        "semantic graph publication stage=binding-literal-start"
      val literal_context = Simplifier.add_simps (([bindings_definition, binding_pairs_definition,
          @{thm comma_semantic_b1_binding_from_pair_def}] @ @{thms list.map})) (put_simpset HOL_basic_ss ctxt)
      val bindings_literal = Goal.prove ctxt [] [] literal_prop
        (fn {context, ...} =>
          HEADGOAL (Simplifier.asm_full_simp_tac literal_context))
        |> (fn result => checked literal_prop result
          "Semantic graph literal binding rows failed their exact table proof")
      val _ = Comma_Fast_Kernel.report
        ("semantic graph publication stage=binding-literal-finished elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms literal_started)
      val bindings_literal_meta = bindings_literal RS @{thm eq_reflection}

      fun publish_binding_lookup (i, ((source, cid), indexed)) =
        let
          val some_nat = Const (@{const_name Some},
            natT --> Type (@{type_name option}, [natT])) $ nat cid
          val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (@{term comma_semantic_b1_binding_cid_of} $
              bindings_constant $ source, some_nat))
          val context = Simplifier.add_simps ([bindings_definition]) (put_simpset HOL_basic_ss ctxt)
          val equation = Simplifier.rewrite context (Thm.cterm_of context expected)
          val _ = if Thm.term_of (Thm.rhs_of equation) aconv Thm.prop_of indexed
            then () else error "Binding lookup did not transport through its published table definition"
          val theorem = Thm.equal_elim (Thm.symmetric equation) indexed
          val theorem = checked expected theorem
            "Published binding lookup is not its exact closed source equation"
          val done = i + 1
          val _ = if done mod 64 = 0 orelse done = length rows then
            Comma_Fast_Kernel.report
              ("semantic graph publication stage=published-binding-lookups rows=" ^
                Int.toString done ^ "/" ^ Int.toString (length rows))
            else ()
        in theorem end
      val _ = if length rows = length binding_lookup_equations then ()
        else error "Binding lookup certificates do not align with source rows"
      val published_binding_lookups = map_index publish_binding_lookup
        (ListPair.zip (rows, binding_lookup_equations))

      val source_indices = fold (fn (i, (source, _)) =>
        Termtab.update (source, i)) (map_index I rows) Termtab.empty
      fun find_source source =
        (case Termtab.lookup source_indices source of
          SOME i => i
        | NONE => error "A local Goto has no published source binding")
      fun goto_target action =
        (case strip_comb action of
          (Const (name, _), [target, _]) =>
            if name = @{const_name Comma_Continuation_Goto} then [target] else []
        | _ => [])
      fun add_unique term [] = [term]
        | add_unique term (head :: tail) =
            if term aconv head then head :: tail
            else head :: add_unique term tail
      fun unique_gotos actions =
        fold (fn action => fn acc =>
          fold (fn target => fn current => add_unique target current)
            (goto_target action) acc) actions []
      fun lookup_facts actions =
        map (fn target => List.nth (published_binding_lookups, find_source target))
          (unique_gotos actions)
      val base_simp =
        @{thms comma_semantic_b1_binding_row_valid_def
          comma_semantic_b1_binding_from_pair_def
          comma_semantic_b1_binding.select_convs
          comma_semantic_b1_node_from_data_def
          comma_semantic_b1_node.select_convs
          comma_semantic_b1_edge_refs_valid_def
          comma_semantic_b1_edge_of_continuation.simps
          comma_semantic_b1_local_action_shape.simps
          comma_round_admitted.simps
          list.map list_all_Cons_iff list_all_Nil_iff nth_Cons' upt_rec
          list.size(3) list.size(4) dvd_eq_mod_eq_0
          comma_finite_position.case
          power2_eq_square of_nat_numeral of_nat_0 of_nat_1
          zmod_zminus1_eq_if zmod_zminus2_eq_if Let_def
          option.case option.distinct option.inject option.map
          prod.case fst_conv snd_conv case_prod_beta
          comma_semantic_b1_edge.case comma_semantic_b1_edge.distinct
          comma_semantic_b1_edge.inject
          comma_source_continuation_action.case
          comma_source_continuation_action.distinct
          comma_source_continuation_action.inject}
      val pointwise_transport_time = Unsynchronized.ref Time.zeroTime
      val entry_class_binding_transports = Unsynchronized.ref 0
      val near_representative_row_proofs = Unsynchronized.ref 0
      val near_representative_cache_hits = Unsynchronized.ref 0
      val near_source_binding_transports = Unsynchronized.ref 0
      fun row_source (source_info:
          Comma_Semantic_Source_Ports.source_class) =
        (case #kind (#shape source_info) of
          Comma_Semantic_Source_Ports.EntryClass =>
            #representative (#shape source_info)
        | Comma_Semantic_Source_Ports.NearClass => #source source_info)
      fun certificate_key (source_info:
          Comma_Semantic_Source_Ports.source_class) =
        (case #kind (#shape source_info) of
          Comma_Semantic_Source_Ports.EntryClass => #application_key source_info
        | Comma_Semantic_Source_Ports.NearClass => #action_key source_info)
      fun checked_near_selection_id
          (source_info: Comma_Semantic_Source_Ports.source_class) =
        (case #kind (#shape source_info) of
          Comma_Semantic_Source_Ports.EntryClass => NONE
        | Comma_Semantic_Source_Ports.NearClass =>
            let
              val source = #source source_info
              val action = (case #selected_action source_info of
                  SOME result => result
                | NONE => error "Near application has no selected control action")
              val expected_key = HOLogic.mk_prod (nat 1,
                HOLogic.mk_list @{typ comma_source_continuation_action} [action])
              val _ = if #action_key source_info aconv expected_key then ()
                else error "Near action key does not encode its selected action"
              val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq
                (@{term comma_source_continuation_id} $ source,
                 #action_key source_info))
              val theorem = (case #selection_id source_info of
                  SOME result => result
                | NONE => error "Near application lacks its checked action-class selection")
              val _ = if null (Thm_Deps.all_oracles [theorem]) then ()
                else error "Near action-class selection depends on an oracle"
              val _ = checked expected theorem
                "Near action-class selection is not bound to its exact source"
            in SOME theorem end)
      fun admitted_fact
          (source_info: Comma_Semantic_Source_Ports.source_class) =
        let
          val source = #source source_info
          val proposition = HOLogic.mk_Trueprop
            (@{term comma_round_admitted} $ source)
          val context = Simplifier.add_simps ([#admitted (#header source_info)]) (put_simpset HOL_basic_ss ctxt)
        in Goal.prove ctxt [] [] proposition
          (fn _ => HEADGOAL (Simplifier.simp_tac context))
          |> (fn result => checked proposition result
            "Source occurrence lost its checked admission") end
      fun normalized_fact
          (source_info: Comma_Semantic_Source_Ports.source_class) =
        let
          val source = #source source_info
          val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (source, @{term comma_source_continuation_base} $ source))
          val context = Simplifier.add_simps ([#base (#header source_info)]) (put_simpset HOL_basic_ss ctxt)
        in Goal.prove ctxt [] [] proposition
          (fn _ => HEADGOAL (Simplifier.simp_tac context))
          |> (fn result => checked proposition result
            "Source occurrence lost its checked normalization") end
      fun source_pointwise source
          (source_info: Comma_Semantic_Source_Ports.source_class) =
        let
          val source_header = #header source_info
          val phase = Free ("semantic_port_phase", natT)
          val port_action = Term.lambda phase
            (@{term comma_semantic_b1_source_port_action} $ source $ phase)
          val action_at = @{term comma_source_continuation_action_at} $ source $ phase
          val selected_port = Term.betapply (port_action, phase)
          val period = @{term comma_decisive_sector_period} $ source
          val pointwise = HOLogic.mk_Trueprop
            (HOLogic.mk_all ("semantic_port_phase", natT,
              HOLogic.mk_imp
                (HOLogic.mk_binrel @{const_name less} (phase, period),
                 HOLogic.mk_eq (action_at, selected_port))))
          val pointwise_started = Time.now ()
          (* The theorem is the shared source-to-port bridge for both Entry
             and Near.  Resolve its conditional premises explicitly, then
             discharge only the checked admission and normalization facts.
             This avoids reopening either family-specific evaluator here. *)
          val transport_context = Simplifier.add_simps ([#base source_header, #admitted source_header]) (put_simpset HOL_basic_ss ctxt)
          val theorem = Goal.prove ctxt [] [] pointwise
            (fn {context = goal_context, ...} =>
              (REPEAT_DETERM
                (resolve_tac goal_context @{thms allI impI} 1)) THEN
              HEADGOAL (resolve_tac goal_context
                [@{thm comma_semantic_b1_source_action_at_port}]
                THEN_ALL_NEW Simplifier.asm_simp_tac transport_context))
            |> (fn result => checked pointwise result
              "Generic source-action pointwise port transport did not check")
          val elapsed = Time.- (Time.now (), pointwise_started)
          val _ = pointwise_transport_time := Time.+
            (!pointwise_transport_time, elapsed)
        in (theorem, elapsed) end
      type class_certificate =
        {source_class: Comma_Semantic_Source_Ports.source_class,
         class_row: Comma_Semantic_Source_Ports.class_row,
         row_binding: term,
         row_valid: thm}
      val class_certificates = Unsynchronized.ref
        (Termtab.empty: class_certificate Termtab.table)
      val class_row_time = Unsynchronized.ref Time.zeroTime
      val id_transport_time = Unsynchronized.ref Time.zeroTime
      fun prove_class_row row_source_info row port_list_equation =
        let
          val row_started = Time.now ()
          val first_class = Termtab.is_empty (!class_certificates)
          val representative = row_source row_source_info
          val cid = #cid row
          val actions = #actions row
          val period = #period (#shape row_source_info)
          val row_binding = binding_from_pair $
            HOLogic.mk_prod (representative, nat cid)
          val node_lookup = List.nth (node_lookup_equations, cid)
          val (_, selected_node) = HOLogic.dest_eq
            (HOLogic.dest_Trueprop (Thm.prop_of node_lookup))
          val node = (case strip_comb selected_node of
              (Const (name, _), [value]) =>
                if name = @{const_name Some} then value
                else error "Canonical class row has no checked node"
            | _ => error "Canonical class row has a malformed node lookup")
          val phase = Free ("semantic_port_phase", natT)
          val port_action = Term.lambda phase
            (@{term comma_semantic_b1_source_port_action} $
              representative $ phase)
          val pointwise_started = Time.now ()
          val (pointwise_theorem, _) =
            source_pointwise representative row_source_info
          val _ = if first_class then
            Comma_Fast_Kernel.report
              ("semantic graph publication stage=first-row-pointwise-finished period=" ^
                Int.toString period ^ " elapsed_ms=" ^
                Comma_Proof_Profile.elapsed_ms pointwise_started)
            else ()
          val pointwise_rule = Drule.infer_instantiate ctxt
            [(("port_action", 0), Thm.cterm_of ctxt port_action),
             (("source", 0), Thm.cterm_of ctxt representative),
             (("node", 0), Thm.cterm_of ctxt node)]
            @{thm comma_semantic_b1_binding_row_valid_from_pointwise_port}
          val lookups = lookup_facts actions
          val row_context = Simplifier.add_simps ((base_simp @
              [#base (#header row_source_info),
               #period_equation (#header row_source_info),
               #admitted (#header row_source_info),
               port_list_equation, pointwise_theorem,
               @{thm comma_semantic_graph_source_port_action_nth},
               @{thm comma_semantic_graph_forall_less_iff_list_all},
               node_lookup] @ orbit_equations @ lookups)) (Comma_Entry_Arithmetic.natural_context ctxt)
          val proposition = HOLogic.mk_Trueprop
            (@{term comma_semantic_b1_binding_row_valid} $
              bindings_constant $ nodes_constant $ row_binding)
          val _ = if period > 0 andalso period = length actions andalso
              924 mod period = 0 then ()
            else error "Canonical source class has an invalid checked period"
          val theorem = Goal.prove ctxt [] [] proposition
            (fn {context, ...} =>
              let
                val simplify =
                  (case #kind (#shape row_source_info) of
                    Comma_Semantic_Source_Ports.NearClass =>
                      Simplifier.asm_simp_tac
                    | Comma_Semantic_Source_Ports.EntryClass =>
                      Simplifier.asm_full_simp_tac)
              in HEADGOAL (resolve_tac context [pointwise_rule] THEN_ALL_NEW
                simplify row_context) end)
            |> (fn result => checked proposition result
              "Canonical class row failed its pointwise-port local-action proof")
          val _ = class_row_time := Time.+
            (!class_row_time, Time.- (Time.now (), row_started))
        in (row_binding, theorem) end
      fun certified_class source =
        let
          val source_info = source_class source
          val shape = #shape source_info
          val class_key = certificate_key source_info
          val _ = checked_near_selection_id source_info
        in case Termtab.lookup (!class_certificates) class_key of
          SOME certificate =>
            let
              val representative = #source_class certificate
              val row = #class_row certificate
              val valid_reuse =
                (case #kind shape of
                  Comma_Semantic_Source_Ports.EntryClass =>
                    #application_key representative aconv class_key
                | Comma_Semantic_Source_Ports.NearClass =>
                    #action_key representative aconv class_key andalso
                    #action_key row aconv class_key andalso
                    #application_key representative aconv #application_key row)
              val _ = if valid_reuse then ()
                else error "Cached representative row lost its action/source authority"
              val _ = if #kind shape = Comma_Semantic_Source_Ports.NearClass then
                  near_representative_cache_hits :=
                    !near_representative_cache_hits + 1
                else ()
            in certificate end
        | NONE =>
            let
              val row = (case class_row source of
                  SOME result => result
                | NONE => error "Local graph source has no application transition row")
              val row_source_info = #class_source row
              val representative = row_source row_source_info
              val representative_header = #header row_source_info
              val row_source_period = #period (#shape row_source_info)
              val same_near_action =
                (case (#selected_action source_info, #actions row) of
                  (SOME selected, [row_action]) => selected aconv row_action
                | _ => false)
              val row_source_key =
                (case #kind (#shape row_source_info) of
                  Comma_Semantic_Source_Ports.EntryClass =>
                    #application_key row_source_info
                | Comma_Semantic_Source_Ports.NearClass =>
                    #action_key row_source_info)
              val exact_source_row =
                (case #kind shape of
                  Comma_Semantic_Source_Ports.EntryClass =>
                    #key (#shape row_source_info) aconv class_key
                | Comma_Semantic_Source_Ports.NearClass =>
                    row_source_key aconv class_key andalso
                    #action_key row aconv class_key andalso
                    #application_key row_source_info aconv #application_key row andalso
                    same_near_action)
              val _ = if row_source_period = length (#actions row) andalso
                    exact_source_row then ()
                else error "Published source row disagrees with its class/application key"
              val action_list = HOLogic.mk_list
                @{typ comma_source_continuation_action} (#actions row)
              val port_list = @{term comma_semantic_b1_source_port_actions} $
                representative
              val port_list_prop = HOLogic.mk_Trueprop
                (HOLogic.mk_eq (port_list, action_list))
              val exact_transitions = map #exact (#transitions row)
              val list_context = Simplifier.add_simps ((base_simp @
                  [#base representative_header,
                   #period_equation representative_header,
                   #admitted representative_header,
                   @{thm comma_semantic_b1_source_port_actions_def}] @
                  @{thms comma_source_continuation_base.simps} @
                  exact_transitions)) (Comma_Entry_Arithmetic.natural_context ctxt)
              val first_class = Termtab.is_empty (!class_certificates)
              val port_list_started = Time.now ()
              val _ = if first_class then Comma_Fast_Kernel.report
                "semantic graph publication stage=first-class-port-list-start" else ()
              val port_list_equation = Goal.prove ctxt [] [] port_list_prop
                (fn {context, ...} =>
                  HEADGOAL (Simplifier.asm_full_simp_tac list_context))
                |> (fn result => checked port_list_prop result
                  "Canonical class transitions did not reconstruct its checked port row")
              val _ = if first_class then Comma_Fast_Kernel.report
                ("semantic graph publication stage=first-class-port-list-finished elapsed_ms=" ^
                  Comma_Proof_Profile.elapsed_ms port_list_started) else ()
              val class_row_started = Time.now ()
              val _ = if first_class then Comma_Fast_Kernel.report
                "semantic graph publication stage=first-class-row-proof-start" else ()
              val (row_binding, row_valid) =
                prove_class_row row_source_info row port_list_equation
              val _ = if first_class then Comma_Fast_Kernel.report
                ("semantic graph publication stage=first-class-row-proof-finished elapsed_ms=" ^
                  Comma_Proof_Profile.elapsed_ms class_row_started) else ()
              val result : class_certificate =
                {source_class=row_source_info, class_row=row,
                 row_binding=row_binding,
                 row_valid=row_valid}
              val _ = if #kind shape = Comma_Semantic_Source_Ports.NearClass then
                  near_representative_row_proofs :=
                    !near_representative_row_proofs + 1
                else ()
              val _ = class_certificates :=
                Termtab.update (class_key, result) (!class_certificates)
            in result end
        end
      fun certify_row (i, (source, cid)) =
        let
          val first_row = Time.toMilliseconds (!id_transport_time) = 0
          val _ = if i = 0 then Comma_Fast_Kernel.report
            "semantic graph publication stage=first-binding-row-start" else ()
          val source_class_started = Time.now ()
          val source_info = source_class source
          val _ = if first_row then Comma_Fast_Kernel.report
            ("semantic graph publication stage=first-binding-source-class-finished elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms source_class_started) else ()
          val class_certificate_started = Time.now ()
          val certificate = certified_class source
          val _ = if first_row then Comma_Fast_Kernel.report
            ("semantic graph publication stage=first-binding-class-certificate-finished elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms class_certificate_started) else ()
          val id_transport_started = Time.now ()
          val row_source_info = #source_class certificate
          val representative = row_source row_source_info
          val row = #class_row certificate
          val period = #period (#shape source_info)
          val row_source_period = #period (#shape row_source_info)
          val _ = if period > 0 andalso period = row_source_period andalso
              period = length (#actions row) andalso 924 mod period = 0 andalso
              #cid row = cid then ()
            else error "Binding source did not receive its exact class transition row"
          val theorem =
            (case #kind (#shape source_info) of
              Comma_Semantic_Source_Ports.NearClass =>
                let
                  val same_id =
                    (case (checked_near_selection_id source_info,
                           checked_near_selection_id row_source_info) of
                      (SOME occurrence, SOME representative_id) =>
                        Thm.transitive
                          (occurrence RS @{thm eq_reflection})
                          (Thm.symmetric
                            (representative_id RS @{thm eq_reflection}))
                        RS @{thm meta_eq_to_obj_eq}
                    | _ => error "Near row reuse lacks exact occurrence action IDs")
                  val _ = if #action_key source_info aconv #action_key row andalso
                      #action_key row_source_info aconv #action_key row andalso
                      #application_key row_source_info aconv #application_key row
                    then ()
                    else error "Near representative row changed action or source authority"
                  val admitted = admitted_fact source_info
                  val normalized = normalized_fact source_info
                  val pair = HOLogic.mk_prod (source, nat cid)
                  val binding = binding_from_pair $ pair
                  val row_rule = Drule.infer_instantiate ctxt
                    [(("bindings", 0), Thm.cterm_of ctxt bindings_constant),
                     (("nodes", 0), Thm.cterm_of ctxt nodes_constant),
                     (("source", 0), Thm.cterm_of ctxt source),
                     (("representative", 0), Thm.cterm_of ctxt representative),
                     (("cid", 0), Thm.cterm_of ctxt (nat cid))]
                    @{thm comma_semantic_b1_binding_row_valid_pair_id_rebase}
                  val theorem = row_rule OF
                    [#row_valid certificate, same_id, admitted, normalized]
                  val expected = HOLogic.mk_Trueprop
                    (@{term comma_semantic_b1_binding_row_valid} $
                      bindings_constant $ nodes_constant $
                      binding)
                in checked expected theorem
                  "Near representative row did not transport to its exact source binding" end
            | Comma_Semantic_Source_Ports.EntryClass =>
                let
                  val membership =
                    (case #membership source_info of
                      SOME theorem => theorem
                    | NONE => error "Entry class has no guarded membership proof")
                  val pair = HOLogic.mk_prod (source, nat cid)
                  val binding = binding_from_pair $ pair
                  val row_rule = Drule.infer_instantiate ctxt
                    [(("bindings", 0), Thm.cterm_of ctxt bindings_constant),
                     (("nodes", 0), Thm.cterm_of ctxt nodes_constant),
                     (("source", 0), Thm.cterm_of ctxt source),
                     (("representative", 0), Thm.cterm_of ctxt representative),
                     (("cid", 0), Thm.cterm_of ctxt (nat cid))]
                    @{thm comma_semantic_b1_binding_row_valid_pair_guarded_rebase}
                  val theorem = row_rule OF
                    [#row_valid certificate, membership]
                  val proposition = HOLogic.mk_Trueprop
                    (@{term comma_semantic_b1_binding_row_valid} $
                      bindings_constant $ nodes_constant $ binding)
                in checked proposition theorem
                  "Entry class did not transport its certified representative row" end)
          val _ = id_transport_time := Time.+
            (!id_transport_time, Time.- (Time.now (), id_transport_started))
          val _ = if #kind (#shape source_info) =
              Comma_Semantic_Source_Ports.EntryClass then
              entry_class_binding_transports := !entry_class_binding_transports + 1
            else near_source_binding_transports :=
              !near_source_binding_transports + 1
          val done = i + 1
          val _ = if done = 1 then Comma_Fast_Kernel.report
            ("semantic graph publication stage=first-class-row-transport-finished elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms id_transport_started)
            else if done mod 32 = 0 orelse done = length rows then
            Comma_Fast_Kernel.report
              ("semantic graph publication stage=class-row-transports source_index=" ^
                Int.toString done ^ "/" ^ Int.toString (length rows) ^
                " transport_cumulative_ms=" ^
                  LargeInt.toString (Time.toMilliseconds (!id_transport_time)) ^
                " class_row_cumulative_ms=" ^
                  LargeInt.toString (Time.toMilliseconds (!class_row_time)))
            else ()
        in theorem end
      val indexed_rows = map_index I rows
      val representatives = filter (fn (_, (source, _)) =>
        is_none (source_forward source)) indexed_rows
      fun collect_near_actions (_, (source, _)) actions =
        let val info = source_class source
        in case #kind (#shape info) of
          Comma_Semantic_Source_Ports.NearClass =>
            Termtab.update (#action_key info, ()) actions
        | Comma_Semantic_Source_Ports.EntryClass => actions end
      val near_action_classes =
        Termtab.size (fold collect_near_actions representatives Termtab.empty)
      val near_source_rows = length (filter (fn (_, (source, _)) =>
        #kind (#shape (source_class source)) =
          Comma_Semantic_Source_Ports.NearClass) representatives)
      val local_row_theorems = map certify_row representatives
      val expected_near_reuses = near_source_rows - near_action_classes
      val _ = if !near_representative_row_proofs = near_action_classes andalso
          !near_representative_cache_hits = expected_near_reuses andalso
          !near_source_binding_transports = near_source_rows then ()
        else error
          "Near publication repeated a representative proof or skipped occurrence transport"
      val _ = Thm.consolidate local_row_theorems
      val local_rows = fold (fn ((_, (source, _)), theorem) =>
        Termtab.update (source, theorem))
        (ListPair.zip (representatives, local_row_theorems)) Termtab.empty
      fun completed_row (i, (source, cid)) =
        let
          val (representative, transport_facts, base, period_equation) =
            (case source_forward source of
              NONE => let val class = source_class source
                in (source, [], #base (#header class),
                    #period_equation (#header class)) end
            | SOME {child, completed, action, direct,
                header={base, period_equation, admitted, ...}} =>
                (child, [completed, action, direct, admitted], base, period_equation))
          val local_row = (case Termtab.lookup local_rows representative of
              SOME theorem => theorem
            | NONE => error "Completed source alias has no certified local representative")
          val found = List.nth (published_binding_lookups, find_source representative)
          val rule = Drule.infer_instantiate ctxt
            [(("representative", 0), Thm.cterm_of ctxt representative),
             (("source", 0), Thm.cterm_of ctxt source),
             (("cid", 0), Thm.cterm_of ctxt (nat cid))]
            @{thm comma_semantic_graph_completed_binding_from_lookup}
          (* Lookup and local action certificates are consumed directly.
             Reopening their definitions here would reconstruct the row. *)
          val context = Simplifier.add_simps (([base, period_equation] @
              @{thms comma_round_admitted.simps} @ transport_facts)) (Comma_Entry_Arithmetic.natural_context ctxt)
          val binding = binding_from_pair $ HOLogic.mk_prod (source, nat cid)
          val proposition = HOLogic.mk_Trueprop
            (@{term comma_semantic_b1_completed_binding_row_valid} $
              bindings_constant $ nodes_constant $ binding)
          val _ = if i = 0 then Comma_Fast_Kernel.report
            "semantic graph publication stage=first-completed-binding-proof-start" else ()
          val theorem = Goal.prove ctxt [] [] proposition
            (fn {context=goal_context, ...} =>
              resolve_tac goal_context [rule] 1 THEN
              resolve_tac goal_context [found] 1 THEN
              resolve_tac goal_context [local_row] 1 THEN
              ALLGOALS (Simplifier.asm_full_simp_tac context))
            |> (fn result => checked proposition result
              "Completed source binding did not transport its representative certificate")
          val _ = if i = 0 orelse (i+1) mod 64 = 0 orelse i+1 = length rows then
            Comma_Fast_Kernel.report
              ("semantic graph publication stage=completed-bindings rows=" ^
                Int.toString (i+1) ^ "/" ^ Int.toString (length rows) ^
                " class_row_transports=" ^ Int.toString (length local_row_theorems))
            else ()
        in theorem end
      val row_theorems = map completed_row indexed_rows
      val list_conversion = Conv.arg_conv
        (Conv.arg_conv (Conv.rewr_conv bindings_literal_meta))
      val list_equation = list_conversion
        (Thm.cterm_of ctxt (HOLogic.mk_Trueprop component))
      val literal_goal = Thm.term_of (Thm.rhs_of list_equation)
      val aggregation_context = Simplifier.add_simps ((@{thms list_all_Cons_iff list_all_Nil_iff} @ row_theorems)) (put_simpset HOL_basic_ss ctxt)
      val aggregated = Goal.prove ctxt [] [] literal_goal
        (fn {context, ...} =>
          HEADGOAL (Simplifier.asm_full_simp_tac aggregation_context))
        |> (fn result => checked literal_goal result
          "Semantic graph source-row certificates did not cover the published list")
      val result = Thm.equal_elim (Thm.symmetric list_equation) aggregated
      val component_prop = HOLogic.mk_Trueprop component
      val result = checked component_prop result
        "Semantic graph source-row theorem changed the graph-valid component"
      val _ = Comma_Fast_Kernel.report
        ("semantic graph publication stage=binding-rows-finished count=" ^
          Int.toString (length row_theorems) ^
          " class_row_proofs=" ^ Int.toString (Termtab.size (!class_certificates)) ^
          " class_row_cumulative_ms=" ^
            LargeInt.toString (Time.toMilliseconds (!class_row_time)) ^
          " pointwise_transport_cumulative_ms=" ^
            LargeInt.toString (Time.toMilliseconds (!pointwise_transport_time)) ^
          " entry_class_binding_transports=" ^
            Int.toString (!entry_class_binding_transports) ^
          " near_action_classes=" ^ Int.toString near_action_classes ^
          " near_representative_row_proofs=" ^
            Int.toString (!near_representative_row_proofs) ^
          " near_representative_cache_hits=" ^
            Int.toString (!near_representative_cache_hits) ^
          " near_source_binding_transports=" ^
            Int.toString (!near_source_binding_transports) ^
          " id_row_transport_cumulative_ms=" ^
            LargeInt.toString (Time.toMilliseconds (!id_transport_time)) ^
          " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
    in result end

  fun certify_node_coverage
      {ctxt, component, nodeT, bindingT, natT,
       bindings_constant, bindings_definition,
       nodes_constant, nodes_definition, node_values: term list,
       node_cids: int list, node_children: int list list,
       rows: (term * int) list, binding_cid_witnesses: thm list,
       node_lookup_equations: thm list} =
    let
      val started = Time.now ()
      val cid_indices = fold_rev (fn (i, (_, cid)) =>
        Inttab.update (cid, i)) (map_index I rows) Inttab.empty
      fun binding_index cid =
        (case Inttab.lookup cid_indices cid of
          SOME i => i
        | NONE => error "A semantic node has no checked source binding")
      fun set_of itemT value =
        Const (@{const_name set}, HOLogic.listT itemT --> HOLogic.mk_setT itemT) $ value
      val binding_value = Free ("semantic_graph_binding", bindingT)
      val binding_cid = Const (@{const_name comma_semantic_b1_binding_cid},
        bindingT --> natT) $ binding_value
      val binding_set = set_of bindingT bindings_constant
      fun witness_goal cid = HOLogic.mk_Trueprop
        (Const (@{const_name Bex}, HOLogic.mk_setT bindingT -->
          (bindingT --> HOLogic.boolT) --> HOLogic.boolT) $ binding_set $
          Term.lambda binding_value (HOLogic.mk_eq (binding_cid, nat cid)))
      fun split_ball term =
        (case strip_comb term of
          (Const (name, _), [set_term, predicate]) =>
            if name = @{const_name Ball} then (set_term, predicate)
            else error "Graph coverage component is not a bounded universal"
        | _ => error "Malformed graph coverage component")
      val (published_set, predicate) = split_ball component
      val node_literal = HOLogic.mk_list nodeT node_values
      val nodes_set = set_of nodeT nodes_constant
      val literal_set = set_of nodeT node_literal
      val set_equation_prop = HOLogic.mk_Trueprop
        (HOLogic.mk_eq (nodes_set, literal_set))
      val set_equation = Goal.prove ctxt [] [] set_equation_prop
        (fn {context, ...} =>
          HEADGOAL (Simplifier.asm_full_simp_tac
            (Simplifier.add_simps ([nodes_definition]) (put_simpset HOL_basic_ss context))))
        |> (fn result => checked set_equation_prop result
          "Semantic graph node-set expansion changed the published table")
      val _ = if published_set aconv nodes_set then ()
        else error "Graph coverage quantifies over a different node set"
      val set_meta = set_equation RS @{thm eq_reflection}
      val set_conversion = Conv.arg_conv
        (Conv.arg1_conv (Conv.rewr_conv set_meta))
      val component_prop = HOLogic.mk_Trueprop component
      val list_equation = set_conversion (Thm.cterm_of ctxt component_prop)
      val list_goal = Thm.term_of (Thm.rhs_of list_equation)
      val _ = if length node_values = length node_cids andalso
          length node_values = length node_children then ()
        else error "Semantic graph node coverage vectors are misaligned"
      val node_time = Unsynchronized.ref Time.zeroTime
      fun certify_node (i, (value, cid)) =
        let
          val row_started = Time.now ()
          val binding = binding_index cid
          val indexed_witness = List.nth (binding_cid_witnesses, binding)
          val witness_proposition = witness_goal cid
          val indexed_witness_theorem = Goal.prove ctxt [] [] witness_proposition
            (fn {context, ...} =>
              HEADGOAL (Simplifier.asm_full_simp_tac
                (Simplifier.add_simps ([bindings_definition, indexed_witness]) (put_simpset HOL_basic_ss context))))
            |> (fn result => checked witness_proposition result
              "Node source binding did not transfer from its checked table row")
          val node_cid = Const (@{const_name comma_semantic_b1_node_cid},
            nodeT --> natT) $ value
          val cid_proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq
            (node_cid, nat cid))
          val cid_context = Simplifier.add_simps ((@{thms comma_semantic_b1_node_from_data_def
              comma_semantic_b1_node.select_convs list.map
              prod.case fst_conv snd_conv})) (put_simpset HOL_basic_ss ctxt)
          val cid_theorem = Goal.prove ctxt [] [] cid_proposition
            (fn {context, ...} =>
              HEADGOAL (Simplifier.asm_full_simp_tac cid_context))
            |> (fn result => checked cid_proposition result
              "Published node row has a different CID from its indexed key")
          val child_lookups = map (fn child =>
            List.nth (node_lookup_equations, child))
            (List.nth (node_children, i))
          val edge_proposition = HOLogic.mk_Trueprop
            (@{term comma_semantic_b1_edge_refs_valid} $
              nodes_constant $ value)
          val edge_context = Simplifier.add_simps ((@{thms comma_semantic_b1_edge_refs_valid_def
              comma_semantic_b1_node_from_data_def
              comma_semantic_b1_node.select_convs
              comma_semantic_b1_edge.case comma_semantic_b1_edge.distinct
              comma_semantic_b1_edge.inject list_all_Cons_iff
              list_all_Nil_iff comma_semantic_graph_Ball_set_list_all
              option.case option.distinct option.inject
              option.map prod.case fst_conv snd_conv Let_def
              of_nat_numeral of_nat_0 of_nat_1} @ child_lookups)) (Comma_Entry_Arithmetic.natural_context ctxt)
          val edge_theorem = Goal.prove ctxt [] [] edge_proposition
            (fn {context, ...} =>
              HEADGOAL (Simplifier.asm_full_simp_tac edge_context))
            |> (fn result => checked edge_proposition result
              "Semantic graph node has an uncertified child edge")
          val node_claim = Envir.beta_eta_contract (Term.betapply (predicate, value))
          val conjuncts = HOLogic.dest_conj node_claim
          val _ = if length conjuncts = 2 andalso
              List.nth (conjuncts, 1) aconv
                (HOLogic.dest_Trueprop edge_proposition) then ()
            else error "Node witnesses do not match the graph coverage predicate"
          val binding_claim = hd conjuncts
          val binding_claim_proposition = HOLogic.mk_Trueprop binding_claim
          val binding_claim_theorem = Goal.prove ctxt [] [] binding_claim_proposition
            (fn {context, ...} =>
              HEADGOAL (Simplifier.asm_full_simp_tac
                (Simplifier.add_simps ([cid_theorem, indexed_witness_theorem]) (put_simpset HOL_basic_ss context))))
            |> (fn result => checked binding_claim_proposition result
              "Node binding witness does not match the node's published CID")
          val node_theorem = @{thm conjI} OF [binding_claim_theorem, edge_theorem]
          val expected = HOLogic.mk_Trueprop node_claim
          val _ = checked expected node_theorem
            "Node binding and edge obligations did not prove the exact coverage row"
          val _ = node_time := Time.+ (!node_time, Time.- (Time.now (), row_started))
          val done = i + 1
          val _ = if done mod 32 = 0 orelse done = length node_values then
            Comma_Fast_Kernel.report
              ("semantic graph publication stage=node-coverage rows=" ^
                Int.toString done ^ "/" ^ Int.toString (length node_values) ^
                " row_cumulative_ms=" ^
                  LargeInt.toString (Time.toMilliseconds (!node_time)))
            else ()
        in node_theorem end
      val node_theorems = map_index certify_node (ListPair.zip (node_values, node_cids))
      val aggregate_context = Simplifier.add_simps ((@{thms comma_semantic_graph_Ball_set_list_all
          list_all_Cons_iff list_all_Nil_iff} @ node_theorems)) (put_simpset HOL_basic_ss ctxt)
      val aggregated = Goal.prove ctxt [] [] list_goal
        (fn {context, ...} =>
          HEADGOAL (Simplifier.asm_full_simp_tac aggregate_context))
        |> (fn result => checked list_goal result
          "Semantic graph node certificates did not cover the exact published table")
      val result = Thm.equal_elim (Thm.symmetric list_equation) aggregated
      val theorem = checked component_prop result
        "Semantic graph coverage theorem changed its quantified contract"
      val _ = Comma_Fast_Kernel.report
        ("semantic graph publication stage=node-coverage-finished count=" ^
          Int.toString (length node_theorems) ^
          " row_cumulative_ms=" ^
            LargeInt.toString (Time.toMilliseconds (!node_time)) ^
          " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started)
    in theorem end
end
