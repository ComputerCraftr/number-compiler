(* Proof-producing evaluator memoizing only exact closed occurrence/CRT terms. *)
structure Comma_Semantic_B1_Occurrence_Check_Cache =
struct
  val memo_capacity = 8192
  val maximum_lift_catalog_extent =
    Comma_Semantic_B1_Construction_Check.maximum_lift_catalog_extent
  val schematize = Comma_Selected_List_Conversion.schematize
  val head_name = Comma_Selected_List_Conversion.head_name
  val closed = Comma_Selected_List_Conversion.closed
  val validate_equation = Comma_Selected_List_Conversion.validate_equation
  fun catalogue_setup ctxt =
    let
      val started = Time.now ()
      val _ = Comma_Proof_Profile.report
        "B1 occurrence cache stage=catalogue-setup-start"
      fun select name root_definition pattern extents =
        let
          val selected_started = Time.now ()
          val _ = Comma_Proof_Profile.report
            ("B1 occurrence cache stage=selector-start name=" ^ name)
          val selector = Comma_Selected_List_Conversion.make
          {ctxt = ctxt, name = "semantic_b1_" ^ name,
           root_definition = root_definition, table_pattern = pattern,
           extents = extents}
          val _ = Comma_Proof_Profile.report
            ("B1 occurrence cache stage=selector-complete name=" ^ name ^
             " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms selected_started)
        in selector end
      fun select_named_children make_selector name pattern child_name_prefix get_definitions =
        make_selector {ctxt = ctxt, name = "semantic_b1_" ^ name,
          table_pattern = pattern, child_name_prefix = child_name_prefix,
          get_definitions = get_definitions}
      val selectors =
        [select "sources" @{thm comma_semantic_b1_crt_sources_def}
           @{term "comma_semantic_b1_crt_sources ! index"} [1024],
         select "descriptors" @{thm comma_semantic_b1_crt_descriptors_def}
           @{term "comma_semantic_b1_crt_descriptors ! index"} [1024],
         select "root_indices" @{thm comma_semantic_b1_crt_root_occurrence_indices_def}
           @{term "comma_semantic_b1_crt_root_occurrence_indices ! index"} [46],
         (* At most 1024 checked sources times the declared maximum period 28. *)
         select "lift_descriptors"
           @{thm comma_semantic_b1_crt_lift_descriptors_def}
           @{term "comma_semantic_b1_crt_lift_descriptors ! index"} [1024 * 28],
         select "lift_refs"
           @{thm comma_semantic_b1_crt_lift_refs_def}
           @{term "comma_semantic_b1_crt_lift_refs ! index"} [1024],
         select "template_column_ids"
           @{thm comma_semantic_b1_crt_template_column_ids_def}
           @{term "comma_semantic_b1_crt_template_column_ids ! index"} [1024],
         select_named_children
           Comma_Selected_List_Conversion.make_named_children_from_source
           "construction_piece_refs"
           @{term "comma_semantic_b1_crt_construction_piece_refs ! source ! row"}
           "comma_semantic_b1_crt_construction_piece_source_"
           Comma_Semantic_B1_Occurrence_Publication.get_construction_piece_source_definitions,
         select "offsets" @{thm comma_offset_representatives_def}
           @{term "comma_offset_representatives ! index"} [46]]
      val lift_column_projection =
        Comma_Semantic_B1_Lift_Column_Projection.make ctxt
      val lift_column_procedures =
        [#procedure lift_column_projection, #post_procedure lift_column_projection]
      val procedures = maps
        (fn selector => [#procedure selector, #post_procedure selector]) selectors @
        lift_column_procedures
      val base_context = fold Simplifier.add_proc procedures
        (ctxt addsimps Comma_Semantic_B1_Construction_Check.occurrence_cache_catalogue_simp_rules)
      val template_projection =
        Comma_Semantic_B1_Column_Conversion.make_template_projection ctxt
          base_context (Proof_Context.get_thm ctxt
            "comma_semantic_b1_crt_templates_def")
      val template_projection_procedures =
        [#procedure template_projection, #post_procedure template_projection]
      val all_procedures = procedures @ template_projection_procedures
      val context = fold Simplifier.add_proc template_projection_procedures base_context
      fun stats () = String.concatWith " "
        (map (fn selector => #stats selector ()) selectors) ^
        (#stats lift_column_projection) () ^ " " ^
        (#stats template_projection) ()
      val _ = Comma_Proof_Profile.report
        ("B1 occurrence cache stage=catalogue-setup-complete elapsed_ms=" ^
         Comma_Proof_Profile.elapsed_ms started)
    in
      {context = context, procedures = all_procedures, stats = stats}
    end

  fun make ctxt =
    let
      val started = Time.now ()
      val _ = Comma_Proof_Profile.report
        "B1 occurrence cache stage=make-entry"
      val columns = Comma_Semantic_B1_Column_Conversion.make ctxt
        (Comma_Semantic_B1_Occurrence_Publication.get_definitions ctxt)
      val _ = Comma_Semantic_B1_Certificate_Store_Fixtures.check_cid_transition_cache
        {transition = #cofactor_transition columns,
         counts = #cofactor_transition_counts columns,
         node_level = #cofactor_node_level columns,
         column_value = #column_value columns,
         node_count = #node_count columns,
         head_opens = #head_opens columns}
      val _ = Comma_Semantic_B1_Certificate_Store_Fixtures.check_partition_transition_dag
        {ctxt = ctxt, column_value = #column_value columns,
         step = #step columns,
         cofactor_transition = #cofactor_transition columns,
         node_count = #node_count columns,
         node_level = #cofactor_node_level columns,
         column_counts = #cofactor_transition_counts columns,
         head_opens = #head_opens columns}
      val prove_table_admission = #prove_all_columns_admitted columns
      (* Reuse the proof-producing endpoint arithmetic at selected source
         actions. Its simproc only accepts closed endpoint requests, so this
         does not send catalogue terms through Code_Simp. *)
      val fast_kernel = Comma_Fast_Kernel.make ctxt
      val endpoint_kernel = Comma_Decisive_Endpoint_Kernel.make ctxt
        (#context fast_kernel)
      val indexed_successors = Comma_Semantic_B1_Construction_Check.make_successor_cache
        ctxt maximum_lift_catalog_extent
      val memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      (* Cache partial requests separately; never publish them as hits. *)
      val incomplete = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      val publications = Unsynchronized.ref 0
      val partials = Unsynchronized.ref 0
      val uncached = Unsynchronized.ref 0
      val failures = Unsynchronized.ref 0
      val recursive = Unsynchronized.ref 0
      val source_partial_probe = Unsynchronized.ref false
      val slot_origin_traces = Unsynchronized.ref 0
      val source_origin_traces = Unsynchronized.ref 0
      val context_build_traces = Unsynchronized.ref 0
      val value_checks = Unsynchronized.ref 0
      val value_nodes = Unsynchronized.ref 0
      val rhs_reuse_hits = Unsynchronized.ref 0 and closed_reuse_hits = Unsynchronized.ref 0
      val last_head = Unsynchronized.ref "<none>"
      val checked_items = Unsynchronized.ref 0
      val operation_times = Unsynchronized.ref
        (Symtab.empty: (int * LargeInt.int) Symtab.table)
      val binding_source_action_evaluations = Unsynchronized.ref 0
      val binding_source_action_reuses = Unsynchronized.ref 0
      val binding_evaluation_depth = Unsynchronized.ref 0
      val lift_option_evaluations = Unsynchronized.ref 0
      val lift_option_memo_hits = Unsynchronized.ref 0
      val {profile = template_partition_profile,
        prove_checker = prove_partition_checker} =
        Comma_Semantic_B1_Partition_Conversion.make_template_partition_session ctxt
          {column_value = #column_value columns, step = #step columns,
           cofactor_transition = #cofactor_transition columns,
           node_count = #node_count columns}
      val certificate_store =
        Comma_Semantic_B1_Certificate_Store.make_instance_store ctxt
      val _ = Comma_Semantic_B1_Certificate_Store_Fixtures.check ctxt
      fun counters () =
        "lookups=" ^ Int.toString (!lookups) ^
        " hits=" ^ Int.toString (!hits) ^
        " misses=" ^ Int.toString (!misses) ^
        " publications=" ^ Int.toString (!publications) ^
        " partials=" ^ Int.toString (!partials) ^
        " failures=" ^ Int.toString (!failures) ^
        " recursive=" ^ Int.toString (!recursive) ^
        " value_checks=" ^ Int.toString (!value_checks) ^
        " value_nodes=" ^ Int.toString (!value_nodes) ^ " rhs_reuse_hits=" ^ Int.toString (!rhs_reuse_hits) ^ " closed_reuse_hits=" ^ Int.toString (!closed_reuse_hits) ^
        " retained=" ^ Int.toString (Termtab.size (!memo)) ^
        " source_action_evaluations_during_binding=" ^
          Int.toString (!binding_source_action_evaluations) ^
        " source_action_reuses_during_binding=" ^
          Int.toString (!binding_source_action_reuses) ^
        " lift_columns_option_evaluations=" ^ Int.toString (!lift_option_evaluations) ^
        " lift_columns_option_memo_hits=" ^ Int.toString (!lift_option_memo_hits) ^
        " " ^ (#stats template_partition_profile) () ^
        " " ^ (#stats certificate_store) () ^
        #counters columns () ^
        (case Comma_Semantic_B1_Construction_Check.operation_timing_report
            (!operation_times) of
          "" => ""
        | timings => " operation_timing=" ^ timings) ^
        " " ^ (#stats indexed_successors) ()
      val {checkpoint, milestone, endpoint_stats} =
        Comma_Semantic_B1_Construction_Check.make_occurrence_cache_reporters
          started counters (fn () => " fast_kernel={" ^ #stats fast_kernel () ^
            "} endpoint_kernel={" ^ #stats endpoint_kernel () ^ "}") misses last_head
      val _ = milestone "before-code-context-setup"
      val code_context = ctxt addsimps Comma_Semantic_B1_Construction_Check.occurrence_cache_checker_simp_rules
      val _ = milestone "after-code-context-setup"
      val split_action_rules = @{thms comma_crt_occurrence_split_action_def
        comma_crt_occurrence_split_from_bindings.simps
        comma_crt_occurrence_split_initial_def comma_crt_mdd_paint_binding_def
        comma_crt_mdd_paint_column.simps comma_crt_mdd_node_def
        comma_crt_split_invalid_action_def comma_crt_control_of_result.simps
        comma_crt_weight_of_result.simps}
      val code_conversion = Unsynchronized.ref
        (NONE: (Proof.context -> conv) option)
      val operation_conversion = Unsynchronized.ref
        (NONE: (cterm ->
          Comma_Semantic_B1_CRT_Operation_Conversion.staged_result) option)
      val operation_context_ref = Unsynchronized.ref
        (NONE: Proof.context option)
      fun partition_operation_context () =
        (case !operation_context_ref of SOME context => context
        | NONE => error "B1 partition operation context is not initialized")
      val partition_canonicalizer_ref = Unsynchronized.ref
        (NONE: (cterm -> thm) option)
      val selected_construction_contexts_ref = Unsynchronized.ref
        (NONE: {slot_origins: Proof.context, offset_orbit: Proof.context,
          source_arithmetic: Proof.context} option)
      val selected_action_context_ref = Unsynchronized.ref
        (NONE: Proof.context option)
      val thy = Proof_Context.theory_of ctxt
      val {patterns = paint_patterns, roots = paint_roots} =
        Comma_Semantic_B1_CRT_Operation_Conversion.selected_paint_memo_spec ctxt
      val selected_patterns = Comma_Semantic_B1_Construction_Check.occurrence_cache_patterns @
        Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_base_patterns @
        paint_patterns
      val occurrence_projector =
        Comma_Semantic_B1_Construction_Check.make_occurrence_projector ctxt
      val selected_schematic_patterns = map schematize
        (selected_patterns @ Comma_Semantic_B1_Construction_Check.occurrence_projection_patterns)
      val catalogue_schematic_patterns = map schematize Comma_Semantic_B1_Construction_Check.occurrence_cache_catalogue_patterns
      fun cacheable request =
        Comma_Semantic_B1_Construction_Check.matches_owned_request thy Comma_Semantic_B1_Construction_Check.occurrence_cache_generic_constants
          selected_schematic_patterns request orelse
        Comma_Semantic_B1_Construction_Check.matches_owned_request thy []
          catalogue_schematic_patterns request
      val {check = check_equation, complete_value} =
        Comma_Semantic_B1_CRT_Operation_Conversion.make_equation_checker_with_columns
          ctxt (#known_column columns)
      fun catalogue_request request =
        Comma_Semantic_B1_Construction_Check.matches_owned_request thy Comma_Semantic_B1_Construction_Check.occurrence_cache_catalogue_constants
          catalogue_schematic_patterns request
      val operation_roots =
        [@{const_name comma_semantic_b1_source_slot_action},
         @{const_name comma_decisive_sector_period}, @{const_name comma_offset_orbit},
         @{const_name comma_semantic_b1_crt_construction_check},
         @{const_name comma_semantic_b1_crt_template_geometry_certified}, @{const_name comma_semantic_b1_crt_lift_geometry_certified},
         @{const_name comma_semantic_b1_crt_constructed_goto_slot_certificate},
         @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches}, @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions},
         @{const_name comma_semantic_b1_crt_column_ids_resolve},
         @{const_name comma_semantic_b1_crt_group_construction_bound},
         @{const_name comma_semantic_b1_crt_constructed_source_origins}, @{const_name comma_semantic_b1_crt_constructed_slot_origins},
         @{const_name comma_semantic_b1_crt_lift_slot_valid_from_actions}, @{const_name comma_semantic_b1_crt_source_slot_action_row_certified},
         @{const_name comma_semantic_b1_crt_slot_actions_table}, @{const_name comma_semantic_b1_crt_lift_columns_option},
         @{const_name comma_crt_occurrence_split_action},
         @{const_name comma_crt_occurrence_split_from_bindings},
         @{const_name comma_crt_mdd_paint_binding},
         @{const_name comma_semantic_b1_terminal_action_result},
         @{const_name comma_semantic_b1_crt_occurrence_binding_check},
         @{const_name comma_crt_equiv_check}, @{const_name comma_crt_supported},
         @{const_name comma_crt_admitted}, @{const_name comma_crt_apply},
         @{const_name comma_crt_apply_shifted}, @{const_name comma_crt_negate},
         @{const_name comma_crt_group_rows}, @{const_name comma_crt_group_column}] @
        paint_roots @
        Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_base_heads
      val operation_context_roots =
        [@{const_name comma_semantic_b1_crt_construction_check},
         @{const_name comma_semantic_b1_crt_template_geometry_certified}, @{const_name comma_semantic_b1_crt_lift_geometry_certified},
         @{const_name comma_semantic_b1_crt_constructed_goto_slot_certificate},
         @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches}, @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions},
         @{const_name comma_semantic_b1_crt_column_ids_resolve},
         @{const_name comma_semantic_b1_crt_group_construction_bound},
         @{const_name comma_semantic_b1_crt_constructed_source_origins}, @{const_name comma_semantic_b1_crt_constructed_slot_origins},
         @{const_name comma_semantic_b1_crt_lift_slot_valid_from_actions}, @{const_name comma_semantic_b1_crt_source_slot_action_row_certified},
         @{const_name comma_semantic_b1_crt_slot_actions_table}, @{const_name comma_semantic_b1_crt_lift_columns_option},
         @{const_name comma_crt_occurrence_split_action},
         @{const_name comma_crt_occurrence_split_from_bindings},
         @{const_name comma_crt_mdd_paint_binding},
         @{const_name comma_semantic_b1_terminal_action_result},
         @{const_name comma_semantic_b1_crt_occurrence_binding_check}]
      val operation_request = Comma_Semantic_B1_Construction_Check.make_head_matcher operation_roots
      val operation_context_request = Comma_Semantic_B1_Construction_Check.make_head_matcher operation_context_roots
      val selected_paint_request = Comma_Semantic_B1_Construction_Check.make_head_matcher paint_roots

      val timed_origin = Comma_Semantic_B1_Construction_Check.timed_origin
      fun note_source_action_reuse request =
        if #is_source_action_request certificate_store request then
          (#note_source_action_reuse certificate_store ();
           if !binding_evaluation_depth > 0 then binding_source_action_reuses :=
             !binding_source_action_reuses + 1 else ())
        else ()
      val {is_request = is_lift_option_request, note_hit = note_lift_option_hit} =
        Comma_Semantic_B1_Construction_Check.make_lift_option_tracker
          @{const_name comma_semantic_b1_crt_lift_columns_option} lift_option_memo_hits
      fun publish_completed context request theorem =
        let
          val {equation = theorem, status = {complete, nodes}, reused_rhs, reused_closed} =
            check_equation request theorem
          val _ = value_checks := !value_checks + 1
          val _ = (value_nodes := !value_nodes + nodes;
            if reused_rhs then rhs_reuse_hits := !rhs_reuse_hits + 1 else ();
            if reused_closed then closed_reuse_hits := !closed_reuse_hits + 1 else ())
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val is_source_action = #is_source_action_request certificate_store request
          val _ = if not complete then #report_partial template_partition_profile request rhs counters else ()
          val _ = if complete then
              #note_context_request_completed certificate_store request else ()
          val _ = if complete then
              #remember_equation certificate_store context request theorem else ()
          val _ = if not complete andalso is_source_action andalso
              not (!source_partial_probe) then
            (source_partial_probe := true;
             if Comma_Proof_Profile.enabled () then
               Comma_Proof_Profile.report
                 ("B1 selected source-action partial nodes=" ^ Int.toString nodes ^
                  " rhs_head=" ^ the_default "<non-constant>" (head_name rhs) ^
                  " rhs_shape=" ^ Comma_Semantic_B1_Partition_Conversion.shape 10 rhs ^
                  " rhs_nodes_cap=" ^ Int.toString
                    (Comma_Semantic_B1_Construction_Check.capped_nodes 1024 rhs))
             else ())
            else ()
          val retained = Termtab.size (!memo) + Termtab.size (!incomplete)
        in
          if complete then
            (if retained < memo_capacity then
               (memo := Termtab.update (request, theorem) (!memo);
                publications := !publications + 1)
             else uncached := !uncached + 1;
             SOME theorem)
          else
            (if retained < memo_capacity then
               incomplete := Termtab.update (request, ()) (!incomplete)
             else uncached := !uncached + 1;
             partials := !partials + 1;
             NONE)
        end
      fun convert context cterm =
        let
                (* Reuse the simproc-certified cterm; publication still checks
                   the exact theorem shape. *)
                val request = Thm.term_of cterm
                val conversion_started = Time.now ()
                val _ = misses := !misses + 1
                val _ = last_head := the_default "<non-constant>" (head_name request)
                val _ = checkpoint ()
                val _ = if Termtab.defined (!active) request
                  then error "Recursive B1 occurrence proof conversion"
                  else ()
                val _ = active := Termtab.update (request, ()) (!active)
                val is_binding_request = #is_binding_request certificate_store request
                val is_source_action = #is_source_action_request certificate_store request
                val is_partition_certificate =
                  #is_certificate template_partition_profile request
                val is_partition_state =
                  #is_cofactor_state template_partition_profile request
                val is_template_geometry = head_name request = SOME
                  @{const_name comma_semantic_b1_crt_template_geometry_certified}
                val _ = if is_lift_option_request request then
                  lift_option_evaluations := !lift_option_evaluations + 1 else ()
                val _ = if is_source_action andalso
                    !binding_evaluation_depth > 0 then
                  binding_source_action_evaluations :=
                    !binding_source_action_evaluations + 1 else ()
                val _ = if is_binding_request then
                  binding_evaluation_depth := !binding_evaluation_depth + 1 else ()
                val attempt = #capture_conversion template_partition_profile request (fn () =>
                  let
                    val theorem =
                      if Comma_Semantic_B1_Construction_Check.is_occurrence_projection request then
                        (case !operation_context_ref of
                          SOME operation_context =>
                            #project occurrence_projector operation_context cterm
                        | NONE => error "B1 occurrence projection context is not initialized")
                      else if selected_paint_request request then
                        Simplifier.rewrite context cterm
                      else if head_name request = SOME
                          @{const_name comma_semantic_b1_crt_constructed_slot_origins} then
                        timed_origin "constructed slot origins" slot_origin_traces 8 (fn () =>
                          (case !selected_construction_contexts_ref of
                            SOME contexts => Comma_Semantic_B1_Construction_Check.bounded_upt_rewrite (#slot_origins contexts) cterm
                          | NONE => error "B1 slot-origin context is not initialized"))
                      else if head_name request = SOME
                          @{const_name comma_semantic_b1_crt_constructed_source_origins} then
                        timed_origin "constructed source origins" source_origin_traces 4 (fn () =>
                          (case !operation_context_ref of
                            SOME source_context => Comma_Semantic_B1_Construction_Check.bounded_upt_rewrite source_context cterm
                          | NONE => error "B1 source-origin context is not initialized"))
                      else if head_name request = SOME @{const_name comma_offset_orbit} then
                        (case !selected_construction_contexts_ref of
                          SOME contexts => Simplifier.rewrite (#offset_orbit contexts) cterm
                        | NONE => error "B1 offset-orbit context is not initialized")
                      else if head_name request = SOME
                          @{const_name comma_decisive_sector_period} then
                        (case !operation_context_ref of
                          SOME operation_context =>
                            Comma_Semantic_B1_CRT_Operation_Conversion.selected_period_equation
                              {ctxt = ctxt, context = operation_context,
                               period = #period endpoint_kernel,
                               shape = Comma_Semantic_B1_Partition_Conversion.shape 5} cterm
                        | NONE => error "B1 operation context is not initialized for source period")
                      else if head_name request = SOME
                          @{const_name comma_semantic_b1_source_slot_action} then
                        (* These exact closed source terms are shared once in
                           the caller's selected arithmetic context.  Sending
                           them through whole-program Code_Simp reopens the
                           period catalogue and defeats that sharing. *)
                        (case !selected_construction_contexts_ref of
                          SOME contexts => Simplifier.rewrite
                            (#source_arithmetic contexts) cterm
                        | NONE => error "B1 source arithmetic context is not initialized")
                      else if head_name request = SOME
                          @{const_name comma_semantic_b1_crt_lift_geometry_certified} then
                        #rewrite_lift_geometry certificate_store ctxt context request cterm
                      else if is_partition_state then
                        Comma_Semantic_B1_Partition_Conversion.rewrite_partition_cofactor_checked
                          (partition_operation_context ())
                          (#note_cofactor_state_rewrite template_partition_profile) cterm
                      else if is_partition_certificate orelse is_template_geometry then
                        Comma_Semantic_B1_Construction_Check.convert_template_certificate
                          {ctxt = ctxt, context = partition_operation_context (),
                           request = request, cterm = cterm,
                           note_stage_time =
                             #note_template_geometry_stage template_partition_profile,
                           prove_table_admission = prove_table_admission,
                           prove_partition_checker = prove_partition_checker}
                      else if operation_request request
                      then
                        if operation_context_request request
                        then
                          (case !operation_context_ref of
                            SOME operation_context =>
                              Simplifier.rewrite operation_context cterm
                          | NONE => error "B1 operation context is not initialized")
                        else
                          (case !operation_conversion of
                            SOME convert => #equation (convert cterm)
                          | NONE => error "B1 staged operation conversion is not initialized")
                      else if catalogue_request request
                      then Simplifier.rewrite context cterm
                    else
                      (case !code_conversion of
                        SOME conversion => conversion context cterm
                        | NONE => error "B1 occurrence code conversion is not initialized")
                    handle CTERM (reason, _) =>
                      (Comma_Proof_Profile.report
                        ("B1 occurrence conversion CTERM head=" ^ !last_head ^
                         " reason=" ^ reason ^ " request_shape=" ^
                         Comma_Semantic_B1_Partition_Conversion.shape 5 request);
                       error ("B1 occurrence conversion CTERM head=" ^
                         !last_head ^ " reason=" ^ reason ^
                         " request=" ^
                         Comma_Semantic_B1_Partition_Conversion.shape 6 request))
                  in publish_completed context request theorem end)
                val _ = if is_binding_request then
                  binding_evaluation_depth := !binding_evaluation_depth - 1 else ()
                val _ = if operation_request request orelse
                    Comma_Semantic_B1_Construction_Check.is_occurrence_projection request then
                  Comma_Semantic_B1_Construction_Check.add_named_operation_time
                    operation_times (the_default "<non-constant>" (head_name request))
                    (Time.toMilliseconds (Time.- (Time.now (), conversion_started)))
                  else ()
                val _ = active := Termtab.delete request (!active)
                val published =
                  (case attempt of
                    Exn.Res result => result
                  | Exn.Exn exn =>
                      (failures := !failures + 1; Exn.reraise exn))
                val _ = #note_result template_partition_profile request published
        in published end
      fun record_completed_hit request =
        (hits := !hits + 1; #note_memo_hit template_partition_profile request;
         note_lift_option_hit request; note_source_action_reuse request)
      fun memo_proc context ct =
        let
          val original_request = Thm.term_of ct
          val original_cofactor_state =
            #is_cofactor_state template_partition_profile original_request
          val already_active = Termtab.defined (!active) original_request
          val canonicalization =
            if not original_cofactor_state orelse already_active orelse
                not (closed original_request)
            then Thm.reflexive ct
            else
              let
                val started = Time.now ()
                val equation = (case !partition_canonicalizer_ref of
                  SOME canonicalize => canonicalize ct
                | NONE => error "B1 partition cofactor canonicalizer is not initialized")
                val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
                val _ = #note_cofactor_state_normalization template_partition_profile
                  (elapsed, not (Thm.is_reflexive equation))
              in equation end
          val request = Thm.term_of (Thm.rhs_of canonicalization)
          val canonical_ct = Thm.rhs_of canonicalization
          val projection =
            Comma_Semantic_B1_Construction_Check.is_occurrence_projection original_request
          val _ = if projection then #note_request occurrence_projector () else ()
          fun projection_miss () =
            if projection then #note_miss occurrence_projector () else ()
          fun restore_original theorem =
            if Thm.is_reflexive canonicalization then theorem
            else Thm.transitive canonicalization theorem
        in
          if not (cacheable original_request) then NONE
          else if already_active then
            (recursive := !recursive + 1; NONE)
          else if Termtab.defined (!incomplete) request then
            (projection_miss (); NONE)
          else
            let
              val _ = lookups := !lookups + 1
              val probe_started = Time.now ()
              val stored_equation = #lookup_equation certificate_store request
              val remembered_equation = (case stored_equation of
                SOME _ => NONE
              | NONE => Termtab.lookup (!memo) request)
              val _ = #note_cofactor_state_cache_probe template_partition_profile
                (Time.toMilliseconds (Time.- (Time.now (), probe_started)))
            in
             case stored_equation of
                 SOME theorem => (record_completed_hit request;
                   SOME (restore_original theorem))
             | NONE =>
                 (case remembered_equation of
                     SOME theorem =>
                       if Thm.is_reflexive theorem then NONE
                       else (record_completed_hit request;
                         if projection then #note_hit occurrence_projector () else ();
                       SOME (restore_original theorem))
                 | NONE =>
                     if not (closed request) then (projection_miss (); NONE)
                     else if Termtab.defined (!active) request then
                       (recursive := !recursive + 1; NONE)
                     else (projection_miss ();
                       (case convert context canonical_ct of
                         SOME theorem => SOME (restore_original theorem)
                       | NONE => NONE)))
            end
        end
      val proc = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_occurrence_exact_memo",
         kind = Simplifier.Congproc false,
         lhss = selected_schematic_patterns @ catalogue_schematic_patterns,
         proc = fn _ => memo_proc,
         identifier = []}
      val selectors = catalogue_setup ctxt
      val _ = milestone "after-catalogue-setup"
      val _ = milestone "before-evaluation-context-setup"
      val evaluation_context = (code_context addsimps Comma_Semantic_B1_Construction_Check.occurrence_cache_catalogue_simp_rules)
        |> fold Simplifier.add_proc (#procedures selectors)
        |> Simplifier.add_proc proc
        |> fold Simplifier.add_proc [#procedure columns, #post_procedure columns]
      val construction_context = ((evaluation_context addsimps
        Comma_Semantic_B1_Construction_Check.occurrence_cache_arithmetic_rules) delsimps @{thms sort_key_simps insort_key.simps})
        |> Simplifier.add_proc
          (Comma_Semantic_B1_Construction_Check.make_origin_sort_proc ctxt)
      val operation_base_context =
        Comma_Entry_Arithmetic.natural_context ctxt
        |> (fn context => context addsimps (Comma_Semantic_B1_Construction_Check.occurrence_cache_checker_simp_rules @ Comma_Semantic_B1_Construction_Check.occurrence_cache_catalogue_simp_rules))
        |> fold Simplifier.add_proc (#procedures selectors)
        |> Simplifier.add_proc proc
        |> fold Simplifier.add_proc [#procedure columns, #post_procedure columns]
      val operation_context =
        Comma_Semantic_B1_CRT_Operation_Conversion.operation_context operation_base_context
      val _ = operation_context_ref := SOME operation_context
      val _ = partition_canonicalizer_ref := SOME
        (Comma_Semantic_B1_Partition_Conversion.make_partition_cofactor_canonicalizer
          operation_context
          {note_shape_check = #note_cofactor_state_shape_check template_partition_profile,
           note_shape_cache_hit =
             #note_cofactor_state_shape_cache_hit template_partition_profile})
      val _ = timed_origin "selected context setup" context_build_traces 1 (fn () =>
        selected_construction_contexts_ref := SOME
          (Comma_Semantic_B1_Selected_Contexts.make ctxt operation_context
            Comma_Semantic_B1_Construction_Check.occurrence_cache_arithmetic_rules (#simproc endpoint_kernel)))
      val _ = milestone "after-evaluation-context-setup"
      val _ = milestone "before-static-converter-init"
      val _ = code_conversion := SOME (Code_Simp.static_conv
        {ctxt = ctxt, simpset = SOME (Simplifier.simpset_of evaluation_context),
         consts = filter_out (member (op =) operation_roots) Comma_Semantic_B1_Construction_Check.occurrence_cache_generic_constants})
      val apply_depth_rules =
        Comma_Semantic_B1_CRT_Operation_Conversion.apply_depth_simp_rules ctxt
      val operation_boundaries =
        Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_boundaries
          apply_depth_rules
      val _ = operation_conversion := SOME
        (Comma_Semantic_B1_CRT_Operation_Conversion.make_staged_operation_converter
          {context = operation_context, boundaries = operation_boundaries,
           staged_heads =
             Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_staged_heads,
           lazy_function_heads =
             Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_lazy_function_heads,
           final_argument_stagers = [],
           complete_value = complete_value})
      val _ = milestone "after-static-converter-init"
      val _ = Comma_Semantic_B1_Certificate_Store_Fixtures.check_cofactor_state_warm_memo
        {ctxt = ctxt, context = operation_context,
         with_partition_scope = (fn work => Exn.release
           (#capture_conversion template_partition_profile
             @{term "comma_semantic_b1_crt_columns_partition_certified []"} work)),
         state_counts = #cofactor_state_counts template_partition_profile,
         canonicalize = (case !partition_canonicalizer_ref of SOME canonicalize => canonicalize
           | NONE => error "B1 partition cofactor canonicalizer was not initialized"),
         memo_proc = memo_proc, isolate = (fn work => work ())}
      val _ = (memo := Termtab.empty; incomplete := Termtab.empty;
        active := Termtab.empty; lookups := 0; hits := 0; misses := 0;
        publications := 0; failures := 0; recursive := 0;
        value_checks := 0; value_nodes := 0;
        rhs_reuse_hits := 0; closed_reuse_hits := 0; last_head := "<none>";
        #reset_cofactor_run_counts template_partition_profile ())
      val _ = Comma_Semantic_B1_Certificate_Store_Fixtures.check_partial_equation_gate
        {ctxt = ctxt, context = evaluation_context,
         publish = (fn request => fn theorem => publish_completed ctxt request theorem),
         dispatch = (fn cterm => memo_proc evaluation_context cterm),
         memo_has = (fn request => Termtab.defined (!memo) request),
         incomplete_has = (fn request => Termtab.defined (!incomplete) request),
         memo_size = (fn () => Termtab.size (!memo)),
         publication_count = (fn () => !publications),
         clear_incomplete = (fn request => incomplete :=
           Termtab.delete request (!incomplete))}
      val _ = milestone "after-incomplete-equation-regression"
      val _ = Comma_Semantic_B1_Column_Regression.check_cache_column_dispatch
        ctxt evaluation_context operation_context (#post_procedure columns) (#column_value columns)
        (#known_column columns) (#node_count columns) (#step columns)
        (#head_opens columns)
      val _ = Comma_Semantic_B1_Certificate_Store_Fixtures.check_projection_memo_dispatch
        (fn request => memo_proc operation_context (Thm.cterm_of ctxt request))
        hits misses (#head_opens columns)
      val _ = Comma_Semantic_B1_Construction_Check.check_evaluator_smoke
        {ctxt = ctxt, context = evaluation_context, counters = counters,
         capped_nodes = Comma_Semantic_B1_Construction_Check.capped_nodes,
         shape = Comma_Semantic_B1_Partition_Conversion.shape}
      val _ = milestone "after-typed-smoke"
      fun select_root_occurrence cterm =
        Comma_Semantic_B1_Construction_Check.select_root_occurrence
          {ctxt = ctxt, context = evaluation_context, closed = closed,
           validate_equation = validate_equation} cterm

      fun selected_action_context () =
        (case !selected_action_context_ref of
          SOME context => context
        | NONE =>
            let
              val context = evaluation_context addsimps split_action_rules
              val _ = selected_action_context_ref := SOME context
            in context end)

      fun convert_selected cterm =
        let
          val request = Thm.term_of cterm
          val context = selected_action_context ()
          val action_definition = hd
            (Proof_Context.get_thms ctxt "comma_crt_occurrence_split_action_def")
          val definition_lhs =
            (case try Thm.lhs_of action_definition of
              SOME lhs => Thm.term_of lhs
            | NONE =>
                let
                  val (lhs, _) = HOLogic.dest_eq
                    (HOLogic.dest_Trueprop (Thm.prop_of action_definition))
                in lhs end)
          val expected_head = head_name definition_lhs
          val (request_head, arguments) = strip_comb request
          val _ = (case (request_head, arguments) of
            (Const (name, _), [occurrence]) =>
              if expected_head = SOME name andalso closed occurrence andalso
                  fastype_of occurrence = domain_type (fastype_of request_head)
              then () else error "B1 selected action request has a foreign occurrence"
          | _ => error "B1 selected action request must have one occurrence argument")
          val _ = if closed request then ()
            else error "B1 selected action request is not closed"
          val theorem = Simplifier.rewrite context cterm
        in validate_equation request theorem end
      fun report () =
        counters () ^ " " ^ #stats selectors () ^ " " ^
        #stats occurrence_projector () ^ endpoint_stats ()

      fun prove cterm =
        let
          val request = Thm.term_of cterm
          val construction_handler = Unsynchronized.ref
            (NONE: (term -> thm) option)
          val component_counter = Synchronized.var
            "semantic_b1_construction_component_traces" 0
          val construction_progress = Synchronized.var
            "semantic_b1_construction_progress" 0
          val item_counter = Synchronized.var
            "semantic_b1_construction_item_traces" 0
          fun prove_true_using small_upt context proposition =
            let
              val construction =
                (case strip_comb proposition of
                  (Const (name, _), [_]) =>
                    name = @{const_name comma_semantic_b1_crt_construction_check}
                | _ => false)
              val theorem =
                if construction then
                  (case !construction_handler of
                    SOME check => check proposition
                  | NONE => error "B1 construction checker is not initialized")
                else
                  let
                    val goal = Thm.cterm_of ctxt (HOLogic.mk_Trueprop proposition)
                    val first_pass = Simplifier.rewrite context goal
                    val normalized =
                      if not small_upt then first_pass
                      else
                        let
                          val residual = HOLogic.dest_Trueprop
                            (Thm.term_of (Thm.rhs_of first_pass))
                        in
                          (case Comma_Semantic_B1_CRT_Operation_Conversion.small_closed_upt_context
                              context residual of
                            SOME small_context => Thm.transitive first_pass
                              (Simplifier.rewrite small_context (Thm.rhs_of first_pass))
                          | NONE => first_pass)
                        end
                    val rhs = Thm.term_of (Thm.rhs_of normalized)
                    val _ = if rhs aconv @{prop True} then ()
                      else
                        let
                          val reduced = HOLogic.dest_Trueprop rhs
                          val status =
                            if reduced aconv @{term False} then "false"
                            else if reduced aconv proposition then "unchanged"
                            else "residual"
                          val _ = Comma_Proof_Profile.report
                            ("B1 occurrence item failure head=" ^
                             (case head_name proposition of SOME name => name | NONE => "boolean") ^
                             " status=" ^ status ^
                             " normalized_nodes_cap=" ^ Int.toString
                               (Comma_Semantic_B1_Construction_Check.capped_nodes 2048 reduced) ^
                             " normalized_shape=" ^
                               Comma_Semantic_B1_Partition_Conversion.shape 5 reduced ^
                             " counters=" ^ counters () ^ endpoint_stats ())
                        in error ("B1 occurrence item failed: " ^
                          (case head_name proposition of SOME name => name | NONE => "boolean") ^
                          " counters=" ^ counters () ^ endpoint_stats ()) end
                  in Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI} end
              val _ = checked_items := !checked_items + 1
              val _ = if Comma_Proof_Profile.enabled () andalso
                  !checked_items mod 32 = 0 then
                Comma_Proof_Profile.report
                  ("B1 occurrence indexed items=" ^ Int.toString (!checked_items) ^
                   " " ^ counters () ^ " " ^ #stats selectors () ^ endpoint_stats ()) else ()
              val _ = if Thm.prop_of theorem aconv
                  HOLogic.mk_Trueprop proposition then ()
                else error "B1 occurrence item theorem changed its proposition"
            in theorem end

          fun prove_list_all prove_selected context predicate range =
        let
              (* Normalize the upper bound, then prove items by zero/Suc. *)
              val predicate_name =
                the_default "non-constant" (head_name predicate)
              val (range_head, range_args) = strip_comb range
              val (lower, upper) =
                (case (range_head, range_args) of
                  (Const (name, _), [lo, hi]) =>
                    if name = @{const_name upt} then (lo, hi)
                    else error "B1 indexed certificate expected an upt range"
                | _ => error "B1 indexed certificate expected a closed upt range")
              val _ = if lower aconv @{term "0::nat"} andalso
                  fastype_of range = @{typ "nat list"} andalso
                  fastype_of predicate = @{typ "nat => bool"}
                then () else error "B1 indexed certificate expected a natural zero-based range"
              val upper_selected = Simplifier.rewrite context
                (Thm.cterm_of ctxt upper)
              val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt
              val upper_scalar = Simplifier.rewrite scalar_context
                (Thm.rhs_of upper_selected)
              val upper_equation = validate_equation upper
                (Thm.transitive upper_selected upper_scalar)
              val (_, bound) = HOLogic.dest_number
                (Thm.term_of (Thm.rhs_of upper_equation))
              val (predicate_label, declared_extent) =
                Comma_Semantic_B1_Construction_Check.indexed_extent_contract
                  predicate upper
              val _ = if
                  Comma_Semantic_B1_Construction_Check.indexed_extent_admitted
                    bound declared_extent then ()
                else error ("B1 indexed certificate range exceeds its declared extent: " ^
                  "predicate=" ^ predicate_label ^ " bound=" ^ Int.toString bound ^
                  " declared_extent=" ^ Int.toString declared_extent)
              val natT = @{typ nat}
              val list_type = @{typ "nat list"}
              val list_all = Const (@{const_name list_all},
                fastype_of predicate --> list_type --> @{typ bool}) $ predicate
          fun prove_item index =
                let
                  val item_stage = predicate_name ^ "-item-" ^ Int.toString index
                  val theorem = Comma_Proof_Profile.trace_stage
                    (Comma_Proof_Profile.enabled ()) item_counter
                    (fn current => (current, current + 1)) 256
                    "B1 occurrence indexed list" item_stage
                    (fn () => Comma_Semantic_B1_Construction_Check.prove_beta_item
                      ctxt prove_selected (predicate $
                        Comma_Semantic_B1_CRT_Operation_Conversion.natural_numeral index))
                in theorem end
              val prefix = Comma_Selected_List_Conversion.prove_indexed_list_all
                {ctxt = ctxt, predicate = predicate, bound = bound,
                 prove_item = prove_item,
                 zero_fact = @{thm comma_indexed_all_zero},
                 step_fact = @{thm comma_indexed_all_Suc}, successor_equation = #equation indexed_successors}
              val normalized_range = Const (@{const_name upt},
                natT --> natT --> list_type) $ lower $
                  Comma_Semantic_B1_CRT_Operation_Conversion.natural_numeral bound
              val application_eq = Conv.arg_conv
                (Conv.arg_conv (Conv.rewr_conv upper_equation))
                (Thm.cterm_of ctxt (list_all $ range))
              val _ = if Thm.term_of (Thm.rhs_of application_eq) aconv
                  list_all $ normalized_range then ()
                else error "B1 indexed range normalization changed its structure"
              val proposition_eq = Thm.combination
                (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) application_eq
              val _ = if Thm.prop_of prefix aconv
                  HOLogic.mk_Trueprop (list_all $ normalized_range) then ()
                else error "B1 indexed recurrence does not match its normalized bound"
            in Thm.equal_elim (Thm.symmetric proposition_eq) prefix end
          fun prove_expression small_upt context expression =
            (case try (HOLogic.dest_bin @{const_name HOL.conj} @{typ bool}) expression of
              SOME (left, right) =>
                @{thm conjI} OF
                  [prove_expression small_upt context left,
                   prove_expression small_upt context right]
            | NONE =>
                (case strip_comb expression of
                  (Const (name, _), [predicate, range]) =>
                    if name = @{const_name list_all}
                    then
                      if predicate aconv @{term "comma_crt_admitted (0::nat)"}
                          andalso range aconv @{term comma_semantic_b1_crt_columns}
                      then prove_table_admission ()
                      else if head_name range = SOME @{const_name upt} then
                        prove_list_all (prove_expression small_upt context)
                          context predicate range
                      else prove_true_using small_upt context expression
                    else prove_true_using small_upt context expression
                | _ => prove_true_using small_upt context expression))
          val _ = construction_handler := SOME (fn proposition =>
            Comma_Semantic_B1_Construction_Check.prove_construction
              {ctxt = ctxt, evaluation_context = evaluation_context,
               construction_context = construction_context,
               prove_expression = prove_expression,
               component_counter = component_counter,
               progress_counter = construction_progress,
               reset_certificate_source =
                 #reset_current_source certificate_store,
               profile_certificate_source =
                 #profile_current_source certificate_store} proposition)
          val definition = @{thm comma_semantic_b1_crt_occurrence_data_checked_def}
            RS @{thm eq_reflection}
          val unfolded = Conv.arg_conv (Conv.rewr_conv definition) cterm
          val rhs = HOLogic.dest_Trueprop (Thm.term_of (Thm.rhs_of unfolded))
                  val rhs_proof = prove_expression false evaluation_context rhs
          val theorem = Thm.equal_elim (Thm.symmetric unfolded) rhs_proof
          val _ = milestone "after-piecewise-proof"
          val _ = if Thm.prop_of theorem aconv request andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) then ()
            else error "B1 occurrence checker did not prove its aggregate claim"
        in theorem end
    in {prove = prove, report = report,
        select_root_occurrence = select_root_occurrence,
        convert_selected = convert_selected} end
  fun tactic ctxt i =
    let
      val started = Time.now ()
      fun solve (goal, subgoal) =
        let
          val cterm = Thm.cterm_of ctxt goal
          val request = goal
          val expected = HOLogic.mk_Trueprop
            @{term comma_semantic_b1_crt_occurrence_data_checked}
          val _ = if request aconv expected then ()
            else error "B1 occurrence cache method used for an unexpected goal"
          val evaluator = make ctxt
          val theorem = #prove evaluator cterm
          val _ = if Comma_Proof_Profile.enabled () then
            let val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
            in Comma_Proof_Profile.report
              ("B1 occurrence proof cache completed " ^ #report evaluator () ^
               " elapsed_ms=" ^ LargeInt.toString elapsed) end
            else ()
        in
          resolve_tac ctxt [theorem] subgoal
        end
    in SUBGOAL solve i end
  val _ = Theory.setup
    (Method.setup @{binding comma_semantic_b1_occurrence_check}
      (Scan.succeed (fn ctxt => SIMPLE_METHOD' (tactic ctxt)))
      "proof-producing cached evaluation of the B1 occurrence certificate")
end
