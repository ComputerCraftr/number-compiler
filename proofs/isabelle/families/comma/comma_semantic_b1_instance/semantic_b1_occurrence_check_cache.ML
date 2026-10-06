(* Proof-producing evaluator memoizing only exact closed occurrence/CRT terms. *)
structure Comma_Semantic_B1_Occurrence_Check_Cache =
struct
  val memo_capacity = 8192

  val generic_constants =
    [@{const_name comma_semantic_b1_crt_occurrence_geometry_check},
     @{const_name comma_semantic_b1_crt_lift_local_cover_witness},
     @{const_name comma_semantic_b1_crt_lift_local_slot_valid},
     @{const_name comma_semantic_b1_crt_local_piece_covered},
     @{const_name comma_semantic_b1_crt_local_parent_column},
     @{const_name comma_semantic_b1_crt_find_result_index},
     @{const_name comma_semantic_b1_crt_lift_slot_valid},
     @{const_name comma_semantic_b1_crt_lift_columns_option},
     @{const_name comma_semantic_b1_crt_occurrence_entry_checked},
     @{const_name comma_semantic_b1_crt_occurrence_binding_check},
     @{const_name comma_semantic_b1_terminal_action_result},
     @{const_name comma_crt_equiv_check},
     @{const_name comma_crt_supported},
     @{const_name comma_crt_admitted},
     @{const_name comma_crt_apply},
     @{const_name comma_crt_apply_shifted},
     @{const_name comma_crt_group_rows},
     @{const_name comma_crt_group_column},
     @{const_name comma_crt_negate}]

  val catalogue_constants =
    [@{const_name comma_semantic_b1_crt_occurrence_at_index},
     @{const_name comma_semantic_b1_crt_resolve_descriptor}]

  val cached_patterns =
    [@{term "comma_semantic_b1_crt_occurrence_geometry_check columns"},
     @{term "comma_semantic_b1_crt_geometry_fold accumulated entries"},
     @{term "comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at occurrence_descriptors templates source parent refs descriptors"},
     @{term "comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at occurrence_descriptors templates source parent refs descriptors slot"},
     @{term "comma_semantic_b1_crt_local_piece_covered parent candidate result"},
     @{term "comma_semantic_b1_crt_local_parent_column parent result"},
     @{term "comma_semantic_b1_crt_find_result_index beta result"},
     @{term "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at occurrence_descriptors templates source parent refs descriptors slot"},
     @{term "comma_semantic_b1_crt_lift_columns_option templates descriptor"},
     @{term "comma_semantic_b1_crt_occurrence_entry_checked index"},
     @{term "comma_semantic_b1_crt_lift_ref_slot ref"},
     @{term "comma_semantic_b1_crt_lift_ref_cid ref"},
     @{term "comma_semantic_b1_crt_lift_ref_parent ref"},
     @{term "comma_semantic_b1_crt_lift_ref_child_index ref"},
     @{term "comma_semantic_b1_crt_lift_descriptor_period descriptor"},
     @{term "comma_semantic_b1_crt_lift_descriptor_slot descriptor"},
     @{term "comma_semantic_b1_crt_lift_descriptor_template_cid descriptor"},
     @{term "comma_semantic_b1_crt_lift_descriptor_net_shift descriptor"},
     @{term "comma_semantic_b1_crt_occurrence_binding_check occurrence"},
     @{term "comma_crt_occurrence_split_action occurrence"},
     @{term "comma_crt_occurrence_split_from_bindings rebase columns outcomes action"},
     @{term "comma_crt_mdd_paint_binding rebase column outcome action"},
     @{term "comma_crt_equiv_check left right"},
     @{term "comma_crt_supported column"},
     @{term "comma_crt_admitted lower column"},
     @{term "comma_crt_apply operation left right"},
     @{term "comma_crt_apply_shifted operation shift left right"},
     @{term "comma_crt_group_rows rows"},
     @{term "comma_crt_group_column outcome rows"},
     @{term "comma_crt_negate column"}]

  val catalogue_patterns =
    [@{term "length comma_semantic_b1_crt_sources"},
     @{term "length comma_semantic_b1_crt_descriptors"},
     @{term "length comma_semantic_b1_crt_root_occurrence_indices"},
     @{term "length comma_semantic_b1_crt_lift_descriptors"},
     @{term "length comma_semantic_b1_crt_sources = length comma_semantic_b1_crt_descriptors"},
     @{term "length comma_semantic_b1_crt_lift_descriptors \<le> 28 * length comma_semantic_b1_crt_sources"},
     @{term "length comma_semantic_b1_crt_lift_refs = length comma_semantic_b1_crt_sources"},
     @{term "length comma_semantic_b1_crt_lift_refs"},
     @{term "comma_semantic_b1_crt_source_order_step index"},
     @{term "length comma_semantic_b1_crt_root_occurrence_indices = 46"},
     @{term "comma_semantic_b1_crt_template_geometry_at index"},
     @{term "comma_semantic_b1_crt_occurrence_entry_checked index"},
     @{term "comma_semantic_b1_crt_lift_refs ! index"},
     @{term "comma_semantic_b1_crt_lift_descriptors ! index"}]

  val checker_simp_rules =
    @{thms comma_semantic_b1_crt_occurrence_data_checked_def
      comma_semantic_b1_crt_template_geometry_at_def
      comma_semantic_b1_crt_occurrence_entry_checked_def
      comma_semantic_b1_crt_source_order_key_def
      comma_semantic_b1_crt_source_order_step_def
      comma_semantic_b1_crt_lift_local_cover_witness_def
      comma_semantic_b1_crt_lift_local_slot_valid_def
      comma_semantic_b1_crt_local_piece_covered_def
      comma_semantic_b1_crt_local_parent_column_def
      comma_semantic_b1_crt_find_result_index.simps
      comma_semantic_b1_crt_lift_slot_valid_def
      comma_semantic_b1_crt_lift_descriptor_valid_def
      comma_semantic_b1_crt_lift_columns_option_def
      comma_semantic_b1_crt_occurrence_binding_check_def
      comma_semantic_b1_crt_lift_ref_slot.simps
      comma_semantic_b1_crt_lift_ref_parent.simps
      comma_semantic_b1_crt_lift_ref_child_index.simps
      comma_semantic_b1_crt_lift_ref_cid.simps
      comma_semantic_b1_crt_lift_descriptor.select_convs
      comma_semantic_b1_crt_occurrence_geometry_check_def
      comma_semantic_b1_crt_occurrence_indexed_columns_def
      comma_semantic_b1_source_slot_action_code
      comma_semantic_b1_source_slot_action_width_def
      comma_semantic_b1_terminal_action_result.simps
      comma_semantic_b1_source_slot_scope_def
      comma_crt_source_scope_column_def
      comma_crt_source_axis_column_def
      comma_near_terminal_width_j_def
      comma_source_continuation_action_of_packet.simps
      comma_source_continuation_base.simps comma_round_admitted.simps
      comma_decisive_sector_period_def
      comma_semantic_b1_crt_occurrence.select_convs
      list_all_Nil_iff list_all_Cons_iff}

  val catalogue_simp_rules =
    @{thms comma_semantic_b1_crt_occurrence_at_index_def
      comma_semantic_b1_crt_root_occurrence_def
      comma_semantic_b1_crt_resolve_descriptor_def
      distinct.simps option.case list.case prod.case Let_def}

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
      val selectors =
        [select "sources" @{thm comma_semantic_b1_crt_sources_def}
           @{term "comma_semantic_b1_crt_sources ! index"} [1024],
         select "descriptors" @{thm comma_semantic_b1_crt_descriptors_def}
           @{term "comma_semantic_b1_crt_descriptors ! index"} [1024],
         select "templates" @{thm comma_semantic_b1_crt_templates_def}
           @{term "comma_semantic_b1_crt_templates ! index"} [1024],
         select "root_indices" @{thm comma_semantic_b1_crt_root_occurrence_indices_def}
           @{term "comma_semantic_b1_crt_root_occurrence_indices ! index"} [46],
         (* At most 1024 checked sources times the declared maximum period 28. *)
         select "lift_descriptors"
           @{thm comma_semantic_b1_crt_lift_descriptors_def}
           @{term "comma_semantic_b1_crt_lift_descriptors ! index"} [1024 * 28],
         select "lift_refs"
           @{thm comma_semantic_b1_crt_lift_refs_def}
           @{term "comma_semantic_b1_crt_lift_refs ! index"} [1024],
         select "offsets" @{thm comma_offset_representatives_def}
           @{term "comma_offset_representatives ! index"} [46]]
      val procedures = map #procedure selectors
      fun stats () = String.concatWith " "
        (map (fn selector => #stats selector ()) selectors)
      val context = fold Simplifier.add_proc procedures
        (ctxt addsimps catalogue_simp_rules)
      val _ = Comma_Proof_Profile.report
        ("B1 occurrence cache stage=catalogue-setup-complete elapsed_ms=" ^
         Comma_Proof_Profile.elapsed_ms started)
    in
      {context = context, procedures = procedures, stats = stats}
    end

  fun make ctxt =
    let
      val started = Time.now ()
      val _ = Comma_Proof_Profile.report
        "B1 occurrence cache stage=make-entry"
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
      val value_checks = Unsynchronized.ref 0
      val value_nodes = Unsynchronized.ref 0
      val rhs_reuse_hits = Unsynchronized.ref 0 and closed_reuse_hits = Unsynchronized.ref 0
      val last_head = Unsynchronized.ref "<none>"
      val checked_items = Unsynchronized.ref 0
      val geometry_fold_lookups = Unsynchronized.ref 0
      val geometry_fold_hits = Unsynchronized.ref 0
      val selected_row_visits = Unsynchronized.ref 0
      val selected_row_lets = Unsynchronized.ref 0
      val selected_row_conversions = Unsynchronized.ref 0 and
        selected_row_conversion_ms = Unsynchronized.ref 0
      val operation_times = Unsynchronized.ref
        (Symtab.empty: (int * LargeInt.int) Symtab.table)
      fun geometry_fold_request request =
        head_name request = SOME @{const_name comma_semantic_b1_crt_geometry_fold}
      fun add_operation_time name elapsed =
        let
          val (calls, total) = the_default (0, 0)
            (Symtab.lookup (!operation_times) name)
        in
          operation_times := Symtab.update (name, (calls + 1, total + elapsed))
            (!operation_times)
        end
      fun operation_timing_report () =
        String.concatWith " "
          (map (fn (name, (calls, elapsed)) =>
            Long_Name.base_name name ^ "_calls=" ^ Int.toString calls ^
            "_inclusive_ms=" ^ LargeInt.toString elapsed)
          (Symtab.dest (!operation_times)))
      fun counters () =
        "lookups=" ^ Int.toString (!lookups) ^
        " hits=" ^ Int.toString (!hits) ^
        " misses=" ^ Int.toString (!misses) ^
        " publications=" ^ Int.toString (!publications) ^
        " partials=" ^ Int.toString (!partials) ^
        " uncached=" ^ Int.toString (!uncached) ^
        " failures=" ^ Int.toString (!failures) ^
        " recursive=" ^ Int.toString (!recursive) ^
        " value_checks=" ^ Int.toString (!value_checks) ^
        " value_nodes=" ^ Int.toString (!value_nodes) ^ " rhs_reuse_hits=" ^ Int.toString (!rhs_reuse_hits) ^ " closed_reuse_hits=" ^ Int.toString (!closed_reuse_hits) ^
        " retained=" ^ Int.toString (Termtab.size (!memo)) ^
        " geometry_fold_lookups=" ^ Int.toString (!geometry_fold_lookups) ^
        " geometry_fold_hits=" ^ Int.toString (!geometry_fold_hits) ^
        " selected_row_conversions=" ^ Int.toString (!selected_row_conversions) ^
        " selected_row_visits=" ^ Int.toString (!selected_row_visits) ^
        " selected_row_lets=" ^ Int.toString (!selected_row_lets) ^
        " selected_row_conversion_ms=" ^
          LargeInt.toString (!selected_row_conversion_ms) ^
        (case operation_timing_report () of
          "" => ""
        | timings => " operation_timing=" ^ timings)
      fun capped_nodes cap term =
        let
          fun visit terms count =
            if count >= cap then cap
            else
              (case terms of
                [] => count
              | current :: rest =>
                  let val (_, arguments) = strip_comb current
                  in visit (arguments @ rest) (count + 1) end)
        in visit [term] 0 end
      fun shape depth term =
        let
          fun label current =
            (case Term.head_of current of
              Const (name, _) => Long_Name.base_name name
            | Free (_, _) => "Free"
            | Var (_, _) => "Var"
            | Bound _ => "Bound"
            | Abs _ => "Abs")
          val head = label term
          val (_, arguments) = strip_comb term
        in
          if depth = 0 orelse null arguments then head
          else head ^ "(" ^ String.concatWith ","
            (map (shape (depth - 1)) (take 4 arguments)) ^
            (if length arguments > 4 then ",..." else "") ^ ")"
        end

      fun checkpoint () =
        if !misses mod 1024 = 0 then
          let
            val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
          in
            Comma_Proof_Profile.report
              ("B1 occurrence proof cache checkpoint " ^ counters () ^
               " last_head=" ^ !last_head ^
               " elapsed_ms=" ^ LargeInt.toString elapsed)
          end
        else ()

      fun milestone label =
        let
          val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
        in
          Comma_Proof_Profile.report
            ("B1 occurrence proof cache " ^ label ^ " " ^ counters () ^
             " elapsed_ms=" ^ LargeInt.toString elapsed)
        end

      val _ = milestone "before-code-context-setup"
      val code_context = ctxt addsimps checker_simp_rules
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
      val local_cover_context_ref = Unsynchronized.ref
        (NONE: Proof.context option)
      val selector_context_ref = Unsynchronized.ref
        (NONE: Proof.context option)
      val selected_action_context_ref = Unsynchronized.ref
        (NONE: Proof.context option)
      val thy = Proof_Context.theory_of ctxt
      val {patterns = paint_patterns, roots = paint_roots} =
        Comma_Semantic_B1_CRT_Operation_Conversion.selected_paint_memo_spec ctxt
      val selected_patterns = cached_patterns @
        Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_base_patterns @
        paint_patterns
      val selected_schematic_patterns = map schematize selected_patterns
      val catalogue_schematic_patterns = map schematize catalogue_patterns
      fun matches patterns request =
        exists (fn pattern => Pattern.matches thy (pattern, request)) patterns

      fun cacheable request =
        member (op =) generic_constants
          (the_default "" (head_name request)) orelse
        matches selected_schematic_patterns request orelse
        matches catalogue_schematic_patterns request
      val {check = check_equation, complete_value} =
        Comma_Semantic_B1_CRT_Operation_Conversion.make_equation_checker ctxt
      fun catalogue_request request =
        member (op =) catalogue_constants (the_default "" (head_name request)) orelse
        matches catalogue_schematic_patterns request
      val operation_roots =
        [@{const_name comma_semantic_b1_crt_occurrence_geometry_check},
         @{const_name comma_semantic_b1_crt_geometry_fold},
         @{const_name comma_semantic_b1_crt_lift_local_cover_witness},
         @{const_name comma_semantic_b1_crt_lift_local_slot_valid},
         @{const_name comma_semantic_b1_crt_local_piece_covered},
         @{const_name comma_semantic_b1_crt_local_parent_column},
         @{const_name comma_semantic_b1_crt_find_result_index},
         @{const_name comma_semantic_b1_crt_lift_slot_valid},
         @{const_name comma_semantic_b1_crt_lift_columns_option},
         @{const_name comma_crt_occurrence_split_action},
         @{const_name comma_crt_occurrence_split_from_bindings},
         @{const_name comma_crt_mdd_paint_binding},
         @{const_name comma_semantic_b1_crt_occurrence_entry_checked},
         @{const_name comma_semantic_b1_terminal_action_result},
         @{const_name comma_semantic_b1_crt_occurrence_binding_check},
         @{const_name comma_crt_equiv_check}, @{const_name comma_crt_supported},
         @{const_name comma_crt_admitted}, @{const_name comma_crt_apply},
         @{const_name comma_crt_apply_shifted}, @{const_name comma_crt_negate},
         @{const_name comma_crt_group_rows}, @{const_name comma_crt_group_column}] @
        paint_roots @
        Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_base_heads
      val operation_context_roots =
        [@{const_name comma_semantic_b1_crt_occurrence_geometry_check},
         @{const_name comma_semantic_b1_crt_geometry_fold},
         @{const_name comma_semantic_b1_crt_lift_slot_valid},
         @{const_name comma_semantic_b1_crt_lift_columns_option},
         @{const_name comma_crt_occurrence_split_action},
         @{const_name comma_crt_occurrence_split_from_bindings},
         @{const_name comma_crt_mdd_paint_binding},
         @{const_name comma_semantic_b1_crt_occurrence_entry_checked},
         @{const_name comma_semantic_b1_terminal_action_result},
         @{const_name comma_semantic_b1_crt_occurrence_binding_check}]
      val local_cover_roots =
        [@{const_name comma_semantic_b1_crt_lift_local_cover_witness},
         @{const_name comma_semantic_b1_crt_lift_local_slot_valid},
         @{const_name comma_semantic_b1_crt_local_piece_covered},
         @{const_name comma_semantic_b1_crt_local_parent_column},
         @{const_name comma_semantic_b1_crt_find_result_index}]
      fun operation_request request =
        member (op =) operation_roots (the_default "" (head_name request))
      fun operation_context_request request =
        member (op =) operation_context_roots (the_default "" (head_name request))
      fun local_cover_request request =
        member (op =) local_cover_roots (the_default "" (head_name request))
      fun selected_paint_request request =
        member (op =) paint_roots (the_default "" (head_name request))

      val geometry_check_name =
        @{const_name comma_semantic_b1_crt_occurrence_geometry_check}
      fun selected_geometry_rewrite operation_context cterm =
        let
          val started = Time.now ()
          fun unfold_let _ current =
            let
              val _ = selected_row_visits := !selected_row_visits + 1
              val term = Thm.term_of current
            in
              (case term of
                Const (name, _) =>
                  if name = @{const_name Let} then
                    (selected_row_lets := !selected_row_lets + 1;
                     Conv.rewr_conv @{thm Let_def[abs_def]} current)
                  else Conv.all_conv current
              | _ => Conv.all_conv current)
            end
          val selector_context =
            (case !selector_context_ref of
              SOME context => context
            | NONE => error "B1 selector-only context is not initialized")
          val selected = Simplifier.rewrite selector_context cterm
          val lets_removed = Conv.bottom_conv unfold_let ctxt
            (Thm.rhs_of selected)
          val beta_normalized = Thm.beta_conversion true
            (Thm.rhs_of lets_removed)
          val selected_beta = Thm.transitive selected
            (Thm.transitive lets_removed beta_normalized)
          val selected_request = Thm.term_of (Thm.rhs_of selected_beta)
          val selected_was_active = Termtab.defined (!active) selected_request
          val _ = if selected_was_active then ()
            else active := Termtab.update (selected_request, ()) (!active)
          fun rewrite_leaf leaf = Simplifier.rewrite operation_context leaf
          val simplify_attempt = Exn.capture (fn () =>
            let
              val definition = @{thm
                comma_semantic_b1_crt_occurrence_geometry_check_def} RS
                  @{thm eq_reflection}
              val definition_step = Conv.rewr_conv definition
                (Thm.rhs_of selected_beta)
              val let_step = Conv.fun_conv (Conv.fun_conv
                (Conv.rewr_conv @{thm Let_def[abs_def]}))
                (Thm.rhs_of definition_step)
              val beta_step = Thm.beta_conversion true (Thm.rhs_of let_step)
              val expanded = Thm.transitive definition_step
                (Thm.transitive let_step beta_step)
              val split =
                Comma_Semantic_B1_CRT_Operation_Conversion.rewrite_conjuncts
                  rewrite_leaf (Thm.rhs_of expanded)
              val reduced = Simplifier.rewrite operation_context (Thm.rhs_of split)
            in Thm.transitive expanded (Thm.transitive split reduced) end) ()
          val _ = if selected_was_active then ()
            else active := Termtab.delete selected_request (!active)
          val simplified = Exn.release simplify_attempt
          val result = Thm.transitive selected_beta simplified
          val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
          val _ = selected_row_conversions := !selected_row_conversions + 1
          val _ = selected_row_conversion_ms :=
            !selected_row_conversion_ms + elapsed
        in result end

      fun publish_completed request theorem =
        let
          val {equation = theorem, status = {complete, nodes}, reused_rhs, reused_closed} =
            check_equation request theorem
          val _ = value_checks := !value_checks + 1
          val _ = (value_nodes := !value_nodes + nodes;
            if reused_rhs then rhs_reuse_hits := !rhs_reuse_hits + 1 else ();
            if reused_closed then closed_reuse_hits := !closed_reuse_hits + 1 else ())
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
                val attempt = Exn.capture (fn () =>
                  let
                    val theorem =
                      if selected_paint_request request then
                        Simplifier.rewrite context cterm
                      else if operation_request request
                      then
                        if local_cover_request request then
                          (case !local_cover_context_ref of
                            SOME local_context => Simplifier.rewrite local_context cterm
                          | NONE => error "B1 local-cover context is not initialized")
                        else if operation_context_request request
                        then
                          if head_name request = SOME geometry_check_name then
                            (case !operation_context_ref of
                              SOME operation_context =>
                                selected_geometry_rewrite operation_context cterm
                            | NONE => error "B1 operation context is not initialized")
                          else if geometry_fold_request request then
                            (case !operation_conversion of
                              SOME convert => #equation (convert cterm)
                            | NONE => error "B1 staged fold conversion is not initialized")
                          else
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
                         " reason=" ^ reason ^ " request_shape=" ^ shape 5 request);
                       error ("B1 occurrence conversion CTERM head=" ^
                         !last_head ^ " reason=" ^ reason ^
                         " request=" ^ shape 6 request))
                  in publish_completed request theorem end) ()
                val _ = if operation_request request then
                  add_operation_time (the_default "<non-constant>" (head_name request))
                    (Time.toMilliseconds (Time.- (Time.now (), conversion_started)))
                  else ()
                val _ = active := Termtab.delete request (!active)
                val published =
                  (case attempt of
                    Exn.Res result => result
                  | Exn.Exn exn =>
                      (failures := !failures + 1; Exn.reraise exn))
        in published end

      fun memo_proc context ct =
        let val request = Thm.term_of ct in
          if not (cacheable request) then NONE
          else if Termtab.defined (!incomplete) request then NONE
          else
            (lookups := !lookups + 1;
             if geometry_fold_request request then
               geometry_fold_lookups := !geometry_fold_lookups + 1 else ();
             case Termtab.lookup (!memo) request of
               SOME theorem =>
                 if Thm.is_reflexive theorem then NONE
                 else (hits := !hits + 1;
                   if geometry_fold_request request then
                     geometry_fold_hits := !geometry_fold_hits + 1 else ();
                   SOME theorem)
             | NONE =>
                 if not (closed request) then NONE
                 else if Termtab.defined (!active) request then
                   (recursive := !recursive + 1; NONE)
                 else
                   convert context ct)
        end

      val proc = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_occurrence_exact_memo",
         kind = Simplifier.Congproc false,
         lhss = selected_schematic_patterns @ catalogue_schematic_patterns,
         proc = fn _ => memo_proc,
         identifier = []}

      val selectors = catalogue_setup ctxt
      (* Select one row before installing Let_def and operation rules. *)
      val selector_context = fold Simplifier.add_proc (#procedures selectors)
        (put_simpset HOL_basic_ss ctxt)
      val _ = selector_context_ref := SOME selector_context
      val _ = milestone "after-catalogue-setup"
      val _ = milestone "before-evaluation-context-setup"
      val evaluation_context = (code_context addsimps catalogue_simp_rules)
        |> fold Simplifier.add_proc (#procedures selectors)
        |> Simplifier.add_proc proc
      val operation_base_context =
        Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.del_simps @{thms comma_semantic_b1_crt_geometry_fold.simps}
        |> (fn context => context addsimps (checker_simp_rules @ catalogue_simp_rules))
        |> fold Simplifier.add_proc (#procedures selectors)
        |> Simplifier.add_proc proc
      val operation_context = Simplifier.del_simps
        @{thms upt_0 upt_Suc upt_rec upt_rec_numeral zip.simps zip_Nil zip_Cons_Cons}
        (Comma_Semantic_B1_CRT_Operation_Conversion.operation_context operation_base_context)
      val _ = operation_context_ref := SOME operation_context
      val local_cover_context = operation_context addsimps
        @{thms upt_0 upt_Suc upt_rec upt_rec_numeral
          zip.simps zip_Nil zip_Cons_Cons}
      val _ = local_cover_context_ref := SOME local_cover_context
      val _ = milestone "after-evaluation-context-setup"
      val _ = milestone "before-static-converter-init"
      val _ = code_conversion := SOME (Code_Simp.static_conv
        {ctxt = ctxt, simpset = SOME (Simplifier.simpset_of evaluation_context),
         consts = filter_out (member (op =) operation_roots) generic_constants})
      val apply_depth_rules =
        Comma_Semantic_B1_CRT_Operation_Conversion.apply_depth_simp_rules ctxt
      val operation_boundaries =
        Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_boundaries
          apply_depth_rules @
          [(@{const_name comma_semantic_b1_crt_geometry_fold},
            @{thms comma_semantic_b1_crt_geometry_fold.simps})]
      val _ = operation_conversion := SOME
        (Comma_Semantic_B1_CRT_Operation_Conversion.make_staged_operation_converter
          {context = operation_context, boundaries = operation_boundaries,
           staged_heads =
             @{const_name comma_semantic_b1_crt_geometry_fold} ::
               Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_staged_heads,
           lazy_function_heads =
             Comma_Semantic_B1_CRT_Operation_Conversion.crt_operation_lazy_function_heads,
           final_argument_stagers =
             [(@{const_name comma_semantic_b1_crt_geometry_fold},
               Comma_Semantic_B1_CRT_Operation_Conversion.make_indexed_zip_spine_stager ctxt
                 {indexed_columns_def = @{thm comma_semantic_b1_crt_occurrence_indexed_columns_def},
                  length_nil = @{thm comma_selected_length_nil}, length_cons =
                    @{thm comma_selected_length_cons}})],
           complete_value = complete_value})
      val _ = milestone "after-static-converter-init"

      (* A residual Boolean must be rejected by the production cache gate. *)
      val partial_request = @{term "comma_crt_supported (Comma_CRT_Bool True)"}
      val partial_key = Thm.cterm_of ctxt partial_request
      val partial_theorem = Thm.reflexive partial_key
      val before_publications = !publications
      val before_retained = Termtab.size (!memo)
      val _ = if Termtab.defined (!memo) partial_request orelse
          Termtab.defined (!incomplete) partial_request
        then error "B1 residual-equation fixture key unexpectedly preexists"
        else ()
      val rejected_partial = publish_completed partial_request partial_theorem
      val was_rejected = (case rejected_partial of NONE => true | SOME _ => false)
      val _ = if was_rejected andalso
          not (Termtab.defined (!memo) partial_request) andalso
          Termtab.defined (!incomplete) partial_request andalso
          !publications = before_publications andalso
          Termtab.size (!memo) = before_retained
        then ()
        else error "B1 residual Boolean equation escaped completion publication gate"
      val returned_by_congproc = memo_proc evaluation_context partial_key
      val was_not_returned = (case returned_by_congproc of NONE => true | SOME _ => false)
      val _ = if was_not_returned andalso
          not (Termtab.defined (!memo) partial_request)
        then ()
        else error "B1 Congproc returned or published an incomplete Boolean equation"
      val _ = incomplete := Termtab.delete partial_request (!incomplete)
      val _ = milestone "after-incomplete-equation-regression"

      fun smoke proposition expected label =
        let
          (* Exercise the installed dispatcher, not a separate evaluator. *)
          val normalized = Simplifier.rewrite evaluation_context
            (Thm.cterm_of ctxt (HOLogic.mk_Trueprop proposition))
          val rhs = Thm.term_of (Thm.rhs_of normalized)
          val expected_proposition = HOLogic.mk_Trueprop expected
        in
          if rhs aconv expected_proposition then ()
          else
            let
              val residual = the_default rhs (try HOLogic.dest_Trueprop rhs)
            in error ("B1 occurrence evaluator smoke failed: " ^ label ^
              " residual_nodes_cap=" ^ Int.toString (capped_nodes 2048 residual) ^
              " residual_shape=" ^ shape 6 residual ^
              " counters=" ^ counters ()) end
        end

      val _ = smoke
        @{term "comma_crt_supported
          (Comma_CRT_Node 1
            (map (\<lambda>index. Comma_CRT_Bool (index = 0)) [0..<3]))"}
        @{term True} "positive map/upt/node support"
      val _ = smoke
        @{term "comma_crt_supported
          (Comma_CRT_Node 1
            (map (\<lambda>index. Comma_CRT_Bool False) [0..<3]))"}
        @{term False} "negative map/upt/node support"
      val complementary_left = @{term
        "Comma_CRT_Node 0 [Comma_CRT_Bool True, Comma_CRT_Bool True,
          Comma_CRT_Bool False, Comma_CRT_Bool False]"}
      val complementary_right = @{term
        "Comma_CRT_Node 0 [Comma_CRT_Bool False, Comma_CRT_Bool False,
          Comma_CRT_Bool True, Comma_CRT_Bool True]"}
      val complementary_columns = HOLogic.mk_list @{typ comma_crt_column}
        [complementary_left, complementary_right]
      val complementary_geometry =
        @{term "comma_semantic_b1_crt_occurrence_geometry_check"} $
          complementary_columns
      val _ = smoke complementary_geometry @{term True}
        "complementary phase-column geometry"
      val admitted_join = @{term "comma_crt_admitted (0::nat)"} $
        (@{term "comma_crt_apply Comma_CRT_Or"} $
          complementary_left $ complementary_right)
      val _ = smoke admitted_join @{term True} "admitted CRT apply result"
      val selected_template_geometry = @{term
        "comma_semantic_b1_crt_occurrence_geometry_check
          (comma_semantic_b1_crt_templates ! 0)"}
      val selected_template_lets_before = !selected_row_lets
      val _ = smoke selected_template_geometry @{term True}
        "selector-first published template geometry"
      val _ = if !selected_row_lets > selected_template_lets_before then ()
        else error "B1 selected template was not Let-normalized after row selection"
      val _ = milestone "after-selected-template-smoke"
      val shared_row_geometry = @{term
        "comma_semantic_b1_crt_occurrence_geometry_check
          (let shared_column = Comma_CRT_Node 0
            [Comma_CRT_Bool True, Comma_CRT_Bool True,
             Comma_CRT_Bool False, Comma_CRT_Bool False]
           in [shared_column, shared_column])"}
      val shared_row_hits_before = !hits
      val shared_row_visits_before = !selected_row_visits
      val shared_row_lets_before = !selected_row_lets
      val _ = smoke shared_row_geometry @{term False}
        "nested shared-row geometry"
      val shared_row_reused =
        !hits > shared_row_hits_before andalso
        !selected_row_visits > shared_row_visits_before andalso
        !selected_row_lets > shared_row_lets_before
      val _ = if shared_row_reused then ()
        else error "B1 selected Let-DAG row did not exercise exact-node reuse"
      val fold_request = @{term "comma_semantic_b1_crt_geometry_fold"} $
        complementary_right $
        HOLogic.mk_list @{typ "nat * comma_crt_column"}
          [HOLogic.mk_prod (@{term "0::nat"}, complementary_left)]
      val fold_key = Thm.cterm_of ctxt fold_request
      val fold_request_theorem = memo_proc evaluation_context fold_key
      val fold_is_published =
        (case fold_request_theorem of SOME _ => true | NONE => false) andalso
        Termtab.defined (!memo) fold_request
      val fold_result_is_exact =
        (case fold_request_theorem of
          SOME theorem => Thm.term_of (Thm.rhs_of theorem) aconv
            HOLogic.mk_prod (@{term True}, @{term "Comma_CRT_Bool True"})
        | NONE => false)
      val _ = if fold_is_published andalso fold_result_is_exact then ()
        else error "B1 geometry fold did not publish its exact joined result"
      val fold_hits_before_projections = !geometry_fold_hits
      val fold_misses_before_projections = !misses
      val fold_productT = @{typ "bool * comma_crt_column"}
      val first_projection = Const (@{const_name fst}, fold_productT --> @{typ bool}) $
        fold_request
      val second_projection = Const (@{const_name snd}, fold_productT --> @{typ comma_crt_column}) $
        fold_request
      val first_result = Simplifier.rewrite evaluation_context
        (Thm.cterm_of ctxt first_projection)
      val second_result = Simplifier.rewrite evaluation_context
        (Thm.cterm_of ctxt second_projection)
      val fold_projections_are_exact =
        Thm.term_of (Thm.rhs_of first_result) aconv @{term True} andalso
        Thm.term_of (Thm.rhs_of second_result) aconv @{term "Comma_CRT_Bool True"}
      val _ = if fold_projections_are_exact andalso
          !geometry_fold_hits - fold_hits_before_projections >= 2 andalso
          !misses = fold_misses_before_projections
        then ()
        else error "B1 geometry-fold projections did not reuse the completed pair"
      val _ = milestone "after-typed-smoke"
      fun root_occurrence_index request =
        (case strip_comb request of
          (Const (name, _), [root]) =>
            if name = @{const_name comma_semantic_b1_crt_root_occurrence} then
              (case try HOLogic.dest_number root of
                SOME (typ, index) =>
                  if typ = @{typ nat} andalso 0 <= index andalso index < 46
                  then SOME index else NONE
              | NONE => NONE)
            else NONE
        | _ => NONE)

      fun select_root_occurrence cterm =
        let
          val request = Thm.term_of cterm
          val _ = if closed request then ()
            else error "B1 root occurrence selector request is not closed"
          val _ = (case root_occurrence_index request of
            SOME _ => ()
          | NONE => error "B1 root occurrence selector requires a literal root in 0..45")
          val theorem = Simplifier.rewrite evaluation_context cterm
          val checked = validate_equation request theorem
          val rhs = Thm.term_of (Thm.rhs_of checked)
          val _ = (case strip_comb rhs of
            (Const (name, _), [occurrence]) =>
              if name = @{const_name Some} andalso closed occurrence andalso
                  fastype_of occurrence = @{typ comma_semantic_b1_crt_occurrence}
              then () else error "B1 root selector returned an invalid occurrence"
          | _ => error "B1 root selector did not return Some occurrence")
        in checked end

      fun selected_action_rules () = split_action_rules
      fun selected_action_context () =
        (case !selected_action_context_ref of
          SOME context => context
        | NONE =>
            let
              val rules = selected_action_rules ()
              val context = evaluation_context addsimps rules
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
        counters () ^ " " ^ #stats selectors ()

      fun prove cterm =
        let
          val request = Thm.term_of cterm
          val indexed_items = Unsynchronized.ref 0
          fun prove_true proposition =
            let
              val goal = Thm.cterm_of ctxt (HOLogic.mk_Trueprop proposition)
              val normalized = Simplifier.rewrite evaluation_context goal
              val rhs = Thm.term_of (Thm.rhs_of normalized)
              val _ = checked_items := !checked_items + 1
              val _ = if !checked_items mod 32 = 0 then
                Comma_Proof_Profile.report
                  ("B1 occurrence indexed items=" ^ Int.toString (!checked_items) ^
                   " " ^ counters () ^ " " ^ #stats selectors ()) else ()
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
                       " normalized_nodes_cap=" ^ Int.toString (capped_nodes 2048 reduced) ^
                       " normalized_shape=" ^ shape 5 reduced ^
                       " counters=" ^ counters ())
                  in error ("B1 occurrence item failed: " ^
                    (case head_name proposition of SOME name => name | NONE => "boolean") ^
                    " counters=" ^ counters ()) end
            in Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI} end

      fun prove_list_all predicate range =
        let
              (* Normalize the upper bound, then prove items by zero/Suc. *)
              val predicate_name =
                the_default "non-constant" (head_name predicate)
              val _ = Comma_Proof_Profile.report
                ("B1 occurrence proof stage=list-all-bound-start predicate=" ^
                 predicate_name)
              val bound_started = Time.now ()
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
              val upper_selected = Simplifier.rewrite evaluation_context
                (Thm.cterm_of ctxt upper)
              val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt
              val upper_scalar = Simplifier.rewrite scalar_context
                (Thm.rhs_of upper_selected)
              val upper_equation = validate_equation upper
                (Thm.transitive upper_selected upper_scalar)
              val (_, bound) = HOLogic.dest_number
                (Thm.term_of (Thm.rhs_of upper_equation))
              val _ = Comma_Proof_Profile.report
                ("B1 occurrence proof stage=list-all-bound-complete predicate=" ^
                 predicate_name ^ " bound=" ^ Int.toString bound ^
                 " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms bound_started)
              val _ = if bound >= 0 andalso bound <= 1024 then ()
                else error "B1 indexed certificate range exceeds its declared extent"
              val natT = @{typ nat}
              fun numeral value = HOLogic.mk_number natT value
              val list_type = @{typ "nat list"}
              val list_all = Const (@{const_name list_all},
                fastype_of predicate --> list_type --> @{typ bool}) $ predicate
          fun prove_item index =
                let
                  val item_started = Time.now ()
                  val template_item = predicate_name =
                    @{const_name comma_semantic_b1_crt_template_geometry_at}
                  val _ = if template_item then Comma_Proof_Profile.report
                    ("B1 occurrence template index=" ^ Int.toString index ^ " start")
                    else ()
                  val theorem = prove_true (predicate $ numeral index)
                  val _ = indexed_items := !indexed_items + 1
                  val _ = if template_item then Comma_Proof_Profile.report
                    ("B1 occurrence template index=" ^ Int.toString index ^
                     " complete elapsed_ms=" ^
                     Comma_Proof_Profile.elapsed_ms item_started) else ()
                in theorem end
              val prefix = Comma_Selected_List_Conversion.prove_indexed_list_all
                {ctxt = ctxt, predicate = predicate, bound = bound,
                 prove_item = prove_item,
                 zero_fact = @{thm comma_indexed_all_zero},
                 step_fact = @{thm comma_indexed_all_Suc}}
              val normalized_range = Const (@{const_name upt},
                natT --> natT --> list_type) $ lower $ numeral bound
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

          fun prove_expression expression =
            (case try (HOLogic.dest_bin @{const_name HOL.conj} @{typ bool}) expression of
              SOME (left, right) =>
                @{thm conjI} OF
                  [prove_expression left, prove_expression right]
            | NONE =>
                (case strip_comb expression of
                  (Const (name, _), [predicate, range]) =>
                    if name = @{const_name list_all}
                    then prove_list_all predicate range
                    else prove_true expression
                | _ => prove_true expression))
          val definition = @{thm comma_semantic_b1_crt_occurrence_data_checked_def}
            RS @{thm eq_reflection}
          val unfolded = Conv.arg_conv (Conv.rewr_conv definition) cterm
          val rhs = HOLogic.dest_Trueprop (Thm.term_of (Thm.rhs_of unfolded))
          val rhs_proof = prove_expression rhs
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
          val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
          val _ = Comma_Proof_Profile.report
            ("B1 occurrence proof cache completed " ^ #report evaluator () ^
             " elapsed_ms=" ^ LargeInt.toString elapsed)
        in
          resolve_tac ctxt [theorem] subgoal
        end
    in SUBGOAL solve i end

  val _ = Theory.setup
    (Method.setup @{binding comma_semantic_b1_occurrence_check}
      (Scan.succeed (fn ctxt => SIMPLE_METHOD' (tactic ctxt)))
      "proof-producing cached evaluation of the B1 occurrence certificate")

end
