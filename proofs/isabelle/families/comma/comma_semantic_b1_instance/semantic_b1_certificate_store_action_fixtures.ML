(* Action-row and action-backed consumer fixtures for the bounded B1 store. *)
structure Comma_Semantic_B1_Certificate_Store_Action_Fixtures =
struct
  fun check
      {ctxt, base, store, action_table, columns, templates, template_ids,
       lift_ids, sources, occurrence_at, occurrence_descriptors,
       lift_descriptors, refs, terminal_refs, source, occurrence, request,
       capture, reset_current_source} =
    let
      val thy = Proof_Context.theory_of ctxt
      val natT = @{typ nat}
      val actionT = @{typ comma_source_continuation_action}
      val action_listT = HOLogic.listT actionT
      val zero = HOLogic.mk_number natT 0
      val period = @{term comma_decisive_sector_period} $
        (@{term comma_source_continuation_base} $ source)
      val row_tableT = HOLogic.listT action_listT
      val actions = Const (@{const_name nth}, row_tableT --> natT --> action_listT) $
        action_table $ zero
      val action_context = base addsimps @{thms
        comma_semantic_b1_crt_source_slot_action_row_certified_def
        comma_semantic_b1_crt_slot_actions_table_def
        comma_semantic_b1_crt_lift_slot_valid_from_actions_def
        comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions_def
        comma_semantic_b1_crt_constructed_piece_binding_matches_def
        comma_semantic_b1_crt_lift_slot_valid_def Let_def}
      val row_head = @{const_name comma_semantic_b1_crt_source_slot_action_row_certified}
      val slot_actions_head = @{const_name comma_semantic_b1_crt_lift_slot_valid_from_actions}
      val binding_actions_head =
        @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions}
      val row_request = request row_head [source, period, actions]
      val slot_request = request slot_actions_head
        [sources, occurrence_at, occurrence_descriptors, templates, source,
         occurrence, terminal_refs, lift_descriptors, actions, zero]
      val _ = reset_current_source 0
      val row_equation = capture "canonical action row" true action_context row_request
      val slot_equation = capture "action-backed terminal slot" true action_context slot_request
      fun warm target proposition theorem =
        (case #lookup_equation target proposition of
          SOME found => Thm.eq_thm_prop (theorem, found)
        | NONE => false)
      val canonical_row_warm = warm store row_request row_equation
      val canonical_slot_warm = warm store slot_request slot_equation

      (* The selected Near source has period one and a terminal action.  Use a
         same-context store whose fixed catalog has the corresponding scope
         column, so the action-backed Terminal binding is itself a true hit. *)
      val bool_true = @{term "Comma_CRT_Bool True"}
      val scope_one = @{term "comma_crt_source_scope_column (1,0)"}
      val binding_columns = HOLogic.mk_list @{typ comma_crt_column}
        [bool_true, scope_one]
      val refsT = HOLogic.listT @{typ comma_semantic_b1_crt_lift_ref}
      val lift_refs_table = HOLogic.mk_list refsT [terminal_refs, refs]
      val binding_store = Comma_Semantic_B1_Certificate_Store.make_certificate_store
        {ctxt = ctxt,
         template_head = @{const_name comma_semantic_b1_crt_template_geometry_certified},
         lift_head = @{const_name comma_semantic_b1_crt_lift_geometry_certified},
         slot_head = @{const_name comma_semantic_b1_crt_constructed_goto_slot_certificate},
         slot_valid_head = @{const_name comma_semantic_b1_crt_lift_slot_valid},
         binding_head = @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches},
         action_row_head = row_head,
         slot_valid_actions_head = slot_actions_head,
         binding_actions_head = binding_actions_head,
         action_table = action_table, columns = binding_columns,
         templates_table = templates, template_ids = template_ids,
         lift_ids = lift_ids, sources_table = sources, occurrence_at = occurrence_at,
         occurrence_descriptors = occurrence_descriptors,
         lift_descriptors = lift_descriptors, lift_refs_table = lift_refs_table}
      val _ = #reset_current_source binding_store 0
      val binding_row = capture "binding-store action row" false action_context row_request
      val _ = #remember_equation binding_store action_context row_request binding_row
      val binding_slot_request = request slot_actions_head
        [sources, occurrence_at, occurrence_descriptors, templates, source,
         occurrence, terminal_refs, lift_descriptors, actions, zero]
      val binding_slot = capture "binding-store terminal slot" false
        action_context binding_slot_request
      val _ = #remember_equation binding_store action_context
        binding_slot_request binding_slot
      val periodT = Sign.the_const_type thy @{const_name Comma_B1_Piece_Terminal}
      val terminal_piece = list_comb
        (Const (@{const_name Comma_B1_Piece_Terminal}, periodT),
          [period, zero, HOLogic.mk_number natT 1, zero])
      fun binding_request cols selected_actions selected_parent =
        request binding_actions_head
          [cols, lift_ids, sources, occurrence_at, terminal_refs, source,
           selected_actions, selected_parent, zero, terminal_piece]
      val binding = binding_request binding_columns actions occurrence
      val binding_equation = capture "action-backed terminal binding" false
        action_context binding
      val _ = #remember_equation binding_store action_context binding binding_equation
      val binding_warm = warm binding_store binding binding_equation

      (* A later action cell may differ without changing this slot's valid
         consumer proposition.  The store still requires the whole row to be
         the canonical source row before it accepts the consumer. *)
      val extended_actions = Const (@{const_name append},
        action_listT --> action_listT --> action_listT) $ actions $
        HOLogic.mk_list actionT [@{term Comma_Continuation_Invalid}]
      val changed_action_consumer =
        binding_request binding_columns extended_actions occurrence
      val changed_action_equation = capture "changed action row consumer" false
        action_context changed_action_consumer
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 action-piece binding changed action row"
        "changed action row consumer"
        (fn () => #remember_equation binding_store action_context
          changed_action_consumer changed_action_equation)
      val changed_action_rejected = true

      (* Keep the consumer theorem valid while changing its parent record; the
         beta row remains Stop 8, but the selected parent identity changes. *)
      val alternate_parent = @{term
        "\<lparr>comma_semantic_b1_crt_occurrence_columns = [Comma_CRT_Bool False],
          comma_semantic_b1_crt_occurrence_rebase = 1,
          comma_semantic_b1_crt_occurrence_beta = [Comma_Semantic_B1_Stop 8]\<rparr>"}
      val changed_parent_consumer =
        binding_request binding_columns actions alternate_parent
      val changed_parent_equation = capture "changed parent consumer" false
        action_context changed_parent_consumer
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 action-piece binding changed parent"
        "changed parent consumer"
        (fn () => #remember_equation binding_store action_context
          changed_parent_consumer changed_parent_equation)
      val changed_parent_rejected = true

      val changed_columns = HOLogic.mk_list @{typ comma_crt_column}
        [@{term "Comma_CRT_Bool False"}, scope_one]
      val changed_catalog_consumer =
        binding_request changed_columns actions occurrence
      val changed_catalog_equation = capture "changed catalog consumer" false
        action_context changed_catalog_consumer
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 action-piece binding used foreign catalogue terms"
        "changed catalog consumer"
        (fn () => #remember_equation binding_store action_context
          changed_catalog_consumer changed_catalog_equation)
      val changed_catalog_rejected = true

      val other_source = @{term "Comma_Near 8 0 19 :: comma_finite_position"}
      val other_period = @{term comma_decisive_sector_period} $
        (@{term comma_source_continuation_base} $ other_source)
      val other_actions = @{term
        "map (comma_semantic_b1_source_slot_action (Comma_Near 8 0 19))
          [0..<comma_decisive_sector_period
            (comma_source_continuation_base (Comma_Near 8 0 19))]"}
      val other_row_request = request row_head
        [other_source, other_period, other_actions]
      val other_row_equation = capture "different source action row" false
        action_context other_row_request
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 action row changed its source, period, or canonical row"
        "different source action row"
        (fn () => #remember_equation store action_context
          other_row_request other_row_equation)
      val changed_source_rejected = true
      val restored_slot = capture "restored action-backed terminal slot" true
        action_context slot_request
      val restored_slot_warm = warm store slot_request restored_slot
    in
      if canonical_row_warm andalso canonical_slot_warm andalso restored_slot_warm andalso
        binding_warm andalso
        changed_action_rejected andalso changed_parent_rejected andalso
        changed_catalog_rejected andalso changed_source_rejected
      then true
      else error "B1 action certificate store positive/negative fixtures failed"
    end
end
