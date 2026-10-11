(* Run-local CID theorem store and its kernel-level negative/warm-hit fixtures. *)
structure Comma_Semantic_B1_Certificate_Store_Fixtures =
struct
  fun check_partition_profile_scope () =
    let
      val profile = Comma_Semantic_B1_Partition_Conversion.make_template_partition_profile ()
      val exception_request = @{term "comma_semantic_b1_crt_columns_partition_certified []"}
      val exception_fixture = #capture_conversion profile exception_request
        (fn () => error "B1 partition conversion exception-path fixture")
      val _ = (case exception_fixture of
        Exn.Exn (ERROR message) =>
          if message = "B1 partition conversion exception-path fixture" andalso
              not (#inside profile ()) then ()
          else error "B1 partition exception fixture leaked active profiling scope"
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error "B1 partition conversion exception fixture did not raise")
      val geometry_request = @{term
        "comma_semantic_b1_crt_template_geometry_certified ([]::comma_crt_column list) ([]::comma_crt_column list list) ([]::nat list list) (0::nat)"}
      val state_request = @{term
        "comma_semantic_b1_crt_partition_cofactor_checked [0] [Comma_CRT_Bool True]"}
      val state_counts_before = #cofactor_state_counts profile ()
      val certificate_counts_before = #certificate_counts profile ()
      val geometry_fixture = #capture_conversion profile geometry_request
        (fn () => if #inside profile () then #note_result profile state_request (SOME ())
          else error "B1 template geometry did not open partition profiling scope")
      val _ = (case geometry_fixture of
        Exn.Res () => ()
      | Exn.Exn exn => Exn.reraise exn)
      val (states_before, hits_before) = state_counts_before
      val _ = if #cofactor_state_counts profile () = (states_before + 1, hits_before) andalso
          #certificate_counts profile () = certificate_counts_before then ()
        else error "B1 geometry profile scope misclassified cofactor work as certificate work"
      val outside_counts = #cofactor_state_counts profile ()
      val _ = #note_result profile state_request (SOME ())
      val _ = #note_memo_hit profile state_request
      val _ = if not (#inside profile ()) andalso
          #cofactor_state_counts profile () = outside_counts then ()
        else error "B1 partition exception fixture leaked into later cofactor metrics"
    in () end
  fun check ctxt =
    let
      val _ = check_partition_profile_scope ()
      val bool_true = @{term "Comma_CRT_Bool True"}
      val scope_true = @{term "comma_crt_apply_shifted Comma_CRT_And 0 (comma_crt_source_scope_column (3,0)) (Comma_CRT_Bool True)"}
      val columns = HOLogic.mk_list @{typ comma_crt_column} [bool_true, scope_true]
      val templates = @{term "[[Comma_CRT_Bool True]] :: comma_crt_column list list"} and template_ids = @{term "[[0::nat]]"} and lift_ids = @{term "[[1::nat]]"}
      val sources = @{term "[Comma_Near 9 0 19, Comma_Near 9 0 19] :: comma_finite_position list"}
      val occurrence = @{term "\<lparr>comma_semantic_b1_crt_occurrence_columns = [Comma_CRT_Bool True], comma_semantic_b1_crt_occurrence_rebase = 0, comma_semantic_b1_crt_occurrence_beta = [Comma_Semantic_B1_Stop 8]\<rparr>"}
      val occurrence_at = Abs ("i", @{typ nat},
        Const (@{const_name Some}, fastype_of occurrence -->
          @{typ "comma_semantic_b1_crt_occurrence option"}) $ occurrence)
      val occurrence_descriptors = @{term "[(0::nat,(0::nat,[Comma_Semantic_B1_Stop 8]))]"}
      val lift_descriptor = @{term "comma_semantic_b1_crt_lift_descriptor.make 3 0 0 0"}
      val lift_descriptors = HOLogic.mk_list @{typ comma_semantic_b1_crt_lift_descriptor} [lift_descriptor]
      val refs = @{term "[Comma_B1_Lift_Goto_Ref 0 0 0]"}
      val terminal_refs = @{term "[Comma_B1_Lift_Terminal_Ref 0 0]"}
      val refs_row_type = HOLogic.listT @{typ comma_semantic_b1_crt_lift_ref}
      val lift_refs_table = HOLogic.mk_list refs_row_type [terminal_refs, refs]
      val action_table = Const (@{const_name comma_semantic_b1_crt_slot_actions_table},
        Sign.the_const_type (Proof_Context.theory_of ctxt)
          @{const_name comma_semantic_b1_crt_slot_actions_table}) $ sources
      val template_head = @{const_name comma_semantic_b1_crt_template_geometry_certified} and lift_head = @{const_name comma_semantic_b1_crt_lift_geometry_certified}
      val slot_head = @{const_name comma_semantic_b1_crt_constructed_goto_slot_certificate} and binding_head = @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches}
      val thy = Proof_Context.theory_of ctxt
      fun request name arguments = list_comb (Const (name, Sign.the_const_type thy name), arguments)
      val template_request = request template_head [columns, templates, template_ids, @{term "0::nat"}]
      val lift_request = request lift_head [columns, templates, template_ids, lift_ids, lift_descriptors, @{term "0::nat"}]
      val slot_request = request slot_head [columns, templates, template_ids, lift_ids, occurrence_descriptors, lift_descriptors, @{term "1::nat"}, refs, @{term "0::nat"}]
      val source = @{term "Comma_Near 9 0 19 :: comma_finite_position"}
      fun binding_request selected_source = request binding_head
        [columns, lift_ids, sources, occurrence_at, refs, selected_source, occurrence, @{term "0::nat"}, @{term "Comma_B1_Piece_Goto 1 0 0 0 0 1 0"}]
      val binding = binding_request source
      val slot_valid_head = @{const_name comma_semantic_b1_crt_lift_slot_valid}
      val slot_valid_request = request slot_valid_head
        [sources, occurrence_at, occurrence_descriptors, templates, source,
         occurrence, terminal_refs, lift_descriptors, @{term "0::nat"}]
      val source_action_request = request
        @{const_name comma_semantic_b1_source_slot_action}
        [source, @{term "0::nat"}]
      val source_action_eq = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt source_action_request)
      val source_action_rhs = Thm.term_of (Thm.rhs_of source_action_eq)
      val expected_source_action = @{term
        "Comma_Continuation_Landmine 0 :: comma_source_continuation_action"}
      val source_action_exact =
        Thm.term_of (Thm.lhs_of source_action_eq) aconv source_action_request andalso
        source_action_rhs aconv expected_source_action andalso
        Comma_Selected_List_Conversion.closed source_action_rhs andalso
        Comma_Semantic_B1_Construction_Check.standalone source_action_eq andalso
        null (Thm_Deps.all_oracles [source_action_eq])
      val _ = if source_action_exact then ()
        else error ("B1 certificate-store fixture did not reduce the selected " ^
          "near source action exactly; request=" ^
          Syntax.string_of_term ctxt source_action_request ^ "; rhs=" ^
          Syntax.string_of_term ctxt source_action_rhs ^ "; expected=" ^
          Syntax.string_of_term ctxt expected_source_action)
      val fixture_partition_request = @{term
        "comma_semantic_b1_crt_columns_partition_certified [Comma_CRT_Bool True]"}
      val fixture_partition_eq = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt fixture_partition_request)
      val fixture_partition_exact =
        Thm.term_of (Thm.lhs_of fixture_partition_eq) aconv fixture_partition_request andalso
        Thm.term_of (Thm.rhs_of fixture_partition_eq) aconv @{term True} andalso
        Comma_Semantic_B1_Construction_Check.standalone fixture_partition_eq andalso
        null (Thm_Deps.all_oracles [fixture_partition_eq])
      val _ = if fixture_partition_exact then ()
        else error "B1 one-column partition fixture was not an exact oracle-free theorem"
      val store = Comma_Semantic_B1_Certificate_Store.make_certificate_store {ctxt = ctxt, template_head = template_head, lift_head = lift_head, slot_head = slot_head,
        slot_valid_head = @{const_name comma_semantic_b1_crt_lift_slot_valid}, binding_head = binding_head,
        action_row_head = @{const_name comma_semantic_b1_crt_source_slot_action_row_certified},
        slot_valid_actions_head = @{const_name comma_semantic_b1_crt_lift_slot_valid_from_actions},
        binding_actions_head = @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions},
        action_table = action_table, columns = columns, templates_table = templates,
        template_ids = template_ids, lift_ids = lift_ids, sources_table = sources, occurrence_at = occurrence_at,
        occurrence_descriptors = occurrence_descriptors, lift_descriptors = lift_descriptors,
        lift_refs_table = lift_refs_table}
      val base = (ctxt addsimps @{thms comma_semantic_b1_crt_template_geometry_certified_def comma_semantic_b1_crt_lift_geometry_certified_def
        comma_semantic_b1_crt_constructed_goto_slot_certificate_def comma_semantic_b1_crt_constructed_piece_binding_matches_def
        comma_semantic_b1_crt_column_ids_resolve_def comma_semantic_b1_crt_lift_descriptor_valid_def
        comma_semantic_b1_crt_source_periods_def Let_def
        comma_semantic_b1_crt_lift_columns_option_def
        comma_semantic_b1_crt_lift_columns_def comma_semantic_b1_crt_lift_descriptor.make_def comma_semantic_b1_crt_lift_descriptor.select_convs
        comma_semantic_b1_crt_lift_slot_valid_def
        comma_semantic_b1_terminal_action_result.simps comma_semantic_b1_crt_occurrence.select_convs
        comma_decisive_sector_period_def comma_source_continuation_base.simps})
        addsimps [source_action_eq, fixture_partition_eq]
      fun capture_equation label remember context proposition theorem =
        let
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val exact_lhs = lhs aconv proposition
          val true_rhs = rhs aconv @{term True}
          val standalone = Comma_Semantic_B1_Construction_Check.standalone theorem
          val oracle_free = null (Thm_Deps.all_oracles [theorem])
          fun show term = Syntax.string_of_term context term
          fun head term =
            (case strip_comb term of
              (Const (name, _), _) => name
            | _ => "<non-constant-head>")
          val exact = exact_lhs andalso true_rhs andalso standalone andalso oracle_free
          val summary = "B1 certificate-store fixture equation case=" ^ label ^
            "; request_head=" ^ head proposition ^
            "; exact_lhs=" ^ Bool.toString exact_lhs ^
            "; true_rhs=" ^ Bool.toString true_rhs ^
            "; standalone=" ^ Bool.toString standalone ^
            "; oracle_free=" ^ Bool.toString oracle_free
          val _ = if exact then () else Comma_Proof_Profile.report summary
          val _ = if exact then ()
            else error (summary ^ "; request=" ^ show proposition ^ "; lhs=" ^ show lhs ^
              "; rhs=" ^ show rhs)
        in
          if remember then #remember_equation store context proposition theorem else ();
          theorem
        end
      fun capture label remember context proposition =
        capture_equation label remember context proposition
          (Simplifier.rewrite context (Thm.cterm_of ctxt proposition))
      val ignored_generic_request = @{term True}
      val ignored_generic_equation = Simplifier.rewrite base
        (Thm.cterm_of ctxt ignored_generic_request)
      val oracle_counts_before_ignored_generic = #oracle_check_counts store ()
      val _ = #remember_equation store base ignored_generic_request
        ignored_generic_equation
      val ignored_generic_skips_oracle_scan =
        oracle_counts_before_ignored_generic = #oracle_check_counts store ()
      val _ = #reset_current_source store 0
      fun certificate_entry_counts counts = take 7 counts
      val before_missing_template_lift = #retained_entry_counts store ()
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 admitted lift geometry is missing its captured TemplateCID certificate"
        "missing TemplateCID lift certificate"
        (fn () => #rewrite_lift_geometry store ctxt base lift_request
          (Thm.cterm_of ctxt lift_request))
      val missing_template_lift_rejected = true
      val missing_template_lift_not_published =
        missing_template_lift_rejected andalso
        (case #lookup_equation store lift_request of NONE => true | SOME _ => false) andalso
          certificate_entry_counts before_missing_template_lift =
          certificate_entry_counts (#retained_entry_counts store ())
      val binding_eq = capture "pre-scope binding" false base binding
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 piece binding has no active lift labels" "pre-scope binding"
        (fn () => #remember_equation store base binding binding_eq)
      val pre_scope_rejected = true
      val _ = #reset_current_source store 1
      val noncanonical_slot = request slot_head
        [columns, templates, template_ids, lift_ids, occurrence_descriptors,
         lift_descriptors, @{term "1::nat"}, terminal_refs, @{term "0::nat"}]
      val noncanonical_slot_eq = capture "noncanonical slot references" false base noncanonical_slot
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 slot certificate used noncanonical lift labels"
        "noncanonical slot references"
        (fn () => #remember_equation store base
          noncanonical_slot noncanonical_slot_eq)
      val noncanonical_refs_rejected = true
      val template_eq = capture "template geometry" true base template_request
      val lift_eq = capture_equation "lift geometry" true base lift_request
        (#rewrite_lift_geometry store ctxt base lift_request
          (Thm.cterm_of ctxt lift_request))
      val slot_eq = capture "constructed goto slot" true base slot_request
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 certificate callback received an open, mismatched, or oracle theorem"
        "template request with slot theorem"
        (fn () => #remember_equation store base template_request slot_eq)
      val mismatched_template_rejected = true
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 certificate callback received an open, mismatched, or oracle theorem"
        "slot request with template theorem"
        (fn () => #remember_equation store base slot_request template_eq)
      val mismatched_slot_rejected = true
      val _ = #remember_equation store base binding binding_eq
      val _ = #note_context_request_completed store lift_request
      fun warm proposition theorem = (case #lookup_equation store proposition of SOME found => Thm.eq_thm_prop (theorem, found) | NONE => false)
      fun absent proposition = (case #lookup_equation store proposition of NONE => true | SOME _ => false)
      val false_template = request template_head
        [columns, templates, template_ids, @{term "77::nat"}]
      val false_template_eq = Simplifier.rewrite base (Thm.cterm_of ctxt false_template)
      val false_template_exact =
        Thm.term_of (Thm.lhs_of false_template_eq) aconv false_template andalso
        Thm.term_of (Thm.rhs_of false_template_eq) aconv @{term False} andalso
        Comma_Semantic_B1_Construction_Check.standalone false_template_eq andalso
        null (Thm_Deps.all_oracles [false_template_eq])
      val _ = if false_template_exact then ()
        else error "B1 failed-root fixture did not produce an exact standalone False equation"
      val before_false_shape = #retained_entry_counts store ()
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 certificate callback received an open, mismatched, or oracle theorem"
        "false request with true template theorem"
        (fn () => #remember_equation store base false_template template_eq)
      val false_shape_rejected = true
      val false_shape_not_inserted = false_shape_rejected andalso
        absent false_template andalso
        before_false_shape = #retained_entry_counts store ()
      val false_template_entries = #retained_entry_counts store ()
      val _ = #remember_equation store base false_template false_template_eq
      val false_template_noop = absent false_template andalso
        false_template_entries = #retained_entry_counts store ()
      val changed_slot = request slot_head [columns, templates, template_ids, lift_ids, @{term "[(0::nat,(0::nat,[Comma_Semantic_B1_Stop 9]))]"}, lift_descriptors, @{term "1::nat"}, refs, @{term "0::nat"}]
      val shifted_slot = request slot_head [columns, templates, template_ids, lift_ids, occurrence_descriptors, @{term "[comma_semantic_b1_crt_lift_descriptor.make 3 0 0 1]"}, @{term "1::nat"}, refs, @{term "0::nat"}]
      val changed_slot_eq = capture "changed occurrence slot" false base changed_slot
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 slot certificate used foreign catalogue terms" "changed occurrence slot"
        (fn () => #remember_equation store base changed_slot changed_slot_eq)
      val changed_slot_rejected = true
      val changed_binding = binding_request @{term "Comma_Near 9 1 19 :: comma_finite_position"}
      val changed_binding_eq = capture "changed source binding" false base changed_binding
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 piece binding changed the active source" "changed source binding"
        (fn () => #remember_equation store base changed_binding changed_binding_eq)
      val changed_binding_rejected = true
      val forged_columns = HOLogic.mk_list @{typ comma_crt_column}
        [bool_true, scope_true, bool_true]
      (* Keep CID 0 fixed while changing the catalog.  A CID hit must not
         authorize geometry certified in this foreign catalog. *)
      val forged_root = request template_head
        [forged_columns, templates, template_ids, @{term "0::nat"}]
      val forged_root_eq = capture "foreign catalog CID" false base forged_root
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 template certificate used foreign catalogue terms" "foreign catalog CID"
        (fn () => #remember_equation store base forged_root forged_root_eq)
      val forged_root_rejected = true
      val foreign_theory = Context.begin_thy
        (Long_Name.qualify (Context.theory_long_name thy)
          "B1_Certificate_Store_Foreign") [thy]
      val foreign_context = Proof_Context.transfer foreign_theory base
      val foreign_template_eq = Simplifier.rewrite foreign_context
        (Thm.cterm_of foreign_context template_request)
      val foreign_theorem_has_descendant_provenance =
        Context.proper_subthy (thy, Thm.theory_of_thm foreign_template_eq)
      val foreign_theorem_is_exact_kernel_equation =
        Thm.term_of (Thm.lhs_of foreign_template_eq) aconv template_request andalso
        Thm.term_of (Thm.rhs_of foreign_template_eq) aconv @{term True} andalso
        Comma_Semantic_B1_Construction_Check.standalone foreign_template_eq andalso
        null (Thm_Deps.all_oracles [foreign_template_eq])
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 certificate theorem comes from a non-ancestor theory"
        "foreign-theory theorem" (fn () =>
          #remember_equation store base template_request foreign_template_eq)
      val foreign_theorem_rejected = true
      val off_thread_lookup = Synchronized.var
        "b1 certificate store off-thread lookup" false
      val off_thread = Isabelle_Thread.fork
        (Isabelle_Thread.params "b1-certificate-store-guard")
        (fn () =>
          let
            val rejected =
              (Comma_Semantic_B1_Column_Regression.expect_error
                "B1 certificate store used outside its owning ML thread"
                "off-thread lookup"
                (fn () => #lookup_equation store template_request);
               true)
          in Synchronized.change off_thread_lookup (K rejected) end)
      val _ = Isabelle_Thread.join off_thread
      val off_thread_rejected = Synchronized.value off_thread_lookup
      val warm_geometry = warm template_request template_eq andalso warm lift_request lift_eq andalso warm slot_request slot_eq
      val _ = #reset_current_source store 0
      val _ = #remember_equation store base source_action_request source_action_eq
      val slot_valid_base = base
      val slot_valid_eq = capture "action-backed slot validity" true slot_valid_base slot_valid_request
      val changed_descriptors = HOLogic.mk_list @{typ comma_semantic_b1_crt_lift_descriptor}
        [@{term "comma_semantic_b1_crt_lift_descriptor.make 3 0 0 1"}]
      val changed_slot_valid = request slot_valid_head
        [sources, occurrence_at, occurrence_descriptors, templates, source,
         occurrence, terminal_refs, changed_descriptors, @{term "0::nat"}]
      val changed_slot_valid_eq = capture "changed slot descriptors" false slot_valid_base changed_slot_valid
      val _ = Comma_Semantic_B1_Column_Regression.expect_error
        "B1 source-slot certificate used foreign lift descriptors"
        "changed slot descriptors"
        (fn () => #remember_equation store base
          changed_slot_valid changed_slot_valid_eq)
      val changed_descriptors_rejected = true
      val warm_slot_valid = warm slot_valid_request slot_valid_eq
      val legacy_negative_absence = absent changed_slot andalso absent shifted_slot andalso
        absent changed_binding andalso absent forged_root
      val action_head_fixtures_pass =
        Comma_Semantic_B1_Certificate_Store_Action_Fixtures.check
          {ctxt = ctxt, base = slot_valid_base, store = store,
           action_table = action_table, columns = columns, templates = templates,
           template_ids = template_ids, lift_ids = lift_ids, sources = sources,
           occurrence_at = occurrence_at,
           occurrence_descriptors = occurrence_descriptors,
           lift_descriptors = lift_descriptors, refs = refs,
           terminal_refs = terminal_refs, source = source, occurrence = occurrence,
           request = request, capture = capture,
           reset_current_source = #reset_current_source store}
      val fixture_checks =
        [("pre_scope_rejected", pre_scope_rejected),
         ("missing_template_lift_rejected", missing_template_lift_rejected),
         ("missing_template_lift_not_published", missing_template_lift_not_published),
         ("noncanonical_refs_rejected", noncanonical_refs_rejected),
         ("mismatched_template_rejected", mismatched_template_rejected),
         ("mismatched_slot_rejected", mismatched_slot_rejected),
         ("changed_slot_rejected", changed_slot_rejected),
         ("changed_binding_rejected", changed_binding_rejected),
         ("changed_descriptors_rejected", changed_descriptors_rejected),
         ("forged_root_rejected", forged_root_rejected),
         ("foreign_theorem_has_descendant_provenance", foreign_theorem_has_descendant_provenance),
         ("foreign_theorem_is_exact_kernel_equation", foreign_theorem_is_exact_kernel_equation),
         ("foreign_theorem_rejected", foreign_theorem_rejected),
         ("off_thread_rejected", off_thread_rejected),
         ("ignored_generic_skips_oracle_scan", ignored_generic_skips_oracle_scan),
         ("action_head_fixtures_pass", action_head_fixtures_pass),
         ("warm_geometry", warm_geometry),
         ("warm_slot_valid", warm_slot_valid),
         ("legacy_negative_absence", legacy_negative_absence),
         ("false_shape_not_inserted", false_shape_not_inserted),
         ("false_template_noop", false_template_noop)]
      val failed_fixture_checks = map #1 (filter (not o #2) fixture_checks)
      val _ = if null failed_fixture_checks then ()
        else error ("B1 exact certificate-store fixture failed: " ^
          String.concatWith ", " failed_fixture_checks)
    in () end
  fun check_projection_memo_dispatch dispatch hits misses head_opens =
    let
      val fields = @{term
        "\<lparr>comma_semantic_b1_crt_occurrence_columns = comma_semantic_b1_crt_columns,
          comma_semantic_b1_crt_occurrence_rebase = 0,
          comma_semantic_b1_crt_occurrence_beta = [Comma_Semantic_B1_Stop 8]\<rparr>"}
      val changed_fields = @{term
        "\<lparr>comma_semantic_b1_crt_occurrence_columns = comma_semantic_b1_crt_columns,
          comma_semantic_b1_crt_occurrence_rebase = 0,
          comma_semantic_b1_crt_occurrence_beta = [Comma_Semantic_B1_Stop 9]\<rparr>"}
      val selector = @{term "comma_semantic_b1_crt_occurrence_beta ::
        comma_semantic_b1_crt_occurrence => comma_semantic_b1_result list"}
      val request = selector $ fields
      val changed_request = selector $ changed_fields
      val expected = @{term "[Comma_Semantic_B1_Stop 8]"}
      val changed_expected = @{term "[Comma_Semantic_B1_Stop 9]"}
      val before_hits = !hits
      val before_misses = !misses
      val before_opens = head_opens ()
      fun equation key =
        (case dispatch key of SOME theorem => theorem
        | NONE => error "B1 occurrence field projection was not published")
      val cold = equation request
      val warm = equation request
      val changed = equation changed_request
      val after_opens = head_opens ()
      val exact = fn theorem => Thm.term_of (Thm.rhs_of theorem)
      val _ = if exact cold aconv expected andalso exact warm aconv expected andalso
          exact changed aconv changed_expected andalso Thm.eq_thm_prop (cold, warm) andalso
          Thm.nprems_of cold = 0 andalso null (Thm.hyps_of cold) andalso
          null (Thm.tpairs_of cold) andalso null (Thm_Deps.all_oracles [cold]) andalso
          !hits = before_hits + 1 andalso !misses = before_misses + 2 andalso
          after_opens = before_opens
        then () else error "B1 occurrence field projection/cache regression failed"
    in () end
  fun check_partial_equation_gate
      {ctxt, context, publish, dispatch, memo_has, incomplete_has,
       memo_size, publication_count, clear_incomplete} =
    let
      val request = @{term "comma_crt_supported (Comma_CRT_Bool True)"}
      val cterm = Thm.cterm_of ctxt request
      val before_publications = publication_count ()
      val before_retained = memo_size ()
      val _ = if memo_has request orelse incomplete_has request then
          error "B1 residual-equation fixture key unexpectedly preexists" else ()
      val rejected = publish request (Thm.reflexive cterm)
      val _ = if (case rejected of NONE => true | SOME _ => false) andalso
          not (memo_has request) andalso incomplete_has request andalso
          publication_count () = before_publications andalso
          memo_size () = before_retained
        then () else error "B1 residual Boolean equation escaped completion publication gate"
      val returned = dispatch cterm
      val _ = if (case returned of NONE => true | SOME _ => false) andalso
          not (memo_has request)
        then () else error "B1 Congproc returned or published an incomplete Boolean equation"
      val _ = clear_incomplete request
    in () end
  fun check_cid_transition_cache
      {transition, counts, node_level, column_value, node_count, head_opens} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val cofactor = Const (@{const_name comma_crt_cofactor_or_false},
        natT --> natT --> columnT --> columnT)
      fun checked (level, digit, cid) =
        let
          val {target_cid, theorem} = transition (level, digit, cid)
          val expected = cofactor $ HOLogic.mk_number natT level $
            HOLogic.mk_number natT digit $ column_value cid
          val _ = if Thm.term_of (Thm.lhs_of theorem) aconv expected andalso
              Thm.term_of (Thm.rhs_of theorem) aconv column_value target_cid andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso
              null (Thm_Deps.all_oracles [theorem]) then ()
            else error "B1 CID transition fixture received another edge theorem"
        in (target_cid, theorem) end
      val level = (case node_level 2 of SOME level => level
        | NONE => error "B1 CID transition fixture has no nonterminal column")
      val {lookups = l0, hits = h0, misses = m0, proofs = p0} = counts ()
      val cold = checked (level, 0, 2)
      val {lookups = l1, hits = h1, misses = m1, proofs = p1} = counts ()
      val opened = head_opens ()
      val warm = checked (level, 0, 2)
      val {lookups = l2, hits = h2, misses = m2, proofs = p2} = counts ()
      val _ = if l1 = l0 + 1 andalso h1 = h0 andalso m1 = m0 + 1 andalso
          p1 = p0 + 1 andalso l2 = l1 + 1 andalso h2 = h1 + 1 andalso
          m2 = m1 andalso p2 = p1 andalso head_opens () = opened andalso
          #1 cold = #1 warm andalso Thm.eq_thm_prop (#2 cold, #2 warm)
        then () else error "B1 warm CID edge repeated proof construction or DAG opening"
      val _ = checked (level, 1, 2)
      val _ = if #1 (checked (0, 0, 0)) = 0 andalso
          #1 (checked (0, 0, 1)) = 1 then ()
        else error "B1 CID transition changed a Boolean terminal"
      val {lookups = _, hits = invalid_hits, misses = invalid_misses,
        proofs = invalid_proofs} = counts ()
      val expect = Comma_Semantic_B1_Column_Regression.expect_error
      val _ = expect "B1 cofactor transition has an invalid CRT level"
        "out-of-range transition level" (fn () => transition (4, 0, 2))
      val _ = expect "B1 cofactor transition has a digit outside its radix"
        "out-of-range transition digit" (fn () => transition (0, 4, 2))
      val _ = expect "B1 cofactor transition requested a foreign CID"
        "foreign transition CID" (fn () => transition (0, 0, node_count))
      val _ = expect "B1 cofactor metadata requested a foreign CID"
        "foreign metadata CID" (fn () => node_level (~1))
      val {lookups = _, hits = after_hits, misses = after_misses,
        proofs = after_proofs} = counts ()
      val _ = if after_hits = invalid_hits andalso after_misses = invalid_misses
          andalso after_proofs = invalid_proofs then ()
        else error "B1 invalid CID edge changed the admitted transition cache"
    in () end

  fun check_partition_transition_dag
      {ctxt, column_value, step, cofactor_transition, node_count,
       node_level, column_counts, head_opens} =
    let
      val state_misses = Unsynchronized.ref 0
      val state_hits = Unsynchronized.ref 0
      val vector_misses = Unsynchronized.ref 0
      val vector_hits = Unsynchronized.ref 0
      fun note hits misses hit =
        if hit then hits := !hits + 1 else misses := !misses + 1
      val engine = Comma_Semantic_B1_Partition_Conversion.make_template_state_prover ctxt
        {column_value = column_value, step = step,
         cofactor_transition = cofactor_transition, node_count = node_count}
        {note_cid_state = note state_hits state_misses,
         note_cid_vector_transition = note vector_hits vector_misses}
      val level = (case node_level 2 of SOME level => level
        | NONE => error "B1 vector fixture requires a nonterminal CID")
      val first = #prove_transition engine level 0 [2]
      val misses = !vector_misses
      val hits = !vector_hits
      val opened = head_opens ()
      val {lookups = _, hits = _, misses = _, proofs = proofs_before} = column_counts ()
      val second = #prove_transition engine level 0 [2]
      val {lookups = _, hits = _, misses = _, proofs = proofs_after} = column_counts ()
      val _ = if #1 first = #1 second andalso
          Thm.eq_thm_prop (#2 first, #2 second) andalso
          !vector_misses = misses andalso !vector_hits = hits + 1 andalso
          head_opens () = opened andalso proofs_after = proofs_before then ()
        else error "B1 warm vector transition rebuilt column proofs or reopened the DAG"
      val duplicate = #prove_transition engine 0 0 [1, 1]
      val with_false = #prove_transition engine 0 0 [0, 1]
      val without_false = #prove_transition engine 0 0 [1]
      val _ = if #1 duplicate = [1, 1] andalso
          #1 with_false = [1] andalso #1 without_false = [1] andalso
          not (Thm.term_of (Thm.lhs_of (#2 with_false)) aconv
            Thm.term_of (Thm.lhs_of (#2 without_false))) then ()
        else error "B1 vector transition erased multiplicity or the original request"
      val (fallbacks_before_state, derived_before_state) = #residual_work_counts engine ()
      val _ = if derived_before_state > 0 then () else error
        "B1 vector transition did not publish a child residual theorem"
      val cold_state = #prove_state engine [0, 1, 2, 3] [1]
      val (fallbacks_after_state, derived_after_state) = #residual_work_counts engine ()
      val states = !state_misses
      val reused = !state_hits
      val warm_state = #prove_state engine [0, 1, 2, 3] [1]
      val _ = if Thm.eq_thm_prop (cold_state, warm_state) andalso
          !state_misses = states andalso !state_hits = reused + 1 andalso
          fallbacks_after_state = fallbacks_before_state andalso
          derived_after_state >= derived_before_state then ()
        else error "B1 warm partition state reconstructed its proof"
      val (head_builds_before, head_hits_before) = #residual_head_counts engine ()
      val one_true = #prove_state engine [3] [0, 1]
      val (head_builds_middle, head_hits_middle) = #residual_head_counts engine ()
      val (duplicates, duplicate_ids) = #prove_residual engine [0, 1, 1]
      val (head_builds_after, head_hits_after) = #residual_head_counts engine ()
      val residual = Const (@{const_name comma_semantic_b1_crt_partition_drop_false},
        @{typ "comma_crt_column list"} --> @{typ "comma_crt_column list"})
      val expected_duplicate_lhs = residual $ (#literal_columns engine [0, 1, 1])
      val expected_duplicate_rhs = #literal_columns engine [1, 1]
      val _ = if Thm.term_of (Thm.rhs_of one_true) aconv @{term True} andalso
          duplicate_ids = [1, 1] andalso
          Thm.term_of (Thm.lhs_of duplicates) aconv expected_duplicate_lhs andalso
          Thm.term_of (Thm.rhs_of duplicates) aconv expected_duplicate_rhs andalso
          head_builds_middle = head_builds_before + 2 andalso
          head_hits_middle = head_hits_before andalso
          head_builds_after = head_builds_middle andalso
          head_hits_after = head_hits_middle + 3 then ()
        else error "B1 false-removal cons equations failed ordered warm reuse"
      val stored = #state_counts engine ()
      val expect = Comma_Semantic_B1_Column_Regression.expect_error
      val _ = expect "B1 CID partition vector has an invalid CRT level"
        "empty-vector level guard" (fn () => #prove_transition engine 4 0 [])
      val _ = expect "B1 CID partition vector digit is outside its radix"
        "empty-vector digit guard" (fn () => #prove_transition engine 0 4 [])
      val _ = expect "B1 CID partition vector contains a foreign CID"
        "vector source authority" (fn () => #prove_transition engine 0 0 [node_count])
      val _ = if #state_counts engine () = stored then ()
        else error "B1 rejected vector request retained a certificate"
    in () end

  fun check_cofactor_state_warm_memo
      {ctxt, context, with_partition_scope, state_counts,
       canonicalize, memo_proc, isolate} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val columnsT = HOLogic.listT columnT
      val levelsT = HOLogic.listT natT
      val true_column = @{term "Comma_CRT_Bool True"}
      val false_column = @{term "Comma_CRT_Bool False"}
      val cofactor = Const (@{const_name comma_crt_cofactor_or_false},
        natT --> natT --> columnT --> columnT) $
          HOLogic.mk_number natT 0 $ HOLogic.mk_number natT 0
      val map_column = Const (@{const_name map},
        (columnT --> columnT) --> columnsT --> columnsT)
      val drop_false = Const (@{const_name comma_semantic_b1_crt_partition_drop_false},
        columnsT --> columnsT)
      val checked = Const
        (@{const_name comma_semantic_b1_crt_partition_cofactor_checked},
         levelsT --> columnsT --> @{typ bool})
      fun level_list levels = HOLogic.mk_list natT (map (HOLogic.mk_number natT) levels)
      fun request levels columns = checked $ level_list levels $ columns
      fun make_recipe extra_false =
        drop_false $ (map_column $ cofactor $
          HOLogic.mk_list columnT (true_column ::
            (if extra_false then [false_column] else [])))
      val first_request = request [0] (make_recipe false)
      val second_request = request [0] (make_recipe true)
      val different_level_request = request [1] (make_recipe false)
      val different_columns_request = request []
        (HOLogic.mk_list columnT [true_column, true_column])
      val false_request = request [] (HOLogic.mk_list columnT [false_column])
      val true_after_false_request = request []
        (HOLogic.mk_list columnT [true_column, false_column])
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val empty_dag = Const (@{const_name Comma_B1_CRT_Column_DAG_Empty}, dagT)
      val column_at = Const (@{const_name comma_semantic_b1_crt_column_at},
        dagT --> natT --> columnT)
      val direct_column_at_request = request [] (HOLogic.mk_list columnT
        [column_at $ empty_dag $ HOLogic.mk_number natT 2])
      val partition_head = Const
        (@{const_name comma_semantic_b1_crt_columns_partition_certified},
         columnsT --> @{typ bool})
      val complementary_quarters = @{term
        "[Comma_CRT_Node 0 [Comma_CRT_Bool True,Comma_CRT_Bool True,
           Comma_CRT_Bool False,Comma_CRT_Bool False],
          Comma_CRT_Node 0 [Comma_CRT_Bool False,Comma_CRT_Bool False,
           Comma_CRT_Bool True,Comma_CRT_Bool True]] :: comma_crt_column list"}
      val complementary_quarters_request = partition_head $ complementary_quarters
      val catalog_dag = Const
        (@{const_name comma_semantic_b1_crt_column_node_dag}, dagT)
      val named_column = column_at $ catalog_dag $ HOLogic.mk_number natT 2
      val negate_column = Const (@{const_name comma_crt_negate}, columnT --> columnT)
      val named_complement_request = partition_head $
        HOLogic.mk_list columnT [named_column, negate_column $ named_column]
      val expected_canonical = request [0] (HOLogic.mk_list columnT [true_column])
      fun canonical_request term =
        Thm.term_of (Thm.rhs_of (canonicalize (Thm.cterm_of ctxt term)))
      val _ = if canonical_request first_request aconv expected_canonical andalso
          canonical_request second_request aconv expected_canonical andalso
          not (canonical_request different_level_request aconv expected_canonical) andalso
          not (canonical_request different_columns_request aconv expected_canonical) andalso
          canonical_request false_request aconv false_request andalso
          canonical_request true_after_false_request aconv true_after_false_request andalso
          canonical_request direct_column_at_request aconv direct_column_at_request
        then () else error
          "B1 cofactor-state fixture lost vector order, false inputs, dimensions, or canonical column authority"
      fun exact request expected =
        (case memo_proc context (Thm.cterm_of ctxt request) of
          SOME theorem =>
            if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
                Thm.term_of (Thm.rhs_of theorem) aconv expected andalso
                Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
                null (Thm.tpairs_of theorem)
            then theorem
            else error "B1 cofactor-state fixture returned a non-exact theorem"
        | NONE => error "B1 cofactor-state fixture missed a closed checker request")
      fun run_fixture () =
        let
          val (conversions0, hits0) = state_counts ()
          val first = exact first_request @{term True}
          val (conversions1, hits1) = state_counts ()
          val _ = if conversions1 = conversions0 + 1 andalso hits1 = hits0
            then () else error "B1 first cofactor state was not constructed once"
          val second = exact second_request @{term True}
          val (conversions2, hits2) = state_counts ()
          val _ = if conversions2 = conversions1 andalso hits2 = hits1 + 1
            then () else error "B1 equivalent cofactor recipe did not reuse its canonical state"
          val _ = exact different_level_request @{term True}
          val (conversions3, hits3) = state_counts ()
          val _ = if conversions3 = conversions2 + 1 andalso hits3 = hits2
            then () else error "B1 cofactor memo ignored remaining-level identity"
          val _ = exact different_columns_request @{term False}
          val (conversions4, hits4) = state_counts ()
          val _ = if conversions4 = conversions3 + 1 andalso hits4 = hits3
            then () else error "B1 cofactor memo ignored column order or multiplicity"
          val _ = exact false_request @{term False}
          val _ = exact true_after_false_request @{term True}
          val _ = if Thm.term_of (Thm.lhs_of first) aconv first_request andalso
              Thm.term_of (Thm.lhs_of second) aconv second_request then ()
            else error "B1 cofactor-state warm fixture lost the original theorem request"
          val (quarter_conversions_before, quarter_hits_before) = state_counts ()
          val _ = exact complementary_quarters_request @{term True}
          val (quarter_conversions_after, quarter_hits_after) = state_counts ()
          val _ = if quarter_conversions_after > quarter_conversions_before + 1 andalso
              quarter_hits_after > quarter_hits_before then ()
            else error
              "B1 complementary-quarter fixture bypassed recursive cofactor-state reuse"
          val _ = exact named_complement_request @{term True}
        in SOME first end
      val outcome = isolate (fn () => with_partition_scope run_fixture)
    in
      (case outcome of
        SOME _ => ()
      | NONE => error "B1 cofactor-state warm fixture did not complete")
    end
end
