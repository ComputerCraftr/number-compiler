(* Proof-producing decomposition of one selected occurrence construction check. *)
structure Comma_Semantic_B1_Construction_Check =
struct
  fun residual_conjunct_summary term =
    let
      fun visit remaining current atoms =
        if remaining = 0 then (remaining, atoms, true)
        else (case current of
          Const (name, _) $ left $ right =>
            if name = @{const_name HOL.conj} then
              let val (after_left, left_atoms, left_truncated) =
                    visit (remaining - 1) left atoms
                  val (after_right, right_atoms, right_truncated) =
                    visit after_left right left_atoms
              in (after_right, right_atoms,
                left_truncated orelse right_truncated) end
            else (remaining - 1, current :: atoms, false)
        | _ => (remaining - 1, current :: atoms, false))
      val (_, reverse_atoms, truncated) = visit 64 term []
      val atoms = rev reverse_atoms
      fun clip limit text = String.substring (text, 0, Int.min (limit, String.size text))
      fun render atom =
        let
          fun show 0 _ = ("...", 0)
            | show remaining current =
                (case current of
                  Const (name, _) => (Long_Name.base_name name, remaining - 1)
                | Free (name, _) => ("Free:" ^ name, remaining - 1)
                | Var ((name, index), _) =>
                    ("Var:" ^ name ^ "." ^ Int.toString index, remaining - 1)
                | Bound index => ("Bound:" ^ Int.toString index, remaining - 1)
                | Abs (name, _, body) =>
                    let val (body_text, rest) = show (remaining - 1) body
                    in ("(lambda " ^ name ^ ". " ^ body_text ^ ")", rest) end
                | function $ argument =>
                    let val (function_text, after_function) =
                          show (remaining - 1) function
                        val (argument_text, after_argument) =
                          show after_function argument
                    in ("(" ^ function_text ^ " " ^ argument_text ^ ")",
                      after_argument) end)
          val (text, _) = show 32 atom
        in clip 160 text end
      val summary = String.concatWith " && " (map render atoms)
    in clip 900 summary ^ (if truncated then " ..." else "") end

  val maximum_source_extent = 1024
  (* The occurrence contract admits at most 28 lift descriptors per source. *)
  val maximum_lift_catalog_extent = 28 * maximum_source_extent
  fun indexed_extent_contract predicate upper =
    let
      val zero = @{term "0::nat"}
      val predicate_at_zero =
        (case predicate of Abs _ => Term.betapply (predicate, zero)
        | _ => predicate $ zero)
      val (predicate_head, arguments) = strip_comb predicate_at_zero
      val exact_lift_catalog =
        (case predicate_head of
          Const (name, _) => name =
            @{const_name comma_semantic_b1_crt_lift_geometry_certified}
        | _ => false) andalso
        length arguments = 6 andalso
        ListPair.allEq (op aconv) (arguments,
          [@{term comma_semantic_b1_crt_columns},
           @{term comma_semantic_b1_crt_templates},
           @{term comma_semantic_b1_crt_template_column_ids},
           @{term comma_semantic_b1_crt_lift_column_ids},
           @{term comma_semantic_b1_crt_lift_descriptors}, zero]) andalso
        upper aconv @{term "length comma_semantic_b1_crt_lift_descriptors"}
      val label = the_default "non-constant" (case predicate_head of
        Const (name, _) => SOME name | _ => NONE)
    in (label, if exact_lift_catalog then maximum_lift_catalog_extent
      else maximum_source_extent) end
  fun indexed_extent_admitted bound extent = bound >= 0 andalso bound <= extent
  fun check_indexed_extent_regressions () =
    let
      val exact_lift = @{term
        "\<lambda>cid::nat. comma_semantic_b1_crt_lift_geometry_certified
          comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_template_column_ids
          comma_semantic_b1_crt_lift_column_ids
          comma_semantic_b1_crt_lift_descriptors cid"}
      val forged_lift = @{term
        "\<lambda>cid::nat. comma_semantic_b1_crt_lift_geometry_certified
          comma_semantic_b1_crt_columns [] comma_semantic_b1_crt_template_column_ids
          comma_semantic_b1_crt_lift_column_ids
          comma_semantic_b1_crt_lift_descriptors cid"}
      val unrelated = @{term "\<lambda>index::nat. True"}
      val (_, exact_extent) = indexed_extent_contract exact_lift
        @{term "length comma_semantic_b1_crt_lift_descriptors"}
      val (_, unrelated_extent) = indexed_extent_contract unrelated @{term "1025::nat"}
      val (_, forged_extent) = indexed_extent_contract forged_lift
        @{term "length comma_semantic_b1_crt_lift_descriptors"}
    in
      if exact_extent = maximum_lift_catalog_extent andalso
          not (indexed_extent_admitted 1025 unrelated_extent) andalso
          not (indexed_extent_admitted 1025 forged_extent) then ()
      else error "B1 indexed catalog extent regression failed"
    end
  val _ = check_indexed_extent_regressions ()
  val occurrence_projection_patterns =
    [@{term "comma_semantic_b1_crt_occurrence_columns occurrence"},
     @{term "comma_semantic_b1_crt_occurrence_rebase occurrence"},
     @{term "comma_semantic_b1_crt_occurrence_beta occurrence"}]
  val occurrence_projection_roots = map
    (fn pattern => (case Term.head_of pattern of Const (name, _) => name
      | _ => error "B1 occurrence projection pattern is not a constant"))
    occurrence_projection_patterns
  fun is_occurrence_projection request =
    member (op =) occurrence_projection_roots
      (case Term.head_of request of Const (name, _) => name | _ => "")
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
  fun matches_owned_request thy roots patterns request =
    member (op =) roots (the_default "" (Comma_Selected_List_Conversion.head_name request))
      orelse exists (fn pattern => Pattern.matches thy (pattern, request)) patterns
  fun make_head_matcher roots = fn request =>
    member (op =) roots
      (the_default "" (Comma_Selected_List_Conversion.head_name request))
  fun make_lift_option_tracker lift_head hits =
    let
      fun is_request request =
        Comma_Selected_List_Conversion.head_name request = SOME lift_head
      fun note_hit request = if is_request request then
        hits := !hits + 1 else ()
    in {is_request = is_request, note_hit = note_hit} end
  fun make_occurrence_cache_reporters started counters endpoint_counters misses last_head =
    let
      fun report message details =
        if Comma_Proof_Profile.enabled () then
          let val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
          in Comma_Proof_Profile.report
            (message ^ details ^ " elapsed_ms=" ^ LargeInt.toString elapsed) end
        else ()
      fun endpoint_stats () = endpoint_counters ()
      fun checkpoint () = if !misses mod 1024 = 0 then
        report "B1 occurrence proof cache checkpoint "
          (counters () ^ " last_head=" ^ !last_head) else ()
      fun milestone label = report ("B1 occurrence proof cache " ^ label ^ " ")
        (counters () ^ endpoint_stats ())
    in {checkpoint = checkpoint, milestone = milestone,
        endpoint_stats = endpoint_stats} end
  fun add_named_operation_time table name elapsed =
    let val (calls, total) = the_default (0, 0) (Symtab.lookup (!table) name)
    in table := Symtab.update (name, (calls + 1, total + elapsed)) (!table) end
  fun timed_stage label calls limit compute =
    let
      val call = !calls
      val _ = calls := call + 1
      val started = if call < limit andalso Comma_Proof_Profile.enabled ()
        then SOME (Time.now ()) else NONE
      val _ = (case started of SOME _ => Comma_Proof_Profile.report
        ("B1 " ^ label ^ " start call=" ^ Int.toString call) | NONE => ())
      val result = compute ()
      val _ = (case started of
        SOME start => Comma_Proof_Profile.report ("B1 " ^ label ^
          " complete call=" ^ Int.toString call ^ " elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms start)
      | NONE => ())
    in result end
  fun make_occurrence_projector ctxt =
    let
      val requests = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val misses = Unsynchronized.ref 0
      fun stats () = "occurrence_projection_requests=" ^ Int.toString (!requests) ^
        " occurrence_projection_hits=" ^ Int.toString (!hits) ^
        " occurrence_projection_misses=" ^ Int.toString (!misses)
      fun selector_data theorem =
        let
          val equation = Local_Defs.meta_rewrite_rule ctxt theorem
          val (selector, arguments) = strip_comb (Thm.term_of (Thm.lhs_of equation))
        in
          (case (selector, arguments) of
            (Const (selector_name, _), [record_pattern]) =>
              if not (member (op =) occurrence_projection_roots selector_name) then NONE
              else
                let
                  val (record_constructor, _) = strip_comb record_pattern
                  val (constructor_name, constructor_type) =
                    (case record_constructor of Const (name, typ) => (name, typ)
                    | _ => error "B1 occurrence selector theorem has no record constructor")
                in SOME (selector_name, constructor_name,
                  Const (constructor_name, constructor_type), equation) end
          | _ => NONE)
        end
      val selectors = map_filter selector_data
        @{thms comma_semantic_b1_crt_occurrence.select_convs}
      val constructor_name = #2 (hd selectors)
      val _ = if length selectors = 3 andalso
          forall (fn (_, name, _, _) => name = constructor_name) selectors andalso
          sort string_ord (map #1 selectors) =
            sort string_ord occurrence_projection_roots
        then () else error "B1 occurrence selector theorem inventory changed"
      fun selected_rule name =
        (case filter (fn (selector, _, _, _) => selector = name) selectors of
          [(_, _, _, equation)] => equation
        | _ => error "B1 occurrence selector theorem is missing or duplicated")
      fun project context cterm =
        let
          val request = Thm.term_of cterm
          val _ = if is_occurrence_projection request andalso
              Comma_Selected_List_Conversion.closed request then ()
            else error "B1 occurrence projection request is not an owned closed selector"
          val (selector, [occurrence]) = strip_comb request
          val selector_name = (case selector of Const (name, _) => name
            | _ => error "B1 occurrence projection has a nonconstant selector")
          val occurrence_ct = Thm.cterm_of ctxt occurrence
          val occurrence_equation =
            (case strip_comb occurrence of
              (Const (name, _), _) =>
                if name = constructor_name then Thm.reflexive occurrence_ct
                else Simplifier.rewrite context occurrence_ct
            | _ => Simplifier.rewrite context occurrence_ct)
          val checked_occurrence = Comma_Selected_List_Conversion.validate_equation
            occurrence occurrence_equation
          val selected_record = Thm.term_of (Thm.rhs_of checked_occurrence)
          val _ = (case strip_comb selected_record of
            (Const (name, _), _) => if name = constructor_name then ()
              else error "B1 occurrence projection did not select the record constructor"
          | _ => error "B1 occurrence projection did not select a record")
          val expose = Comma_Semantic_B1_CRT_Operation_Conversion.argument_at 0
            (Conv.rewr_conv checked_occurrence) cterm
          val selection = Conv.rewr_conv (selected_rule selector_name) (Thm.rhs_of expose)
          val selected_rhs = Thm.rhs_of selection
          val selected_rhs_term = Thm.term_of selected_rhs
          val selected_value = Simplifier.rewrite context selected_rhs
          val selected_value = Comma_Selected_List_Conversion.validate_equation
            selected_rhs_term selected_value
          val theorem = Thm.transitive expose (Thm.transitive selection selected_value)
          val checked = Comma_Selected_List_Conversion.validate_equation request theorem
          val _ = if fastype_of (Thm.term_of (Thm.rhs_of checked)) = fastype_of request
            then () else error "B1 occurrence selector changed its result type"
        in checked end
    in {project = project,
        note_request = fn () => requests := !requests + 1,
        note_hit = fn () => hits := !hits + 1,
        note_miss = fn () => misses := !misses + 1,
        stats = stats} end

  fun make_successor_cache ctxt capacity =
    let
      val _ = if capacity > 0 andalso
          capacity <= maximum_lift_catalog_extent then () else
        error "B1 indexed successor cache exceeds the checked catalog extent"
      val cache = Comma_Selected_List_Conversion.make_successor_cache ctxt capacity
      val equation = #equation cache
      val stats = #stats cache
      val clear = #clear cache
      fun numeral value = HOLogic.mk_number @{typ nat} value
      fun expect_error expected attempt =
        (case attempt of
          Exn.Exn (ERROR message) => if message = expected then ()
            else error ("B1 successor regression failed for the wrong reason: " ^ message)
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "B1 successor regression unexpectedly accepted its input")
      val cold = equation 0
      val hits_before_warm = #hits cache ()
      val warm = equation 0
      val _ = if Thm.eq_thm_prop (cold, warm) andalso
          Thm.term_of (Thm.rhs_of cold) aconv numeral 1 andalso
          Thm.nprems_of cold = 0 andalso null (Thm.hyps_of cold) andalso
          null (Thm.tpairs_of cold) andalso null (Thm_Deps.all_oracles [cold]) andalso
          #hits cache () = hits_before_warm + 1
        then () else error "B1 cold/warm successor cache regression failed"
      val _ = expect_error "selected-list conversion returned an open or mismatched theorem"
        (Exn.capture (fn () =>
          Comma_Selected_List_Conversion.checked_successor_equation (fn _ => cold) 1) ())
      val _ = expect_error "Indexed successor cache exceeded its declared extent"
        (Exn.capture (fn () => equation capacity) ())
      val _ = clear ()
    in {equation = equation, stats = stats} end

  fun prove_construction
      {ctxt, evaluation_context, construction_context, prove_expression,
       component_counter, progress_counter, reset_certificate_source,
       profile_certificate_source} proposition =
    let
      val (head, [index_term]) = strip_comb proposition
      val name = (case head of Const (constant, _) => constant
        | _ => error "B1 construction checker expected a constant head")
      val _ = if name = @{const_name comma_semantic_b1_crt_construction_check}
        then () else error "B1 construction checker received another predicate"
      val (index_type, index_value) = HOLogic.dest_number index_term
      val _ = if index_type = @{typ nat} then ()
        else error "B1 construction index is not a natural numeral"
      val owner = "B1 construction index=" ^ Int.toString index_value
      val _ = reset_certificate_source index_value
      fun time stage f =
        let
          val ordinal = Synchronized.change_result progress_counter
            (fn current => (current, current + 1))
          val _ = if Comma_Proof_Profile.enabled () andalso ordinal mod 4 = 0 then
            Comma_Proof_Profile.report
              (owner ^ " progress ordinal=" ^ Int.toString ordinal ^ " active=" ^ stage)
            else ()
          val started = if Comma_Proof_Profile.enabled () then SOME (Time.now ()) else NONE
          val _ = if Comma_Proof_Profile.enabled () then
            profile_certificate_source (stage ^ "-start") false else ()
          val attempt = Exn.capture (fn () =>
            Comma_Proof_Profile.trace_stage (Comma_Proof_Profile.enabled ())
              component_counter (fn current => (current, current + 1)) 256 owner stage f) ()
          val _ = if Comma_Proof_Profile.enabled () then
            (case attempt of Exn.Res _ =>
              profile_certificate_source (stage ^ "-complete") false | _ => ()) else ()
          val _ = (case (attempt, started) of
            (Exn.Res _, SOME start) =>
              let val elapsed = Time.toMilliseconds (Time.- (Time.now (), start))
              in if elapsed >= 100 then Comma_Proof_Profile.report
                (owner ^ " slow_component=" ^ stage ^ " elapsed_ms=" ^
                  LargeInt.toString elapsed) else () end
          | _ => ())
        in
          (case attempt of
          Exn.Res result => result
          | Exn.Exn failure =>
              (profile_certificate_source
                 (if Comma_Proof_Profile.enabled () then stage ^ "-failed" else stage) true;
               if Comma_Proof_Profile.enabled () then
                 Comma_Proof_Profile.report
                   (owner ^ " failed ordinal=" ^ Int.toString ordinal ^
                    " active=" ^ stage ^ " exception=" ^ General.exnMessage failure)
               else ();
               Exn.reraise failure))
        end
      val check_def = @{thm comma_semantic_b1_crt_construction_check_def}
        RS @{thm eq_reflection}
      val compact_def = @{thm comma_semantic_b1_crt_compact_occurrence_check_def}
        RS @{thm eq_reflection}
      val check_ct = Thm.cterm_of ctxt proposition
      val check_step = time "definition" (fn () => Conv.rewr_conv check_def check_ct)
      val compact_step = time "compact-definition" (fn () =>
        Conv.rewr_conv compact_def (Thm.rhs_of check_step))
      val body_ct = Thm.rhs_of compact_step
      val if_true = @{thm if_True} RS @{thm eq_reflection}
      fun expose_if ct =
        (case strip_comb (Thm.term_of ct) of
          (Const (if_name, _), [condition, _, _]) =>
            if if_name <> @{const_name If} then
              error "B1 construction guard is not an if expression"
            else
              let
                val condition_eq = Simplifier.rewrite evaluation_context
                  (Thm.cterm_of ctxt condition)
                val selected_condition = Thm.term_of (Thm.rhs_of condition_eq)
                val _ = if selected_condition aconv @{term True} then ()
                  else error "B1 construction index guard rejected its selected item"
                val expose = Comma_Semantic_B1_CRT_Operation_Conversion.argument_at
                  2 (Conv.rewr_conv condition_eq) ct
                val branch = Conv.rewr_conv if_true (Thm.rhs_of expose)
              in Thm.transitive expose branch end
        | _ => error "B1 constructed bound has no outer index guard")
      val guard_step = time "index-guard" (fn () => expose_if body_ct)
      val case_ct = Thm.rhs_of guard_step
      val case_term = Thm.term_of case_ct
      val case_arguments = snd (strip_comb case_term)
      val occurrence_term =
        (case rev case_arguments of
          scrutinee :: _ => scrutinee
        | [] => error "B1 construction bound has a malformed occurrence case")
      val occurrence_eq = time "occurrence-resolution" (fn () =>
        Simplifier.rewrite evaluation_context (Thm.cterm_of ctxt occurrence_term))
      val occurrence_value = Thm.term_of (Thm.rhs_of occurrence_eq)
      val _ = (case strip_comb occurrence_value of
        (Const (some_name, _), [_]) =>
          if some_name = @{const_name Some} then ()
          else error "B1 construction occurrence resolved to None"
      | _ => error "B1 construction occurrence did not resolve to Some")
      val occurrence_step = time "selected-occurrence" (fn () =>
        Comma_Semantic_B1_CRT_Operation_Conversion.argument_at
          0 (Conv.rewr_conv occurrence_eq) case_ct)
      val case_rule = Local_Defs.meta_rewrite_rule ctxt @{thm option.case(2)}
      val selected_case = time "occurrence-case" (fn () =>
        Conv.rewr_conv case_rule (Thm.rhs_of occurrence_step))
      val selected_beta = Thm.beta_conversion true (Thm.rhs_of selected_case)
      val let_rule = Local_Defs.meta_rewrite_rule ctxt @{thm Let_def}
      fun reduce_root_lets ct accumulated =
        (case strip_comb (Thm.term_of ct) of
          (Const (let_name, _), _) =>
            if let_name <> @{const_name Let} then (accumulated, ct)
            else
              let
                val opened = Conv.rewr_conv let_rule ct
                val beta = Thm.beta_conversion true (Thm.rhs_of opened)
                val next = Thm.rhs_of beta
              in reduce_root_lets next
                (Thm.transitive accumulated (Thm.transitive opened beta)) end
        | _ => (accumulated, ct))
      val let_step = time "selected-let-chain" (fn () =>
        let
          val identity = Thm.reflexive (Thm.rhs_of selected_beta)
        in reduce_root_lets (Thm.rhs_of selected_beta) identity end)
      val (lets_eq, body) = let_step
      val skeleton_eq = Thm.transitive guard_step
        (Thm.transitive occurrence_step
          (Thm.transitive selected_case (Thm.transitive selected_beta lets_eq)))
      val expanded = Thm.transitive check_step
        (Thm.transitive compact_step skeleton_eq)
      val body_term = Thm.term_of body
      fun conjuncts term =
        (case try (HOLogic.dest_bin @{const_name HOL.conj} @{typ bool}) term of
          SOME (left, right) => left :: conjuncts right
        | NONE => [term])
      val components = conjuncts body_term
      val _ = if null components then
          error "B1 compact construction body unexpectedly had no components" else ()
      fun prove_components [] =
            error "B1 compact construction body unexpectedly had no components"
        | prove_components [component] =
            time "compact-component-0" (fn () => prove_expression
              false construction_context component)
        | prove_components (component :: rest) =
            let
              val ordinal = length components - length rest - 1
              val head = time ("compact-component-" ^ Int.toString ordinal)
                (fn () => prove_expression false construction_context component)
              val tail = prove_components rest
            in @{thm conjI} OF [head, tail] end
      val body_proof = prove_components components
      val proposition_equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) expanded
      val result = Thm.equal_elim (Thm.symmetric proposition_equation) body_proof
      val _ = if Thm.prop_of result aconv
          HOLogic.mk_Trueprop proposition andalso Thm.nprems_of result = 0
        then profile_certificate_source "proof-complete" true
        else error "B1 staged construction proof changed its proposition"
    in result end
  fun standalone theorem =
    Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
      null (Thm.tpairs_of theorem)
  fun bounded_upt_rewrite context cterm =
    let
      val first = Simplifier.rewrite context cterm
      val residual = Thm.term_of (Thm.rhs_of first)
    in
      (case Comma_Semantic_B1_CRT_Operation_Conversion.small_closed_upt_context
          context residual of
        SOME bounded_context => Thm.transitive first
          (Simplifier.rewrite bounded_context (Thm.rhs_of first))
      | NONE => first)
    end
  fun beta_body proposition =
    (case proposition of
      Abs _ $ _ => true
    | _ => false)
  fun prove_beta_item_with_body ctxt prove_body proposition =
    let
      val proposition_ct = Thm.cterm_of ctxt proposition
      val beta = if beta_body proposition then
          Thm.beta_conversion false proposition_ct
        else Thm.reflexive proposition_ct
      val body = Thm.term_of (Thm.rhs_of beta)
      val body_proof = prove_body body
      val expected = HOLogic.mk_Trueprop body
      val _ = if Thm.prop_of body_proof aconv expected andalso standalone body_proof
        then () else error "B1 beta item prover returned a theorem for a different item"
      val proposition_eq = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) beta
      val result = Thm.equal_elim (Thm.symmetric proposition_eq) body_proof
      val _ = if Thm.prop_of result aconv HOLogic.mk_Trueprop proposition andalso
          standalone result
        then () else error "B1 beta item proof changed its exact proposition"
    in {theorem = result, body_theorem = body_proof, body = body} end
  fun prove_beta_item ctxt prove_body proposition =
    #theorem (prove_beta_item_with_body ctxt prove_body proposition)
  fun prove_indexed_list_all
      {ctxt, context, predicate, range, prove_selected, item_counter,
       successor_equation} =
    let
      (* Normalize the upper bound, then prove items by zero/Suc. *)
      val predicate_name =
        the_default "non-constant" (Comma_Selected_List_Conversion.head_name predicate)
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
      val upper_selected = Simplifier.rewrite context (Thm.cterm_of ctxt upper)
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt
      val upper_scalar = Simplifier.rewrite scalar_context (Thm.rhs_of upper_selected)
      val upper_equation = Comma_Selected_List_Conversion.validate_equation upper
        (Thm.transitive upper_selected upper_scalar)
      val (_, bound) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of upper_equation))
      val (predicate_label, declared_extent) = indexed_extent_contract predicate upper
      val _ = if indexed_extent_admitted bound declared_extent then ()
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
            (fn () => prove_beta_item ctxt prove_selected
              (predicate $ Comma_Semantic_B1_CRT_Operation_Conversion.natural_numeral index))
        in theorem end
      val prefix = Comma_Selected_List_Conversion.prove_indexed_list_all
        {ctxt = ctxt, predicate = predicate, bound = bound,
         prove_item = prove_item,
         zero_fact = @{thm comma_indexed_all_zero},
         step_fact = @{thm comma_indexed_all_Suc},
         successor_equation = successor_equation}
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

  fun check_helper_fixtures ctxt =
    let
      val _ = Comma_Proof_Profile.report "B1 construction helper fixtures start"
      val beta_prop = @{term "(\<lambda>x::nat. True \<and> x = 0) 0"}
      fun prove_body body = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop body)
        (fn {context, ...} => simp_tac
          (Comma_Entry_Arithmetic.natural_context context) 1)
      val beta_proof = prove_beta_item ctxt prove_body beta_prop
      val _ = if Thm.prop_of beta_proof aconv HOLogic.mk_Trueprop beta_prop andalso
          standalone beta_proof
        then () else error "B1 beta conjunction fixture returned the wrong theorem"
      val wrong_callback = Exn.capture (fn () =>
        prove_beta_item ctxt (fn _ => @{thm TrueI}) beta_prop) ()
      val _ = (case wrong_callback of
        Exn.Exn (ERROR message) => if message =
            "B1 beta item prover returned a theorem for a different item"
          then () else error message
      | Exn.Exn exn => Exn.reraise exn
      | Exn.Res _ => error "B1 beta item prover accepted a theorem for another item")
    in Comma_Proof_Profile.report "B1 construction helper fixtures complete" end

  fun check_evaluator_smoke {ctxt, context, counters, capped_nodes, shape} =
    let
      fun smoke proposition expected label =
        let
          val normalized = Simplifier.rewrite context
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
      val _ = smoke
        @{term "comma_semantic_b1_crt_lift_descriptor_period
            (comma_semantic_b1_crt_lift_descriptor.make 3 1 2 7) = 3 \<and>
          comma_semantic_b1_crt_lift_descriptor_slot
            (comma_semantic_b1_crt_lift_descriptor.make 3 1 2 7) = 1 \<and>
          comma_semantic_b1_crt_lift_descriptor_template_cid
            (comma_semantic_b1_crt_lift_descriptor.make 3 1 2 7) = 2 \<and>
          comma_semantic_b1_crt_lift_descriptor_net_shift
            (comma_semantic_b1_crt_lift_descriptor.make 3 1 2 7) = 7"}
        @{term True} "selected lift descriptor constructor fields"
      val _ = smoke
        @{term "comma_semantic_b1_crt_lift_columns_option []
          (comma_semantic_b1_crt_lift_descriptor.make 3 1 0 0) = None"}
        @{term True} "malformed lift descriptor rejected"
      val complementary_left = @{term
        "Comma_CRT_Node 0 [Comma_CRT_Bool True, Comma_CRT_Bool True,
          Comma_CRT_Bool False, Comma_CRT_Bool False]"}
      val complementary_right = @{term
        "Comma_CRT_Node 0 [Comma_CRT_Bool False, Comma_CRT_Bool False,
          Comma_CRT_Bool True, Comma_CRT_Bool True]"}
      val admitted_join = @{term "comma_crt_admitted (0::nat)"} $
        (@{term "comma_crt_apply Comma_CRT_Or"} $
          complementary_left $ complementary_right)
      val _ = smoke admitted_join @{term True} "admitted CRT apply result"
    in () end

  fun select_root_occurrence {ctxt, context, closed, validate_equation} cterm =
    let
      val request = Thm.term_of cterm
      val _ = if closed request then ()
        else error "B1 root occurrence selector request is not closed"
      val root_index =
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
      val _ = (case root_index of SOME _ => ()
        | NONE => error "B1 root occurrence selector requires a literal root in 0..45")
      val theorem = Simplifier.rewrite context cterm
      val checked = validate_equation request theorem
      val rhs = Thm.term_of (Thm.rhs_of checked)
      val _ = (case strip_comb rhs of
        (Const (name, _), [occurrence]) =>
          if name = @{const_name Some} andalso closed occurrence andalso
              fastype_of occurrence = @{typ comma_semantic_b1_crt_occurrence}
          then () else error "B1 root selector returned an invalid occurrence"
      | _ => error "B1 root selector did not return Some occurrence")
    in checked end

  (* Prove one TemplateCID's partition certificate from a memoized DAG of
     ordered CID states and kernel-certified per-CID cofactor transitions;
     then assemble the strengthened geometry theorem from exact row resolution.
     The state prover preserves duplicate CIDs and never enumerates phases. *)
  fun prove_template_geometry_certificate
      {ctxt: Proof.context, context: Proof.context, request: term,
       note_stage_time, prove_table_admission, prove_partition_checker} =
    let
      val (columns, templates, template_ids, cid) =
        (case strip_comb request of
          (Const (name, _), [columns, templates, template_ids, cid]) =>
            if name = @{const_name comma_semantic_b1_crt_template_geometry_certified}
              andalso columns aconv @{term comma_semantic_b1_crt_columns}
              andalso templates aconv @{term comma_semantic_b1_crt_templates}
              andalso template_ids aconv @{term comma_semantic_b1_crt_template_column_ids}
            then (columns, templates, template_ids, cid)
            else error "B1 template partition proof received a foreign catalogue"
        | _ => error "B1 template partition proof received a malformed request")
      val _ = (case try HOLogic.dest_number cid of
          SOME (typ, value) =>
            if typ = @{typ nat} andalso value >= 0 andalso
                value < maximum_source_extent then ()
            else error "B1 template partition proof CID exceeds its checked bound"
        | NONE => error "B1 template partition proof CID is not a numeral")
      val natT = @{typ nat}
      val boolT = @{typ bool}
      val columnT = @{typ comma_crt_column}
      val templatesT = fastype_of templates
      val rowT = (case templatesT of
          Type (name, [rowT]) =>
            if name = @{type_name list} then rowT
            else error "B1 template catalogue is not a list"
        | _ => error "B1 template catalogue has an invalid type")
      val nth = Const (@{const_name nth}, templatesT --> natT --> rowT)
      val row = nth $ templates $ cid
      val size = Const (@{const_name size}, templatesT --> natT) $ templates
      val less = Const (@{const_name less}, natT --> natT --> boolT)
      fun prove_true label proof_context proposition =
        let
          val expected = HOLogic.mk_Trueprop proposition
          val normalized = Simplifier.rewrite proof_context
            (Thm.cterm_of ctxt expected)
          val left = Thm.term_of (Thm.lhs_of normalized)
          val right = Thm.term_of (Thm.rhs_of normalized)
          val _ = if left aconv expected andalso right aconv @{prop True} andalso
              standalone normalized then ()
            else error
              ("B1 template geometry premise " ^ label ^
               " did not reduce to True; lhs=" ^
               Comma_Semantic_B1_Partition_Conversion.shape 5 left ^
               "; rhs=" ^
               Comma_Semantic_B1_Partition_Conversion.shape 5 right)
        in Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI} end
      fun timed_stage metric work =
        let
          val started = Time.now ()
          val theorem = work ()
          val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
          val _ = note_stage_time (metric, elapsed)
        in theorem end
      fun timed_prove_true metric label proposition =
        timed_stage metric (fn () => prove_true label context proposition)
      val template_bound = timed_prove_true "template_extent" "template extent"
        (less $ cid $ size)
      val idsT = fastype_of template_ids
      val ids_rowT = (case idsT of
          Type (name, [rowT]) =>
            if name = @{type_name list} then rowT
            else error "B1 template column-ID catalogue is not a list"
        | _ => error "B1 template column-ID catalogue has an invalid type")
      val ids_nth = Const (@{const_name nth}, idsT --> natT --> ids_rowT)
      val ids_row = ids_nth $ template_ids $ cid
      val ids_size = Const (@{const_name size}, idsT --> natT) $ template_ids
      val ids_bound = timed_prove_true "template_id_extent"
        "template column-ID extent" (less $ cid $ ids_size)
      val thy = Proof_Context.theory_of ctxt
      val resolve_name = @{const_name comma_semantic_b1_crt_column_ids_resolve}
      val resolve = Const (resolve_name, Sign.the_const_type thy resolve_name)
      val resolved = list_comb (resolve, [columns, ids_row, row])
      val resolved_fact = timed_prove_true "column_id_resolution"
        "column-ID resolution" resolved
      val table_admission = timed_stage "template_table_admission"
        prove_table_admission
      val partition_name =
        @{const_name comma_semantic_b1_crt_columns_partition_certified}
      val partition_certificate = Const
        (partition_name, Sign.the_const_type thy partition_name) $ row
      val partition_fact = timed_stage "partition_certificate" (fn () =>
        let
          val certificate_ct = Thm.cterm_of ctxt partition_certificate
          val definition = Local_Defs.meta_rewrite_rule ctxt
            @{thm comma_semantic_b1_crt_columns_partition_certified_def}
          val unfold = Conv.rewr_conv definition certificate_ct
          val (conjunction_and_admission, checker_ct) =
            Thm.dest_comb (Thm.rhs_of unfold)
          val (_, admission_ct) = Thm.dest_comb conjunction_and_admission
          val admission_predicate = @{term "comma_crt_admitted (0::nat)"}
          val admission_request = Const (@{const_name list_all},
            fastype_of admission_predicate --> HOLogic.listT columnT --> boolT) $
            admission_predicate $ row
          val _ = if Thm.term_of admission_ct aconv admission_request then ()
            else error "B1 template partition has another admission conjunct"
          val preserved_admission =
            @{thm comma_semantic_b1_crt_column_ids_resolve_preserves_list_all}
              OF [table_admission, resolved_fact]
          val resolved_map =
            @{thm comma_semantic_b1_crt_column_ids_resolve_map} OF [resolved_fact]
          val resolved_map_meta = resolved_map RS @{thm eq_reflection}
          val admission_function =
            Const (@{const_name list_all},
              fastype_of admission_predicate --> HOLogic.listT columnT --> boolT) $
              admission_predicate
          val admission_map_equation = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt admission_function)) resolved_map_meta
          val admission_proposition_equation = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) admission_map_equation
          val row_admission = Thm.equal_elim admission_proposition_equation preserved_admission
          val expected_admission = HOLogic.mk_Trueprop admission_request
          val _ = if Thm.prop_of row_admission aconv expected_admission andalso
              Thm.nprems_of row_admission = 0 andalso null (Thm.hyps_of row_admission) andalso
              null (Thm.tpairs_of row_admission)
            then () else error "B1 template row admission transport changed its exact request"
          val checker_equation = prove_partition_checker
            {context = context, checker_ct = checker_ct, ids_row = ids_row,
             row = row, resolved_fact = resolved_fact}
          val checker = Thm.term_of checker_ct
          val _ = if Thm.term_of (Thm.lhs_of checker_equation) aconv checker andalso
              Thm.term_of (Thm.rhs_of checker_equation) aconv @{term True} andalso
              standalone checker_equation
            then () else error "B1 template cofactor checker did not complete exactly"
          val checker_proposition_equation = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) checker_equation
          val checker_fact = Thm.equal_elim
            (Thm.symmetric checker_proposition_equation) @{thm TrueI}
          val conjunction_fact = @{thm conjI} OF [row_admission, checker_fact]
          val proposition_unfold = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) unfold
          val fact = Thm.equal_elim (Thm.symmetric proposition_unfold) conjunction_fact
          val expected = HOLogic.mk_Trueprop partition_certificate
          val _ = if Thm.prop_of fact aconv expected andalso standalone fact
            then () else error "B1 template partition certificate assembly changed its request"
        in fact end)
      val geometry_fact =
        @{thm comma_semantic_b1_crt_template_geometry_certified_from_facts}
          OF [template_bound, ids_bound, resolved_fact, partition_fact]
      val expected = HOLogic.mk_Trueprop request
      val _ = if Thm.prop_of geometry_fact aconv expected
        then () else error "B1 composed template geometry changed its exact request"
      val equation = geometry_fact RS @{thm eqTrueI} RS @{thm eq_reflection}
      val equation_left = Thm.term_of (Thm.lhs_of equation)
      val equation_right = Thm.term_of (Thm.rhs_of equation)
      val _ = if equation_left aconv request andalso
          equation_right aconv @{term True} andalso standalone equation
        then () else error "B1 composed template geometry is not an exact closed equation"
    in equation end
  fun convert_template_certificate
      {ctxt, context, request, cterm, note_stage_time,
       prove_table_admission, prove_partition_checker} =
    (case Term.head_of request of
      Const (name, _) =>
        if name = @{const_name comma_semantic_b1_crt_columns_partition_certified}
        then Comma_Semantic_B1_Partition_Conversion.rewrite_template_partition_certificate context cterm
        else prove_template_geometry_certificate
          {ctxt = ctxt, context = context, request = request,
           note_stage_time = note_stage_time,
           prove_table_admission = prove_table_admission,
           prove_partition_checker = prove_partition_checker}
    | _ => prove_template_geometry_certificate
        {ctxt = ctxt, context = context, request = request,
         note_stage_time = note_stage_time,
         prove_table_admission = prove_table_admission,
         prove_partition_checker = prove_partition_checker})

  val occurrence_cache_arithmetic_rules =
    @{thms comma_finite_period_fast_def comma_compiled_period_facts
      comma_core_primary_def comma_core_modulus_def comma_core_period_def
      comma_short_period_def comma_compiled_short_period_facts upt_rec_numeral}
  val occurrence_cache_generic_constants =
    [@{const_name comma_semantic_b1_crt_construction_check},
     @{const_name comma_semantic_b1_crt_compact_occurrence_check},
     @{const_name comma_semantic_b1_crt_template_mass_certified},
     @{const_name comma_semantic_b1_crt_used_lift_bindings_checked},
     @{const_name comma_semantic_b1_crt_template_geometry_certified},
     @{const_name comma_semantic_b1_crt_lift_geometry_certified},
     @{const_name comma_semantic_b1_crt_partition_cofactor_checked},
     @{const_name comma_semantic_b1_crt_lift_columns_option},
     @{const_name comma_semantic_b1_source_slot_action},
     @{const_name comma_decisive_sector_period},
     @{const_name comma_offset_orbit},
     @{const_name comma_semantic_b1_terminal_action_result},
     @{const_name comma_crt_equiv_check},
     @{const_name comma_crt_supported},
     @{const_name comma_crt_admitted},
     @{const_name comma_crt_apply},
     @{const_name comma_crt_apply_shifted},
     @{const_name comma_crt_group_rows},
     @{const_name comma_crt_group_column},
     @{const_name comma_crt_negate}] @
    occurrence_projection_roots
  val occurrence_cache_catalogue_constants =
    [@{const_name comma_semantic_b1_crt_occurrence_at_index},
     @{const_name comma_semantic_b1_crt_resolve_descriptor}]
  val occurrence_cache_patterns =
    [@{term "comma_semantic_b1_crt_construction_check index"},
     @{term "comma_semantic_b1_source_slot_action source slot"},
     @{term "comma_decisive_sector_period source"},
     @{term "comma_offset_orbit offset"},
     @{term "comma_semantic_b1_crt_column_ids_resolve columns ids values"},
     @{term "comma_semantic_b1_crt_columns_partition_certified row"},
     @{term "comma_semantic_b1_crt_partition_cofactor_checked levels columns"},
     @{term "comma_semantic_b1_crt_template_geometry_certified columns templates template_column_ids template_cid"},
     @{term "comma_semantic_b1_crt_lift_geometry_certified columns templates template_column_ids lift_column_ids lift_descriptors lift_cid"},
     @{term "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at occurrence_descriptors refs descriptors index"},
     @{term "comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at occurrence_descriptors templates source parent refs descriptors"},
     @{term "comma_semantic_b1_crt_lift_columns_option templates descriptor"},
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
  val occurrence_cache_catalogue_patterns =
    [@{term "length comma_semantic_b1_crt_sources"},
     @{term "length comma_semantic_b1_crt_sources \<le> 1024"}, @{term "length comma_semantic_b1_crt_templates \<le> 1024"},
     @{term "length comma_semantic_b1_crt_descriptors"},
     @{term "length comma_semantic_b1_crt_root_occurrence_indices"},
     @{term "length comma_semantic_b1_crt_lift_descriptors"},
     @{term "length comma_semantic_b1_crt_sources = length comma_semantic_b1_crt_descriptors"},
     @{term "length comma_semantic_b1_crt_lift_descriptors \<le> 28 * length comma_semantic_b1_crt_sources"},
     @{term "length comma_semantic_b1_crt_lift_refs = length comma_semantic_b1_crt_sources"},
     @{term "length comma_semantic_b1_crt_lift_refs"},
     @{term "comma_semantic_b1_crt_source_order_step index"},
     @{term "length comma_semantic_b1_crt_root_occurrence_indices = 46"},
     @{term "comma_semantic_b1_crt_construction_check index"},
     @{term "comma_semantic_b1_crt_lift_refs ! index"},
     @{term "comma_semantic_b1_crt_lift_descriptors ! index"}]
  val occurrence_cache_checker_simp_rules =
    @{thms comma_semantic_b1_crt_occurrence_data_checked_def
      comma_semantic_b1_crt_construction_check_def
      comma_semantic_b1_crt_compact_occurrence_check_def
      comma_semantic_b1_crt_template_geometry_certified_def
      comma_semantic_b1_crt_lift_geometry_certified_def
      comma_semantic_b1_crt_used_lift_bindings_checked_def
      comma_semantic_b1_crt_lift_binding_certified_def
      sort_key_simps insort_key.simps sorted_wrt.simps list.set less_eq_prod_simp
      insert_iff empty_iff
      comma_semantic_b1_crt_column_ids_resolve_list_all2
      comma_semantic_b1_crt_columns_def
      comma_semantic_b1_crt_column_count_def
      comma_semantic_b1_crt_columns_for_length
      comma_semantic_b1_crt_columns_for_nth
      comma_semantic_b1_crt_source_order_key_def
      comma_semantic_b1_crt_source_order_step_def
      comma_semantic_b1_crt_lift_descriptor_valid_def
      comma_semantic_b1_crt_lift_columns_option_def
      comma_semantic_b1_crt_source_periods_def
      comma_semantic_b1_crt_lift_ref_slot.simps
      comma_semantic_b1_crt_lift_ref_parent.simps
      comma_semantic_b1_crt_lift_ref_child_index.simps
      comma_semantic_b1_crt_lift_ref_cid.simps
      comma_semantic_b1_crt_lift_descriptor.select_convs
      comma_semantic_b1_crt_lift_descriptor.make_def
      comma_semantic_b1_terminal_action_result.simps
      comma_semantic_b1_source_slot_scope_def
      comma_crt_source_scope_column_def
      comma_crt_source_axis_column_def
      comma_near_terminal_width_j_def
      comma_source_continuation_action_of_packet.simps
      comma_source_continuation_base.simps comma_round_admitted.simps
      comma_semantic_b1_crt_occurrence.select_convs
      list_all_Nil_iff list_all_Cons_iff
      list_all2_Nil list_all2_Nil2 list_all2_Cons}
  val occurrence_cache_catalogue_simp_rules =
    @{thms comma_semantic_b1_crt_occurrence_at_index_def
      comma_semantic_b1_crt_root_occurrence_def
      comma_semantic_b1_crt_resolve_descriptor_def
      distinct.simps option.case list.case list.map length_map prod.case Let_def}
  fun operation_timing_report operation_times =
    String.concatWith " "
      (map (fn (name, (calls, elapsed)) =>
        Long_Name.base_name name ^ "_calls=" ^ Int.toString calls ^
        "_inclusive_ms=" ^ LargeInt.toString elapsed)
      (Symtab.dest operation_times))
end
