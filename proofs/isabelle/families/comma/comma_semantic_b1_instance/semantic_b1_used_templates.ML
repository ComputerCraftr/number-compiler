(* Certify the distinct used-template catalogue, then transport its exact
   theorem to the named occurrence catalogue. No source chooses a fresh
   arithmetic proof after this boundary. *)
structure Comma_Semantic_B1_Used_Templates =
struct
  (* Inputs have already been checked as closed natural numerals. Preserve
     first-seen proof order without a quadratic pairwise aconv scan. *)
  fun distinct_numerals entries =
    let
      fun add entry (seen, result) =
        if Termtab.defined seen entry then (seen, result)
        else (Termtab.update (entry, ()) seen, entry :: result)
    in rev (#2 (fold add entries (Termtab.empty, []))) end

  fun fold_exact_list_all ctxt pred elements facts =
    let
      val natT = @{typ nat}
      val list_all_function =
        @{term "list_all :: (nat => bool) => nat list => bool"} $ pred
      val predicate_ct = Thm.cterm_of ctxt list_all_function
      fun proposition_equation equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) equation
      val _ = if length elements = length facts then ()
        else error "B1 used-template list fold has mismatched item facts"
      val nil_ids = HOLogic.mk_list natT []
      val nil_equation = Conv.rewr_conv
        (@{thm list_all_Nil_iff} RS @{thm eq_reflection})
        (Thm.apply predicate_ct (Thm.cterm_of ctxt nil_ids))
      val nil_fact = Thm.equal_elim
        (Thm.symmetric (proposition_equation nil_equation)) @{thm TrueI}
      fun add (element, head_fact) (tail_ids, tail_fact) =
        let
          val ids = HOLogic.cons_const natT $ element $ tail_ids
          val equation = Conv.rewr_conv
            (@{thm list_all_Cons_iff} RS @{thm eq_reflection})
            (Thm.apply predicate_ct (Thm.cterm_of ctxt ids))
          val fact = Thm.equal_elim
            (Thm.symmetric (proposition_equation equation))
            (@{thm conjI} OF [head_fact, tail_fact])
        in (ids, fact) end
      val pairs = ListPair.zip (elements, facts)
      val (ids, fact) = fold_rev add pairs (nil_ids, nil_fact)
      val expected = HOLogic.mk_Trueprop (list_all_function $ ids)
      val _ = if Thm.prop_of fact aconv expected andalso
          Thm.nprems_of fact = 0 andalso null (Thm.hyps_of fact) andalso
          null (Thm.tpairs_of fact) then ()
        else error "B1 used-template list fold changed its exact theorem"
    in (ids, fact) end

  fun prove_owned_certificate ctxt dispatch expected_head label proposition =
    let
      val actual_head = (case Term.head_of proposition of
        Const (name, _) => SOME name
      | _ => NONE)
      val _ = if actual_head = SOME expected_head andalso
          fastype_of proposition = @{typ bool} andalso
          Comma_Selected_List_Conversion.closed proposition then ()
        else error ("B1 " ^ label ^ " request has a foreign owner")
      val request_ct = Thm.cterm_of ctxt proposition
      val theorem = (case dispatch request_ct of
          SOME fact => fact
        | NONE => error ("B1 " ^ label ^ " certificate was not completed"))
      val _ = if Thm.term_of (Thm.lhs_of theorem) aconv proposition andalso
          Thm.term_of (Thm.rhs_of theorem) aconv @{term True} andalso
          Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem) then ()
        else error ("B1 " ^ label ^ " owner changed its exact request")
      val proposition_equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) theorem
      val result = Thm.equal_elim
        (Thm.symmetric proposition_equation) @{thm TrueI}
      val _ = if Thm.prop_of result aconv HOLogic.mk_Trueprop proposition andalso
          Thm.nprems_of result = 0 andalso null (Thm.hyps_of result) andalso
          null (Thm.tpairs_of result) then ()
        else error ("B1 " ^ label ^ " fact changed its exact proposition")
    in result end

  fun make_lift_binding_rewrite ctxt lift_capacity lift_ids lift_descriptors
      templates_table template_ids actual_numeral selected_equation
      selected_numeral_equation selected_catalogue_equation =
    let
      val selected_rules = Unsynchronized.ref (Inttab.empty: thm list Inttab.table)
      val table_extents = Synchronized.var "semantic_b1_lift_table_extents"
        (Termtab.empty: (int * thm) Termtab.table)
      val map_congruence =
        Comma_Semantic_B1_Column_Lookup_Cache.weak_map_input_congruence
      val map_congruence_uses = Unsynchronized.ref 0
      val apply_rules =
        @{thms comma_crt_apply_def comma_crt_apply_from_def
          comma_crt_apply_shifted_def comma_crt_apply_shifted_from.simps
          comma_crt_source_scope_column_def comma_crt_source_axis_column_def
          comma_semantic_b1_crt_lift_columns_option_def
          comma_semantic_b1_crt_lift_descriptor_valid_def} @
        Comma_Semantic_B1_CRT_Operation_Conversion.apply_depth_simp_rules ctxt
      val admission_base_context = Comma_Entry_Arithmetic.natural_context ctxt
      val selected_lookup_ms = Unsynchronized.ref (0: LargeInt.int)
      val sterile_option_ms = Unsynchronized.ref (0: LargeInt.int)
      val active_apply_ms = Unsynchronized.ref (0: LargeInt.int)
      fun elapsed_ms started = Time.toMilliseconds (Time.- (Time.now (), started))
      (* LiftProofIDs share one theory and the same nonrecursive staging
         rules. Build this sterile base context once, then add the checked
         CID-specific equations only after admission. The exact catalogue,
         descriptor, and option equations remain mandatory for every CID. *)
      val sterile_base_context =
        (Comma_Entry_Arithmetic.natural_context ctxt addsimps
          @{thms list.map list.case prod.case if_True if_False Let_def})
        delsimps apply_rules
      fun table_extent_equation context table =
        let
          val extent_request = Const (@{const_name size},
            fastype_of table --> @{typ nat}) $ table
          fun admitted (extent, theorem) =
            let
              val lhs = Thm.term_of (Thm.lhs_of theorem)
              val rhs = Thm.term_of (Thm.rhs_of theorem)
            in
              if lhs aconv extent_request andalso null (Thm.prems_of theorem) andalso
                  null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
                  Comma_Selected_List_Conversion.closed rhs andalso
                  actual_numeral rhs = SOME extent then (extent, theorem)
              else error "B1 cached lift table extent lost its exact numeral authority"
            end
        in
          (case Termtab.lookup (Synchronized.value table_extents) extent_request of
            SOME result => admitted result
          | NONE =>
              let
                val (extent_equation, normalized_extent) =
                  selected_numeral_equation context extent_request
                val raw_rhs = Thm.term_of (Thm.rhs_of extent_equation)
                val normalized_rhs = Thm.term_of (Thm.rhs_of normalized_extent)
                val result =
                  (case actual_numeral normalized_rhs of
                    SOME extent => (extent, normalized_extent)
                  | NONE => error
                      ("B1 exact lift catalogue has a non-numeral table extent; " ^
                       "request=" ^ Syntax.string_of_term context extent_request ^
                       "; raw_rhs=" ^ Syntax.string_of_term context raw_rhs ^
                       "; normalized_rhs=" ^ Syntax.string_of_term context normalized_rhs))
                val selected = Synchronized.change_result table_extents
                  (fn cache =>
                    (case Termtab.lookup cache extent_request of
                      SOME existing => (existing, cache)
                    | NONE =>
                        if Termtab.size cache < 4 then
                          (result, Termtab.update (extent_request, result) cache)
                        else (result, cache)))
              in admitted selected end)
        end
      fun table_extent context table = #1 (table_extent_equation context table)
      fun admission_failure context lift_cid =
        if lift_cid >= lift_capacity then
          SOME ("CID exceeds cap: cid=" ^ Int.toString lift_cid ^
            " cap=" ^ Int.toString lift_capacity)
        else
          (case Inttab.lookup (!selected_rules) lift_cid of
            SOME _ => NONE
          | NONE =>
            let
              val selected_started = Time.now ()
              val (lift_id_extent, lift_id_extent_equation) =
                table_extent_equation context lift_ids
              val (descriptor_extent, descriptor_extent_equation) =
                table_extent_equation context lift_descriptors
            in
              if lift_cid >= lift_id_extent then
                SOME ("CID outside lift-ID table: cid=" ^ Int.toString lift_cid ^
                  " extent=" ^ Int.toString lift_id_extent)
              else if lift_cid >= descriptor_extent then
                SOME ("CID outside descriptor table: cid=" ^ Int.toString lift_cid ^
                  " extent=" ^ Int.toString descriptor_extent)
              else
                let
                  val descriptor_type = @{typ comma_semantic_b1_crt_lift_descriptor}
                  val descriptor_request = Const (@{const_name nth},
                    HOLogic.listT descriptor_type --> @{typ nat} --> descriptor_type) $
                    lift_descriptors $ HOLogic.mk_number @{typ nat} lift_cid
                  val descriptor_equation = selected_catalogue_equation context
                    @{thms list.sel nth_Cons' nth_Cons_0
                      comma_semantic_b1_crt_lift_descriptor.make_def}
                    descriptor_request
                  val descriptor = Thm.term_of (Thm.rhs_of descriptor_equation)
                  val validity_request = Const
                    (@{const_name comma_semantic_b1_crt_lift_descriptor_valid},
                      fastype_of templates_table --> descriptor_type --> @{typ bool}) $
                      templates_table $ descriptor
                  val validity_equation = selected_catalogue_equation context
                    @{thms comma_semantic_b1_crt_lift_descriptor_valid_def
                      comma_semantic_b1_crt_source_periods_def
                      comma_semantic_b1_crt_lift_descriptor.select_convs
                      comma_semantic_b1_crt_lift_descriptor.make_def} validity_request
                  val validity_rhs = Thm.term_of (Thm.rhs_of validity_equation)
                in
                  if not (validity_rhs aconv @{term True}) then
                    SOME ("descriptor validity did not reduce to True: cid=" ^
                      Int.toString lift_cid ^ " descriptor=" ^
                      Syntax.string_of_term context descriptor ^ " rhs=" ^
                      Syntax.string_of_term context validity_rhs)
                  else
                    let
                      val template_request = Const
                        (@{const_name comma_semantic_b1_crt_lift_descriptor_template_cid},
                          descriptor_type --> @{typ nat}) $ descriptor
                      val template_equation = selected_catalogue_equation context
                        @{thms comma_semantic_b1_crt_lift_descriptor.select_convs
                          comma_semantic_b1_crt_lift_descriptor.make_def} template_request
                      val template_rhs = Thm.term_of (Thm.rhs_of template_equation)
                    in
                      (case actual_numeral template_rhs of
                        NONE => SOME ("descriptor template CID is not a canonical natural: " ^
                          "lift_cid=" ^ Int.toString lift_cid ^ " rhs=" ^
                          Syntax.string_of_term context template_rhs)
                      | SOME template_cid =>
                          let
                            val template_extent = table_extent context templates_table
                            val template_id_extent = table_extent context template_ids
                          in
                            if template_cid >= template_extent then
                              SOME ("template CID outside template table: lift_cid=" ^
                                Int.toString lift_cid ^ " template_cid=" ^
                                Int.toString template_cid ^ " extent=" ^
                                Int.toString template_extent)
                            else if template_cid >= template_id_extent then
                              SOME ("template CID outside template-ID table: lift_cid=" ^
                                Int.toString lift_cid ^ " template_cid=" ^
                                Int.toString template_cid ^ " extent=" ^
                                Int.toString template_id_extent)
                            else
                              let
                                val natT = @{typ nat}
                                fun descriptor_field field =
                                  let
                                    val field_request = Const
                                      (field, descriptor_type --> natT) $ descriptor
                                  in
                                    selected_catalogue_equation context
                                      @{thms comma_semantic_b1_crt_lift_descriptor.select_convs
                                        comma_semantic_b1_crt_lift_descriptor.make_def}
                                      field_request
                                  end
                                val period_equation = descriptor_field
                                  @{const_name comma_semantic_b1_crt_lift_descriptor_period}
                                val slot_equation = descriptor_field
                                  @{const_name comma_semantic_b1_crt_lift_descriptor_slot}
                                val shift_equation = descriptor_field
                                  @{const_name comma_semantic_b1_crt_lift_descriptor_net_shift}
                                val ids_request = Const (@{const_name nth},
                                  fastype_of lift_ids --> natT --> HOLogic.listT natT) $
                                  lift_ids $ HOLogic.mk_number natT lift_cid
                                val ids_equation = selected_equation context ids_request
                                val template_row_request = Const (@{const_name nth},
                                  fastype_of templates_table --> natT -->
                                    HOLogic.listT @{typ comma_crt_column}) $
                                  templates_table $ HOLogic.mk_number natT template_cid
                                val template_row_equation =
                                  selected_equation context template_row_request
                                (* Select the concrete child row before asking
                                   the simplifier to cross the lift's map.
                                   Its function contains an Apply redex with a
                                   bound column; evaluating that lambda first
                                   creates open DAG probes for every binding.
                                   This exact option equation fixes the list
                                   input first, so the existing Apply owner
                                   sees only closed column applications. *)
                                val lifted_columns_request = Const
                                  (@{const_name comma_semantic_b1_crt_lift_columns_option},
                                    fastype_of templates_table --> descriptor_type -->
                                      Type (@{type_name option},
                                        [HOLogic.listT @{typ comma_crt_column}])) $
                                  templates_table $ descriptor
                                val staged_facts = [lift_id_extent_equation,
                                  descriptor_extent_equation, descriptor_equation,
                                  validity_equation, template_equation,
                                  period_equation, slot_equation, shift_equation,
                                  template_row_equation]
                                val _ = selected_lookup_ms :=
                                  !selected_lookup_ms + elapsed_ms selected_started
                                val sterile_context =
                                  (admission_base_context addsimps
                                    (staged_facts @ @{thms list.map})) delsimps apply_rules
                                (* Do not send the option root through the
                                   occurrence operation simproc while selecting
                                   its descriptor and row. The first pass is
                                   deliberately sterile: it has exact scalar,
                                   validity, and row facts, but no Apply
                                   procedures or equations. Consequently it
                                   reduces map over the selected literal row
                                   before any operation request can see an open
                                   lambda. The active pass then receives only
                                   closed per-column applications. *)
                                val sterile_started = Time.now ()
                                val lifted_columns_unfolded = Conv.rewr_conv
                                  (@{thm comma_semantic_b1_crt_lift_columns_option_def}
                                    RS @{thm eq_reflection})
                                  (Thm.cterm_of sterile_context
                                    lifted_columns_request)
                                val lifted_columns_specialized = Simplifier.rewrite
                                  sterile_context
                                  (Thm.rhs_of lifted_columns_unfolded)
                                val _ = sterile_option_ms :=
                                  !sterile_option_ms + elapsed_ms sterile_started
                                val specialized_rhs =
                                  Thm.term_of (Thm.rhs_of lifted_columns_specialized)
                                val _ = (case specialized_rhs of
                                  Const (@{const_name Some}, _) $ selected_row =>
                                    (case try HOLogic.dest_list selected_row of
                                      SOME columns =>
                                        if List.all Comma_Selected_List_Conversion.closed
                                            columns then ()
                                        else error
                                          "B1 sterile lift specialization left an open column"
                                    | NONE => error
                                        "B1 sterile specialization did not select a literal row")
                                | _ => error
                                    "B1 sterile lift specialization did not prove Some")
                                val active_started = Time.now ()
                                val active_context = fold Simplifier.add_cong
                                  [map_congruence] (context addsimps staged_facts)
                                val lifted_columns_completed = Simplifier.rewrite
                                  active_context (Thm.rhs_of lifted_columns_specialized)
                                val _ = active_apply_ms :=
                                  !active_apply_ms + elapsed_ms active_started
                                val lifted_columns_equation =
                                  Comma_Selected_List_Conversion.validate_equation
                                    lifted_columns_request
                                    (Thm.transitive lifted_columns_unfolded
                                      (Thm.transitive lifted_columns_specialized
                                        lifted_columns_completed))
                                val lifted_columns_rhs =
                                  Thm.term_of (Thm.rhs_of lifted_columns_equation)
                                val lifted_columns_fact =
                                  (case lifted_columns_rhs of
                                    Const (@{const_name Some}, _) $ lifted_columns =>
                                      if Comma_Selected_List_Conversion.closed lifted_columns
                                      then SOME lifted_columns_equation else NONE
                                  | _ => NONE)
                                val exact_lifted_columns_equation =
                                  (case lifted_columns_fact of
                                    SOME equation => equation
                                  | NONE => error
                                      "B1 admitted lift lacks its exact closed option result")
                                val facts = [lift_id_extent_equation,
                                  descriptor_extent_equation, descriptor_equation,
                                  validity_equation,
                                  template_equation, period_equation, slot_equation,
                                  shift_equation, ids_equation, template_row_equation,
                                  exact_lifted_columns_equation]
                                val _ = selected_rules :=
                                  Inttab.update (lift_cid, facts) (!selected_rules)
                              in NONE end
                          end)
                    end
                end
            end)
      fun rewrite_context context lift_cid =
        (case Inttab.lookup (!selected_rules) lift_cid of
          NONE => error "B1 LiftProofID lost its selected catalogue equations"
        | SOME facts =>
            (map_congruence_uses := !map_congruence_uses + 1;
             fold Simplifier.add_cong [map_congruence] (context addsimps facts)))
      fun specialization_context _ lift_cid =
        (case Inttab.lookup (!selected_rules) lift_cid of
          NONE => error "B1 LiftProofID lost its sterile specialization equations"
        | SOME facts => sterile_base_context addsimps facts)
      fun congruence_uses () = !map_congruence_uses
      fun stage_timings () =
        "lift_binding_selected_lookup_ms=" ^ LargeInt.toString (!selected_lookup_ms) ^
        " lift_binding_sterile_option_ms=" ^ LargeInt.toString (!sterile_option_ms) ^
        " lift_binding_active_apply_ms=" ^ LargeInt.toString (!active_apply_ms)
    in {admission_failure = admission_failure,
      rewrite_context = rewrite_context,
      specialization_context = specialization_context,
      congruence_uses = congruence_uses,
      stage_timings = stage_timings} end

  fun prove_used_lift_bindings_checked ctxt expression prove_body =
    let
      val _ = if expression aconv
          @{term comma_semantic_b1_crt_used_lift_bindings_checked} then ()
        else error "B1 used LiftProofID unfolding received another predicate"
      val definition =
        @{thm comma_semantic_b1_crt_used_lift_bindings_checked_def}
        RS @{thm eq_reflection}
      val unfolded = Conv.rewr_conv definition (Thm.cterm_of ctxt expression)
      val rhs = Thm.term_of (Thm.rhs_of unfolded)
      val rhs_fact = prove_body rhs
      val proposition_equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) unfolded
      val result = Thm.equal_elim
        (Thm.symmetric proposition_equation) rhs_fact
      val _ = if Thm.prop_of result aconv HOLogic.mk_Trueprop expression andalso
          Thm.nprems_of result = 0 andalso null (Thm.hyps_of result) andalso
          null (Thm.tpairs_of result) then ()
        else error "B1 used LiftProofID definition transport changed its theorem"
    in result end

  fun check_fold ctxt =
    let
      val predicate = @{term "(\<le>) (0::nat)"}
      val ids = [@{term "0::nat"}, @{term "1::nat"}]
      fun prove element = Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop (predicate $ element))
        (fn _ => simp_tac ctxt 1)
      val (folded_ids, _) = fold_exact_list_all ctxt predicate ids (map prove ids)
      val _ = if folded_ids aconv HOLogic.mk_list @{typ nat} ids then ()
        else error "B1 used-template early list-fold fixture changed its result"
    in Comma_Proof_Profile.report "B1 used-template load-time fold fixture checked" end

  fun literal_lift_cids maximum refs_table =
    let
      val refT = @{typ comma_semantic_b1_crt_lift_ref}
      val natT = @{typ nat}
      fun nat_value term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) =>
            if typ = natT andalso value >= 0 then value
            else error "B1 lift reference contains a non-natural field"
        | NONE => error "B1 lift reference contains a non-numeral field")
      fun project_ref reference =
        let
          val _ = if fastype_of reference = refT then ()
            else error "B1 lift reference has a foreign type"
          val (head, fields) = Term.strip_comb reference
          val _ = List.app (ignore o nat_value) fields
        in
          (case (head, fields) of
            (Const (name, _), [_, _]) =>
              if name = @{const_name Comma_B1_Lift_Terminal_Ref} then NONE
              else error "B1 lift reference has a noncanonical constructor"
          | (Const (name, _), [_, _, lift_cid]) =>
              if name = @{const_name Comma_B1_Lift_Goto_Ref} then
                let
                  val cid = nat_value lift_cid
                  val _ = if cid < maximum then ()
                    else error "B1 lift reference is outside the admitted catalogue"
                in SOME lift_cid end
              else error "B1 lift reference has a noncanonical constructor"
          | _ => error "B1 lift reference has a noncanonical constructor")
        end
      val rows = HOLogic.dest_list refs_table
      val refs = maps HOLogic.dest_list rows
    in map_filter project_ref refs end

  fun lift_projection_context ctxt extra_rules =
    put_simpset HOL_basic_ss ctxt addsimps
      (extra_rules @ @{thms list.map list.case concat.simps append.simps
        comma_semantic_b1_crt_lift_ref.case})

  fun certify_literal_lift_projection ctxt projection_context projection expected =
    let
      val equation = Simplifier.rewrite projection_context
        (Thm.cterm_of ctxt projection)
        |> Comma_Selected_List_Conversion.validate_equation projection
      val actual = Thm.term_of (Thm.rhs_of equation)
      val expected_term = HOLogic.mk_list @{typ nat} expected
      val _ = if actual aconv expected_term then ()
        else error "B1 LiftProofID closed projection disagrees with its literal refs"
    in equation end

  fun check_lift_projection_fixture ctxt =
    let
      val natT = @{typ nat}
      val refT = @{typ comma_semantic_b1_crt_lift_ref}
      fun nat n = HOLogic.mk_number natT n
      val terminal = Const (@{const_name Comma_B1_Lift_Terminal_Ref},
        natT --> natT --> refT) $ nat 0 $ nat 0
      val goto = Const (@{const_name Comma_B1_Lift_Goto_Ref},
        natT --> natT --> natT --> refT)
      val refs = HOLogic.mk_list refT
        [goto $ nat 0 $ nat 0 $ nat 0,
         terminal,
         goto $ nat 1 $ nat 0 $ nat 1,
         goto $ nat 2 $ nat 0 $ nat 2443,
         goto $ nat 3 $ nat 0 $ nat 1]
      val empty = HOLogic.mk_list refT []
      val table = HOLogic.mk_list (HOLogic.listT refT) [refs, empty]
      val maximum = Comma_Semantic_B1_Construction_Check.maximum_lift_catalog_extent
      val projected = literal_lift_cids maximum table
      val expected = map nat [0, 1, 2443, 1]
      val _ = if HOLogic.mk_list natT projected aconv HOLogic.mk_list natT expected then ()
        else error "B1 structural LiftProofID fixture changed its occurrences"
      val rejected = (literal_lift_cids 2443 table; false)
        handle ERROR _ => true
      val _ = if rejected then ()
        else error "B1 structural LiftProofID fixture accepted an out-of-range ID"
      val _ = if null (literal_lift_cids maximum (HOLogic.mk_list
          (HOLogic.listT refT) [])) then ()
        else error "B1 structural LiftProofID fixture changed empty-table behavior"
      val range = @{term "comma_semantic_b1_crt_used_lift_cids
        comma_semantic_b1_crt_lift_refs"}
      val used_definition = @{thm comma_semantic_b1_crt_used_lift_cids_def}
        RS @{thm eq_reflection}
      val unfolded = Conv.rewr_conv used_definition (Thm.cterm_of ctxt range)
      val (_, raw_projection_ct) = Thm.dest_comb (Thm.rhs_of unfolded)
      val refs_constant = @{term comma_semantic_b1_crt_lift_refs}
      val projection = Term.subst_atomic
        [(refs_constant, table)] (Thm.term_of raw_projection_ct)
      val _ = certify_literal_lift_projection ctxt
        (lift_projection_context ctxt []) projection projected
      val _ = Comma_Proof_Profile.report
        "B1 closed LiftProofID projection fixture checked"
    in () end

  fun prove ctxt context prove_item predicate range =
    let
      fun stage name = Comma_Proof_Profile.report
        ("B1 used-template stage=" ^ name)
      val _ = stage "start"
      val expected_range =
        @{term "remdups (map fst comma_semantic_b1_crt_descriptors)"}
      val expected_mass_predicate =
        @{term "comma_semantic_b1_crt_template_mass_certified
          comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_template_column_ids"}
      val _ = if range aconv expected_range andalso
          predicate aconv expected_mass_predicate then ()
        else error "B1 used-template proof has foreign catalogue authority"
      val extent = Simplifier.rewrite context
        (Thm.cterm_of ctxt @{term "length comma_semantic_b1_crt_descriptors"})
      val (_, bound) = HOLogic.dest_number (Thm.term_of (Thm.rhs_of extent))
      val _ = if bound >= 0 andalso bound <= 1024 then ()
        else error "B1 used-template catalogue exceeds its admitted extent"
      val _ = stage "mass-range-start"

      (* The descriptor rows carry large binding payloads.  Do not turn their
         projection into indexed lookups: nth conversion revisits every
         remaining payload for each CID.  Rewrite the exact owner definition
         once and fold map/fst over its certified list spine instead. *)
      val descriptor_definition = Local_Defs.meta_rewrite_rule ctxt
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_descriptors_def")
      val descriptor_table = @{term comma_semantic_b1_crt_descriptors}
      val descriptor_definition =
        Comma_Selected_List_Conversion.validate_equation descriptor_table
          descriptor_definition
      val descriptor_listT = fastype_of descriptor_table
      val descriptorT = (case descriptor_listT of
        Type (@{type_name list}, [entryT]) => entryT
      | _ => error "B1 occurrence descriptors are not a list")
      val descriptor_rhs = Thm.rhs_of descriptor_definition
      val descriptor_entries = HOLogic.dest_list (Thm.term_of descriptor_rhs)
      val _ = if length descriptor_entries = bound then ()
        else error "B1 descriptor definition disagrees with its checked extent"
      val _ = stage "mass-range-complete"
      val _ = stage "mass-descriptors-complete"

      val natT = @{typ nat}
      val nat_listT = HOLogic.listT natT
      val fst_const = Const (@{const_name fst}, descriptorT --> natT)
      val map_const = Const (@{const_name map},
        (descriptorT --> natT) --> descriptor_listT --> nat_listT)
      val map_function = map_const $ fst_const
      val map_function_ct = Thm.cterm_of ctxt map_function
      val fst_ct = Thm.cterm_of ctxt fst_const
      val nat_cons_ct = Thm.cterm_of ctxt
        (Const (@{const_name Cons}, natT --> nat_listT --> nat_listT))
      val map_nil = @{thm list.map(1)} RS @{thm eq_reflection}
      val map_cons = @{thm list.map(2)} RS @{thm eq_reflection}
      val fst_pair = @{thm fst_conv} RS @{thm eq_reflection}

      fun project_list source =
        let
          val map_request = Thm.apply map_function_ct source
          fun fold_spine current remaining =
            let
              val source_term = Thm.term_of current
            in
              (case source_term of
                Const (name, _) =>
                  if name = @{const_name Nil} andalso remaining = 0 then
                    Conv.rewr_conv map_nil (Thm.apply map_function_ct current)
                  else error "B1 descriptor projection ended at a malformed list"
              | _ =>
                  if remaining <= 0 then
                    error "B1 descriptor projection exceeded its checked extent"
                  else
                    let
                      val (cons_head, tail) = Thm.dest_comb current
                      val (cons_ct, head) = Thm.dest_comb cons_head
                      val _ = (case Thm.term_of cons_ct of
                        Const (name, _) => if name = @{const_name Cons} then ()
                          else error "B1 descriptor projection found a non-cons spine"
                      | _ => error "B1 descriptor projection found a malformed spine")
                      val (descriptor_first, _) =
                        (case try HOLogic.dest_prod (Thm.term_of head) of
                          SOME pair => pair
                        | NONE => error "B1 descriptor row is not a literal pair")
                      val _ = (case try HOLogic.dest_number descriptor_first of
                        SOME (typ, value) => if typ = natT andalso value >= 0 then ()
                          else error "B1 descriptor has a non-natural template ID"
                      | NONE => error "B1 descriptor template ID is not a numeral")
                      val head_request = Thm.apply fst_ct head
                      val head_equation = Conv.rewr_conv fst_pair head_request
                      val _ = if Thm.term_of (Thm.rhs_of head_equation) aconv
                          descriptor_first then ()
                        else error "B1 descriptor projection changed its template ID"
                      val tail_equation = fold_spine tail (remaining - 1)
                      val map_equation = Conv.rewr_conv map_cons
                        (Thm.apply map_function_ct current)
                      val cons_head_equation = Thm.combination
                        (Thm.reflexive nat_cons_ct) head_equation
                      val target_cons_equation = Thm.combination
                        cons_head_equation tail_equation
                    in Thm.transitive map_equation target_cons_equation end)
            end
          val result = fold_spine source (length descriptor_entries)
          val _ = if Thm.term_of (Thm.lhs_of result) aconv
              Thm.term_of map_request then ()
            else error "B1 structural descriptor projection changed its request"
        in result end

      val descriptor_map_equation = Thm.combination
        (Thm.reflexive map_function_ct) descriptor_definition
      val projected_literal = project_list descriptor_rhs
      val mapped = Thm.transitive descriptor_map_equation projected_literal
      val map_request = map_function $ descriptor_table
      val mapped = Comma_Selected_List_Conversion.validate_equation
        map_request mapped
      val _ = stage "mass-map-complete"

      val range_ct = Thm.cterm_of ctxt range
      val (remdups_ct, _) = Thm.dest_comb range_ct
      val remdups_map = Thm.combination (Thm.reflexive remdups_ct) mapped
      val range_equation = Comma_Selected_List_Conversion.validate_equation range
        remdups_map
      val literal_ids = Thm.term_of (Thm.rhs_of mapped)
      val entries = HOLogic.dest_list literal_ids
      fun numeral term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => typ = @{typ nat} andalso value >= 0
        | NONE => false)
      val _ = if length entries = bound andalso forall numeral entries then ()
        else error "B1 projected template IDs disagree with their checked extent"
      val unique_entries = distinct_numerals entries
      val _ = if length unique_entries <= bound then ()
        else error "B1 used-template catalogue exceeds its admitted extent"

      (* The remdups theorem transports the checked occurrence list to the
         published range.  Prove each distinct ID once, then reuse its exact
         theorem at each matching occurrence instead of proving a large set
         inclusion over the two closed lists. *)
      val list_all = Const (@{const_name list_all},
        @{typ "(nat => bool) => nat list => bool"}) $ predicate
      val remdups_all = Drule.infer_instantiate ctxt
        [( ("P", 0), Thm.cterm_of ctxt predicate),
         (("xs", 0), Thm.cterm_of ctxt literal_ids)]
        @{thm comma_semantic_b1_crt_list_all_remdups} RS @{thm eq_reflection}
      val remdups_all_prop = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) remdups_all
      val _ = stage "mass-deduplicate-complete"

      fun check_item entry =
        let
          val request = predicate $ entry
          val head = prove_item request
          val _ = if Thm.prop_of head aconv HOLogic.mk_Trueprop request andalso
              Thm.nprems_of head = 0 andalso null (Thm.hyps_of head) andalso
              null (Thm.tpairs_of head) then ()
            else error "B1 used-template item changed its exact theorem"
        in head end
      val _ = stage ("mass-items-start distinct=" ^ Int.toString
        (length unique_entries) ^ " occurrences=" ^ Int.toString (length entries))
      fun check_items [] _ facts = rev facts
        | check_items (entry :: rest) index facts =
            let
              val item_started = Time.now ()
              val _ = stage ("template-item-start index=" ^ Int.toString index ^
                " cid=" ^ Int.toString (#2 (HOLogic.dest_number entry)))
              val fact = check_item entry
              val elapsed = Time.toMilliseconds (Time.- (Time.now (), item_started))
              val _ = stage ("template-item-done index=" ^ Int.toString index ^
                " cid=" ^ Int.toString (#2 (HOLogic.dest_number entry)) ^
                " elapsed_ms=" ^ LargeInt.toString elapsed)
            in check_items rest (index + 1) (fact :: facts) end
      val item_facts = check_items unique_entries 0 []
      val _ = stage "distinct-item-proofs-complete"
      val _ = if length unique_entries = length item_facts then ()
        else error "B1 used-template distinct cache has mismatched proof count"
      val item_pairs = ListPair.zip (unique_entries, item_facts)
      val item_facts_by_id = fold (fn (entry, fact) => fn table =>
        if Termtab.defined table entry then
          error "B1 used-template distinct cache contains a duplicate ID"
        else Termtab.update (entry, fact) table) item_pairs Termtab.empty
      val occurrence_fact_lookups = Unsynchronized.ref 0
      val occurrence_fact_hits = Unsynchronized.ref 0
      fun occurrence_item entry =
        let
          val _ = occurrence_fact_lookups := !occurrence_fact_lookups + 1
          val request = predicate $ entry
          val fact = (case Termtab.lookup item_facts_by_id entry of
            SOME checked => checked
          | NONE => error "B1 used-template occurrence has no distinct item proof")
          val _ = if Thm.prop_of fact aconv HOLogic.mk_Trueprop request andalso
              Thm.nprems_of fact = 0 andalso null (Thm.hyps_of fact) andalso
              null (Thm.tpairs_of fact) then
            occurrence_fact_hits := !occurrence_fact_hits + 1
          else error "B1 used-template occurrence changed its cached item theorem"
        in fact end
      val occurrence_facts = map occurrence_item entries
      val (folded_occurrence_ids, literal_fact) =
        fold_exact_list_all ctxt predicate entries occurrence_facts
      val literal_request = HOLogic.mk_Trueprop (list_all $ literal_ids)
      val _ = if folded_occurrence_ids aconv literal_ids andalso
          Thm.prop_of literal_fact aconv literal_request andalso
          Thm.nprems_of literal_fact = 0 andalso null (Thm.hyps_of literal_fact)
          andalso null (Thm.tpairs_of literal_fact) then ()
        else error "B1 used-template occurrence fold changed its theorem"
      val _ = stage ("occurrence-list-transport-complete refs=" ^
        Int.toString (!occurrence_fact_lookups) ^ " hits=" ^
        Int.toString (!occurrence_fact_hits))
      val deduplicated_fact = Thm.equal_elim
        (Thm.symmetric remdups_all_prop) literal_fact
      val equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt list_all)) range_equation
      val proposition_equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) equation
      val result = Thm.equal_elim
        (Thm.symmetric proposition_equation) deduplicated_fact
      val _ = if Thm.prop_of result aconv HOLogic.mk_Trueprop (list_all $ range)
          andalso Thm.nprems_of result = 0 andalso null (Thm.hyps_of result)
          andalso null (Thm.tpairs_of result) then ()
        else error "B1 used-template publication changed its exact theorem"
      val _ = Comma_Proof_Profile.report
        ("B1 used-template publication distinct=" ^ Int.toString (length unique_entries) ^
          " occurrences=" ^ Int.toString bound)
    in result end

  (* The compact occurrence theorem separately authenticates each canonical
     LiftProofID used by a Goto reference.  Project that exact, fixed catalogue
     once; each resulting predicate is discharged by the occurrence cache's
     certificate-store owner, which validates the complete descriptor/source
     authority before a proof is admitted. *)
  fun prove_used_lift_bindings ctxt prove_item predicate range =
    let
      val expected_range =
        @{term "comma_semantic_b1_crt_used_lift_cids comma_semantic_b1_crt_lift_refs"}
      val expected_predicate =
        @{term "comma_semantic_b1_crt_lift_binding_certified
          comma_semantic_b1_crt_columns comma_semantic_b1_crt_templates
          comma_semantic_b1_crt_lift_column_ids comma_semantic_b1_crt_lift_descriptors"}
      val _ = if range aconv expected_range andalso
          predicate aconv expected_predicate then ()
        else error "B1 LiftProofID fold has foreign catalogue authority"
      val _ = Comma_Proof_Profile.report "B1 used LiftProofID stage=projection-start"
      (* Preserve the outer remdups as a symbolic list transform.  Rewriting it
         over the complete reference stream expands membership tests against
         each prior CID, which reintroduces quadratic publication work.  Open
         only the inner projection once, then use list_all/remdups transport
         after proving each distinct authenticated CID. *)
      val used_cids_definition =
        @{thm comma_semantic_b1_crt_used_lift_cids_def} RS @{thm eq_reflection}
      val unfolded = Conv.rewr_conv used_cids_definition
        (Thm.cterm_of ctxt range)
      val (remdups_function, raw_cids_ct) = Thm.dest_comb (Thm.rhs_of unfolded)
      val refs_definition =
        Proof_Context.get_thm ctxt "comma_semantic_b1_crt_lift_refs_def"
        |> Local_Defs.meta_rewrite_rule ctxt
        |> Comma_Selected_List_Conversion.validate_equation
          @{term comma_semantic_b1_crt_lift_refs}
      val projection_context = lift_projection_context ctxt [refs_definition]
      val maximum = Comma_Semantic_B1_Construction_Check.maximum_lift_catalog_extent
      val refs_table = Thm.term_of (Thm.rhs_of refs_definition)
      val candidate_ids = literal_lift_cids maximum refs_table
      val raw_projection = Thm.term_of raw_cids_ct
      val raw_cids_equation = certify_literal_lift_projection ctxt
        projection_context raw_projection candidate_ids
      val raw_ids = Thm.term_of (Thm.rhs_of raw_cids_equation)
      val _ = if Thm.term_of (Thm.lhs_of raw_cids_equation) aconv
          Thm.term_of raw_cids_ct then ()
        else error "B1 LiftProofID projection changed its exact source expression"
      val entries = HOLogic.dest_list raw_ids
      fun numeral term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => typ = @{typ nat} andalso value >= 0 andalso value < maximum
        | NONE => false)
      val _ = if length entries <= maximum then ()
        else error ("B1 used LiftProofID projection exceeds its admitted catalogue: " ^
          Int.toString (length entries) ^ " > " ^ Int.toString maximum)
      val _ = (case find_first (not o numeral) entries of
          NONE => ()
        | SOME entry => error ("B1 used LiftProofID projection contains a noncanonical ID: " ^
            ML_Syntax.print_term entry))
      val unique_entries = distinct_numerals entries
      val projected = Thm.transitive unfolded
        (Thm.combination (Thm.reflexive remdups_function) raw_cids_equation)
      val projected = Comma_Selected_List_Conversion.validate_equation range projected
      val _ = Comma_Proof_Profile.report
        ("B1 used LiftProofID stage=projection-complete occurrences=" ^
          Int.toString (length entries) ^ " unique=" ^ Int.toString (length unique_entries))
      fun check_item entry =
        let
          val request = predicate $ entry
          val theorem = prove_item request
          val _ = if Thm.prop_of theorem aconv HOLogic.mk_Trueprop request andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) then ()
            else error "B1 used LiftProofID item changed its exact theorem"
        in theorem end
      val unique_facts = map check_item unique_entries
      val facts_by_id = fold (fn (entry, fact) => fn facts =>
        if Termtab.defined facts entry then
          error "B1 LiftProofID distinct proof table contains a duplicate"
        else Termtab.update (entry, fact) facts)
        (ListPair.zip (unique_entries, unique_facts)) Termtab.empty
      val occurrence_lookups = Unsynchronized.ref 0
      val occurrence_hits = Unsynchronized.ref 0
      fun occurrence_fact entry =
        let
          val _ = occurrence_lookups := !occurrence_lookups + 1
          val request = predicate $ entry
          val fact = (case Termtab.lookup facts_by_id entry of
              SOME theorem => theorem
            | NONE => error "B1 LiftProofID occurrence has no distinct proof")
          val _ = if Thm.prop_of fact aconv HOLogic.mk_Trueprop request andalso
              Thm.nprems_of fact = 0 andalso null (Thm.hyps_of fact) andalso
              null (Thm.tpairs_of fact) then occurrence_hits := !occurrence_hits + 1
            else error "B1 LiftProofID occurrence changed its cached theorem"
        in fact end
      val occurrence_facts = map occurrence_fact entries
      val (folded_ids, literal_fact) =
        fold_exact_list_all ctxt predicate entries occurrence_facts
      val literal_request = HOLogic.mk_Trueprop
        (Const (@{const_name list_all}, fastype_of predicate --> fastype_of raw_ids -->
          @{typ bool}) $ predicate $ raw_ids)
      val _ = if folded_ids aconv raw_ids andalso
          Thm.prop_of literal_fact aconv literal_request andalso
          Thm.nprems_of literal_fact = 0 andalso null (Thm.hyps_of literal_fact) andalso
          null (Thm.tpairs_of literal_fact) then ()
        else error "B1 used LiftProofID fold changed its exact theorem"
      val remdups_all = Drule.infer_instantiate ctxt
        [(("P", 0), Thm.cterm_of ctxt predicate),
         (("xs", 0), Thm.cterm_of ctxt raw_ids)]
        @{thm comma_semantic_b1_crt_list_all_remdups} RS @{thm eq_reflection}
      val remdups_all_proposition = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) remdups_all
      val deduplicated_fact = Thm.equal_elim
        (Thm.symmetric remdups_all_proposition) literal_fact
      val list_all = Const (@{const_name list_all},
        fastype_of predicate --> fastype_of range --> @{typ bool}) $ predicate
      val list_equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt list_all)) projected
      val proposition_equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) list_equation
      val result = Thm.equal_elim (Thm.symmetric proposition_equation) deduplicated_fact
      val expected = HOLogic.mk_Trueprop (list_all $ range)
      val _ = if Thm.prop_of result aconv expected andalso
          Thm.nprems_of result = 0 andalso null (Thm.hyps_of result) andalso
          null (Thm.tpairs_of result) then ()
        else error "B1 used LiftProofID publication changed its exact theorem"
      val _ = Comma_Proof_Profile.report
        ("B1 used LiftProofID stage=certified unique=" ^ Int.toString (length unique_entries) ^
          " occurrences=" ^ Int.toString (!occurrence_lookups) ^
          " cached_item_hits=" ^ Int.toString (!occurrence_hits))
    in result end
end

val _ = Comma_Semantic_B1_Used_Templates.check_fold @{context}
val _ = Comma_Semantic_B1_Used_Templates.check_lift_projection_fixture @{context}
