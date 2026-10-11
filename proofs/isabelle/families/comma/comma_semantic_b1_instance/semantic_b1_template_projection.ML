(* Lazy selected-row projection from the bounded CID catalogue. *)
structure Comma_Semantic_B1_Template_Projection =
struct
  (* Select one published template row from its named CID catalogue.  Keep the
     table definition opaque globally: this simproc opens it only under a
     requested nth or length, then uses the generic map/nth theorem and the
     caller's existing selected-list context to materialize that one row. *)
  fun make {ctxt, selected_context, definition, natT, columnT, dagT,
      closed, dest_nat, argument_at} =
    let
      val thy = Proof_Context.theory_of ctxt
      val template_table_name = Sign.intern_const thy
        "comma_semantic_b1_crt_templates"
      val template_ids_name = Sign.intern_const thy
        "comma_semantic_b1_crt_template_column_ids"
      val dag_name = Sign.intern_const thy
        "comma_semantic_b1_crt_column_node_dag"
      val count_name = Sign.intern_const thy
        "comma_semantic_b1_crt_column_count"
      val idsT = HOLogic.listT (HOLogic.listT natT)
      val templatesT = HOLogic.listT (HOLogic.listT columnT)
      (* This memo is deliberately owned by the projection procedure closure:
         its theorems are valid only for this exact template definition and
         selected-list context.  Keep the same bound as the outer occurrence
         cache, and probe it before opening either catalogue definition.  A
         simproc context can be shared between parallel proof calls, so keep
         the memo and its counters in one synchronized state. *)
      val projection_capacity = 8192
      type projection_state =
        {facts: thm Termtab.table, lookups: int, hits: int, raced_reuses: int,
         publications: int, uncached: int, rejected: int, rows: int}
      fun projection_state facts lookups hits raced_reuses publications uncached
          rejected rows =
        {facts = facts, lookups = lookups, hits = hits,
         raced_reuses = raced_reuses, publications = publications,
         uncached = uncached, rejected = rejected, rows = rows}: projection_state
      val projection_memo = Synchronized.var "semantic_b1_template_projection"
        (projection_state Termtab.empty 0 0 0 0 0 0 0)

      fun reject_authority () =
        error "B1 lazy template projection has a foreign or malformed table definition"

      fun parse_authority theorem =
        let
          val equation = Local_Defs.meta_rewrite_rule ctxt theorem
          val table = Thm.term_of (Thm.lhs_of equation)
          val body = Thm.term_of (Thm.rhs_of equation)
          val clean = Thm.nprems_of equation = 0 andalso
            null (Thm.hyps_of equation) andalso null (Thm.tpairs_of equation) andalso
            null (Thm_Deps.all_oracles [equation]) andalso closed table andalso
            closed body
          fun inspect ids dag =
            if (case table of Const (name, _) => name = template_table_name
                | _ => false) andalso
              (case ids of Const (name, _) => name = template_ids_name
                | _ => false) andalso
              (case dag of Const (name, _) => name = dag_name | _ => false) andalso
              fastype_of table = templatesT andalso fastype_of ids = idsT andalso
              fastype_of dag = dagT andalso clean
            then {equation = equation, table = table, ids = ids, dag = dag}
            else reject_authority ()
        in
          (case strip_comb body of
            (Const (outer, _), [row_map, ids]) =>
              if outer <> @{const_name map} then reject_authority ()
              else
                (case strip_comb row_map of
                  (Const (inner, _), [column_function]) =>
                    if inner <> @{const_name map} then reject_authority ()
                    else
                      (case strip_comb column_function of
                        (Const (column_at_name, _), [dag]) =>
                          if column_at_name =
                              @{const_name comma_semantic_b1_crt_column_at}
                          then inspect ids dag
                          else reject_authority ()
                      | _ => reject_authority ())
                | _ => reject_authority ())
          | _ => reject_authority ())
        end

      val {equation = template_definition, table = template_table,
        ids = ids_table, dag = dag_constant} = parse_authority definition
      val count_definition = Local_Defs.meta_rewrite_rule ctxt
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_column_count_def")
      val count_left = Thm.term_of (Thm.lhs_of count_definition)
      val count_right = Thm.term_of (Thm.rhs_of count_definition)
      val _ = if (case count_left of Const (name, _) => name = count_name
                    | _ => false) andalso fastype_of count_left = natT andalso
          Thm.nprems_of count_definition = 0 andalso
          null (Thm.hyps_of count_definition) andalso
          null (Thm.tpairs_of count_definition) andalso
          null (Thm_Deps.all_oracles [count_definition]) andalso
          closed count_left andalso closed count_right
        then () else reject_authority ()
      val projection_column_count = dest_nat count_right
      val _ = if projection_column_count >= 2 then () else reject_authority ()
      val template_rowT = HOLogic.listT columnT
      val nth_const = Const (@{const_name nth},
        fastype_of template_table --> natT --> template_rowT)
      val length_const = Const (@{const_name size},
        fastype_of template_table --> natT)
      val template_nth_pattern = nth_const $ template_table $ Free ("index", natT)
      val template_length_pattern = length_const $ template_table
      val template_index_arithmetic = Comma_Entry_Arithmetic.natural_context ctxt

      fun canonical_nat term =
        (case try HOLogic.dest_number term of
          SOME (typ, number) => typ = natT andalso number >= 0
        | NONE => false)

      fun prove_true proposition =
        let
          val normalized = Simplifier.rewrite selected_context
            (Thm.cterm_of ctxt (HOLogic.mk_Trueprop proposition))
        in
          if Thm.term_of (Thm.rhs_of normalized) aconv @{prop True}
          then SOME (Thm.equal_elim (Thm.symmetric normalized) @{thm TrueI})
          else NONE
        end

      fun canonical_column entry =
        (case strip_comb entry of
          (Const (name, _), [dag, cid]) =>
            name = @{const_name comma_semantic_b1_crt_column_at} andalso
              dag aconv dag_constant andalso
              fastype_of entry = columnT andalso
              (case try HOLogic.dest_number cid of
                SOME (typ, number) => typ = natT andalso number >= 0 andalso
                  number < projection_column_count
              | NONE => false)
        | _ => false)

      fun validate_projection request theorem audit_oracles =
        let
          val row = Thm.term_of (Thm.rhs_of theorem)
          val entries = HOLogic.dest_list row
          val theorem_clean = Thm.term_of (Thm.lhs_of theorem) aconv request andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso
            (not audit_oracles orelse null (Thm_Deps.all_oracles [theorem]))
          val _ = if theorem_clean andalso forall canonical_column entries then ()
            else error "B1 lazy template projection changed selected row authority"
        in length entries end

      fun compose_cached_projection request canonical index_step canonical_theorem =
        let
          val theorem = Thm.transitive index_step canonical_theorem
          val clean = Thm.term_of (Thm.lhs_of canonical_theorem) aconv canonical andalso
            Thm.nprems_of canonical_theorem = 0 andalso
            null (Thm.hyps_of canonical_theorem) andalso
            null (Thm.tpairs_of canonical_theorem) andalso
            Thm.term_of (Thm.lhs_of theorem) aconv request andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso
            Thm.nprems_of index_step = 0 andalso null (Thm.hyps_of index_step) andalso
            null (Thm.tpairs_of index_step)
          val _ = if clean then () else error
            "B1 lazy template cache composition changed its exact request"
        in theorem end

      fun lookup_projection request =
        Synchronized.change_result projection_memo (fn state =>
          let
            val found = Termtab.lookup (#facts state) request
            val next = projection_state (#facts state) (#lookups state + 1)
              (#hits state + (case found of SOME _ => 1 | NONE => 0))
              (#raced_reuses state) (#publications state) (#uncached state)
              (#rejected state) (#rows state)
          in (found, next) end)

      (* Conversion runs outside the lock.  If another proof call publishes
         this exact request meanwhile, return its checked theorem and count a
         race reuse separately from a lookup hit.  Otherwise publish atomically
         under the shared capacity. *)
      fun publish_projection request theorem cells =
        Synchronized.change_result projection_memo (fn state =>
          (case Termtab.lookup (#facts state) request of
            SOME existing =>
              (existing, projection_state (#facts state) (#lookups state)
                (#hits state) (#raced_reuses state + 1) (#publications state)
                (#uncached state) (#rejected state) (#rows state + cells))
          | NONE =>
              if Termtab.size (#facts state) < projection_capacity then
                (theorem, projection_state
                  (Termtab.update (request, theorem) (#facts state))
                  (#lookups state) (#hits state) (#raced_reuses state)
                  (#publications state + 1) (#uncached state) (#rejected state)
                  (#rows state + cells))
              else
                (theorem, projection_state (#facts state) (#lookups state)
                  (#hits state) (#raced_reuses state) (#publications state)
                  (#uncached state + 1) (#rejected state) (#rows state + cells))))

      fun reject_projection () =
        Synchronized.change projection_memo (fn state =>
          projection_state (#facts state) (#lookups state) (#hits state)
            (#raced_reuses state) (#publications state) (#uncached state)
            (#rejected state + 1) (#rows state))

      fun normalize_template_index request cterm index =
        let
          val index_cterm = Thm.cterm_of ctxt index
          (* Canonical literal indices are already normalized and should not
             rebuild or run either simplifier.  For a closed expression,
             select descriptor/table expressions first while the bounded
             sibling-list simprocs are available, then normalize its natural
             arithmetic. *)
          val index_eq = if canonical_nat index then Thm.reflexive index_cterm
            else
              let
                val overloaded = Axclass.overload_conv ctxt index_cterm
                val selected = Simplifier.rewrite selected_context (Thm.rhs_of overloaded)
                val arithmetic = Simplifier.rewrite template_index_arithmetic
                  (Thm.rhs_of selected)
                val arithmetic_term = Thm.term_of (Thm.rhs_of arithmetic)
                val canonical = if canonical_nat arithmetic_term
                  then Thm.reflexive (Thm.rhs_of arithmetic)
                  else Axclass.overload_conv ctxt (Thm.rhs_of arithmetic)
              in Thm.transitive overloaded
                (Thm.transitive selected (Thm.transitive arithmetic canonical)) end
          val index' = Thm.term_of (Thm.rhs_of index_eq)
        in
          (case try HOLogic.dest_number index' of
            SOME (typ, number) =>
              if typ <> natT orelse number < 0 then NONE else
              let
                val index_step = argument_at 0 (Conv.rewr_conv index_eq) cterm
                val canonical_cterm = Thm.rhs_of index_step
                val canonical = Thm.term_of canonical_cterm
                val expected = nth_const $ template_table $ index'
              in
                if canonical aconv expected andalso Thm.term_of (Thm.lhs_of index_step)
                    aconv request
                then SOME (index', canonical, canonical_cterm, index_step)
                else NONE
              end
          | _ => NONE)
        end

      fun compute_template_row canonical canonical_cterm index =
        let
          val definition_step = argument_at 1
            (Conv.rewr_conv template_definition) canonical_cterm
          val bound = Const (@{const_name less}, natT --> natT --> @{typ bool}) $
            index $ (Const (@{const_name size}, fastype_of ids_table --> natT) $
              ids_table)
          val map_rule = Drule.infer_instantiate ctxt
            [(("dag", 0), Thm.cterm_of ctxt dag_constant),
             (("ids", 0), Thm.cterm_of ctxt ids_table),
             (("index", 0), Thm.cterm_of ctxt index)]
            @{thm comma_semantic_b1_crt_column_templates_nth}
        in
          (case prove_true bound of
            NONE => NONE
          | SOME bound_proof =>
              let
                val bridge = Thm.implies_elim map_rule bound_proof
                  RS @{thm eq_reflection}
                val bridge_step = Conv.rewr_conv bridge (Thm.rhs_of definition_step)
                val selected_row = Simplifier.rewrite selected_context
                  (Thm.rhs_of bridge_step)
                val theorem = Thm.transitive definition_step
                  (Thm.transitive bridge_step selected_row)
                val cells = validate_projection canonical theorem true
              in SOME (theorem, cells) end)
        end

      fun project_template cterm =
        let val request = Thm.term_of cterm in
          if not (closed request) then NONE
          else
            (case strip_comb request of
              (Const (name, _), [table, index]) =>
                if name <> @{const_name nth} orelse not (table aconv template_table)
                then NONE
                else
                  (case normalize_template_index request cterm index of
                    NONE => (reject_projection (); NONE)
                  | SOME (index', canonical, canonical_cterm, index_step) =>
                  (case lookup_projection canonical of
                    SOME theorem =>
                      SOME (compose_cached_projection request canonical index_step theorem)
                  | NONE =>
                      (case compute_template_row canonical canonical_cterm index' of
                        NONE => (reject_projection (); NONE)
                      | SOME (theorem, cells) =>
                          let
                            val cached = publish_projection canonical theorem cells
                            val composed = compose_cached_projection request canonical
                              index_step cached
                          in SOME composed end)))
              | (Const (name, _), [table]) =>
                  if name <> @{const_name size} orelse
                      not (table aconv template_table)
                  then NONE
                  else
                    let
                      val definition_step = argument_at 0
                        (Conv.rewr_conv template_definition) cterm
                      val reduced = Simplifier.rewrite selected_context
                        (Thm.rhs_of definition_step)
                    in SOME (Thm.transitive definition_step reduced) end
              | _ => NONE)
        end

      val procedure = Simplifier.make_simproc ctxt
        {name = "semantic_b1_selected_template_projection",
         kind = Simplifier.Congproc false,
         lhss = [Comma_Selected_List_Conversion.schematize template_nth_pattern,
           Comma_Selected_List_Conversion.schematize template_length_pattern],
         proc = fn _ => fn _ => project_template, identifier = []}
      val post_procedure = Simplifier.make_simproc ctxt
        {name = "semantic_b1_selected_template_projection_after_operands",
         kind = Simplifier.Simproc,
         lhss = [Comma_Selected_List_Conversion.schematize template_nth_pattern,
           Comma_Selected_List_Conversion.schematize template_length_pattern],
         proc = fn _ => fn _ => project_template, identifier = []}
      val projection_context = fold Simplifier.add_proc
        [procedure, post_procedure] selected_context
      fun check_fixtures () =
        let
          val template_zero = nth_const $ template_table $ HOLogic.mk_number natT 0
          val template_zero_cterm = Thm.cterm_of ctxt template_zero
          val template_zero_result = Simplifier.rewrite projection_context
            template_zero_cterm
          val template_zero_row = Thm.term_of (Thm.rhs_of template_zero_result)
          val _ = if not (template_zero_row aconv template_zero) andalso
              forall canonical_column (HOLogic.dest_list template_zero_row)
            then () else error "B1 lazy template selector failed its first-row fixture"
          val out_of_range_column =
            Const (@{const_name comma_semantic_b1_crt_column_at},
              dagT --> natT --> columnT) $ dag_constant $
              HOLogic.mk_number natT projection_column_count
          val _ = if not (canonical_column out_of_range_column) then ()
            else error "B1 lazy template projection accepted an out-of-range CID"
          val hits_before_replay = #hits (Synchronized.value projection_memo)
          val replayed_zero = Simplifier.rewrite projection_context template_zero_cterm
          val _ = if Thm.term_of (Thm.rhs_of replayed_zero) aconv template_zero_row andalso
              #hits (Synchronized.value projection_memo) = hits_before_replay + 1
            then () else error
              "B1 lazy template projection did not reuse its exact row theorem"
          val successor_index = Const (@{const_name Suc}, natT --> natT) $
            HOLogic.mk_number natT 0
          val successor_request = nth_const $ template_table $ successor_index
          val rows_before_successor = #rows (Synchronized.value projection_memo)
          val successor_theorem = (case project_template
              (Thm.cterm_of ctxt successor_request) of
            SOME theorem => theorem
          | NONE => error "B1 successor-form template index was not normalized")
          val successor_row = Thm.term_of (Thm.rhs_of successor_theorem)
          val _ = if Thm.term_of (Thm.lhs_of successor_theorem) aconv successor_request andalso
              not (successor_row aconv successor_request) andalso
              forall canonical_column (HOLogic.dest_list successor_row) andalso
              Thm.nprems_of successor_theorem = 0 andalso
              null (Thm.hyps_of successor_theorem) andalso
              null (Thm.tpairs_of successor_theorem) andalso
              null (Thm_Deps.all_oracles [successor_theorem]) andalso
              #rows (Synchronized.value projection_memo) >= rows_before_successor
            then () else error
              "B1 successor-form projection changed its exact request or row authority"
          val numeral_one_request = nth_const $ template_table $ HOLogic.mk_number natT 1
          val hits_before_numeral_alias = #hits (Synchronized.value projection_memo)
          val rows_before_numeral_alias = #rows (Synchronized.value projection_memo)
          val numeral_alias_theorem = (case project_template
              (Thm.cterm_of ctxt numeral_one_request) of
            SOME theorem => theorem
          | NONE => error "B1 canonical numeral template alias was not admitted")
          val _ = if Thm.term_of (Thm.lhs_of numeral_alias_theorem) aconv numeral_one_request andalso
              Thm.term_of (Thm.rhs_of numeral_alias_theorem) aconv successor_row andalso
              #hits (Synchronized.value projection_memo) = hits_before_numeral_alias + 1 andalso
              #rows (Synchronized.value projection_memo) = rows_before_numeral_alias
            then () else error
              "B1 equivalent successor and numeral indices missed canonical row reuse"
          val descriptor_definition = Local_Defs.meta_rewrite_rule ctxt
            (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_descriptors_def")
          val descriptor_table = Thm.term_of (Thm.lhs_of descriptor_definition)
          val descriptorT = (case fastype_of descriptor_table of
            Type (@{type_name list}, [entryT]) => entryT
          | _ => error "B1 occurrence descriptors are not a list")
          val descriptor_nth = Const (@{const_name nth},
            fastype_of descriptor_table --> natT --> descriptorT)
          val descriptor_zero = descriptor_nth $ descriptor_table $
            HOLogic.mk_number natT 0
          val descriptor_index = Const (@{const_name fst}, descriptorT --> natT) $
            descriptor_zero
          val normalized_descriptor_index = Thm.term_of (Thm.rhs_of
            (Simplifier.rewrite selected_context
              (Thm.cterm_of ctxt descriptor_index)))
          val (descriptor_indexT, descriptor_index_value) =
            (case try HOLogic.dest_number normalized_descriptor_index of
              SOME pair => pair
            | NONE => error "B1 descriptor index did not normalize to a numeral")
          val descriptor_bound = Const (@{const_name less},
            natT --> natT --> @{typ bool}) $ normalized_descriptor_index $
            (Const (@{const_name size}, fastype_of ids_table --> natT) $ ids_table)
          val _ = if descriptor_indexT = natT andalso descriptor_index_value >= 0 andalso
              is_some (prove_true descriptor_bound) then ()
            else error "B1 descriptor selected a template outside the checked catalogue"
          val canonical_descriptor_row = nth_const $ template_table $
            normalized_descriptor_index
          val canonical_descriptor_result = Simplifier.rewrite projection_context
            (Thm.cterm_of ctxt canonical_descriptor_row)
          val canonical_descriptor_value = Thm.term_of
            (Thm.rhs_of canonical_descriptor_result)
          val rows_before_descriptor_alias = #rows (Synchronized.value projection_memo)
          val hits_before_descriptor_alias = #hits (Synchronized.value projection_memo)
          val descriptor_alias_request = nth_const $ template_table $ descriptor_index
          val descriptor_alias_result = project_template
            (Thm.cterm_of ctxt descriptor_alias_request)
          val _ = (case descriptor_alias_result of
              SOME theorem =>
                if Thm.term_of (Thm.lhs_of theorem) aconv descriptor_alias_request andalso
                   Thm.term_of (Thm.rhs_of theorem) aconv canonical_descriptor_value andalso
                   #hits (Synchronized.value projection_memo) =
                     hits_before_descriptor_alias + 1 andalso
                   #rows (Synchronized.value projection_memo) =
                     rows_before_descriptor_alias
                then () else error
                  "B1 descriptor alias missed canonical template theorem reuse"
            | NONE => error "B1 descriptor alias was not admitted by template projection")
          val repeated_zero = Simplifier.rewrite projection_context
            (Thm.rhs_of template_zero_result)
          val _ = if Thm.is_reflexive repeated_zero then ()
            else error "B1 lazy template projection did not cancel on its selected row"
          val foreign_definition = Proof_Context.get_thm ctxt
            "comma_semantic_b1_crt_sources_def"
          val foreign_check = Exn.capture
            (fn () => parse_authority foreign_definition) ()
          val _ = (case foreign_check of
              Exn.Exn (ERROR message) => if message =
                  "B1 lazy template projection has a foreign or malformed table definition"
                then () else error "B1 lazy template foreign-definition fixture changed"
            | Exn.Exn exn => Exn.reraise exn
            | Exn.Res _ => error "B1 lazy template projection accepted a foreign table")
          val outside = nth_const $ template_table $ HOLogic.mk_number natT 999999
          val outside_result = Simplifier.rewrite projection_context
            (Thm.cterm_of ctxt outside)
          val _ = if Thm.is_reflexive outside_result then ()
            else error "B1 lazy template projection accepted an out-of-range row"
        in () end
      fun stats () =
        let val state = Synchronized.value projection_memo
        in " template_projection_lookups=" ^ Int.toString (#lookups state) ^
          " template_projection_hits=" ^ Int.toString (#hits state) ^
          " template_projection_race_reuses=" ^
            Int.toString (#raced_reuses state) ^
          " template_projection_publications=" ^ Int.toString (#publications state) ^
          " template_projection_uncached=" ^ Int.toString (#uncached state) ^
          " template_projection_rejected=" ^ Int.toString (#rejected state) ^
          " template_projection_retained=" ^
            Int.toString (Termtab.size (#facts state)) ^
          " template_projection_row_cells=" ^ Int.toString (#rows state)
        end
    in {procedure = procedure, post_procedure = post_procedure,
      stats = stats, check_fixtures = check_fixtures} end

end
