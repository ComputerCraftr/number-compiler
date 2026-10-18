(* Run-local, theorem-backed B1 certificate store. *)
(* The bounded, run-local theorem store is loaded after the construction checker so it can reuse its checked selection helpers. *)
structure Comma_Semantic_B1_Certificate_Store =
struct
  (* Allocated once per occurrence-check tactic invocation; the evaluator
     consumes this closure synchronously and never shares it across workers. *)
  fun make_certificate_store
      {ctxt, template_head, lift_head, slot_head, slot_valid_head, binding_head,
      action_row_head, slot_valid_actions_head, binding_actions_head, action_table,
      columns, templates_table, template_ids, lift_ids, sources_table,
       occurrence_at, occurrence_descriptors, lift_descriptors, lift_refs_table} =
    let
      (* These bounds come from the checked source and period extents: at most
         1024 templates/sources and 28 lift/slot entries per source.  Bindings
         are scoped to one source and have their own fixed retention bound. *)
      val template_capacity = 1024
      val lift_capacity = 1024 * 28
      val slots_per_source_capacity = 28
      val bindings_per_source_capacity = 32768
      val action_capacity = 1024 * 28
      val store_theory = Proof_Context.theory_of ctxt
      (* The occurrence evaluator calls these callbacks synchronously. Guard
         thread ownership instead of locking: Simplifier simprocs re-enter. *)
      val store_owner_thread = Isabelle_Thread.self ()
      val store_generation = serial ()
      val lift_binding_head =
        @{const_name comma_semantic_b1_crt_lift_binding_certified}
      val catalog_terms = [columns, templates_table, template_ids, lift_ids,
        sources_table, occurrence_at, occurrence_descriptors, lift_refs_table,
        lift_descriptors, action_table]
      val lift_authority = [columns, templates_table, template_ids,
        lift_ids, lift_descriptors]
      val lift_binding_authority = [columns, templates_table, lift_ids,
        lift_descriptors]
      val _ = if List.all Comma_Selected_List_Conversion.closed catalog_terms
        then () else error "B1 certificate store requires one closed catalogue"
      (* Geometry identities are the published CIDs.  These tables live only
         inside this store instance, whose catalogue terms and theory are
         fixed by the constructor arguments above.  Occurrence certificates
         below remain keyed by their full closed requests. *)
      val templates = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val lifts = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      (* LiftProofIDs are pinned separately from the temporary exact-term LRU.
         The theorem's full catalogue authority is checked on capture and each
         lookup; the CID is only an index inside this closed store instance. *)
      val lift_bindings = Unsynchronized.ref (Inttab.empty: thm Inttab.table)
      val slots = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val slot_validity = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val bindings = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val source_actions = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val action_rows = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val template_captured = Unsynchronized.ref 0
      val template_reused = Unsynchronized.ref 0
      val lift_captured = Unsynchronized.ref 0
      val lift_reused = Unsynchronized.ref 0
      val lift_binding_captured = Unsynchronized.ref 0
      val lift_binding_reused = Unsynchronized.ref 0
      val lift_binding_recursive_evaluations = Unsynchronized.ref 0
      val lift_binding_admission_ms = Unsynchronized.ref (0: LargeInt.int)
      val lift_binding_specialization_ms = Unsynchronized.ref (0: LargeInt.int)
      val lift_binding_resolution_ms = Unsynchronized.ref (0: LargeInt.int)
      fun timed total action =
        let
          val started = Time.now ()
          val result = Exn.capture action ()
          val elapsed = Time.toMilliseconds (Time.- (Time.now (), started))
          val _ = total := !total + elapsed
        in Exn.release result end
      val lift_geometry_from_binding = Unsynchronized.ref 0
      val slot_captured = Unsynchronized.ref 0
      val slot_reused = Unsynchronized.ref 0
      val slot_valid_captured = Unsynchronized.ref 0
      val slot_valid_reused = Unsynchronized.ref 0
      val binding_captured = Unsynchronized.ref 0
      val binding_reused = Unsynchronized.ref 0
      val source_action_captured = Unsynchronized.ref 0
      val source_action_reused = Unsynchronized.ref 0
      val action_row_captured = Unsynchronized.ref 0
      val action_row_reused = Unsynchronized.ref 0
      val active_index = Unsynchronized.ref (NONE: int option)
      val source_construction_active = Unsynchronized.ref false
      val current_source_metrics = Array.array (4, 0)
      fun bump_current_source_metric metric =
        if !source_construction_active then Array.update (current_source_metrics, metric,
          Array.sub (current_source_metrics, metric) + 1) else ()
      fun track_current_source_counter counter metric action =
        let val prior = !counter val result = action () in
          (if !counter > prior then bump_current_source_metric metric else (); result) end
      val active_refs = Unsynchronized.ref (NONE: term option)
      val active_refs_equation = Unsynchronized.ref (NONE: thm option)
      val active_source = Unsynchronized.ref (NONE: term option)
      val active_parent = Unsynchronized.ref (NONE: term option)
      val active_source_equation = Unsynchronized.ref (NONE: thm option)
      val active_parent_equation = Unsynchronized.ref (NONE: thm option)
      val selected_equation_capacity = 8192
      val selected_equations = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val selected_equation_captured = Unsynchronized.ref 0
      val selected_equation_reused = Unsynchronized.ref 0
      val selected_oracle_checks = Unsynchronized.ref 0
      val selected_oracle_elapsed = Unsynchronized.ref Time.zeroTime
      val captured_oracle_checks = Unsynchronized.ref 0
      val captured_oracle_elapsed = Unsynchronized.ref Time.zeroTime
      val scope_selection_captures = Unsynchronized.ref 0
      val scope_selection_reuses = Unsynchronized.ref 0

      fun root_args name term =
        (case strip_comb term of
          (Const (found, _), args) => if found = name then SOME args else NONE
        | _ => NONE)
      fun require_store_thread () =
        if Isabelle_Thread.equal (store_owner_thread, Isabelle_Thread.self ()) then ()
        else error "B1 certificate store used outside its owning ML thread"
      fun is_certificate_request request =
        exists (fn head => is_some (root_args head request))
          [template_head, lift_head, slot_head, slot_valid_head, binding_head,
           action_row_head, slot_valid_actions_head, binding_actions_head,
           lift_binding_head]
      val source_action_head = @{const_name comma_semantic_b1_source_slot_action}
      fun require_store_theory context =
        (require_store_thread ();
         if Context.eq_thy (Proof_Context.theory_of context, store_theory) then ()
         else error "B1 certificate store used with a foreign theory generation")
      fun require_theorem_theory theorem =
        if Context.subthy (Thm.theory_of_thm theorem, store_theory) then ()
        else error "B1 certificate theorem comes from a non-ancestor theory"
      (* Store ownership fixes the context and thread. Each captured root is
         checked, while immutable dependency nodes are certified once. The
         final published bundle retains Isabelle's full oracle audit. *)
      val (certify_equation, _) =
        Comma_Entry_Arithmetic.make_certifier ctxt
      fun certify_equations selected_equation_check theorems =
        let
          val _ = require_store_thread ()
          val started = Time.now ()
          val result = Exn.capture (fn () =>
            List.app (ignore o certify_equation) theorems) ()
          val elapsed = Time.- (Time.now (), started)
          val _ = if selected_equation_check then
              (selected_oracle_checks := !selected_oracle_checks + 1;
               selected_oracle_elapsed := Time.+ (!selected_oracle_elapsed, elapsed))
            else
              (captured_oracle_checks := !captured_oracle_checks + 1;
               captured_oracle_elapsed := Time.+ (!captured_oracle_elapsed, elapsed))
        in (Exn.release result; true) end
      fun exact_prefix actual expected =
        length actual >= length expected andalso
          ListPair.allEq (op aconv) (take (length expected) actual, expected)
      fun actual_numeral term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => if typ = @{typ nat} andalso value >= 0
            then SOME value else NONE
        | NONE => NONE)
      fun canonical_cid args arity position capacity =
        if length args <> arity then NONE
        else
          (case actual_numeral (nth args position) of
            SOME cid => if cid < capacity then SOME cid else NONE
          | NONE => NONE)
      fun checked_authority actual expected message =
        if exact_prefix actual expected then () else error message
      fun current_index_matches index_term =
        (case (!active_index, actual_numeral index_term) of
          (SOME expected, SOME actual) => expected = actual
        | _ => false)
      fun selected_equation context term =
        (require_store_thread ();
         case Termtab.lookup (!selected_equations) term of
          SOME theorem =>
            (selected_equation_reused := !selected_equation_reused + 1;
             theorem)
        | NONE =>
            let
              val equation = Simplifier.rewrite context (Thm.cterm_of ctxt term)
              val checked = Comma_Selected_List_Conversion.validate_equation term equation
              val _ = if certify_equations true [checked] then ()
                else error "B1 selected occurrence equation depends on an Isabelle oracle"
              val _ = if Comma_Selected_List_Conversion.closed term andalso
                  Termtab.size (!selected_equations) < selected_equation_capacity then
                (selected_equations := Termtab.update (term, checked)
                  (!selected_equations);
                 selected_equation_captured := !selected_equation_captured + 1)
                else ()
            in checked end)
      fun selected_numeral_equation context request =
        let
          val equation = selected_equation context request
          val normalized = Thm.transitive equation
            (Simplifier.rewrite
              (Comma_Entry_Arithmetic.numeral_context context)
              (Thm.rhs_of equation))
        in (equation, normalized) end
      (* Complete memoized RHS values with explicit rules before admission. *)
      fun selected_catalogue_equation context rules request =
        let
          val equation = selected_equation context request
          val completion = Simplifier.rewrite (context addsimps rules)
            (Thm.rhs_of equation)
        in Thm.transitive equation completion end
      fun selected_period_value context source =
        let
          val request = @{term comma_decisive_sector_period} $
            (@{term comma_source_continuation_base} $ source)
          val (equation, exact_period) = selected_numeral_equation context request
          val raw_rhs = Thm.term_of (Thm.rhs_of equation)
          val normalized_rhs = Thm.term_of (Thm.rhs_of exact_period)
        in
          (case actual_numeral normalized_rhs of
            SOME period => period
          | NONE => error ("B1 selected source period did not normalize to a numeral; " ^
              "request=" ^ Syntax.string_of_term context request ^
              "; raw_rhs=" ^ Syntax.string_of_term context raw_rhs ^
              "; normalized_rhs=" ^ Syntax.string_of_term context normalized_rhs))
        end
      fun current_source_and_parent context =
        (case (!active_source, !active_parent) of
          (SOME source, SOME parent) =>
            (scope_selection_reuses := !scope_selection_reuses + 1;
             (source, parent))
        | _ =>
            (case !active_index of
              NONE => error "B1 source-slot certificate has no active source index"
            | SOME index =>
                let
                  val numeral = HOLogic.mk_number @{typ nat} index
                  val source_request = Const (@{const_name nth},
                    fastype_of sources_table --> @{typ nat} --> @{typ comma_finite_position}) $
                    sources_table $ numeral
                  val source_equation = selected_equation context source_request
                  val source = Thm.term_of (Thm.rhs_of source_equation)
                  val parent_request = occurrence_at $ numeral
                  val parent_equation = selected_equation context parent_request
                  val parent_option = Thm.term_of (Thm.rhs_of parent_equation)
                  val parent =
                    (case strip_comb parent_option of
                      (Const (name, _), [parent]) =>
                        if name = @{const_name Some} then parent
                        else error "B1 current occurrence selector returned None"
                    | _ => error "B1 current occurrence selector did not return Some")
                  val _ = (active_source := SOME source;
                    active_parent := SOME parent;
                    active_source_equation := SOME source_equation;
                    active_parent_equation := SOME parent_equation;
                    scope_selection_captures := !scope_selection_captures + 1)
                in (source, parent) end))
      fun current_lift_refs context =
        (case (!active_refs, !active_refs_equation, !active_index) of
          (SOME refs, SOME _, _) => refs
        | (NONE, NONE, SOME index) =>
            let
              val numeral = HOLogic.mk_number @{typ nat} index
              val request = Const (@{const_name nth},
                fastype_of lift_refs_table --> @{typ nat} -->
                  HOLogic.listT @{typ comma_semantic_b1_crt_lift_ref}) $
                  lift_refs_table $ numeral
              val equation = selected_equation context request
              val refs = Thm.term_of (Thm.rhs_of equation)
              val _ = if fastype_of refs =
                  HOLogic.listT @{typ comma_semantic_b1_crt_lift_ref} andalso
                  Comma_Selected_List_Conversion.closed refs andalso
                  Comma_Semantic_B1_Construction_Check.standalone equation
                  andalso (case try HOLogic.dest_list refs of
                    SOME row => length row <= slots_per_source_capacity
                  | NONE => false)
                then ()
                else error "B1 selected lift labels are not a closed canonical row"
              val _ = (active_refs := SOME refs; active_refs_equation := SOME equation)
            in refs end
        | (NONE, NONE, NONE) =>
            error "B1 selected lift labels have no active source index"
        | _ => error "B1 selected lift-label cache lost its exact selection equation")
      fun selected_action_row source =
        (case (!active_index, !active_source) of
          (SOME index, SOME active) =>
            if active aconv source then
              let
                val row_type = HOLogic.listT @{typ comma_source_continuation_action}
                val table_type = HOLogic.listT row_type
                val request = Const (@{const_name nth},
                  table_type --> @{typ nat} --> row_type) $ action_table $
                    HOLogic.mk_number @{typ nat} index
              in request end
            else error "B1 action row changed the selected source"
        | _ => error "B1 action row has no active source scope")
      fun same_selected context left right =
        (* Each normalized side comes from an exact-LHS, closed, standalone,
           oracle-free kernel equation. Equal right sides therefore certify
           equal requests; selected_equation caches that proof by exact term. *)
        left aconv right orelse
          (Thm.term_of (Thm.rhs_of (selected_equation context left)) aconv
             Thm.term_of (Thm.rhs_of (selected_equation context right)))
      fun action_row_scope context source period actions =
        let
          val (selected_source, _) = current_source_and_parent context
          val expected_period = @{term comma_decisive_sector_period} $
            (@{term comma_source_continuation_base} $ selected_source)
          val period_value = selected_period_value context selected_source
        in period_value <= slots_per_source_capacity andalso
          same_selected context source selected_source andalso
          same_selected context period expected_period andalso
          same_selected context actions (selected_action_row selected_source) end
      fun check_scope_cell cell candidate label =
        (case !cell of
          NONE => cell := SOME candidate
        | SOME prior => if prior aconv candidate then ()
            else error ("B1 " ^ label ^ " certificate changed current occurrence scope"))
      fun bind_selected_scope context label =
        let val (source, parent) = current_source_and_parent context
        in check_scope_cell active_source source label;
           check_scope_cell active_parent parent label end
      (* This private path is reachable only after remember_equation's authority gate. *)
      fun insert_cid table capacity captured cid request theorem =
        (case Inttab.lookup (!table) cid of
          SOME prior =>
            if Thm.eq_thm_prop (prior, theorem) then ()
            else error "B1 geometry store received conflicting theorems for one canonical CID"
        | NONE =>
            if Inttab.size (!table) >= capacity then
              error "B1 exact certificate store exceeded its declared capacity"
            else
              (table := Inttab.update (cid, theorem) (!table);
               captured := !captured + 1))
      fun insert_exact table capacity captured request theorem =
        (case Termtab.lookup (!table) request of
          SOME prior =>
            if Thm.eq_thm_prop (prior, theorem) then ()
            else error "B1 certificate store received two propositions for one exact request"
        | NONE =>
            if Termtab.size (!table) >= capacity then
              error "B1 exact certificate store exceeded its declared capacity"
            else
              (table := Termtab.update (request, theorem) (!table);
               captured := !captured + 1))
      fun remember context request theorem =
        let
          val template_authority = [columns, templates_table, template_ids]
          val lift_binding_authority = [columns, templates_table, lift_ids,
            lift_descriptors]
          val slot_authority = [columns, templates_table, template_ids,
            lift_ids, occurrence_descriptors, lift_descriptors]
          val slot_valid_authority = [sources_table, occurrence_at,
            occurrence_descriptors, templates_table]
          val binding_authority = [columns, lift_ids, sources_table, occurrence_at]
          val actions_binding_authority =
            [columns, lift_ids, sources_table, occurrence_at]
        in
          (case root_args action_row_head request of
            SOME [source, period, actions] =>
              if action_row_scope context source period actions then
                insert_exact action_rows 1024 action_row_captured request theorem
              else error "B1 action row changed its source, period, or canonical row"
          | SOME _ => error "B1 action-row certificate has an unexpected shape"
          | NONE => (case root_args template_head request of
            SOME args =>
              (checked_authority args template_authority
                 "B1 template certificate used foreign catalogue terms";
              (case canonical_cid args 4 3 template_capacity of
                SOME cid =>
                  insert_cid templates template_capacity template_captured
                    cid request theorem
              | NONE => error "B1 template geometry certificate has no canonical CID"))
          | NONE =>
            (case root_args lift_head request of
              SOME args =>
                (checked_authority args lift_authority
                   "B1 lift certificate used foreign catalogue terms";
                 (case canonical_cid args 6 5 lift_capacity of
                   SOME cid =>
                     insert_cid lifts lift_capacity lift_captured cid request theorem
                 | NONE => error "B1 lift geometry certificate has no canonical CID"))
            | NONE =>
              (case root_args lift_binding_head request of
                SOME args =>
                  (checked_authority args lift_binding_authority
                     "B1 lift binding used foreign catalogue terms";
                   (case canonical_cid args 5 4 lift_capacity of
                     SOME cid =>
                       insert_cid lift_bindings lift_capacity
                         lift_binding_captured cid request theorem
                   | NONE => error
                       "B1 lift binding certificate has no canonical LiftProofID"))
              | NONE => (case root_args slot_head request of
                SOME args =>
                  (checked_authority args slot_authority
                     "B1 slot certificate used foreign catalogue terms";
                   if length args = 9 andalso current_index_matches (nth args 6)
                   then () else error "B1 slot certificate is outside the current source";
                   if nth args 7 aconv (current_lift_refs context) then ()
                   else error "B1 slot certificate used noncanonical lift labels";
                   bind_selected_scope context "slot";
                   insert_exact slots slots_per_source_capacity slot_captured request theorem)
              | NONE =>
                (case root_args slot_valid_head request of
                  SOME args =>
                    let
                      val _ = checked_authority args slot_valid_authority
                        "B1 source-slot certificate used foreign catalogue terms"
                      val _ = if length args = 9 then ()
                        else error "B1 source-slot certificate shape changed"
                      val _ = if nth args 7 aconv lift_descriptors then ()
                        else error "B1 source-slot certificate used foreign lift descriptors"
                      val _ = if nth args 6 aconv (current_lift_refs context) then ()
                        else error "B1 source-slot certificate used noncanonical lift labels"
                      val (selected_source, selected_parent) =
                        current_source_and_parent context
                      val _ = if nth args 4 aconv selected_source andalso
                          nth args 5 aconv selected_parent then ()
                        else error "B1 source-slot certificate changed selected occurrence"
                      val _ = check_scope_cell active_source (nth args 4) "source-slot"
                      val _ = check_scope_cell active_parent (nth args 5) "source-slot"
                      val _ = track_current_source_counter slot_valid_captured 2
                        (fn () => insert_exact slot_validity slots_per_source_capacity
                          slot_valid_captured request theorem)
                    in () end
                | NONE =>
                  (case root_args binding_head request of
                    SOME args =>
                      (checked_authority args binding_authority
                         "B1 piece binding used foreign catalogue terms";
                       if length args = 9 then ()
                         else error "B1 piece-binding certificate shape changed";
                       (case !active_refs of SOME refs =>
                            if refs aconv nth args 4 then ()
                            else error "B1 piece binding changed the active lift labels"
                        | NONE => error "B1 piece binding has no active lift labels");
                       (case !active_source of SOME source =>
                            if source aconv nth args 5 then ()
                            else error "B1 piece binding changed the active source"
                        | NONE => error "B1 piece binding has no active source");
                       (case !active_parent of SOME parent =>
                            if parent aconv nth args 6 then ()
                            else error "B1 piece binding changed the active parent labels"
                        | NONE => error "B1 piece binding has no active parent labels");
                       insert_exact bindings bindings_per_source_capacity
                         binding_captured request theorem)
                | NONE => (case root_args slot_valid_actions_head request of
                    SOME args =>
                      let
                        val _ = checked_authority args slot_valid_authority
                          "B1 action-slot certificate used foreign catalogue terms"
                        val _ = if length args = 10 then ()
                          else error "B1 action-slot certificate shape changed"
                        val (selected_source, selected_parent) =
                          current_source_and_parent context
                        val _ = if same_selected context (nth args 4) selected_source andalso
                            nth args 5 aconv selected_parent then ()
                          else error "B1 action-slot certificate changed selected occurrence"
                        val _ = if nth args 6 aconv (current_lift_refs context) andalso
                            nth args 7 aconv lift_descriptors then ()
                          else error "B1 action-slot certificate changed lift references"
                        val expected_period = @{term comma_decisive_sector_period} $
                          (@{term comma_source_continuation_base} $ nth args 4)
                        val _ = if action_row_scope context (nth args 4)
                            expected_period (nth args 8) then ()
                          else error "B1 action-slot certificate changed its action row"
                        val period = selected_period_value context selected_source
                        val _ = (case actual_numeral (nth args 9) of
                          SOME slot => if slot < slots_per_source_capacity andalso
                              slot < period then ()
                            else error "B1 action-slot certificate exceeds the slot bound"
                        | NONE => error "B1 action-slot certificate has no canonical slot")
                        val _ = check_scope_cell active_source (nth args 4) "action-slot"
                        val _ = check_scope_cell active_parent (nth args 5) "action-slot"
                      in track_current_source_counter slot_valid_captured 2
                        (fn () => insert_exact slot_validity
                          (2 * slots_per_source_capacity) slot_valid_captured request theorem)
                      end
                  | NONE => (case root_args binding_actions_head request of
                    SOME args =>
                      let
                        val _ = checked_authority args actions_binding_authority
                          "B1 action-piece binding used foreign catalogue terms"
                        val _ = if length args = 10 then ()
                          else error "B1 action-piece binding shape changed"
                        val _ = (case !active_refs of SOME refs =>
                            if same_selected context refs (nth args 4) then ()
                            else error "B1 action-piece binding changed lift labels"
                          | NONE => error "B1 action-piece binding has no lift labels")
                        val _ = (case !active_source of SOME source =>
                            if same_selected context source (nth args 5) then ()
                            else error "B1 action-piece binding changed source"
                          | NONE => error "B1 action-piece binding has no source")
                        val _ = (case !active_parent of SOME parent =>
                            if parent aconv nth args 7 then ()
                            else error "B1 action-piece binding changed parent"
                          | NONE => error "B1 action-piece binding has no parent")
                        val expected_period = @{term comma_decisive_sector_period} $
                          (@{term comma_source_continuation_base} $ nth args 5)
                        val _ = if action_row_scope context (nth args 5)
                            expected_period (nth args 6) then ()
                          else error "B1 action-piece binding changed action row"
                      in insert_exact bindings bindings_per_source_capacity
                        binding_captured request theorem end
                  | NONE => ())))))))))
        end
      fun reset_current_source index =
        (require_store_thread ();
         if index >= 0 andalso index < 1024 then ()
          else error "B1 certificate store source index exceeds its declared extent";
         slots := Termtab.empty;
         slot_validity := Termtab.empty;
         bindings := Termtab.empty;
         active_index := SOME index;
         source_construction_active := true;
         active_refs := NONE;
         active_refs_equation := NONE;
         active_source := NONE;
         active_parent := NONE;
         active_source_equation := NONE;
         active_parent_equation := NONE;
         Array.modify (fn _ => 0) current_source_metrics;
         ())
      fun remember_equation context request theorem =
        let
          val _ = require_store_theory context
          val _ = require_theorem_theory theorem
          fun exact_closed () = Comma_Selected_List_Conversion.closed request andalso
            Thm.term_of (Thm.lhs_of theorem) aconv request andalso
            Comma_Semantic_B1_Construction_Check.standalone theorem andalso
              certify_equations false [theorem]
          fun remember_action args =
            (case args of
              [source, slot_term] =>
                let
                  val (selected_source, _) = current_source_and_parent context
                  val _ = if same_selected context source selected_source then ()
                    else error "B1 source-action certificate changed selected source"
                  val period = selected_period_value context selected_source
                  val _ = (case actual_numeral slot_term of
                    SOME slot => if slot < slots_per_source_capacity andalso
                        slot < period then ()
                      else error "B1 source-action certificate exceeds the slot bound"
                  | NONE => error "B1 source-action certificate has no canonical slot")
                  val _ = if Comma_Selected_List_Conversion.closed
                      (Thm.term_of (Thm.rhs_of theorem)) then ()
                    else error "B1 source-action certificate has an open result"
                  val prior = Termtab.defined (!source_actions) request
                  val _ = insert_exact source_actions action_capacity
                    source_action_captured request theorem
                in if prior then () else bump_current_source_metric 0 end
            | _ => error "B1 source-action certificate has an unexpected shape")
        in
          (case root_args source_action_head request of
            SOME args => if exact_closed () then remember_action args
              else error "B1 source-action callback received an open, mismatched, or oracle theorem"
          | NONE => if not (is_certificate_request request) then ()
            else if not (exact_closed ()) then
              error "B1 certificate callback received an open, mismatched, or oracle theorem"
            else if Thm.term_of (Thm.rhs_of theorem) aconv @{term True} then
              remember context request theorem
            else ())
        end
      fun lookup_exact table request =
        (* Every entry passed the closed, exact-LHS, standalone, oracle-free
           capture gate; exact Termtab lookup preserves that request key. *)
        Termtab.lookup (!table) request
      fun lookup_cid table args arity position capacity authority request =
        if not (exact_prefix args authority) then NONE
        else (case canonical_cid args arity position capacity of
          SOME cid =>
            (case Inttab.lookup (!table) cid of
              SOME theorem =>
                if Thm.term_of (Thm.lhs_of theorem) aconv request
                then SOME theorem else NONE
            | NONE => NONE)
        | NONE => NONE)
      fun lookup_with_use table request used =
        (case lookup_exact table request of
          SOME theorem => (used := !used + 1; SOME theorem)
        | NONE => NONE)
      fun lookup_slot_valid request =
        track_current_source_counter slot_valid_reused 3
          (fn () => lookup_with_use slot_validity request slot_valid_reused)
      fun lookup_binding request =
        lookup_with_use bindings request binding_reused
      fun lookup_first [] = NONE
        | lookup_first (lookup :: rest) =
            (case lookup () of
              SOME result => SOME result
            | NONE => lookup_first rest)
      fun lookup_root request head lookup =
        (case root_args head request of
          SOME args => lookup args
        | NONE => NONE)
      fun lookup_source_action request =
        (case root_args source_action_head request of
          SOME [source, _] =>
            (case !active_source of
              SOME selected_source =>
                if selected_source aconv source then
                  Termtab.lookup (!source_actions) request
                else NONE
            | NONE => NONE)
        | _ => NONE)
      fun lookup_template request args =
        (case lookup_cid templates args 4 3 template_capacity
            [columns, templates_table, template_ids] request of
          SOME theorem =>
            (template_reused := !template_reused + 1; SOME theorem)
        | NONE => NONE)
      fun lookup_lift request args =
        (case lookup_cid lifts args 6 5 lift_capacity
            [columns, templates_table, template_ids, lift_ids,
             lift_descriptors] request of
          SOME theorem => (lift_reused := !lift_reused + 1; SOME theorem)
        | NONE => NONE)
      fun lookup_lift_binding request args =
        if not (exact_prefix args lift_binding_authority) then NONE
        else (case canonical_cid args 5 4 lift_capacity of
          SOME cid =>
            (case Inttab.lookup (!lift_bindings) cid of
              SOME theorem =>
                if Thm.term_of (Thm.lhs_of theorem) aconv request then
                  (lift_binding_reused := !lift_binding_reused + 1; SOME theorem)
                else error "B1 LiftProofID resolved to a different binding request"
            | NONE => NONE)
        | NONE => NONE)
      val lift_binding_rewrite =
        Comma_Semantic_B1_Used_Templates.make_lift_binding_rewrite
          ctxt lift_capacity lift_ids lift_descriptors templates_table template_ids
          actual_numeral selected_equation selected_numeral_equation
          selected_catalogue_equation
      val lift_descriptor_admission_failure =
        #admission_failure lift_binding_rewrite
      val lift_binding_rewrite_context = #rewrite_context lift_binding_rewrite
      val lift_binding_specialization_context =
        #specialization_context lift_binding_rewrite
      val lift_binding_map_congruence_uses = #congruence_uses lift_binding_rewrite
      val lift_binding_stage_timings = #stage_timings lift_binding_rewrite
      fun exact_admitted_lift_request context request =
        (case root_args lift_head request of
          SOME args =>
            if length args <> 6 orelse not (exact_prefix args lift_authority) then false
            else (case canonical_cid args 6 5 lift_capacity of
              NONE => false
            | SOME lift_cid =>
                is_none (lift_descriptor_admission_failure context lift_cid))
        | NONE => false)
      fun lift_binding_admission_failure context request =
        (case root_args lift_binding_head request of
          NONE => SOME "wrong request head"
        | SOME args =>
            if length args <> 5 then SOME "wrong request arity"
            else if not (exact_prefix args lift_binding_authority) then
              SOME "foreign LiftProofID catalogue"
            else if not (Comma_Selected_List_Conversion.closed request) then
              SOME "open request"
            else
              (case actual_numeral (nth args 4) of
                NONE => SOME "CID is not a canonical natural numeral"
              | SOME lift_cid => lift_descriptor_admission_failure context lift_cid))
      fun validate_true_equation request theorem message =
        let
          val checked = Comma_Selected_List_Conversion.validate_equation request theorem
          val rhs = Thm.term_of (Thm.rhs_of checked)
          val cid = (case root_args lift_binding_head request of
            SOME args => (case actual_numeral (List.last args) of
              SOME value => " cid=" ^ Int.toString value | NONE => " cid=?")
          | NONE => "")
        in
          if rhs aconv @{term True} andalso
              Comma_Semantic_B1_Construction_Check.standalone checked then checked
          else error (message ^ cid ^ " residual=" ^
            Comma_Semantic_B1_Construction_Check.residual_conjunct_summary rhs)
        end
      fun bool_true_equation request proposition_fact =
        validate_true_equation request
          (Comma_Semantic_B1_CRT_Operation_Conversion.bool_true_equation
            ctxt request proposition_fact)
          "B1 cached certificate failed exact boolean transport"
      fun true_fact_of_bool_equation context equation =
        let
          val proposition_equation = Thm.combination
            (Thm.reflexive (Thm.cterm_of context @{term Trueprop})) equation
        in Thm.equal_elim (Thm.symmetric proposition_equation) @{thm TrueI} end
      fun rewrite_lift_binding ctxt context request cterm =
        (require_store_theory ctxt;
         require_store_theory context;
         case root_args lift_binding_head request of
           SOME args =>
             (case lookup_lift_binding request args of
               SOME theorem => theorem
             | NONE =>
                 let
                   val next_cold = !lift_binding_recursive_evaluations + 1
                   val _ = if Comma_Proof_Profile.enabled () andalso
                       (next_cold = 1 orelse next_cold mod 32 = 0) then
                     Comma_Proof_Profile.report
                       ("B1 cold-lift admission-start ordinal=" ^
                        Int.toString next_cold ^ " cid=" ^
                        (case actual_numeral (nth args 4) of
                          SOME value => Int.toString value | NONE => "noncanonical"))
                     else ()
                   val admitted = timed lift_binding_admission_ms
                     (fn () => lift_binding_admission_failure context request)
                 in (case admitted of
                   SOME reason => error ("B1 LiftProofID request refused: " ^ reason)
                 | NONE =>
                   let
                     (* This is the only cold shifted-operation evaluation for
                        this canonical LiftProofID.  The exact closed result is
                        pinned before returning to the occurrence consumer.
                        Unfold this outer root explicitly before simplification:
                        the production context contains the occurrence memo
                        simproc for this same head, and simplifying the intact
                        root would recursively re-enter its active request. *)
                     val _ = lift_binding_recursive_evaluations :=
                       !lift_binding_recursive_evaluations + 1
                     val unfolded = Conv.rewr_conv
                       (@{thm comma_semantic_b1_crt_lift_binding_certified_def}
                         RS @{thm eq_reflection}) cterm
                     val lift_cid = (case actual_numeral (nth args 4) of
                       SOME value => value
                     | NONE => error "B1 LiftProofID lost its canonical CID")
                     (* First consume the exact descriptor and option result
                        in a sterile context. The production operation
                        simproc is fixed to the global owner context, so a
                        local option simp fact alone cannot prevent it from
                        rediscovering this option while the binding is
                        rewritten. The staged option theorem removes that
                        root before the active context sees the binding. *)
                     val specialized_binding = timed lift_binding_specialization_ms
                       (fn () =>
                         Simplifier.rewrite
                           (lift_binding_specialization_context context lift_cid)
                           (Thm.rhs_of unfolded))
                     val specialized_rhs =
                       Thm.term_of (Thm.rhs_of specialized_binding)
                     val unresolved_lift_option = Term.exists_subterm
                       (fn Const (name, _) =>
                           name = @{const_name comma_semantic_b1_crt_lift_columns_option}
                         | _ => false) specialized_rhs
                     val _ = if unresolved_lift_option then
                       error "B1 sterile LiftProofID pass left an unresolved option"
                       else ()
                     val theorem = timed lift_binding_resolution_ms (fn () =>
                       let
                         val active_context =
                           lift_binding_rewrite_context context lift_cid
                       in validate_true_equation request
                         (Thm.transitive unfolded
                           (Thm.transitive specialized_binding
                             (Simplifier.rewrite active_context
                               (Thm.rhs_of specialized_binding))))
                         "B1 cold LiftProofID did not certify its exact binding"
                       end)
                     val _ = remember_equation context request theorem
                     val _ = if Comma_Proof_Profile.enabled () andalso
                         (next_cold = 1 orelse next_cold mod 32 = 0) then
                       Comma_Proof_Profile.report
                         ("B1 cold-lift checkpoint count=" ^ Int.toString next_cold ^
                          " cid=" ^ Int.toString lift_cid ^
                          " admission_ms=" ^ LargeInt.toString
                            (!lift_binding_admission_ms) ^
                          " specialization_ms=" ^ LargeInt.toString
                            (!lift_binding_specialization_ms) ^
                          " resolution_ms=" ^ LargeInt.toString
                            (!lift_binding_resolution_ms))
                       else ()
                   in theorem end)
                 end)
         | NONE => error "B1 lift-binding converter received another request")
      fun make_lift_geometry_from_binding ctxt request binding_equation template_equation =
        let
          val binding_fact = true_fact_of_bool_equation ctxt binding_equation
          val template_fact = true_fact_of_bool_equation ctxt template_equation
          val proposition = HOLogic.mk_Trueprop request
          val geometry_fact = Goal.prove ctxt [] [] proposition
            (fn {context, ...} =>
              resolve_tac context
                [@{thm comma_semantic_b1_crt_lift_geometry_from_binding_and_template_geometry}] 1
              THEN resolve_tac context [binding_fact] 1
              THEN resolve_tac context [template_fact] 1)
        in bool_true_equation request geometry_fact end
      fun lookup_equation request =
        (require_store_thread ();
         lookup_first
          [fn () => lookup_root request action_row_head
             (fn _ => lookup_with_use action_rows request action_row_reused),
           fn () => lookup_source_action request,
           fn () => lookup_root request template_head (lookup_template request),
           fn () => lookup_root request lift_head (lookup_lift request),
           fn () => lookup_root request lift_binding_head
             (lookup_lift_binding request),
           fn () => lookup_root request slot_head
             (fn _ => lookup_with_use slots request slot_reused),
           fn () => lookup_root request slot_valid_head
             (fn _ => lookup_slot_valid request),
           fn () => lookup_root request slot_valid_actions_head
             (fn _ => lookup_slot_valid request),
           fn () => lookup_root request binding_head (fn _ => lookup_binding request),
           fn () => lookup_root request binding_actions_head
             (fn _ => lookup_binding request)])
      fun exact_template_equation_for_lift ctxt context request =
        (case root_args lift_head request of
          SOME [lift_columns, lift_templates, lift_template_ids, lift_ids,
                descriptors, lift_cid] =>
            let
              val natT = @{typ nat}
              val descriptorT = @{typ comma_semantic_b1_crt_lift_descriptor}
              val descriptor_listT = HOLogic.listT descriptorT
              val selected_descriptor = Const (@{const_name nth},
                descriptor_listT --> natT --> descriptorT) $ descriptors $ lift_cid
              val descriptor_eq = selected_equation context selected_descriptor
              val descriptor_value = Thm.term_of (Thm.rhs_of descriptor_eq)
              (* Record selectors are polymorphic in the record extension.  Fix
                 that parameter to the concrete descriptor type before applying
                 the selector to the nth descriptor. *)
              val template_selector = Const
                (@{const_name comma_semantic_b1_crt_lift_descriptor_template_cid},
                  descriptorT --> natT)
              val selected_template = template_selector $ descriptor_value
              val template_id_eq = selected_equation context selected_template
              val template_cid = Thm.term_of (Thm.rhs_of template_id_eq)
              val selected_template_from_catalogue =
                template_selector $ selected_descriptor
              val selected_template_equation = Thm.transitive
                (Thm.combination
                  (Thm.reflexive (Thm.cterm_of context template_selector)) descriptor_eq)
                template_id_eq
              val template_request = list_comb
                (Const (template_head,
                  Sign.the_const_type (Proof_Context.theory_of ctxt) template_head),
                 [lift_columns, lift_templates, lift_template_ids, template_cid])
              val symbolic_template_prefix = list_comb
                (Const (template_head,
                  Sign.the_const_type (Proof_Context.theory_of ctxt) template_head),
                 [lift_columns, lift_templates, lift_template_ids])
              val symbolic_template_request = symbolic_template_prefix $
                selected_template_from_catalogue
              val template_index =
                (case actual_numeral template_cid of
                  SOME value => value
                | NONE => error "B1 LiftProofID has a noncanonical template CID")
              val _ = if template_index < template_capacity then ()
                else error "B1 LiftProofID refers outside the template CID extent"
              val template_args =
                [lift_columns, lift_templates, lift_template_ids, template_cid]
              val cached = lookup_template template_request template_args
            in
              (case cached of
                SOME theorem =>
                  let
                    val transported_request = Thm.combination
                      (Thm.reflexive (Thm.cterm_of context symbolic_template_prefix))
                      selected_template_equation
                    val transported = Thm.transitive transported_request theorem
                  in SOME (Comma_Selected_List_Conversion.validate_equation
                    symbolic_template_request transported) end
              | NONE => error
                  "B1 admitted lift geometry is missing its captured TemplateCID certificate")
            end
        | _ => NONE)
      fun rewrite_lift_geometry ctxt context request cterm =
        (require_store_theory ctxt;
         require_store_theory context;
         (case root_args lift_head request of
           NONE => error "B1 lift-geometry converter received another request"
         | SOME args =>
             (case lookup_lift request args of
               SOME theorem => theorem
             | NONE =>
                 if not (exact_admitted_lift_request context request) then
                   error "B1 lift geometry has foreign authority or an invalid descriptor"
                 else
                   (case exact_template_equation_for_lift ctxt context request of
                     NONE => error "B1 admitted lift has no exact template geometry"
                   | SOME template_equation =>
                       let
                         val binding_request = list_comb
                           (Const (lift_binding_head,
                             Sign.the_const_type store_theory lift_binding_head),
                            [nth args 0, nth args 1, nth args 3, nth args 4, nth args 5])
                         val binding_equation = rewrite_lift_binding ctxt context
                           binding_request (Thm.cterm_of ctxt binding_request)
                         val theorem = make_lift_geometry_from_binding ctxt request
                           binding_equation template_equation
                         val _ = remember_equation context request theorem
                         val _ = lift_geometry_from_binding :=
                           !lift_geometry_from_binding + 1
                       in theorem end))))
      fun stats () =
        (require_store_thread ();
        "template_geometry_captured=" ^ Int.toString (!template_captured) ^
        " template_geometry_cid_reused=" ^ Int.toString (!template_reused) ^
        " lift_geometry_captured=" ^ Int.toString (!lift_captured) ^
        " lift_geometry_cid_reused=" ^ Int.toString (!lift_reused) ^
        " lift_binding_proofs_captured=" ^ Int.toString (!lift_binding_captured) ^
        " lift_binding_proofs_reused=" ^ Int.toString (!lift_binding_reused) ^
        " lift_binding_cold_evaluations=" ^
          Int.toString (!lift_binding_recursive_evaluations) ^
        " lift_binding_admission_ms=" ^ LargeInt.toString
          (!lift_binding_admission_ms) ^
        " lift_binding_specialization_ms=" ^ LargeInt.toString
          (!lift_binding_specialization_ms) ^
        " lift_binding_resolution_ms=" ^ LargeInt.toString
          (!lift_binding_resolution_ms) ^
        " lift_binding_map_congruence_uses=" ^
          Int.toString (lift_binding_map_congruence_uses ()) ^
        " " ^ lift_binding_stage_timings () ^
        " lift_geometry_from_binding=" ^ Int.toString (!lift_geometry_from_binding) ^
        " source_slot_certificates_captured=" ^ Int.toString (!slot_captured) ^
        " source_slot_certificates_reused=" ^ Int.toString (!slot_reused) ^
        " source_action_slot_certificates_captured=" ^
          Int.toString (!slot_valid_captured) ^
        " source_action_slot_certificates_reused=" ^
          Int.toString (!slot_valid_reused) ^
        " piece_binding_proofs_captured=" ^ Int.toString (!binding_captured) ^
        " piece_binding_proofs_reused=" ^ Int.toString (!binding_reused) ^
        " source_action_proofs_new=" ^ Int.toString (!source_action_captured) ^
        " source_action_proofs_reused=" ^ Int.toString (!source_action_reused) ^
        " source_action_rows_captured=" ^ Int.toString (!action_row_captured) ^
        " source_action_rows_reused=" ^ Int.toString (!action_row_reused) ^
        " selected_equations_captured=" ^ Int.toString (!selected_equation_captured) ^
        " selected_equations_reused=" ^ Int.toString (!selected_equation_reused) ^
        " selected_equation_oracle_checks=" ^ Int.toString (!selected_oracle_checks) ^
        " selected_equation_oracle_elapsed_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!selected_oracle_elapsed)) ^
        " captured_equation_oracle_checks=" ^ Int.toString (!captured_oracle_checks) ^
        " captured_equation_oracle_elapsed_ms=" ^ LargeInt.toString
          (Time.toMilliseconds (!captured_oracle_elapsed)) ^
        " selected_source_scope_captures=" ^ Int.toString (!scope_selection_captures) ^
        " selected_source_scope_reuses=" ^ Int.toString (!scope_selection_reuses) ^
        " construction_source_index=" ^ (case (!source_construction_active, !active_index) of
          (true, SOME index) => Int.toString index | _ => "none") ^
        " store_generation=" ^ Int.toString store_generation ^ " " ^
        String.concatWith " " (map (fn (label, metric) => label ^ Int.toString
          (Array.sub (current_source_metrics, metric)))
          [("source_action_evaluations_delta=", 0), ("source_action_reuses_delta=", 1),
           ("source_slot_certificates_captured_delta=", 2),
           ("source_slot_certificates_reused_delta=", 3)]))
      fun oracle_check_counts () =
        (require_store_thread ();
         (!selected_oracle_checks, !captured_oracle_checks))
      fun retained_entry_counts () =
        (require_store_thread ();
         [Inttab.size (!templates), Inttab.size (!lifts),
          Inttab.size (!lift_bindings),
          Termtab.size (!slots), Termtab.size (!slot_validity),
          Termtab.size (!bindings), Termtab.size (!source_actions),
          Termtab.size (!action_rows), Termtab.size (!selected_equations)])
      fun is_source_action_request request =
        is_some (root_args source_action_head request)
      fun is_binding_request request =
        exists (fn head => is_some (root_args head request))
          [binding_head,
           @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions}]
      fun note_source_action_reuse () =
        (require_store_thread ();
         source_action_reused := !source_action_reused + 1;
         bump_current_source_metric 1)
      fun profile_current_source stage close =
        (require_store_thread ();
         if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
           ("B1 construction stage=" ^ stage ^ " " ^ stats ()) else ();
         if close then (source_construction_active := false;
           Array.modify (fn _ => 0) current_source_metrics) else ())
    in
      {remember_equation = remember_equation, lookup_equation = lookup_equation,
       reset_current_source = reset_current_source,
       rewrite_lift_geometry = rewrite_lift_geometry,
       rewrite_lift_binding = rewrite_lift_binding,
       lift_geometry_counters = fn () =>
         (require_store_thread ();
          (!lift_geometry_from_binding, !lift_reused)),
       lift_binding_counters = fn () =>
         (require_store_thread ();
          (!lift_binding_recursive_evaluations, !lift_binding_reused)),
       note_source_action_reuse = note_source_action_reuse,
       is_source_action_request = is_source_action_request,
       is_binding_request = is_binding_request,
       profile_current_source = profile_current_source, stats = stats,
       oracle_check_counts = oracle_check_counts,
      retained_entry_counts = retained_entry_counts}
    end
  fun make_instance_store ctxt =
    make_certificate_store
      {ctxt = ctxt,
       template_head = @{const_name comma_semantic_b1_crt_template_geometry_certified},
       lift_head = @{const_name comma_semantic_b1_crt_lift_geometry_certified},
       slot_head = @{const_name comma_semantic_b1_crt_constructed_goto_slot_certificate},
       slot_valid_head = @{const_name comma_semantic_b1_crt_lift_slot_valid},
       binding_head = @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches},
       action_row_head = @{const_name comma_semantic_b1_crt_source_slot_action_row_certified},
       slot_valid_actions_head = @{const_name comma_semantic_b1_crt_lift_slot_valid_from_actions},
       binding_actions_head = @{const_name comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions},
       action_table = @{term "comma_semantic_b1_crt_slot_actions_table comma_semantic_b1_crt_sources"},
       columns = @{term comma_semantic_b1_crt_columns},
       templates_table = @{term comma_semantic_b1_crt_templates},
       template_ids = @{term comma_semantic_b1_crt_template_column_ids},
       lift_ids = @{term comma_semantic_b1_crt_lift_column_ids},
       sources_table = @{term comma_semantic_b1_crt_sources},
       occurrence_at = @{term comma_semantic_b1_crt_occurrence_at_index},
       occurrence_descriptors = @{term comma_semantic_b1_crt_descriptors},
       lift_refs_table = @{term comma_semantic_b1_crt_lift_refs},
       lift_descriptors = @{term comma_semantic_b1_crt_lift_descriptors}}
end
