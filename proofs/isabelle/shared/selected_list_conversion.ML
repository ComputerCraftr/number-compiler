(* Proof-producing, extent-checked traversal of literal list definitions.
   The selected path is reduced with kernel list equations; the full list is
   never normalized by the generic simplifier. *)
structure Comma_Selected_List_Conversion =
struct
  fun closed term = null (Term.add_frees term []) andalso
    null (Term.add_vars term []) andalso not (Term.is_open term)

  fun schematize pattern =
    Term.map_aterms
      (fn Free (name, typ) => Var ((name, 0), typ) | atom => atom) pattern

  fun head_name term =
    (case Term.head_of term of
      Const (name, _) => SOME name
    | _ => NONE)

  fun timed elapsed failures f x =
    let
      val start = Time.now ()
      val result = Exn.capture f x
      val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), start))
      val _ = if Exn.is_exn result then failures := !failures + 1 else ()
    in Exn.release result end

  fun equation_shape_valid request theorem =
    let
      val lhs = Thm.term_of (Thm.lhs_of theorem)
    in
      lhs aconv request andalso
          Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
          null (Thm.tpairs_of theorem)
    end

  fun validate_equation request theorem =
    let val rhs = Thm.term_of (Thm.rhs_of theorem)
    in
      if equation_shape_valid request theorem andalso closed rhs then theorem
      else error "selected-list conversion returned an open or mismatched theorem"
    end

  fun make_cached_equation_validator () =
    let
      val closed_rhs = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val closed_reuse_hits = Unsynchronized.ref 0
      val closed_rhs_capacity = 8192

      fun validate request theorem =
        let
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val shape_valid = equation_shape_valid request theorem
          val already_closed = shape_valid andalso
            Termtab.defined (!closed_rhs) rhs
          val rhs_closed =
            if not shape_valid then false
            else if already_closed then
              (closed_reuse_hits := !closed_reuse_hits + 1; true)
            else if closed rhs then
              (if Termtab.size (!closed_rhs) < closed_rhs_capacity then
                 closed_rhs := Termtab.update (rhs, ()) (!closed_rhs)
               else ();
               true)
            else false
        in
          if shape_valid andalso rhs_closed then theorem
          else error "selected-list conversion returned an open or mismatched theorem"
        end

      fun reuse_hits () = !closed_reuse_hits
    in {validate = validate, closed_reuse_hits = reuse_hits} end

  fun prove_indexed_list_all
      {ctxt, predicate, bound, prove_item, zero_fact, step_fact} =
    let
      val natT = @{typ nat}
      val list_type = @{typ "nat list"}
      val _ = if fastype_of predicate = @{typ "nat => bool"} andalso
          0 <= bound andalso bound <= 65536
        then () else error "Invalid bounded indexed list_all request"
      fun numeral value = HOLogic.mk_number natT value
      val list_all = Const (@{const_name list_all},
        fastype_of predicate --> list_type --> @{typ bool}) $ predicate
      val zero_rule = Drule.infer_instantiate ctxt
        [(("P", 0), Thm.cterm_of ctxt predicate)]
        zero_fact
      val zero_endpoint = Const (@{const_name upt}, natT --> natT --> list_type) $
        numeral 0 $ numeral 0
      val _ = if Thm.prop_of zero_rule aconv
          HOLogic.mk_Trueprop (list_all $ zero_endpoint)
        then () else error "Indexed list_all zero theorem has the wrong interval"
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt
      fun advance index prefix =
        if index = bound then prefix
        else
          let
            val index_term = numeral index
            val head_proof = prove_item index
            val expected_head = HOLogic.mk_Trueprop (predicate $ index_term)
            val _ = if Thm.prop_of head_proof aconv expected_head andalso
                Thm.nprems_of head_proof = 0 andalso null (Thm.hyps_of head_proof) andalso
                null (Thm.tpairs_of head_proof)
              then () else error "Indexed list_all item proof has the wrong proposition"
            val step_rule = Drule.infer_instantiate ctxt
              [(("P", 0), Thm.cterm_of ctxt predicate),
               (("n", 0), Thm.cterm_of ctxt index_term)]
              step_fact
            val raw_step = step_rule OF [prefix, head_proof]
            val successor = Const (@{const_name Suc}, natT --> natT) $ index_term
            val successor_equation = Simplifier.rewrite scalar_context
              (Thm.cterm_of ctxt successor)
            val successor_conversion = Conv.arg_conv
              (Conv.arg_conv (Conv.arg_conv
                (Conv.rewr_conv successor_equation)))
              (Thm.cterm_of ctxt (Thm.prop_of raw_step))
            val step = Thm.equal_elim successor_conversion raw_step
            val expected = HOLogic.mk_Trueprop
              (list_all $ (Const (@{const_name upt}, natT --> natT --> list_type) $
                numeral 0 $ numeral (index + 1)))
            val _ = if Thm.prop_of step aconv expected then ()
              else error "Indexed list_all recurrence produced the wrong interval"
          in advance (index + 1) step end
    in advance 0 zero_rule end

  fun make {ctxt, name, root_definition, table_pattern, extents} =
    let
      val _ = if not (null extents) andalso
          List.all (fn extent => extent > 0) extents
        then () else error "Selected-list extents must be positive"
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms pred_numeral_simps}
      val arithmetic = Simplifier.rewrite scalar_context
      fun normalize_scalar cterm =
        let
          (* Code_Simp presents concrete natural zero/successor constants in
             unoverloaded class form.  Restore the typed numeral first so
             both the extent check and the scalar arithmetic see the same
             canonical natural index. *)
          val overloaded = Axclass.overload_conv ctxt cterm
          val normalized = arithmetic (Thm.rhs_of overloaded)
        in Thm.transitive overloaded normalized end
      val root = (if can Logic.dest_equals (Thm.prop_of root_definition)
        then root_definition else root_definition RS @{thm eq_reflection})
      val root_term = Thm.term_of (Thm.lhs_of root)
      val _ = validate_equation root_term root
      val memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      (* A second, request-local table stores proof-carrying suffixes.  It is
         deliberately keyed by the exact drop expression (which includes the
         source table), so unrelated roots and nested rows cannot alias. *)
      val suffix_memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      fun prefix_capacity [] _ total = total
        | prefix_capacity (extent :: rest) product total =
            let
              val multiplier = IntInf.fromInt extent
              val next_product = product * multiplier
              val next_total = total + next_product
            in prefix_capacity rest next_product next_total end
      val suffix_capacity_big = prefix_capacity extents 1 0
      val _ = if suffix_capacity_big <= IntInf.fromInt 131072 then ()
        else error "Selected-list suffix cache exceeds the proof-session cap"
      val suffix_capacity = Int.max (1, IntInf.toInt suffix_capacity_big)
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val internal_publications = Unsynchronized.ref 0
      val leaf_evaluations = Unsynchronized.ref 0
      val retained = Unsynchronized.ref 0
      val peak_retained = Unsynchronized.ref 0
      val evicted = Unsynchronized.ref 0
      val selected_cells = Unsynchronized.ref 0
      val suffix_lookups = Unsynchronized.ref 0
      val suffix_hits = Unsynchronized.ref 0
      val suffix_misses = Unsynchronized.ref 0
      val suffix_steps = Unsynchronized.ref 0
      val length_spine_nodes = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      val failures = Unsynchronized.ref 0

      fun selector_depth table =
        if table aconv root_term then SOME 0
        else
          (case strip_comb table of
            (Const (constant, _), [parent, _]) =>
              if constant = @{const_name nth} then
                Option.map (fn depth => depth + 1) (selector_depth parent)
              else NONE
          | _ => NONE)

      fun extent_at [] _ = NONE
        | extent_at (extent :: _) 0 = SOME extent
        | extent_at (_ :: rest) depth = extent_at rest (depth - 1)

      fun excerpt term =
        let
          val rendered = XML.content_of
            (YXML.parse_body (Syntax.string_of_term ctxt term))
          val count = Int.min (String.size rendered, 96)
        in String.substring (rendered, 0, count) end

      fun report_extent_failure cterm =
        (case strip_comb (Thm.term_of cterm) of
          (Const (constant, _), [table, raw_index]) =>
            if constant = @{const_name nth} then
              let
                val depth = selector_depth table
                val expected = Option.mapPartial
                  (fn value => extent_at extents value) depth
                val normalized = Exn.capture (fn () =>
                  Thm.term_of (Thm.rhs_of
                    (arithmetic (Thm.cterm_of ctxt raw_index)))) ()
                val normalized_text =
                  (case normalized of
                    Exn.Res value => excerpt value
                  | Exn.Exn _ => "<normalization-failed>")
                val depth_text =
                  (case depth of SOME value => Int.toString value | NONE => "foreign")
                val bound_text =
                  (case expected of SOME value => Int.toString value | NONE => "none")
              in
                Comma_Proof_Profile.report
                  ("selected-list extent failure owner=" ^ name ^
                   " depth=" ^ depth_text ^ " extent=" ^ bound_text ^
                   " root_table=" ^ Bool.toString (table aconv root_term) ^
                   " raw_index=" ^ excerpt raw_index ^
                   " normalized_index=" ^ normalized_text)
              end
            else ()
        | _ => ())

      fun in_extent cterm =
        (case strip_comb (Thm.term_of cterm) of
          (Const (constant, _), [table, raw_index]) =>
            if constant <> @{const_name nth} then false
            else
              (case selector_depth table of
                NONE => false
              | SOME depth =>
                  (case extent_at extents depth of
                    NONE => false
                  | SOME extent =>
                      let
                        val index = Thm.term_of (Thm.rhs_of
                          (normalize_scalar (Thm.cterm_of ctxt raw_index)))
                      in
                        (case try HOLogic.dest_number index of
                          SOME (typ, value) => typ = @{typ nat} andalso
                            0 <= value andalso value < extent
                        | NONE => false)
                      end))
        | _ => false)

      fun root_length cterm =
        (case strip_comb (Thm.term_of cterm) of
          (Const (constant, _), [table]) =>
            (* HOL's `length` is an abbreviation for the size class constant. *)
            constant = @{const_name size} andalso table aconv root_term
        | _ => false)

      (* Once a selector's table spine reaches this conversion's root, an
         out-of-extent numeral is malformed input to this owner, not an
         unrelated term that another simplifier is free to reduce.  The
         lookup path performs the depth-specific bound check and rejects it. *)
      fun owned_selector cterm =
        (case strip_comb (Thm.term_of cterm) of
          (Const (constant, _), [table, _]) =>
            constant = @{const_name nth} andalso
              (case selector_depth table of
                SOME depth => Option.isSome (extent_at extents depth)
              | NONE => false)
        | _ => false)

      fun drop_term index table =
        let
          val list_type = fastype_of table
          val drop_type = @{typ nat} --> list_type --> list_type
        in Const (@{const_name drop}, drop_type) $ index $ table end

      fun validate_suffix key theorem =
        let
          val lhs = Thm.term_of (Thm.lhs_of theorem)
        in
          if lhs aconv key andalso Thm.nprems_of theorem = 0 andalso
              null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
          then theorem
          else error "selected-list suffix proof is open or has the wrong key"
        end

      (* Reduce list size by following only the outer Cons/Nil spine.  The
         generic simplifier descends into each head first, which expands the
         retained Let-DAG payload of every template.  These kernel rewrites
         leave each head opaque and visit exactly one spine constructor. *)
      fun rewrite_size_cell cterm =
        let
          val term = Thm.term_of cterm
          val (_, arguments) = strip_comb term
          val list_term =
            (case arguments of
              [value] => value
            | _ => error "Selected-list size expected one list argument")
          val rule =
            (case Term.head_of list_term of
              Const (constructor, _) =>
                if constructor = @{const_name Nil} then
                  @{thm comma_selected_length_nil}
                else if constructor = @{const_name Cons} then
                  @{thm comma_selected_length_cons}
                else error "Selected-list size expected a literal Cons/Nil cell"
            | _ => error "Selected-list size encountered an open list spine")
        in Conv.rewr_conv (rule RS @{thm eq_reflection}) cterm end
      fun list_size_spine cterm =
        let
          val term = Thm.term_of cterm
          val (_, arguments) = strip_comb term
          val list_term =
            (case arguments of
              [value] => value
            | _ => error "Selected-list size expected one list argument")
          val _ = length_spine_nodes := !length_spine_nodes + 1
          val cell = Term.head_of list_term
          val one_cell = rewrite_size_cell cterm
        in
          (case cell of
            Const (constructor, _) =>
              if constructor = @{const_name Nil} then one_cell
              else if constructor = @{const_name Cons} then
                Thm.transitive one_cell
                  (Conv.arg_conv list_size_spine (Thm.rhs_of one_cell))
              else error "Selected-list size encountered a non-list constructor"
          | _ => error "Selected-list size encountered an open list spine")
        end

      fun suffix table index =
        let
          val index_term = HOLogic.mk_number @{typ nat} index
          val key = drop_term index_term table
          val cterm = Thm.cterm_of ctxt key
          val _ = suffix_lookups := !suffix_lookups + 1
        in
          case Termtab.lookup (!suffix_memo) key of
            SOME theorem => (suffix_hits := !suffix_hits + 1; theorem)
          | NONE =>
              let
                val _ = suffix_misses := !suffix_misses + 1
                val theorem =
                  if index = 0 then
                    let
                      val zero = Conv.rewr_conv
                        (@{thm drop_0} RS @{thm eq_reflection}) cterm
                    in
                      if table aconv root_term
                      then Thm.transitive zero
                        (Conv.rewr_conv root (Thm.rhs_of zero))
                      else zero
                    end
                  else
                    let
                      val previous = suffix table (index - 1)
                      val numeral_suc = Conv.fun_conv
                        (Conv.arg_conv (Conv.rewr_conv
                          ((if index = 1 then @{thm One_nat_def}
                            else @{thm numeral_eq_Suc}) RS @{thm eq_reflection}))) cterm
                      val indexed =
                        if index = 1 then numeral_suc
                        else
                          let
                            val numeral_arg =
                              (case Term.dest_comb index_term of
                                (_, value) => value)
                            val predecessor =
                              Const (@{const_name pred_numeral},
                                @{typ num} --> @{typ nat}) $ numeral_arg
                            val predecessor_eq = arithmetic
                              (Thm.cterm_of ctxt predecessor)
                            val predecessor_value =
                              Thm.term_of (Thm.rhs_of predecessor_eq)
                            val expected_predecessor = HOLogic.mk_number
                              @{typ nat} (index - 1)
                            val _ = if predecessor_value aconv expected_predecessor then ()
                              else error "Selected-list numeral predecessor did not normalize"
                            val reduce_predecessor = Conv.fun_conv
                              (Conv.arg_conv (Conv.arg_conv
                                (Conv.rewr_conv predecessor_eq)))
                              (Thm.rhs_of numeral_suc)
                          in Thm.transitive numeral_suc reduce_predecessor end
                      val after_drop_suc = Conv.rewr_conv
                        (@{thm drop_Suc} RS @{thm eq_reflection})
                        (Thm.rhs_of indexed)
                      val after_drop_tl = Conv.rewr_conv
                        (@{thm drop_tl} RS @{thm eq_reflection})
                        (Thm.rhs_of after_drop_suc)
                      val after_previous = Conv.arg_conv
                        (Conv.rewr_conv previous)
                        (Thm.rhs_of after_drop_tl)
                      val after_one_cell = Conv.rewr_conv
                        (@{thm list.sel(3)} RS @{thm eq_reflection})
                        (Thm.rhs_of after_previous)
                      val one_step = Thm.transitive indexed
                        (Thm.transitive after_drop_suc
                          (Thm.transitive after_drop_tl
                            (Thm.transitive after_previous after_one_cell)))
                    in one_step end
                (* The root equation is validated once above.  Each later
                   right side is obtained by dropping one constructor from
                   that already-closed tail, so rescanning the growing tail
                   here would recreate quadratic validation work. *)
                val checked = validate_suffix key theorem
                val _ = if index = 0 then () else suffix_steps := !suffix_steps + 1
                val _ = if Termtab.size (!suffix_memo) < suffix_capacity then
                    suffix_memo := Termtab.update (key, checked) (!suffix_memo)
                  else error "Selected-list suffix proof cache capacity exceeded"
              in checked end
        end

      fun lookup cterm =
        let
          val key = Thm.term_of cterm
          val _ = lookups := !lookups + 1
        in
          if not (in_extent cterm) then
            (report_extent_failure cterm;
             error "Selected-list nested index exceeds its depth-specific extent")
          else case Termtab.lookup (!memo) key of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val _ = if Termtab.defined (!active) key then
                    error "Recursive selected-list conversion"
                  else active := Termtab.update (key, ()) (!active)
                val attempt = Exn.capture (fn () =>
                  let
                    val theorem =
                      if key aconv root_term then root
                      else
                        (case strip_comb key of
                          (Const (constant, _), [table, _]) =>
                            if constant = @{const_name nth} then
                              let
                                val lookup_table =
                                  (case Term.head_of table of
                                    Const (name, _) => name = @{const_name nth}
                                  | _ => false)
                                val prepared = if lookup_table then
                                    Conv.fun_conv (Conv.arg_conv lookup) cterm
                                  else Thm.reflexive cterm
                              in Thm.transitive prepared (nth (Thm.rhs_of prepared)) end
                            else error "Selected-list cache received a non-selector term"
                        | _ => error "Selected-list cache received an unowned term")
                  in validate_equation key theorem end) ()
                val _ = active := Termtab.delete key (!active)
                val theorem =
                  (case attempt of
                    Exn.Res result => result
                  | Exn.Exn exn => Exn.reraise exn)
                val _ = if fastype_of key = @{typ nat} then
                    leaf_evaluations := !leaf_evaluations + 1
                  else
                    let
                      val _ = if !retained < 8192 then () else
                        (evicted := !evicted + !retained;
                         memo := Termtab.empty; retained := 0)
                      val _ = memo := Termtab.update (key, theorem) (!memo)
                      val _ = retained := !retained + 1
                      val _ = peak_retained := Int.max (!peak_retained, !retained)
                    in internal_publications := !internal_publications + 1 end
              in theorem end
        end

      and nth cterm =
        let
          val index_conversion = Conv.arg_conv normalize_scalar cterm
          val normalized_request = Thm.rhs_of index_conversion
          val (head, arguments) = strip_comb (Thm.term_of normalized_request)
          val (table, normalized_index) =
            (case (head, arguments) of
              (Const (constant, _), [source, index]) =>
                if constant = @{const_name nth} then (source, index)
                else error "Selected-list conversion expected the nth constant"
            | _ => error "Selected-list conversion expected nth table index")
          val (index_type, index) =
            (case try HOLogic.dest_number normalized_index of
              SOME result => result
            | NONE => error "Selected-list index is not a closed numeral")
          val _ = if index_type = @{typ nat} andalso index >= 0 andalso
              index < fold (fn extent => fn maximum => Int.max (extent, maximum))
                extents 0
            then () else error "Selected-list index exceeds its declared extent"
          val _ = selected_cells := !selected_cells + 1
          val selected_suffix = suffix table index
          val suffix_value = Thm.term_of (Thm.rhs_of selected_suffix)
          val is_cons =
            (case Term.head_of suffix_value of
              Const (constant, _) => constant = @{const_name Cons}
            | _ => false)
          val _ = if is_cons then ()
            else error "Selected-list index points beyond the literal table"
          val selected = (@{thm nth_via_drop} OF
            [selected_suffix RS @{thm meta_eq_to_obj_eq}]) RS @{thm eq_reflection}
          val theorem = Thm.transitive index_conversion selected
        in validate_equation (Thm.term_of cterm) theorem end

      fun lookup_length cterm =
        let
          val key = Thm.term_of cterm
          val _ = lookups := !lookups + 1
        in
          case Termtab.lookup (!memo) key of
            SOME theorem => (hits := !hits + 1; theorem)
          | NONE =>
              let
                val selected = Conv.arg_conv (Conv.rewr_conv root) cterm
                val spine_count = list_size_spine (Thm.rhs_of selected)
                (* Only the tiny unary count is normalized here; the list
                   payload has already been left opaque by the spine walk. *)
                val numeral = arithmetic (Thm.rhs_of spine_count)
                val reduced = Thm.transitive spine_count numeral
                val theorem = validate_equation key (Thm.transitive selected reduced)
                val _ = if !retained < 8192 then () else
                  (evicted := !evicted + !retained;
                   memo := Termtab.empty; retained := 0)
                val _ = memo := Termtab.update (key, theorem) (!memo)
                val _ = retained := !retained + 1
                val _ = peak_retained := Int.max (!peak_retained, !retained)
                val _ = internal_publications := !internal_publications + 1
              in theorem end
        end

      fun convert cterm =
        let val term = Thm.term_of cterm in
          if not (closed term) then NONE
          else if root_length cterm then
            SOME (timed elapsed failures lookup_length cterm)
          else if owned_selector cterm then
            SOME (timed elapsed failures lookup cterm)
          else NONE
        end

      val pattern = table_pattern
        |> Term.map_aterms
          (fn Free (variable, typ) => Var ((variable, 0), typ) | atom => atom)
      (* The broad head pattern makes the outermost nested selector visible
         before the simplifier descends into its table argument.  Ownership is
         then checked against the original root spine by [owned_selector]. *)
      val selector_pattern = schematize @{term "selected_table ! selected_index"}
      val length_pattern = schematize @{term "length selected_table"}
      val procedure = Simplifier.make_simproc ctxt
        {name = "comma_selected_list_" ^ name,
         kind = Simplifier.Congproc false,
         lhss = [pattern, selector_pattern, length_pattern],
         proc = fn _ => fn _ => convert, identifier = []}

      fun stats () = name ^ "_lookups=" ^ Int.toString (!lookups) ^
        " " ^ name ^ "_hits=" ^ Int.toString (!hits) ^
        " " ^ name ^ "_leaf_evaluations=" ^ Int.toString (!leaf_evaluations) ^
        " " ^ name ^ "_internal_publications=" ^
          Int.toString (!internal_publications) ^
        " " ^ name ^ "_internal_retained=" ^ Int.toString (!retained) ^
        " " ^ name ^ "_internal_peak=" ^ Int.toString (!peak_retained) ^
        " " ^ name ^ "_evicted=" ^ Int.toString (!evicted) ^
        " " ^ name ^ "_selected_cells=" ^ Int.toString (!selected_cells) ^
        " " ^ name ^ "_suffix_lookups=" ^ Int.toString (!suffix_lookups) ^
        " " ^ name ^ "_suffix_hits=" ^ Int.toString (!suffix_hits) ^
        " " ^ name ^ "_suffix_misses=" ^ Int.toString (!suffix_misses) ^
        " " ^ name ^ "_spine_node_visits=" ^ Int.toString (!suffix_steps) ^
        " " ^ name ^ "_length_spine_nodes=" ^
          Int.toString (!length_spine_nodes) ^
        " " ^ name ^ "_suffix_retained=" ^
          Int.toString (Termtab.size (!suffix_memo)) ^
        " " ^ name ^ "_failed=" ^ Int.toString (!failures) ^
        " " ^ name ^ "_lookup_ms=" ^
          LargeInt.toString (Time.toMilliseconds (!elapsed))
    in {procedure = procedure, stats = stats} end
end
