(* Checked block projection for the public construction-piece source table.
   The public table is the concatenation of a bounded directory; each named
   block contains at most 32 source rows.  A request opens only its selected
   block, source, and piece row. *)
structure Comma_Semantic_B1_Construction_Piece_Projection =
struct
  structure Publication = Comma_Semantic_B1_Occurrence_Publication
  structure Selected = Comma_Selected_List_Conversion

  type catalogue =
    {root_definition: thm, directory_definition: thm,
     child_definitions: thm list, child_row_extents: int list,
     block_source_extents: int list, source_count: int}

  fun closed term = Selected.closed term
  fun sum_ints values = fold (fn value => fn total => total + value) values 0

  fun exact_definition ctxt name expected_type theorem =
    let
      val equation = Local_Defs.meta_rewrite_rule ctxt theorem
      val lhs = Thm.term_of (Thm.lhs_of equation)
      val rhs = Thm.term_of (Thm.rhs_of equation)
      val expected_name = Sign.intern_const (Proof_Context.theory_of ctxt) name
      val actual_name = (case lhs of Const (constant, _) => constant | _ => "")
      val _ = if actual_name = expected_name andalso
          fastype_of lhs = expected_type andalso fastype_of rhs = expected_type andalso
          closed lhs andalso closed rhs andalso Thm.nprems_of equation = 0 andalso
          null (Thm.hyps_of equation) andalso null (Thm.tpairs_of equation) andalso
          Context.subthy (Thm.theory_of_thm equation, Proof_Context.theory_of ctxt)
        then () else error ("B1 construction-piece definition is invalid: " ^ name)
    in equation end

  fun get_catalogue ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val pieceT = @{typ comma_semantic_b1_crt_piece_ref}
      val rowT = HOLogic.listT pieceT
      val sourceT = HOLogic.listT rowT
      val blockT = HOLogic.listT sourceT
      val directoryT = HOLogic.listT blockT
      val rootT = HOLogic.listT sourceT
      val root_name = "comma_semantic_b1_crt_construction_piece_refs"
      val directory_name = Publication.construction_piece_source_blocks_name
      val root_equation = exact_definition ctxt root_name rootT
        (Proof_Context.get_thm ctxt (root_name ^ "_def"))
      val directory_equation = exact_definition ctxt directory_name directoryT
        (Proof_Context.get_thm ctxt (directory_name ^ "_def"))
      val root_body = Thm.term_of (Thm.rhs_of root_equation)
      val (concat_head, concat_args) = strip_comb root_body
      val directory_term =
        (case (concat_head, concat_args) of
          (Const (constant, _), [directory]) =>
            if constant = @{const_name concat} then directory
            else error "B1 construction-piece root is not a block concatenation"
        | _ => error "B1 construction-piece root is not a block concatenation")
      val expected_directory = Sign.intern_const thy directory_name
      val _ = (case directory_term of
        Const (constant, T) =>
          if constant = expected_directory andalso T = directoryT then ()
          else error "B1 construction-piece root names a foreign directory"
      | _ => error "B1 construction-piece root names a malformed directory")
      val descriptor_name = "comma_semantic_b1_crt_descriptors"
      val descriptorT = HOLogic.listT @{typ comma_semantic_b1_crt_descriptor}
      val descriptor_equation = exact_definition ctxt descriptor_name descriptorT
        (Proof_Context.get_thm ctxt (descriptor_name ^ "_def"))
      val descriptor_count = length
        (HOLogic.dest_list (Thm.term_of (Thm.rhs_of descriptor_equation)))
      val directory_terms = HOLogic.dest_list
        (Thm.term_of (Thm.rhs_of directory_equation))
      val block_count = length directory_terms
      val expected_block_count =
        (descriptor_count + Publication.construction_piece_source_block_size - 1) div
          Publication.construction_piece_source_block_size
      val _ = if descriptor_count > 0 andalso descriptor_count <= 1024 andalso
          block_count = expected_block_count then ()
        else error "B1 construction-piece directory has the wrong extent"
      val _ = if fastype_of (Thm.term_of (Thm.lhs_of root_equation)) = rootT
        then () else error "B1 construction-piece root type changed"
      fun block_name index = Publication.construction_piece_source_block_name index
      fun matches_block (index, term) =
        (case term of
          Const (constant, T) => T = blockT andalso
            constant = Sign.intern_const thy (block_name index)
        | _ => false)
      val _ = if forall matches_block (map_index I directory_terms) then ()
        else error "B1 construction-piece blocks are foreign, missing, or reordered"
      val child_definitions = map_index (fn (index, _) =>
        exact_definition ctxt (block_name index) blockT
          (Proof_Context.get_thm ctxt (block_name index ^ "_def"))) directory_terms
      fun parse_block (index, theorem) =
        let
          val sources = HOLogic.dest_list (Thm.term_of (Thm.rhs_of theorem))
          val expected_sources =
            if index + 1 < block_count then Publication.construction_piece_source_block_size
            else descriptor_count - index * Publication.construction_piece_source_block_size
          val _ = if length sources = expected_sources andalso not (null sources) then ()
            else error "B1 construction-piece block has a malformed source extent"
          fun parse_source source =
            let
              val _ = if fastype_of source = sourceT andalso closed source then ()
                else error "B1 construction-piece source has the wrong type"
              val rows = HOLogic.dest_list source
              val _ = if forall (fn row => fastype_of row = rowT) rows then ()
                else error "B1 construction-piece source contains a malformed row"
              val _ = List.app (ignore o HOLogic.dest_list) rows
            in length rows end
          val parsed = map parse_source sources
        in parsed end
      val parsed_blocks = map_index parse_block child_definitions
      val block_source_extents = map length parsed_blocks
      val child_row_extents = maps I parsed_blocks
      val source_count = sum_ints block_source_extents
      val _ = if source_count = descriptor_count andalso
          length child_row_extents = source_count then ()
        else error "B1 construction-piece blocks do not cover all descriptors"
      val _ = Comma_Proof_Profile.report
        ("B1 publication stage=construction-piece-block-catalogue sources=" ^
         Int.toString source_count ^ " blocks=" ^ Int.toString block_count)
    in
      {root_definition = root_equation, directory_definition = directory_equation,
       child_definitions = child_definitions, child_row_extents = child_row_extents,
       block_source_extents = block_source_extents, source_count = source_count}: catalogue
    end

  fun make_with_catalogue ctxt name
      ({root_definition, directory_definition, child_definitions,
        child_row_extents, block_source_extents, source_count}: catalogue) =
    let
      val thy = Proof_Context.theory_of ctxt
      val natT = @{typ nat}
      val pieceT = @{typ comma_semantic_b1_crt_piece_ref}
      val rowT = HOLogic.listT pieceT
      val sourceT = HOLogic.listT rowT
      val blockT = HOLogic.listT sourceT
      val directoryT = HOLogic.listT blockT
      val rootT = HOLogic.listT sourceT
      val root = Thm.term_of (Thm.lhs_of root_definition)
      val directory = Thm.term_of (Thm.lhs_of directory_definition)
      val block_count = length child_definitions
      val root_name = Sign.intern_const thy
        "comma_semantic_b1_crt_construction_piece_refs"
      val directory_name = Sign.intern_const thy
        Publication.construction_piece_source_blocks_name
      val _ = (case root of Const (name, _) => if name = root_name then ()
        else error "B1 construction-piece catalogue has a foreign root" | _ =>
          error "B1 construction-piece catalogue root is malformed")
      val _ = (case directory of Const (name, _) => if name = directory_name then ()
        else error "B1 construction-piece catalogue has a foreign directory" | _ =>
          error "B1 construction-piece catalogue directory is malformed")
      fun canonical_definition name expected_type theorem =
        let
          val expected = exact_definition ctxt name expected_type
            (Proof_Context.get_thm ctxt (name ^ "_def"))
          val actual = exact_definition ctxt name expected_type theorem
        in
          if Thm.prop_of actual aconv Thm.prop_of expected then ()
          else error "B1 construction-piece catalogue contains a noncanonical definition"
        end
      val _ = canonical_definition
        "comma_semantic_b1_crt_construction_piece_refs" rootT root_definition
      val _ = canonical_definition Publication.construction_piece_source_blocks_name
        directoryT directory_definition
      val root_body = Thm.term_of (Thm.rhs_of root_definition)
      val (root_head, root_args) = strip_comb root_body
      val _ = (case (root_head, root_args) of
        (Const (name, _), [directory_term]) =>
          if name = @{const_name concat} andalso directory_term aconv directory then ()
          else error "B1 construction-piece catalogue root has a foreign RHS"
      | _ => error "B1 construction-piece catalogue root is not a concatenation")
      val directory_rows = HOLogic.dest_list (Thm.term_of (Thm.rhs_of directory_definition))
      fun is_block (index, term) =
        (case term of Const (name, T) => T = blockT andalso
          name = Sign.intern_const thy
            (Publication.construction_piece_source_block_name index)
        | _ => false)
      val _ = if length directory_rows = block_count andalso
          forall is_block (map_index I directory_rows) then ()
        else error "B1 construction-piece catalogue block order is invalid"
      fun named_child (index, theorem) =
        let
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val expected = Sign.intern_const thy
            (Publication.construction_piece_source_block_name index)
        in
          case lhs of
            Const (name, T) => if name = expected andalso T = blockT then true else false
          | _ => false
        end
      val _ = if forall named_child (map_index I child_definitions) then ()
        else error "Named selected-list child has a foreign canonical name"
      val _ = List.app (fn (index, theorem) =>
        canonical_definition
          (Publication.construction_piece_source_block_name index) blockT theorem)
        (map_index I child_definitions)
      val _ = if null (Thm_Deps.all_oracles
          (root_definition :: directory_definition :: child_definitions)) then ()
        else error "B1 construction-piece definitions depend on an oracle"
      val block_rows = map (fn theorem =>
        HOLogic.dest_list (Thm.term_of (Thm.rhs_of theorem))) child_definitions
      val actual_block_extents = map length block_rows
      val actual_source_extents = maps (map (length o HOLogic.dest_list)) block_rows
      val _ = if actual_block_extents = block_source_extents then ()
        else error "Named selected-list child has an inconsistent row extent"
      val _ = if actual_source_extents = child_row_extents then ()
        else error "Named selected-list child has an inconsistent row extent"
      val _ = if sum_ints block_source_extents = source_count then ()
        else error "B1 construction-piece catalogue source count is inconsistent"
      val _ = if length block_source_extents = block_count andalso
          length child_row_extents = source_count andalso
          sum_ints block_source_extents = source_count andalso
          fastype_of root = rootT andalso fastype_of directory = directoryT
        then () else error "B1 construction-piece catalogue fields disagree"
      val block_index = Free ("piece_block_index", natT)
      val source_index = Free ("piece_source_index", natT)
      val nth_blocks = Const (@{const_name nth}, directoryT --> natT --> blockT)
      val nth_sources = Const (@{const_name nth}, blockT --> natT --> sourceT)
      val selected_source = nth_sources $ (nth_blocks $ directory $ block_index) $ source_index
      val block_selector = Selected.make_named_children
        {ctxt = ctxt, name = name ^ "_blocks", root_definition = directory_definition,
         table_pattern = selected_source,
         child_name_prefix = Publication.construction_piece_source_block_prefix,
         child_definitions = child_definitions,
         child_row_extents = block_source_extents}
      val selector_procedures =
        [#procedure block_selector, #post_procedure block_selector]
      val root_eq = root_definition
      val directory_eq = directory_definition
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt
      val inner_context = fold Simplifier.add_proc selector_procedures
        (scalar_context addsimps
          (root_eq :: directory_eq ::
            @{thms concat.simps append.simps nth_append length_append
              nth_Cons' comma_selected_length_nil}))
      val source_operation_context = inner_context addsimps
        @{thms comma_selected_length_cons}
      val support_simp_rules = root_eq :: directory_eq ::
        @{thms concat.simps append.simps nth_append length_append
          nth_Cons' comma_selected_length_nil}
      val row_context = scalar_context addsimps @{thms nth_Cons'}
      val nth_root = Const (@{const_name nth}, rootT --> natT --> sourceT)
      val nth_row = Const (@{const_name nth}, sourceT --> natT --> rowT)
      val block_locator_steps = Synchronized.var
        ("b1-piece-block-locator-" ^ name) (0: int)
      fun normalize_index index_context term =
        let
          val equation = Simplifier.rewrite index_context (Thm.cterm_of ctxt term)
          val value = Thm.term_of (Thm.rhs_of equation)
        in
          (case try HOLogic.dest_number value of
            SOME (T, index) => if T = natT andalso index >= 0 then SOME (equation, index)
              else NONE
          | NONE => NONE)
        end
      fun locate index extents =
        let
          val locator_steps = Unsynchronized.ref 0
          fun seek _ _ [] = error "B1 construction-piece index is outside its catalogue"
            | seek position remaining (extent :: rest) =
                (locator_steps := !locator_steps + 1;
                 if remaining < extent then (position, remaining)
                else seek (position + 1) (remaining - extent) rest
                )
          val result = seek 0 index extents
          val _ = Synchronized.change block_locator_steps
            (fn count => count + !locator_steps)
        in result end
      val source_rows = maps (fn theorem =>
        map HOLogic.dest_list (HOLogic.dest_list (Thm.term_of (Thm.rhs_of theorem))))
        child_definitions
      val source_terms = maps (fn theorem =>
        HOLogic.dest_list (Thm.term_of (Thm.rhs_of theorem))) child_definitions
      fun expected_piece_row source row =
        List.nth (List.nth (source_rows, source), row)
      val source_cache = Synchronized.var
        ("b1-piece-source-cache-" ^ name) (Inttab.empty: thm Inttab.table)
      val source_cache_capacity = 8192
      val source_hits = Synchronized.var ("b1-piece-source-hits-" ^ name) (0: int)
      val source_builds = Synchronized.var ("b1-piece-source-builds-" ^ name) (0: int)
      val source_refusals = Synchronized.var ("b1-piece-source-refusals-" ^ name) (0: int)
      fun term_shape term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => "numeral:" ^ Syntax.string_of_typ ctxt typ ^
            "=" ^ Int.toString value
        | NONE =>
            (case try HOLogic.dest_list term of
              SOME values => "list-length:" ^ Int.toString (length values)
            | NONE =>
                (case Term.head_of term of
                  Const (constant, _) => "const:" ^ Long_Name.base_name constant
                | Free (name, _) => "free:" ^ name
                | Var ((name, _), _) => "var:" ^ name
                | Bound index => "bound:" ^ Int.toString index
                | Abs _ => "abstraction")))
      fun validate stage request expected theorem =
        let
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val lhs_matches = lhs aconv request
          val rhs_matches = rhs aconv expected
          val closed_rhs = closed rhs
          val clean_shape = Thm.nprems_of theorem = 0 andalso
            null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
        in
          if lhs_matches andalso rhs_matches andalso closed_rhs andalso clean_shape
          then theorem else error
            ("B1 construction-piece projection mismatch stage=" ^ stage ^
             " lhs_matches=" ^ Bool.toString lhs_matches ^
             " rhs_matches=" ^ Bool.toString rhs_matches ^
             " closed_rhs=" ^ Bool.toString closed_rhs ^
             " clean_shape=" ^ Bool.toString clean_shape ^
             " actual_rhs=" ^ term_shape rhs ^
             " expected_rhs=" ^ term_shape expected)
        end
      fun source_request source = nth_root $ root $ HOLogic.mk_number natT source
      fun source_selection (source, block, local_source) =
        let
          val _ = if source_count > source andalso source >= 0 then ()
            else error "B1 construction-piece source cache key is out of range"
          val block_base = sum_ints (take block block_source_extents)
          val _ = if block_base + local_source = source then ()
            else error "B1 construction-piece source cache lost block order"
          val request = source_request source
        in
          (case Inttab.lookup (Synchronized.value source_cache) source of
            SOME theorem => (Synchronized.change source_hits (fn n => n + 1); theorem)
          | NONE =>
              let
                val theorem = Simplifier.rewrite inner_context (Thm.cterm_of ctxt request)
                val expected = List.nth (source_terms, source)
                val checked = validate "source-selection" request expected theorem
                val _ = Synchronized.change source_builds (fn n => n + 1)
                val (chosen, stored) = Synchronized.change_result source_cache
                  (fn table =>
                    (case Inttab.lookup table source of
                      SOME existing => ((existing, true), table)
                    | NONE => if Inttab.size table < source_cache_capacity then
                        ((checked, true), Inttab.update (source, checked) table)
                      else ((checked, false), table)))
                val _ = if stored then ()
                  else Synchronized.change source_refusals (fn n => n + 1)
              in chosen end)
        end
      val requests = Synchronized.var ("b1-piece-projection-" ^ name)
        (0: int)
      fun source_extent source = List.nth (child_row_extents, source)
      fun source_indexed_request raw_source source_eq =
        let
          val request = nth_root $ root $ raw_source
          val index_step = Conv.arg_conv (Conv.rewr_conv source_eq)
            (Thm.cterm_of ctxt request)
        in (request, index_step) end
      fun expected_flat_source source =
        let
          val rows = List.nth (source_rows, source)
          val pieces = maps HOLogic.dest_list rows
        in HOLogic.mk_list pieceT pieces end
      fun convert_source_operation operation_name expected index_context cterm =
        let
          val request = Thm.term_of cterm
        in
          if not (closed request) then NONE
          else case strip_comb request of
            (Const (actual_operation, _), [selected_source_term]) =>
              if actual_operation <> operation_name then NONE
              else
                (case strip_comb selected_source_term of
                  (Const (source_nth, _), [root_term, raw_source]) =>
                    if source_nth <> @{const_name nth} orelse not (root_term aconv root)
                    then NONE
                    else
                      (case normalize_index index_context raw_source of
                        SOME (source_eq, source) =>
                          if source >= source_count then
                            error "B1 construction-piece source index exceeds its extent"
                          else
                            let
                              val (block, local_source) = locate source block_source_extents
                              val (source_request, source_index_step) =
                                source_indexed_request raw_source source_eq
                              val selected_source = Thm.transitive source_index_step
                                (source_selection (source, block, local_source))
                              val selected_operation = Conv.arg_conv
                                (Conv.rewr_conv selected_source) cterm
                              val reduced = Simplifier.rewrite source_operation_context
                                (Thm.rhs_of selected_operation)
                              val theorem = Thm.transitive selected_operation reduced
                              val checked = validate
                                ("source-operation:" ^ Long_Name.base_name operation_name)
                                request (expected source) theorem
                              val _ = Synchronized.change requests (fn count => count + 1)
                            in SOME checked end
                      | NONE => NONE)
                | _ => NONE)
          | _ => NONE
        end
      val size_operation = Const (@{const_name size}, sourceT --> natT)
      val concat_operation = Const (@{const_name concat}, sourceT --> rowT)
      fun source_operation_procedures (operation_name, pattern, expected) =
        let
          val rule = Selected.schematize pattern
          val before = Simplifier.make_simproc ctxt
            {name = "comma_semantic_b1_piece_source_" ^ operation_name,
             kind = Simplifier.Congproc false, lhss = [rule],
             proc = fn _ => fn index_context =>
               convert_source_operation operation_name expected index_context,
             identifier = []}
          val after = Simplifier.make_simproc ctxt
            {name = "comma_semantic_b1_piece_source_" ^ operation_name ^ "_after_operands",
             kind = Simplifier.Simproc, lhss = [rule],
             proc = fn _ => convert_source_operation operation_name expected,
             identifier = []}
        in [before, after] end
      val source_index = Free ("piece_source_operation_index", natT)
      val size_procedures = source_operation_procedures
        (@{const_name size}, size_operation $ (nth_root $ root $ source_index),
         fn source => HOLogic.mk_number natT (source_extent source))
      val concat_procedures = source_operation_procedures
        (@{const_name concat}, concat_operation $ (nth_root $ root $ source_index),
         expected_flat_source)
      fun convert index_context cterm =
        let
          val request = Thm.term_of cterm
        in
          if not (closed request) then NONE
          else
            (case strip_comb request of
              (Const (nth, _), [selected_source_term, raw_row]) =>
                (case strip_comb selected_source_term of
                  (Const (source_nth, _), [root_term, raw_source]) =>
                    if nth <> @{const_name nth} orelse source_nth <> @{const_name nth} orelse
                        not (root_term aconv root) then NONE
                    else
                      (case (normalize_index index_context raw_source,
                             normalize_index index_context raw_row) of
                        (SOME (source_eq, source), SOME (row_eq, row)) =>
                          if source >= source_count then
                            error "B1 construction-piece source index exceeds its extent"
                          else
                            let
                              val (block, local_source) = locate source block_source_extents
                              val block_base = sum_ints (take block block_source_extents)
                              val _ = if block_base + local_source = source then ()
                                else error "B1 construction-piece block locator lost source order"
                              val row_extent = List.nth (child_row_extents, source)
                              val _ = if row < row_extent then ()
                                else error "B1 construction-piece row index exceeds its source extent"
                              val source_request_raw = nth_root $ root $ raw_source
                              val source_index_step = Conv.arg_conv
                                (Conv.rewr_conv source_eq)
                                (Thm.cterm_of ctxt source_request_raw)
                              val selected_source = Thm.transitive source_index_step
                                (source_selection (source, block, local_source))
                              val selected_source_step = Conv.fun_conv
                                (Conv.arg_conv (Conv.rewr_conv selected_source)) cterm
                              val row_indexed = Conv.arg_conv
                                (Conv.rewr_conv row_eq) (Thm.rhs_of selected_source_step)
                              val reduced = Simplifier.rewrite row_context
                                (Thm.rhs_of row_indexed)
                              val theorem = Thm.transitive selected_source_step
                                (Thm.transitive row_indexed reduced)
                              val checked = validate "piece-row" request
                                (expected_piece_row source row) theorem
                              val _ = Synchronized.change requests (fn count => count + 1)
                            in SOME checked end
                      | _ => NONE)
                  | _ => NONE)
            | _ => NONE)
        end
      val selected_pattern = nth_row $
        (nth_root $ root $ Free ("piece_source", natT)) $
        Free ("piece_row", natT)
      val pattern = Selected.schematize selected_pattern
      val procedure = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_construction_piece_block_projection",
         kind = Simplifier.Congproc false, lhss = [pattern],
         proc = fn _ => fn index_context => convert index_context, identifier = []}
      val post_procedure = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_construction_piece_block_projection_after_operands",
         kind = Simplifier.Simproc, lhss = [pattern],
         proc = fn _ => convert, identifier = []}
      val source_operation_procs = size_procedures @ concat_procedures
      fun stats () =
        let val lookups = Synchronized.value requests
        in "piece_projection_lookups=" ^ Int.toString lookups ^
          " piece_block_locator_steps=" ^
            Int.toString (Synchronized.value block_locator_steps) ^ " " ^
          "piece_source_selection_hits=" ^ Int.toString (Synchronized.value source_hits) ^
          " piece_source_selection_builds=" ^ Int.toString (Synchronized.value source_builds) ^
          " piece_source_selection_capacity_refusals=" ^
            Int.toString (Synchronized.value source_refusals) ^ " " ^
          #stats block_selector () end
    in {procedure = procedure, post_procedure = post_procedure,
        support_procedures = selector_procedures @ source_operation_procs,
        support_simp_rules = support_simp_rules, stats = stats} end

  fun make ctxt = make_with_catalogue ctxt "semantic_b1_construction_piece_refs"
    (get_catalogue ctxt)
end
