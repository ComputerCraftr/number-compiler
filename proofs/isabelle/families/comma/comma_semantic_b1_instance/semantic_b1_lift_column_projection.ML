(* Select one CID row from a bounded block directory without expanding the
   concatenated lift table.  The root and every block come from the checked
   publication catalogue; the selected-list kernel conversion opens only the
   block and row demanded by the numeral. *)
structure Comma_Semantic_B1_Lift_Column_Projection =
struct
  structure Publication = Comma_Semantic_B1_Occurrence_Publication
  structure Selected = Comma_Selected_List_Conversion

  fun make ctxt =
    let
      val {root_definition, directory_definition, child_definitions,
           child_row_extents, row_count} =
        Publication.get_lift_column_id_block_definitions ctxt
      val thy = Proof_Context.theory_of ctxt
      val natT = @{typ nat}
      val rowT = HOLogic.listT natT
      val blockT = HOLogic.listT rowT
      val blocksT = HOLogic.listT blockT
      val rowsT = HOLogic.listT rowT
      (* The publication catalogue has already authenticated and normalized
         these equations.  Keep the constructor's shape/type checks below,
         but do not repeat Local_Defs.meta_rewrite_rule here. *)
      val root_equation = root_definition
      val directory_equation = directory_definition
      val lift_root = Thm.term_of (Thm.lhs_of root_equation)
      val block_directory = Thm.term_of (Thm.lhs_of directory_equation)
      val root_body = Thm.term_of (Thm.rhs_of root_equation)
      val (concat_head, concat_arguments) = strip_comb root_body
      val _ = (case (concat_head, concat_arguments) of
        (Const (name, _), [directory]) =>
          if name = @{const_name concat} andalso directory aconv block_directory then ()
          else error "B1 lift-column projection received a foreign root equation"
      | _ => error "B1 lift-column projection root is not a block concatenation")
      val block_rootT = fastype_of block_directory
      val _ = if fastype_of lift_root = rowsT andalso block_rootT = blocksT then ()
        else error "B1 lift-column projection has mismatched table types"
      val block_index = Free ("lift_block_index", natT)
      val row_index = Free ("lift_block_row", natT)
      val nth_blocks = Const (@{const_name nth}, blocksT --> natT --> blockT)
      val nth_rows = Const (@{const_name nth}, blockT --> natT --> rowT)
      val block_pattern = nth_rows $ (nth_blocks $ block_directory $ block_index) $ row_index
      val block_selector = Selected.make_named_children
        {ctxt = ctxt, name = "semantic_b1_lift_column_blocks",
         root_definition = directory_definition, table_pattern = block_pattern,
         child_name_prefix = Publication.lift_column_id_block_prefix,
         child_definitions = child_definitions,
         child_row_extents = child_row_extents}
      val block_procedures =
        [#procedure block_selector, #post_procedure block_selector]
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt
      val block_context = fold Simplifier.add_proc block_procedures
        (scalar_context addsimps
          (root_equation :: directory_equation ::
            @{thms concat.simps append.simps nth_append length_append
              comma_selected_length_nil}))
      fun canonical_nat term =
        (case try HOLogic.dest_number term of
          SOME (typ, value) => typ = natT andalso value >= 0
        | NONE => false)
      fun normalize_index index_context index_ct =
        let
          val selected = Simplifier.rewrite index_context index_ct
          val first_value = Thm.term_of (Thm.rhs_of selected)
        in
          if canonical_nat first_value then SOME selected
          else
            let
              val arithmetic = Simplifier.rewrite scalar_context (Thm.rhs_of selected)
              val arithmetic_value = Thm.term_of (Thm.rhs_of arithmetic)
            in
              if canonical_nat arithmetic_value then
                SOME (Thm.transitive selected arithmetic)
              else if can (Axclass.overload_conv ctxt) (Thm.rhs_of arithmetic) then
                let
                  val overloaded = Axclass.overload_conv ctxt (Thm.rhs_of arithmetic)
                  val reduced = Simplifier.rewrite scalar_context (Thm.rhs_of overloaded)
                  val final_value = Thm.term_of (Thm.rhs_of reduced)
                in
                  if canonical_nat final_value then
                    SOME (Thm.transitive selected
                      (Thm.transitive arithmetic (Thm.transitive overloaded reduced)))
                  else NONE
                end
              else NONE
            end
        end
      fun block_offset index =
        let
          fun seek _ _ [] = error "B1 lift-column index is outside its block directory"
            | seek block remaining (extent :: rest) =
                if remaining < extent then (block, remaining)
                else seek (block + 1) (remaining - extent) rest
        in seek 0 index child_row_extents end
      fun expected_row block row =
        let
          val theorem = List.nth (child_definitions, block)
          val values = HOLogic.dest_list (Thm.term_of (Thm.rhs_of theorem))
        in List.nth (values, row) end
      fun validate request theorem expected =
        let
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val rhs = Thm.term_of (Thm.rhs_of theorem)
        in
          if lhs aconv request andalso rhs aconv expected andalso
              Selected.closed rhs andalso Thm.nprems_of theorem = 0 andalso
              null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
              null (Thm_Deps.all_oracles [theorem]) then theorem
          else error "B1 lift-column block lookup returned a mismatched or open theorem"
        end
      val lookup_count = Synchronized.var
        "b1-lift-block-lookups" (0: int)
      val locator_visits = Synchronized.var
        "b1-lift-block-locator-visits" (0: int)
      val size_constant = Const (@{const_name size}, rowsT --> natT)
      val length_request = size_constant $ lift_root
      fun validate_length theorem =
        let
          val rhs = Thm.term_of (Thm.rhs_of theorem)
          val exact_count = HOLogic.mk_number natT row_count
        in
          if Thm.term_of (Thm.lhs_of theorem) aconv length_request andalso
              rhs aconv exact_count andalso Selected.closed rhs andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso
              null (Thm_Deps.all_oracles [theorem]) then theorem
          else error "B1 lift-column length did not match its authenticated row count"
        end
      fun convert_length cterm =
        let
          val request = Thm.term_of cterm
        in
          if request aconv length_request then
            SOME (validate_length (Simplifier.rewrite block_context cterm))
          else NONE
        end
      fun convert index_context cterm =
        let
          val request = Thm.term_of cterm
        in
          if not (Selected.closed request) then NONE
          else
            (case strip_comb request of
              (Const (name, _), [table]) =>
                if name = @{const_name size} andalso table aconv lift_root
                then convert_length cterm else NONE
            | (Const (name, _), [table, raw_index]) =>
                if name <> @{const_name nth} orelse not (table aconv lift_root) then NONE
                else
                  (case normalize_index index_context (Thm.cterm_of ctxt raw_index) of
                    NONE => NONE
                  | SOME index_equation =>
                      let
                        val (index_type, index) = HOLogic.dest_number
                          (Thm.term_of (Thm.rhs_of index_equation))
                        val _ = if index_type = natT andalso index >= 0 andalso
                            index < row_count then ()
                          else error "B1 lift-column index exceeds its authenticated extent"
                        val (block, row) = block_offset index
                        val request_step = Conv.arg_conv
                          (Conv.rewr_conv index_equation) cterm
                        val reduced = Simplifier.rewrite block_context
                          (Thm.rhs_of request_step)
                        val theorem = Thm.transitive request_step reduced
                        val checked = validate request theorem (expected_row block row)
                        val _ = Synchronized.change lookup_count (fn count => count + 1)
                        val _ = Synchronized.change locator_visits
                          (fn count => count + block + 1)
                      in SOME checked end)
            | _ => NONE)
        end
      val index_pattern = Selected.schematize
        (Const (@{const_name nth}, rowsT --> natT --> rowT) $ lift_root $
          Free ("lift_column_index", natT))
      val length_pattern = Selected.schematize
        (size_constant $ lift_root)
      val procedure = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_lift_column_block_lookup",
         kind = Simplifier.Congproc false, lhss = [index_pattern, length_pattern],
         proc = fn _ => fn index_context => convert index_context, identifier = []}
      val post_procedure = Simplifier.make_simproc ctxt
        {name = "comma_semantic_b1_lift_column_block_lookup_after_operands",
         kind = Simplifier.Simproc, lhss = [index_pattern, length_pattern],
         proc = fn _ => convert, identifier = []}
      fun stats () =
        "lift_block_lookups=" ^ Int.toString (Synchronized.value lookup_count) ^
        " lift_block_locator_visits=" ^ Int.toString (Synchronized.value locator_visits)
    in
      {procedure = procedure, post_procedure = post_procedure, stats = stats}
    end

  fun check_fixtures expect_error ctxt evaluation_context =
    let
      val {root_definition, directory_definition, child_definitions,
           child_row_extents, row_count} =
        Publication.get_lift_column_id_block_definitions ctxt
      val natT = @{typ nat}
      val rowT = HOLogic.listT natT
      val root = Thm.term_of (Thm.lhs_of root_definition)
      val nth_root = Const (@{const_name nth}, fastype_of root --> natT --> rowT)
      val _ = if row_count = 2444 andalso length child_definitions = 39 andalso
          child_row_extents = replicate 38 64 @ [12] then ()
        else error "B1 lift-column block catalogue has unexpected boundaries"
      fun block_offset index =
        let
          fun seek _ _ [] = error "B1 lift-column fixture index exceeded blocks"
            | seek block remaining (extent :: rest) =
                if remaining < extent then (block, remaining)
                else seek (block + 1) (remaining - extent) rest
        in seek 0 index child_row_extents end
      fun expected_row index =
        let
          val (block, offset) = block_offset index
          val equation = List.nth (child_definitions, block)
          val values = HOLogic.dest_list (Thm.term_of (Thm.rhs_of equation))
        in List.nth (values, offset) end
      fun check_index index =
        let
          val request = nth_root $ root $ HOLogic.mk_number natT index
          val theorem = Simplifier.rewrite evaluation_context
            (Thm.cterm_of ctxt request)
        in
          if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
              Thm.term_of (Thm.rhs_of theorem) aconv expected_row index andalso
              Selected.closed (Thm.term_of (Thm.rhs_of theorem)) andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso
              null (Thm_Deps.all_oracles [theorem]) then ()
          else error ("B1 selected lift block failed at row " ^ Int.toString index)
        end
      val _ = List.app check_index [0, 1, 63, 64, 2443]
      val size_root = Const (@{const_name size}, fastype_of root --> natT) $ root
      val size_theorem = Simplifier.rewrite evaluation_context
        (Thm.cterm_of ctxt size_root)
      val _ = if Thm.term_of (Thm.lhs_of size_theorem) aconv size_root andalso
          Thm.term_of (Thm.rhs_of size_theorem) aconv HOLogic.mk_number natT row_count andalso
          null (Thm_Deps.all_oracles [size_theorem]) then ()
        else error "B1 lift-column bounded root length is not exact"
      val _ = expect_bad_index ctxt evaluation_context
        (nth_root $ root $ HOLogic.mk_number natT row_count)
      val directory_equation = directory_definition
      val directory = Thm.term_of (Thm.lhs_of directory_equation)
      val blockT = HOLogic.listT rowT
      val directoryT = HOLogic.listT blockT
      val nth_block = Const (@{const_name nth}, directoryT --> natT --> blockT)
      val nth_row = Const (@{const_name nth}, blockT --> natT --> rowT)
      val pattern = nth_row $ (nth_block $ directory $ Free ("block", natT)) $
        Free ("row", natT)
      fun selector prefix extents = Selected.make_named_children
        {ctxt = ctxt, name = "lift_block_fixture", root_definition = directory_definition,
         table_pattern = pattern, child_name_prefix = prefix,
         child_definitions = child_definitions, child_row_extents = extents}
      val _ = expect_error "Named selected-list child has a foreign canonical name"
        (fn () => selector "comma_semantic_b1_crt_construction_piece_source_"
          child_row_extents)
      val wrong_extents = (case child_row_extents of
        first :: rest => (first + 1) :: rest
      | [] => error "B1 lift-column fixture has no blocks")
      val _ = expect_error "Named selected-list child has an inconsistent row extent"
        (fn () => selector Publication.lift_column_id_block_prefix wrong_extents)
    in () end

  and expect_bad_index ctxt context request =
    (case Exn.capture (fn () => Simplifier.rewrite context
        (Thm.cterm_of ctxt request)) () of
      Exn.Exn (ERROR message) =>
        if message = "B1 lift-column index exceeds its authenticated extent" then ()
        else error ("B1 out-of-range block fixture failed for the wrong reason: " ^ message)
    | Exn.Exn exn => Exn.reraise exn
    | Exn.Res _ => error "B1 lift-column projection accepted an out-of-range row")
end
