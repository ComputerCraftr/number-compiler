(* Kernel-backed regressions for the closed DAG table and its one-node
   proof-producing interpreter. *)
structure Comma_Semantic_B1_Column_Regression =
struct
  structure Conversion = Comma_Semantic_B1_Column_Conversion
  structure Operations = Comma_Semantic_B1_CRT_Operation_Conversion
  structure Publication = Comma_Semantic_B1_Occurrence_Publication

  fun require condition message = if condition then () else error message

  fun expect_error expected label operation =
    (case Exn.capture operation () of
      Exn.Exn (ERROR message) =>
        if message = expected then ()
        else error (label ^ " failed for the wrong reason: " ^ message)
    | Exn.Exn exn => Exn.reraise exn
    | Exn.Res _ => error (label ^ " was unexpectedly accepted"))

  fun clean_theorem theorem =
    Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
    null (Thm.tpairs_of theorem) andalso
    null (Thm_Deps.all_oracles [theorem])

  fun bounded_shift_context ctxt = Operations.operation_context ctxt

  fun check_bounded_shifts ctxt =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val shift = Const (@{const_name comma_crt_shift},
        natT --> columnT --> columnT)
      val node = Const (@{const_name Comma_CRT_Node},
        natT --> HOLogic.listT columnT --> columnT)
      val boolean = Const (@{const_name Comma_CRT_Bool}, @{typ bool} --> columnT)
      val false_column = boolean $ @{term False}
      val true_column = boolean $ @{term True}
      val source = node $ HOLogic.mk_number natT 1 $
        HOLogic.mk_list columnT [false_column, false_column, true_column]
      val context = bounded_shift_context
        (Comma_Entry_Arithmetic.natural_context ctxt)
      fun pretty term = XML.content_of (YXML.parse_body
        (Syntax.string_of_term ctxt term))
      val cases =
        [(1, [false_column, true_column, false_column]),
         (2, [true_column, false_column, false_column]),
         (924, [false_column, false_column, true_column])]
      fun check (amount, children) =
        let
          val request = shift $ HOLogic.mk_number natT amount $ source
          val expected = node $ HOLogic.mk_number natT 1 $
            HOLogic.mk_list columnT children
          val theorem = Simplifier.rewrite context (Thm.cterm_of ctxt request)
        in
          require (Thm.term_of (Thm.lhs_of theorem) aconv request andalso
              Thm.term_of (Thm.rhs_of theorem) aconv expected andalso
              clean_theorem theorem)
            ("B1 bounded rotation failed for shift " ^ Int.toString amount ^
             "; rhs=" ^ pretty (Thm.term_of (Thm.rhs_of theorem)))
        end
    in List.app check cases end

  (* Run this from the occurrence cache's own evaluation context, after both
     simprocs have been installed.  It exercises the real precedence boundary:
     an owned DAG application must reach the column interpreter, while a
     plain constructor remains a generic CRT value and must not open a DAG node. *)
  fun check_cache_column_dispatch ctxt evaluation_context operation_context
      post_procedure column_value known_column node_count step head_opens =
    let
      val columnT = @{typ comma_crt_column}
      val supported = Const (@{const_name comma_crt_supported},
        columnT --> @{typ bool})
      fun check_owned_scalar cid expected =
        let
          val owned = column_value cid
          val owned_request = supported $ owned
          val before_owned = head_opens ()
          val theorem = Simplifier.rewrite evaluation_context
            (Thm.cterm_of ctxt owned_request)
          val after_owned = head_opens ()
        in
          require (known_column owned andalso
              Thm.term_of (Thm.lhs_of theorem) aconv owned_request andalso
              Thm.term_of (Thm.rhs_of theorem) aconv expected andalso
              clean_theorem theorem andalso after_owned > before_owned)
            ("B1 production cache did not route scalar CID " ^
              Int.toString cid ^ " through its interpreter")
        end
      val _ = check_owned_scalar 0 @{term False}
      val _ = check_owned_scalar 1 @{term True}

      val generic = Const (@{const_name Comma_CRT_Bool},
        @{typ bool} --> columnT) $ @{term True}
      val generic_request = supported $ generic
      val _ = require (not (known_column generic))
        "B1 generic column was claimed by the named-column authority"
      val before_generic = head_opens ()
      val generic_theorem = Simplifier.rewrite evaluation_context
        (Thm.cterm_of ctxt generic_request)
      val after_generic = head_opens ()
      val _ = require (Thm.term_of (Thm.lhs_of generic_theorem) aconv generic_request andalso
          Thm.term_of (Thm.rhs_of generic_theorem) aconv @{term True} andalso
          clean_theorem generic_theorem andalso after_generic = before_generic)
        "B1 production cache failed its generic-column fallback or opened a foreign DAG node"

      val _ = Comma_Semantic_B1_Lift_Column_Projection.check_fixtures
        (fn expected => expect_error expected "B1 lift-column fixture")
        ctxt evaluation_context

      val columnsT = HOLogic.listT columnT
      val columns = Const (Sign.intern_const (Proof_Context.theory_of ctxt)
        "comma_semantic_b1_crt_columns", columnsT)
      val _ = require (node_count > 4)
        "B1 production dispatch fixture needs three distinct owned nodes"
      fun table_request cid = supported $ (Const (@{const_name nth},
        columnsT --> @{typ nat} --> columnT) $ columns $
          HOLogic.mk_number @{typ nat} cid)
      (* Ascending fresh CIDs cannot have been opened as earlier children. *)
      val post_request = table_request 2
      val post_context =
        fold Simplifier.add_simp
          [Proof_Context.get_thm ctxt "comma_semantic_b1_crt_columns_def",
           Proof_Context.get_thm ctxt "comma_semantic_b1_crt_column_count_def",
           @{thm comma_semantic_b1_crt_columns_for_nth}]
          (Operations.operation_context (Comma_Entry_Arithmetic.natural_context ctxt))
        |> Simplifier.add_proc post_procedure
      val before_post = head_opens ()
      val post_theorem = Simplifier.rewrite post_context
        (Thm.cterm_of ctxt post_request)
      val after_post = head_opens ()
      val post_value = Thm.term_of (Thm.rhs_of post_theorem)
      val _ = require (Thm.term_of (Thm.lhs_of post_theorem) aconv post_request andalso
          (post_value aconv @{term True} orelse post_value aconv @{term False}) andalso
          clean_theorem post_theorem andalso after_post > before_post)
        "B1 post-operand Simproc did not revisit support after table selection"

      val selected_request = table_request 3
      val before_selected = head_opens ()
      val selected_theorem = Simplifier.rewrite evaluation_context
        (Thm.cterm_of ctxt selected_request)
      val after_selected = head_opens ()
      val selected_value = Thm.term_of (Thm.rhs_of selected_theorem)
      val _ = require (Thm.term_of (Thm.lhs_of selected_theorem) aconv selected_request andalso
          (selected_value aconv @{term True} orelse selected_value aconv @{term False}) andalso
          clean_theorem selected_theorem andalso after_selected > before_selected)
        "B1 production context did not retry column support after selecting its table CID"

      val owned_node = column_value 4
      val owned_node_request = supported $ owned_node
      val before_node = head_opens ()
      val node_theorem = Simplifier.rewrite operation_context
        (Thm.cterm_of ctxt owned_node_request)
      val after_node = head_opens ()
      val node_value = Thm.term_of (Thm.rhs_of node_theorem)
      val _ = require (known_column owned_node andalso
          Thm.term_of (Thm.lhs_of node_theorem) aconv owned_node_request andalso
          (node_value aconv @{term True} orelse node_value aconv @{term False}) andalso
          clean_theorem node_theorem andalso after_node > before_node)
        "B1 operation context did not evaluate an owned DAG node exactly"

      val foreign = column_value node_count
      val _ = require (not (known_column foreign))
        "B1 out-of-range CID passed named-column authority"
      val _ = expect_error "B1 column lookup requested a foreign CID"
        "out-of-range production column" (fn () => step node_count)
      val foreign_request = supported $ foreign
      val foreign_theorem = Simplifier.rewrite operation_context
        (Thm.cterm_of ctxt foreign_request)
      val _ = require (Thm.term_of (Thm.lhs_of foreign_theorem) aconv foreign_request andalso
          not (Thm.term_of (Thm.rhs_of foreign_theorem) aconv @{term True}) andalso
          clean_theorem foreign_theorem)
        "B1 production cache accepted an out-of-range named column"
    in () end

  fun first_column_node theorem =
    let
      val body = Thm.term_of (Thm.rhs_of theorem)
    in
      (case strip_comb body of
        (Const (name, _), [level_term, children_term]) =>
          if name = @{const_name Comma_CRT_Node} then
            let
              val (level_type, level) = HOLogic.dest_number level_term
              val children = HOLogic.dest_list children_term
            in
              if level_type = @{typ nat} andalso not (null children) then
                (body, level, children)
              else error "B1 regression first DAG node has an invalid shape"
            end
          else error "B1 regression expected the first non-Boolean DAG node"
      | _ => error "B1 regression expected a shallow first DAG node")
    end

  fun swap_adjacent_distinct [] = NONE
    | swap_adjacent_distinct [_] = NONE
    | swap_adjacent_distinct (left :: right :: rest) =
        if left aconv right then
          Option.map (fn tail => left :: tail)
            (swap_adjacent_distinct (right :: rest))
        else SOME (right :: left :: rest)

  fun check_template_projection ctxt =
    let
      val natT = @{typ nat}
      val ids_rowT = HOLogic.listT natT
      val ids_tableT = HOLogic.listT ids_rowT
      val ids_table = Const (Sign.intern_const (Proof_Context.theory_of ctxt)
        "comma_semantic_b1_crt_template_column_ids", ids_tableT)
      val ids_nth = Const (@{const_name nth},
        ids_tableT --> natT --> ids_rowT)
      val ids_pattern = ids_nth $ ids_table $ Free ("index", natT)
      val template_ids_selector = Comma_Selected_List_Conversion.make
        {ctxt = ctxt, name = "regression_template_column_ids",
         root_definition = Proof_Context.get_thm ctxt
           "comma_semantic_b1_crt_template_column_ids_def",
         table_pattern = ids_pattern,
         extents = [1024]}
      val descriptors_definition = Proof_Context.get_thm ctxt
        "comma_semantic_b1_crt_descriptors_def"
      val descriptors_table = Thm.term_of
        (Thm.lhs_of (Local_Defs.meta_rewrite_rule ctxt descriptors_definition))
      val descriptorT = (case fastype_of descriptors_table of
        Type (@{type_name list}, [entryT]) => entryT
      | _ => error "B1 occurrence descriptors are not a list")
      val descriptors_nth = Const (@{const_name nth},
        fastype_of descriptors_table --> natT --> descriptorT)
      val descriptors_pattern = descriptors_nth $ descriptors_table $
        Free ("index", natT)
      val descriptors_selector = Comma_Selected_List_Conversion.make
        {ctxt = ctxt, name = "regression_occurrence_descriptors",
         root_definition = descriptors_definition,
         table_pattern = descriptors_pattern,
         extents = [1024]}
      val selected_context = fold Simplifier.add_proc
        [#procedure template_ids_selector, #post_procedure template_ids_selector,
         #procedure descriptors_selector, #post_procedure descriptors_selector]
        (ctxt addsimps @{thms distinct.simps option.case list.case list.map
          length_map prod.case Let_def comma_semantic_b1_crt_lift_descriptor.make_def
          comma_semantic_b1_crt_lift_descriptor.select_convs})
      val descriptor_zero = descriptors_nth $ descriptors_table $
        HOLogic.mk_number natT 0
      val descriptor_template_index = Const (@{const_name fst},
        descriptorT --> natT) $ descriptor_zero
      val nested_ids_request = ids_nth $ ids_table $ descriptor_template_index
      val nested_ids_theorem = Simplifier.rewrite selected_context
        (Thm.cterm_of ctxt nested_ids_request)
      val nested_ids = HOLogic.dest_list (Thm.term_of (Thm.rhs_of nested_ids_theorem))
      val count_definition = Local_Defs.meta_rewrite_rule ctxt
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_column_count_def")
      val column_count = (case try HOLogic.dest_number
          (Thm.term_of (Thm.rhs_of count_definition)) of
        SOME (typ, value) => if typ = natT then value
          else error "B1 column count has the wrong type"
      | NONE => error "B1 column count is not a numeral")
      fun valid_cid cid =
        (case try HOLogic.dest_number cid of
          SOME (typ, value) => typ = natT andalso value >= 0 andalso
            value < column_count
        | NONE => false)
      val _ = if Thm.term_of (Thm.lhs_of nested_ids_theorem) aconv nested_ids_request andalso
          Thm.nprems_of nested_ids_theorem = 0 andalso
          null (Thm.hyps_of nested_ids_theorem) andalso
          null (Thm.tpairs_of nested_ids_theorem) andalso
          forall valid_cid nested_ids then ()
        else error "B1 nested selected-list did not resolve a sibling descriptor index"
      val descriptor_one = descriptors_nth $ descriptors_table $ @{term "Suc 0"}
      val descriptor_one_index = Const (@{const_name fst}, descriptorT --> natT) $
        descriptor_one
      val computed_index_request = ids_nth $ ids_table $ descriptor_one_index
      val computed_index_theorem = Simplifier.rewrite selected_context
        (Thm.cterm_of ctxt computed_index_request)
      val computed_index_row = HOLogic.dest_list
        (Thm.term_of (Thm.rhs_of computed_index_theorem))
      val _ = if Thm.term_of (Thm.lhs_of computed_index_theorem)
            aconv computed_index_request andalso clean_theorem computed_index_theorem andalso
            forall valid_cid computed_index_row
          then () else error
            "B1 post-operand template lookup failed for a computed descriptor index"
      val out_of_range_descriptor = descriptors_nth $ descriptors_table $
        HOLogic.mk_number natT 1024
      val malformed_nested_ids = ids_nth $ ids_table $
        (Const (@{const_name fst}, descriptorT --> natT) $ out_of_range_descriptor)
      val rejected_nested_ids = Exn.capture
        (fn () => Simplifier.rewrite selected_context
          (Thm.cterm_of ctxt malformed_nested_ids)) ()
      val _ = (case rejected_nested_ids of
          Exn.Exn (ERROR message) => if message =
              "Selected-list nested index exceeds its depth-specific extent"
            then () else error message
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "B1 nested selected-list accepted an out-of-range sibling index")
      val projection = Conversion.make_template_projection ctxt selected_context
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_templates_def")
      val template_rowT = HOLogic.listT @{typ comma_crt_column}
      val templates_table = Const (Sign.intern_const
        (Proof_Context.theory_of ctxt) "comma_semantic_b1_crt_templates",
        HOLogic.listT template_rowT)
      val template_nth = Const (@{const_name nth},
        fastype_of templates_table --> natT --> template_rowT)
      val computed_template_request = template_nth $ templates_table $ descriptor_one_index
      val projection_context = fold Simplifier.add_proc
        [#procedure projection, #post_procedure projection] selected_context
      val computed_template_equation = Simplifier.rewrite projection_context
        (Thm.cterm_of ctxt computed_template_request)
      val computed_template_row = HOLogic.dest_list
        (Thm.term_of (Thm.rhs_of computed_template_equation))
      val ids_for_descriptor = computed_index_row
      val dag_equation = Local_Defs.meta_rewrite_rule ctxt
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_column_node_dag_def")
      val dag_constant = Thm.term_of (Thm.lhs_of dag_equation)
      val column_at = Const (@{const_name comma_semantic_b1_crt_column_at},
        @{typ comma_semantic_b1_crt_column_dag} --> natT --> @{typ comma_crt_column})
      val expected_template_row = map (fn cid => column_at $ dag_constant $ cid)
        ids_for_descriptor
      val _ = if Thm.term_of (Thm.lhs_of computed_template_equation)
            aconv computed_template_request andalso clean_theorem computed_template_equation andalso
            ListPair.allEq (op aconv) (computed_template_row, expected_template_row)
          then () else error
            "B1 post-operand projection changed a computed descriptor template row"
      val computed_lift_template_cid = @{term
        "comma_semantic_b1_crt_lift_descriptor_template_cid
          (comma_semantic_b1_crt_lift_descriptor.make 28 0 0 0)"}
      val lift_template_request = template_nth $ templates_table $
        computed_lift_template_cid
      val lift_template_equation = Simplifier.rewrite projection_context
        (Thm.cterm_of ctxt lift_template_request)
      val direct_template_zero = Simplifier.rewrite projection_context
        (Thm.cterm_of ctxt (template_nth $ templates_table $ HOLogic.mk_number natT 0))
      val _ = if Thm.term_of (Thm.lhs_of lift_template_equation)
            aconv lift_template_request andalso clean_theorem lift_template_equation andalso
            Thm.term_of (Thm.rhs_of lift_template_equation) aconv
              Thm.term_of (Thm.rhs_of direct_template_zero)
          then () else error
            "B1 lift-descriptor getter did not select the exact canonical template-zero row"
      val _ = #check_fixtures projection ()
    in () end

  fun check ctxt =
    let
      val _ = Comma_Proof_Profile.report "B1 column regression stage=check-start"
      val _ = check_template_projection ctxt
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=template-projection-fixtures-complete"
      val thy = Proof_Context.theory_of ctxt
      val canonical_block_name = Sign.intern_const thy
        "comma_semantic_b1_crt_column_block_7"
      val foreign_block_name = Long_Name.qualify "Regression"
        "comma_semantic_b1_crt_column_block_7"
      val _ = require
          (Comma_Semantic_B1_Column_Catalog.parse_block_index canonical_block_name = SOME 7 andalso
           Comma_Semantic_B1_Column_Catalog.canonical_block_name thy 7 canonical_block_name andalso
           not (Comma_Semantic_B1_Column_Catalog.canonical_block_name thy 7 foreign_block_name) andalso
           Comma_Semantic_B1_Column_Catalog.parse_block_index
             "comma_semantic_b1_crt_column_block_07" = NONE andalso
           Comma_Semantic_B1_Column_Catalog.parse_block_index
             "comma_semantic_b1_crt_column_block_7junk" = NONE)
          "canonical or noncanonical block-name regression failed"
      val definitions = Publication.get_definitions ctxt
      val table_definition = (case filter (fn theorem =>
          let val equation = Local_Defs.meta_rewrite_rule ctxt theorem
          in (case Thm.term_of (Thm.lhs_of equation) of
            Const (name, _) => name = Sign.intern_const
              (Proof_Context.theory_of ctxt)
              "comma_semantic_b1_crt_column_node_dag"
          | _ => false) end) definitions of
          [definition] => definition
        | _ => error "B1 regression expected one closed global DAG definition")
      val _ = expect_error "B1 column block authority has missing or foreign definitions"
        "duplicate DAG authority" (fn () => Conversion.make ctxt
          (definitions @ [table_definition]))
      val equation = Local_Defs.meta_rewrite_rule ctxt table_definition
      val _ = Comma_Semantic_B1_Column_Lookup_Regression.check_directory_interval_cache
        ctxt definitions table_definition
      val table_constant = Thm.term_of (Thm.lhs_of equation)
      val stale_definition = Thm.reflexive (Thm.cterm_of ctxt table_constant)
      val _ = expect_error "B1 column DAG has a malformed directory node"
        "stale table value" (fn () => Conversion.make ctxt [stale_definition])
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=stale-and-authority-fixtures-complete"

      val natT = @{typ nat}
      val blockT = @{typ comma_semantic_b1_crt_column_block}
      val empty_block = @{term Comma_B1_CRT_Column_Block_Empty}
      val block_node = Const (@{const_name Comma_B1_CRT_Column_Block_Node},
        natT --> natT --> HOLogic.listT natT --> blockT --> blockT --> blockT)
      fun serialized_node level child_ids = block_node $
        HOLogic.mk_number natT 2 $ HOLogic.mk_number natT level $
        HOLogic.mk_list natT (map (HOLogic.mk_number natT) child_ids) $
        empty_block $ empty_block
      val _ = expect_error "B1 column DAG node has an invalid level"
        "malformed-level block decoder" (fn () =>
          Comma_Semantic_B1_Column_Catalog.parse_block_tree 2 (serialized_node 4 [0, 1, 0, 1]))
      val _ = expect_error "B1 column DAG node has an invalid radix shape"
        "malformed-radix block decoder" (fn () =>
          Comma_Semantic_B1_Column_Catalog.parse_block_tree 2 (serialized_node 0 [0, 1, 0]))
      val forward_nodes : Comma_Semantic_B1_Column_Catalog.node list =
        [{cid = 2, level = 0, children = [3, 0, 1, 0]},
         {cid = 3, level = 1, children = [0, 1, 0]}]
      val foreign_nodes : Comma_Semantic_B1_Column_Catalog.node list =
        [{cid = 2, level = 0, children = [9, 0, 1, 0]}]
      val _ = expect_error
        "B1 column DAG has a foreign, forward, or shallow child CID"
        "forward child CID" (fn () => Comma_Semantic_B1_Column_Catalog.validate_nodes forward_nodes)
      val _ = expect_error
        "B1 column DAG has a foreign, forward, or shallow child CID"
        "foreign child CID" (fn () => Comma_Semantic_B1_Column_Catalog.validate_nodes foreign_nodes)

      val converter = Conversion.make ctxt definitions
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=converter-constructed"
      val known_column = #known_column converter
      val column_value = #column_value converter
      fun find_header_parent cid =
        if cid >= #node_count converter then
          error "B1 header-admission fixture has no nonterminal parent level"
        else
          (case #cofactor_node_level converter cid of
            SOME level => if level > 0 then (cid, level)
              else find_header_parent (cid + 1)
          | NONE => find_header_parent (cid + 1))
      val (header_cid, _) = find_header_parent 2
      val admitted = Const (@{const_name comma_crt_admitted},
        @{typ nat} --> @{typ comma_crt_column} --> @{typ bool})
      val header_request = admitted $ @{term "Suc 0"} $ column_value header_cid
      val header_context = Simplifier.add_proc (#procedure converter)
        (Operations.operation_context (Comma_Entry_Arithmetic.natural_context ctxt))
      val header_misses_before = #step_misses converter ()
      val header_theorem = Simplifier.rewrite header_context
        (Thm.cterm_of ctxt header_request)
      val header_misses_after = #step_misses converter ()
      val _ = require (Thm.term_of (Thm.lhs_of header_theorem) aconv header_request andalso
          Thm.term_of (Thm.rhs_of header_theorem) aconv @{term True} andalso
          clean_theorem header_theorem andalso
          header_misses_after = header_misses_before)
        "B1 Suc-level admission did not use the checked header without opening child steps"
      val column_listT = HOLogic.listT @{typ comma_crt_column}
      val list_all = Const (@{const_name list_all},
        (@{typ comma_crt_column} --> @{typ bool}) --> column_listT --> @{typ bool})
      val admitted_predicate = Const (@{const_name comma_crt_admitted},
        @{typ nat} --> @{typ comma_crt_column} --> @{typ bool}) $
        HOLogic.mk_number @{typ nat} 0
      val columns_constant = Const (Sign.intern_const thy
        "comma_semantic_b1_crt_columns", column_listT)
      val all_columns_target = list_all $ admitted_predicate $ columns_constant
      val all_columns_theorem = #prove_columns_admitted converter
        (Thm.cterm_of ctxt all_columns_target)
      val _ = require (Thm.prop_of all_columns_theorem aconv
          HOLogic.mk_Trueprop all_columns_target andalso clean_theorem all_columns_theorem)
        "B1 generic all-column admission theorem changed its exact target"
      val bad_lower_target = list_all $
        (Const (@{const_name comma_crt_admitted},
          @{typ nat} --> @{typ comma_crt_column} --> @{typ bool}) $
          HOLogic.mk_number @{typ nat} 1) $ columns_constant
      val _ = expect_error
        "B1 admission target is not the published zero-level column list"
        "nonzero admission lower bound" (fn () => #prove_columns_admitted converter
          (Thm.cterm_of ctxt bad_lower_target))
      val dag_constant = Const (Sign.intern_const thy
        "comma_semantic_b1_crt_column_node_dag", @{typ comma_semantic_b1_crt_column_dag})
      val count_constant = Const (Sign.intern_const thy
        "comma_semantic_b1_crt_column_count", @{typ nat})
      val columns_for = Const (@{const_name comma_semantic_b1_crt_columns_for},
        @{typ comma_semantic_b1_crt_column_dag} --> @{typ nat} --> column_listT)
      val computed_columns_target = list_all $ admitted_predicate $
        (columns_for $ dag_constant $ count_constant)
      val _ = expect_error "B1 admission target uses a nonconstant column table"
        "computed rather than named column authority"
        (fn () => #prove_columns_admitted converter
          (Thm.cterm_of ctxt computed_columns_target))
      val node_cid = 2
      val node_constant = column_value node_cid
      val foreign_column = column_value (#node_count converter)
      val empty_dag = @{term Comma_B1_CRT_Column_DAG_Empty}
      val column_at = Const (@{const_name comma_semantic_b1_crt_column_at},
        @{typ comma_semantic_b1_crt_column_dag} --> @{typ nat} -->
          @{typ comma_crt_column})
      val stale_column = column_at $ empty_dag $ HOLogic.mk_number @{typ nat} node_cid
      val nonliteral_column = column_at $ dag_constant $ Free ("cid", @{typ nat})
      val missing_cid = #node_count converter
      val missing_column = column_value missing_cid
      val _ = require (known_column node_constant andalso
          not (known_column foreign_column) andalso not (known_column stale_column) andalso
          not (known_column nonliteral_column) andalso not (known_column missing_column))
        "B1 DAG accepted a foreign, out-of-range, or nonliteral CID/table application"
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=missing-cid-lookup-start"
      val block_definitions = filter (fn theorem =>
        let
          val equation = Local_Defs.meta_rewrite_rule ctxt theorem
          val left = Thm.term_of (Thm.lhs_of equation)
        in
          (case left of Const (name, _) =>
              is_some (Comma_Semantic_B1_Column_Catalog.parse_block_index name)
            | _ => false)
        end) definitions
      val last_block_definition = List.last block_definitions
      val last_block_equation = Local_Defs.meta_rewrite_rule ctxt last_block_definition
      val last_block_constant = Thm.term_of (Thm.lhs_of last_block_equation)
      val dag_equation = Local_Defs.meta_rewrite_rule ctxt table_definition
      val lookup_type = @{typ "(nat \<times> nat list) option"}
      val lookup = Const (@{const_name comma_semantic_b1_crt_column_dag_lookup},
        @{typ comma_semantic_b1_crt_column_dag} --> @{typ nat} --> lookup_type)
      val lookup_rules = Conversion.normalize_lookup_rules ctxt
        @{thms comma_semantic_b1_crt_column_dag_lookup.simps
          comma_semantic_b1_crt_column_block_lookup.simps}
      val lookup_request = lookup $ dag_constant $ HOLogic.mk_number natT missing_cid
      val lookup_ct = Thm.cterm_of ctxt lookup_request
      val table_step = Conversion.argument_at 1 (Conv.rewr_conv dag_equation) lookup_ct
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=missing-cid-directory-opened"
      val lookup_visits = Unsynchronized.ref 0
      val lookup_step = Conversion.controlled_lookup ctxt
        (Comma_Entry_Arithmetic.natural_context ctxt) lookup_rules lookup_visits
        (SOME (last_block_constant, last_block_definition)) (Thm.rhs_of table_step)
      val missing_lookup = Thm.transitive table_step lookup_step
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=missing-cid-lookup-reduced"
      val none = Const (@{const_name None}, lookup_type)
      val _ = require (Thm.term_of (Thm.rhs_of missing_lookup) aconv none andalso
          clean_theorem missing_lookup)
        "B1 out-of-range DAG lookup did not return a clean None theorem"
      val missing_unfold = Conv.rewr_conv (Local_Defs.meta_rewrite_rule ctxt
        @{thm comma_semantic_b1_crt_column_at.simps})
        (Thm.cterm_of ctxt missing_column)
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=missing-cid-decoder-unfolded"
      val missing_decode = Simplifier.rewrite
        (Comma_Entry_Arithmetic.natural_context ctxt addsimps
          (missing_lookup :: @{thms option.case}))
        (Thm.rhs_of missing_unfold)
      val missing_decode_theorem = Thm.transitive missing_unfold missing_decode
      val bool_false = @{term "Comma_CRT_Bool False"}
      val _ = require (Thm.term_of (Thm.rhs_of missing_decode_theorem) aconv bool_false andalso
          clean_theorem missing_decode_theorem)
        "B1 missing CID decoder did not return a clean Bool False theorem"
      val admitted_false = Const (@{const_name comma_crt_admitted},
        natT --> @{typ comma_crt_column} --> @{typ bool}) $
        HOLogic.mk_number natT 0 $ bool_false
      val admitted_false_theorem = Simplifier.rewrite
        (put_simpset HOL_ss ctxt addsimps @{thms comma_crt_admitted.simps})
        (Thm.cterm_of ctxt admitted_false)
      val _ = require (Thm.term_of (Thm.rhs_of admitted_false_theorem) aconv @{term True} andalso
          clean_theorem admitted_false_theorem)
        "B1 missing CID Bool False was not kernel-proved admitted"
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=missing-cid-admission-proved"
      val _ = expect_error "B1 column lookup requested a foreign CID"
        "strict converter rejects missing CID" (fn () => #step converter missing_cid)

      val node_equation = #step converter node_cid
      val (node_body, level, children) = first_column_node node_equation
      fun child_cid child =
        (case strip_comb child of
          (Const (name, _), [_, cid_term]) =>
            if name = @{const_name comma_semantic_b1_crt_column_at} then
              #2 (HOLogic.dest_number cid_term)
            else error "B1 exact-body fixture has a noncanonical child"
        | _ => error "B1 exact-body fixture has a malformed child application")
      val exact_child_ids = map child_cid children
      val _ = require (forall (#known_column converter) children)
        "B1 exact-body fixture contains a foreign child application"
      val expected_node_body = Const (@{const_name Comma_CRT_Node},
        natT --> HOLogic.listT @{typ comma_crt_column} -->
          @{typ comma_crt_column}) $
        HOLogic.mk_number natT level $
        HOLogic.mk_list @{typ comma_crt_column}
          (map column_value exact_child_ids)
      val _ = require (node_body aconv expected_node_body)
        "B1 valid-node exact-body fixture changed its level or child order"
      val reified = #reify converter (Thm.cterm_of ctxt node_body)
      val _ = require (Thm.term_of (Thm.rhs_of reified) aconv node_constant andalso
          clean_theorem reified andalso clean_theorem node_equation)
        "B1 global DAG one-node reification did not return its authenticated CID"
      val reify_hits_before = #reify_cache_hits converter ()
      val repeated_reified = #reify converter (Thm.cterm_of ctxt node_body)
      val _ = require
        (Thm.term_of (Thm.lhs_of repeated_reified) aconv node_body andalso
         Thm.term_of (Thm.rhs_of repeated_reified) aconv node_constant andalso
         clean_theorem repeated_reified andalso
         #reify_cache_hits converter () > reify_hits_before)
        "B1 exact-term reification cache did not reuse its checked theorem"
      val swapped_body =
        (case strip_comb node_body of
          (Const (name, T), [level_term, children_term]) =>
            let
              val swapped = (case swap_adjacent_distinct (HOLogic.dest_list children_term) of
                  SOME values => values
                | NONE => error "B1 first published node has no distinct adjacent children")
            in Const (name, T) $ level_term $ HOLogic.mk_list @{typ comma_crt_column} swapped end
        | _ => error "B1 swapped-child fixture lost its shallow node")
      val swapped_reified = #reify converter (Thm.cterm_of ctxt swapped_body)
      val _ = require
        (not (Thm.term_of (Thm.rhs_of swapped_reified) aconv node_constant) andalso
         clean_theorem swapped_reified)
        "B1 DAG reification accepted a node with reordered children as the same CID"

      val natT = @{typ nat}
      val cofactor = Const (@{const_name comma_crt_cofactor},
        natT --> natT --> @{typ comma_crt_column} -->
          @{typ "comma_crt_column option"})
      val admitted = Const (@{const_name comma_crt_admitted},
        natT --> @{typ comma_crt_column} --> @{typ bool})
      val level_term = HOLogic.mk_number natT level
      val zero = HOLogic.mk_number natT 0
      val one = HOLogic.mk_number natT 1
      val cofactor_request = cofactor $ level_term $ zero $ node_constant
      val different_request = cofactor $ level_term $ one $ node_constant
      val admitted_request = admitted $ zero $ node_constant

      val operation_context = Operations.operation_context
        (Comma_Entry_Arithmetic.natural_context ctxt)
      val evaluation_context = operation_context
        |> Simplifier.add_proc (#procedure converter)
        |> Simplifier.add_proc (#post_procedure converter)
      val checker = Operations.make_equation_checker_with_columns ctxt known_column
      val check_column_value = Operations.make_column_value_checker ctxt known_column
      val apply_partial = Const (@{const_name comma_crt_apply},
        @{typ comma_crt_boolean_operation} --> @{typ comma_crt_column} -->
          @{typ comma_crt_column} --> @{typ comma_crt_column})
      val undefined_column = Const (@{const_name undefined}, @{typ comma_crt_column})
      val partial_request = apply_partial $ @{term Comma_CRT_Or} $
        (column_value 0) $ undefined_column
      val opened_before_partial = #head_opens converter ()
      val partial_result = #try_evaluate converter operation_context
        (Thm.cterm_of ctxt partial_request)
      val opened_after_partial = #head_opens converter ()
      val partial_declined = (case partial_result of NONE => true | SOME _ => false)
      val partial_description =
        (case partial_result of
          NONE => "NONE"
        | SOME theorem =>
            let
              val {complete, nodes} = #status (#check checker partial_request theorem)
              val rhs = Thm.term_of (Thm.rhs_of theorem)
              val pretty = XML.content_of (YXML.parse_body
                (Syntax.string_of_term ctxt rhs))
            in "SOME complete=" ^ Bool.toString complete ^
              " nodes=" ^ Int.toString nodes ^ " rhs=" ^ pretty end)
      val _ = require (opened_after_partial > opened_before_partial)
        "B1 partial-conversion regression did not visit its owned scalar CID"
      val _ = require partial_declined
        ("B1 named-column congruence claimed an incomplete normalization: " ^
          partial_description)
      val pieceT = @{typ comma_semantic_b1_crt_piece_ref}
      fun nat n = HOLogic.mk_number natT n
      val apply = Const (@{const_name comma_crt_apply},
        @{typ comma_crt_boolean_operation} --> @{typ comma_crt_column} -->
          @{typ comma_crt_column} --> @{typ comma_crt_column})
      val false_column = column_value 0
      val first_or = apply $ @{term Comma_CRT_Or} $ false_column $ false_column
      val first_or_theorem = Simplifier.rewrite evaluation_context
        (Thm.cterm_of ctxt first_or)
      val first_or_value = Thm.term_of (Thm.rhs_of first_or_theorem)
      val _ = require (clean_theorem first_or_theorem andalso
          not (known_column first_or_value) andalso
          #complete (check_column_value first_or_value))
        "B1 OR operation did not produce a complete non-DAG intermediate"
      val rowT = HOLogic.listT pieceT
      val sourceT = HOLogic.listT rowT
      val piece_refsT = HOLogic.listT sourceT
      val piece_refs = Const (Sign.intern_const thy
        "comma_semantic_b1_crt_construction_piece_refs", piece_refsT)
      val piece_catalogue =
        Comma_Semantic_B1_Construction_Piece_Projection.get_catalogue ctxt
      val {root_definition = piece_refs_definition, child_definitions,
           child_row_extents, block_source_extents, source_count, ...} = piece_catalogue
      val piece_refs_selector =
        Comma_Semantic_B1_Construction_Piece_Projection.make_with_catalogue ctxt
          "regression_construction_piece_refs" piece_catalogue
      val production_context = fold Simplifier.add_proc
        (#support_procedures piece_refs_selector)
        (Simplifier.add_simps (#support_simp_rules piece_refs_selector)
          (Simplifier.add_proc (#procedure piece_refs_selector)
            (Simplifier.add_proc (#post_procedure piece_refs_selector) evaluation_context)))
      val nth_source = Const (@{const_name nth}, piece_refsT --> natT --> sourceT)
      val nth_row = Const (@{const_name nth}, sourceT --> natT --> rowT)
      val selected_source = nth_source $ piece_refs $ nat 0
      val selected_row = nth_row $ selected_source $ nat 0
      val source_size = Const (@{const_name size}, sourceT --> natT)
      val source_size_request = source_size $ selected_source
      val source_size_equation = Simplifier.rewrite production_context
        (Thm.cterm_of ctxt source_size_request)
      val _ = require
        (Thm.term_of (Thm.lhs_of source_size_equation) aconv source_size_request andalso
         Thm.term_of (Thm.rhs_of source_size_equation) aconv
           nat (hd child_row_extents) andalso clean_theorem source_size_equation)
        "B1 named child size selector did not derive its exact authenticated extent"
      val flatten_source = Const (@{const_name concat}, sourceT --> rowT)
      val flattened_source_request = flatten_source $ selected_source
      val flattened_source_equation = Simplifier.rewrite production_context
        (Thm.cterm_of ctxt flattened_source_request)
      val _ = require
        (Thm.term_of (Thm.lhs_of flattened_source_equation) aconv flattened_source_request andalso
         clean_theorem flattened_source_equation andalso
         can HOLogic.dest_list (Thm.term_of (Thm.rhs_of flattened_source_equation)))
        "B1 named source flattening did not use its authenticated child equation"
      val alternate_source_index = length child_row_extents - 1
      val alternate_row_request = nth_row $
        (nth_source $ piece_refs $ nat alternate_source_index) $ nat 0
      val alternate_row_equation = Simplifier.rewrite production_context
        (Thm.cterm_of ctxt alternate_row_request)
      val _ = require
        (Thm.term_of (Thm.lhs_of alternate_row_equation) aconv alternate_row_request andalso
         clean_theorem alternate_row_equation andalso
         can HOLogic.dest_list (Thm.term_of (Thm.rhs_of alternate_row_equation)))
        "B1 named child selector failed on a second authenticated source row"
      val maximum_row_extent = fold
        (fn extent => fn maximum => Int.max (extent, maximum))
        child_row_extents 0
      fun first_shorter_source index [] = NONE
        | first_shorter_source index (extent :: rest) =
            if extent < maximum_row_extent then SOME (index, extent)
            else first_shorter_source (index + 1) rest
      val (short_source_index, short_source_extent) =
        (case first_shorter_source 0 child_row_extents of
          SOME pair => pair
        | NONE => error "B1 named child fixture requires distinct row extents")
      val out_of_short_row = nth_row $
        (nth_source $ piece_refs $ nat short_source_index) $ nat short_source_extent
      val _ = expect_error "B1 construction-piece row index exceeds its source extent"
        "authenticated child-specific row bound" (fn () =>
          Simplifier.rewrite production_context (Thm.cterm_of ctxt out_of_short_row))
      val _ = if length child_definitions >= 2 then ()
        else error "B1 named child fixtures require at least two source definitions"
      val swapped_children = tl child_definitions @ [hd child_definitions]
      val swapped_blocks = tl block_source_extents @ [hd block_source_extents]
      val reordered_catalogue :
        Comma_Semantic_B1_Construction_Piece_Projection.catalogue =
        {root_definition = #root_definition piece_catalogue,
         directory_definition = #directory_definition piece_catalogue,
         child_definitions = swapped_children,
         child_row_extents = child_row_extents,
         block_source_extents = swapped_blocks,
         source_count = source_count}
      val _ = expect_error "Named selected-list child has a foreign canonical name"
        "reordered named child directory" (fn () =>
          Comma_Semantic_B1_Construction_Piece_Projection.make_with_catalogue ctxt
            "regression_reordered_construction_piece_refs" reordered_catalogue)
      val foreign_child = Proof_Context.get_thm ctxt
        "comma_semantic_b1_crt_lift_refs_def"
      val foreign_children = foreign_child :: tl child_definitions
      val foreign_catalogue :
        Comma_Semantic_B1_Construction_Piece_Projection.catalogue =
        {root_definition = #root_definition piece_catalogue,
         directory_definition = #directory_definition piece_catalogue,
         child_definitions = foreign_children,
         child_row_extents = child_row_extents,
         block_source_extents = block_source_extents,
         source_count = source_count}
      val _ = expect_error "Named selected-list child has a foreign canonical name"
        "foreign named child definition" (fn () =>
          Comma_Semantic_B1_Construction_Piece_Projection.make_with_catalogue ctxt
            "regression_foreign_construction_piece_child" foreign_catalogue)
      val wrong_first_extent = (hd block_source_extents + 1) :: tl block_source_extents
      val wrong_extent_catalogue :
        Comma_Semantic_B1_Construction_Piece_Projection.catalogue =
        {root_definition = #root_definition piece_catalogue,
         directory_definition = #directory_definition piece_catalogue,
         child_definitions = child_definitions,
         child_row_extents = child_row_extents,
         block_source_extents = wrong_first_extent,
         source_count = source_count}
      val _ = expect_error "Named selected-list child has an inconsistent row extent"
        "named child row extent binding" (fn () =>
          Comma_Semantic_B1_Construction_Piece_Projection.make_with_catalogue ctxt
            "regression_wrong_construction_piece_extents" wrong_extent_catalogue)
      val wrong_source_extents = (hd child_row_extents + 1) :: tl child_row_extents
      val wrong_source_catalogue :
        Comma_Semantic_B1_Construction_Piece_Projection.catalogue =
        {root_definition = #root_definition piece_catalogue,
         directory_definition = #directory_definition piece_catalogue,
         child_definitions = child_definitions,
         child_row_extents = wrong_source_extents,
         block_source_extents = block_source_extents,
         source_count = source_count}
      val _ = expect_error "Named selected-list child has an inconsistent row extent"
        "named source-specific row extent binding" (fn () =>
          Comma_Semantic_B1_Construction_Piece_Projection.make_with_catalogue ctxt
            "regression_wrong_source_extents" wrong_source_catalogue)
      val production_request = selected_row
      val production_theorem = Simplifier.rewrite production_context
        (Thm.cterm_of ctxt production_request)
      val production_pieces = HOLogic.dest_list
        (Thm.term_of (Thm.rhs_of production_theorem))
      val _ = require (Thm.term_of (Thm.lhs_of production_theorem) aconv production_request andalso
          clean_theorem production_theorem andalso not (null production_pieces))
        "B1 production-shaped request did not select its authenticated source row"
      (* Exercise the exact multiplicity check used by the construction
         certificate with a real, selected piece from that row.  Adding that
         origin leaves set coverage unchanged, but changes the length of the
         sorted origin list, so the certificate's sorted-list equality must
         reject the mutation. *)
      val originT = @{typ "nat \<times> nat"}
      val origin_listT = HOLogic.listT originT
      val origin_of_piece = Const
        (@{const_name comma_semantic_b1_crt_constructed_piece_origin}, pieceT --> originT)
      val origins = map (fn selected_piece => origin_of_piece $ selected_piece)
        production_pieces
      val origin_list = HOLogic.mk_list originT origins
      val duplicated_origin_list = HOLogic.mk_list originT (hd origins :: origins)
      val set_of_origins = Const (@{const_name set},
        origin_listT --> @{typ "(nat \<times> nat) set"})
      val sort_origins =
        @{term "sort :: (nat \<times> nat) list \<Rightarrow> (nat \<times> nat) list"}
      val size_origins = Const (@{const_name size}, origin_listT --> natT)
      val sorted_duplicate_origins = sort_origins $ duplicated_origin_list
      val sorted_origins = sort_origins $ origin_list
      val same_set = HOLogic.mk_eq
        (set_of_origins $ duplicated_origin_list, set_of_origins $ origin_list)
      val different_sorted_list = HOLogic.mk_not
        (HOLogic.mk_eq (sorted_duplicate_origins, sorted_origins))
      val different_sorted_size = HOLogic.mk_not (HOLogic.mk_eq
        (size_origins $ sorted_duplicate_origins,
         size_origins $ sorted_origins))
      val multiplicity_fixture = Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop (HOLogic.mk_conj (same_set,
          HOLogic.mk_conj (different_sorted_list, different_sorted_size))))
        (fn {context, ...} => Simplifier.simp_tac
          (context addsimps
            @{thms comma_semantic_b1_crt_constructed_piece_origin_def}) 1)
      val _ = require (clean_theorem multiplicity_fixture)
        "B1 duplicate-origin multiplicity fixture was not kernel-proved"
      val outside_row = nth_row $ selected_source $ nat 131072
      val outside_row_request = outside_row
      val _ = expect_error
        "B1 construction-piece row index exceeds its source extent"
        "production-shaped construction row bounds" (fn () =>
          Simplifier.rewrite production_context (Thm.cterm_of ctxt outside_row_request))
      val shift = Const (@{const_name comma_crt_shift}, natT -->
        @{typ comma_crt_column} --> @{typ comma_crt_column})
      val shifted_request = shift $ nat 1 $ first_or_value
      val shifted_context = bounded_shift_context evaluation_context
      val shifted_theorem = Simplifier.rewrite shifted_context
        (Thm.cterm_of ctxt shifted_request)
      val shifted_checked = #check checker shifted_request shifted_theorem
      val shifted_equation = #equation shifted_checked
      val shifted_rhs = Thm.term_of (Thm.rhs_of shifted_equation)
      val shifted_status = #status shifted_checked
      fun excerpt term =
        let val text = XML.content_of (YXML.parse_body
          (Syntax.string_of_term ctxt term))
        in String.substring (text, 0, Int.min (512, String.size text)) end
      val _ = require (#complete (#status shifted_checked) andalso
          clean_theorem shifted_equation)
        ("B1 shifted final OR parent was not a complete exact theorem; complete=" ^
         Bool.toString (#complete shifted_status) ^ " nodes=" ^
         Int.toString (#nodes shifted_status) ^ " exact_lhs=" ^
         Bool.toString (Thm.term_of (Thm.lhs_of shifted_equation) aconv shifted_request) ^
         " rhs=" ^ excerpt shifted_rhs)
      fun rewrite request = Simplifier.rewrite evaluation_context
        (Thm.cterm_of ctxt request)
      val admitted_checked = #check checker admitted_request
        (rewrite admitted_request)
      val _ = require
        (Thm.term_of (Thm.rhs_of (#equation admitted_checked)) aconv @{term True} andalso
         #complete (#status admitted_checked) andalso clean_theorem (#equation admitted_checked))
        "B1 DAG admitted conversion did not produce a clean complete proof"
      val cofactor_theorem = rewrite cofactor_request
      val cofactor_checked = #check checker cofactor_request cofactor_theorem
      val cofactor_value = Thm.term_of (Thm.rhs_of (#equation cofactor_checked))
      val _ = require
        (#complete (#status cofactor_checked) andalso
         not (cofactor_value aconv cofactor_request) andalso
         clean_theorem (#equation cofactor_checked))
        "B1 DAG cofactor conversion did not produce a clean complete proof"
      val wrong_request = Exn.capture
        (fn () => #check checker different_request cofactor_theorem) ()
      val _ = (case wrong_request of
          Exn.Exn (ERROR message) =>
            if message = "selected-list conversion returned an open or mismatched theorem"
            then () else error ("B1 exact request fixture failed for the wrong reason: " ^ message)
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "B1 equation checker accepted a theorem for another request")
    in converter end

  fun check_generic_fixtures ctxt =
    let
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=controlled-lookup-fixtures-start"
      val _ = check_bounded_shifts ctxt
      val _ = Comma_Semantic_B1_Column_Lookup_Regression.check_controlled_lookup ctxt
      val _ = Comma_Semantic_B1_Column_Lookup_Regression.check_mixed_directory_shape ctxt
      val _ = Comma_Semantic_B1_Mass_Rows.check_fixture ctxt
      val _ = Comma_Proof_Profile.report
        "B1 column regression stage=controlled-lookup-fixtures-complete"
    in () end
end
