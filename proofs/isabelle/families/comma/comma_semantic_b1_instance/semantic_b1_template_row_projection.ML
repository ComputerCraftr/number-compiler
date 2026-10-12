(* Authenticated projection from a published template row to its partition
   checker request.  Both the legacy and labelled zipper proof drivers use this
   single boundary, so source IDs and result ordering are checked identically. *)
structure Comma_Semantic_B1_Template_Row_Projection =
struct
  val shape = Comma_Semantic_B1_Partition_Support.shape
  val profile_message = Comma_Semantic_B1_Partition_Support.profile_message
  val profile_stage = Comma_Semantic_B1_Partition_Support.profile_stage
  fun make ctxt
      {column_value, node_count}
      {prove_state, state_counts, state_work_summary} =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val rowT = HOLogic.listT columnT
      val boolT = @{typ bool}
      val thy = Proof_Context.theory_of ctxt
      fun number n = HOLogic.mk_number natT n
      fun check_equation label lhs rhs theorem =
        if Thm.term_of (Thm.lhs_of theorem) aconv lhs andalso
            Thm.term_of (Thm.rhs_of theorem) aconv rhs andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem)
        then theorem
        else error ("B1 template row projection " ^ label ^ " changed its exact equation")
      val table_name = Sign.intern_const thy "comma_semantic_b1_crt_columns"
      val count_name = Sign.intern_const thy "comma_semantic_b1_crt_column_count"
      val table = Const (table_name, rowT)
      val count = Const (count_name, natT)
      val table_definition = Local_Defs.meta_rewrite_rule ctxt
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_columns_def")
      val count_definition = Local_Defs.meta_rewrite_rule ctxt
        (Proof_Context.get_thm ctxt "comma_semantic_b1_crt_column_count_def")
      val table_body = Thm.term_of (Thm.rhs_of table_definition)
      val count_value = Thm.term_of (Thm.rhs_of count_definition)
      val (dag, count_arg) = (case strip_comb table_body of
          (Const (name, _), [dag, count_arg]) =>
            if name = @{const_name comma_semantic_b1_crt_columns_for}
            then (dag, count_arg)
            else error "B1 template table is not a checked DAG projection"
        | _ => error "B1 template table definition is malformed")
      val declared_count_matches =
        (case try HOLogic.dest_number count_value of
          SOME (typ, value) => typ = natT andalso value = node_count
        | NONE => false)
      val _ = if Thm.term_of (Thm.lhs_of table_definition) aconv table andalso
          Thm.term_of (Thm.lhs_of count_definition) aconv count andalso
          count_arg aconv count andalso
          fastype_of dag = @{typ comma_semantic_b1_crt_column_dag} andalso
          declared_count_matches andalso
          fastype_of (column_value 0) = columnT
        then () else error "B1 template table extent or DAG does not match the checked catalogue"
      val (column_at_head, column_at_args) = strip_comb (column_value 0)
      val _ = (case (column_at_head, column_at_args) of
          (Const (name, _), [column_dag, zero]) =>
            if name = @{const_name comma_semantic_b1_crt_column_at} andalso
                column_dag aconv dag andalso
                (case try HOLogic.dest_number zero of
                  SOME (typ, value) => typ = natT andalso value = 0
                | NONE => false)
            then () else error "B1 column-value callback changed the fixed DAG"
        | _ => error "B1 column-value callback returned another term")
      fun dest_nat_list label term =
        (case try HOLogic.dest_list term of
          SOME values => map (fn value =>
            (case try HOLogic.dest_number value of
              SOME (typ, number) => if typ = natT andalso number >= 0 then number
                else error ("B1 partition " ^ label ^ " has an invalid natural")
            | NONE => error ("B1 partition " ^ label ^ " is not a numeral"))) values
        | NONE => error ("B1 partition " ^ label ^
            " is not a literal list; rhs=" ^ shape 8 term))
      val level_schedule_cache = Unsynchronized.ref
        (Termtab.empty: thm Termtab.table)
      val level_schedule_hits = Unsynchronized.ref 0
      val level_schedule_misses = Unsynchronized.ref 0
      fun checked_level_schedule levels_term =
        (case Termtab.lookup (!level_schedule_cache) levels_term of
          SOME equation =>
            (level_schedule_hits := !level_schedule_hits + 1;
             check_equation "cached checker levels" levels_term
               (HOLogic.mk_list natT (map number [0, 1, 2, 3])) equation)
        | NONE =>
            let
              val levels_base_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
                @{thms upt_rec_numeral}
              val levels_context = the_default levels_base_context
                (Comma_Semantic_B1_CRT_Operation_Conversion.small_closed_upt_context
                  levels_base_context levels_term)
                  addsimps @{thms upt_0 upt_Suc upt_rec upt_rec_numeral}
              val equation = Simplifier.rewrite levels_context
                (Thm.cterm_of ctxt levels_term)
              val levels = dest_nat_list "checker levels"
                (Thm.term_of (Thm.rhs_of equation))
              val expected = HOLogic.mk_list natT (map number [0, 1, 2, 3])
              val _ = check_equation "checker levels" levels_term expected equation
              val _ = if levels = [0, 1, 2, 3] then ()
                else error "B1 template partition checker has another CRT level schedule"
              val _ = level_schedule_misses := !level_schedule_misses + 1
              val _ = if Termtab.size (!level_schedule_cache) < 4 then
                level_schedule_cache := Termtab.update
                  (levels_term, equation) (!level_schedule_cache)
                else ()
            in equation end)
      fun prove_checker {context, checker_ct, ids_row, row, resolved_fact} =
        let
          val _ = profile_stage "row_projection" "start" NONE
          val row_started = Time.now ()
          val checker_request = Thm.term_of checker_ct
          val (checker_head, checker_arguments) = strip_comb checker_request
          val (levels_term, row_term) =
            (case (checker_head, checker_arguments) of
              (Const (name, _), [levels, columns]) =>
                if name = @{const_name comma_semantic_b1_crt_partition_cofactor_checked} andalso
                    columns aconv row
                then (levels, columns)
                else error "B1 template partition checker request changed its exact row"
            | _ => error "B1 template partition checker request is malformed")
          val ids_equation = Simplifier.rewrite context (Thm.cterm_of ctxt ids_row)
          val _ = check_equation "selected IDs" ids_row
            (Thm.term_of (Thm.rhs_of ids_equation)) ids_equation
          val ids = dest_nat_list "selected column IDs"
            (Thm.term_of (Thm.rhs_of ids_equation))
          val _ = if Thm.term_of (Thm.rhs_of ids_equation) aconv
                  HOLogic.mk_list natT (map (HOLogic.mk_number natT) ids) andalso
              Thm.term_of (Thm.lhs_of ids_equation) aconv ids_row andalso
              Thm.nprems_of ids_equation = 0 andalso
              null (Thm.hyps_of ids_equation) andalso null (Thm.tpairs_of ids_equation) andalso
              forall (fn cid => cid < node_count) ids then ()
            else error "B1 selected template row has a foreign column ID"
          val selected_ids = HOLogic.mk_list natT (map (HOLogic.mk_number natT) ids)
          val column_at = Const (@{const_name comma_semantic_b1_crt_column_at},
            @{typ "comma_semantic_b1_crt_column_dag"} --> natT --> columnT) $ dag
          val map_column_at = Const (@{const_name map},
            (natT --> columnT) --> HOLogic.listT natT --> rowT) $ column_at
          val selected_map = map_column_at $ selected_ids
          val selected_columns = HOLogic.mk_list columnT (map column_value ids)
          val selected_equation = Simplifier.rewrite
            (put_simpset HOL_basic_ss ctxt addsimps @{thms list.map})
            (Thm.cterm_of ctxt selected_map)
          val _ = check_equation "catalogue row projection" selected_map
            selected_columns selected_equation
          val table_object = table_definition RS @{thm meta_eq_to_obj_eq}
          val resolved_columns =
            @{thm comma_semantic_b1_crt_column_ids_resolve_columns_for}
              OF [table_object, resolved_fact]
          val resolved_columns_meta = resolved_columns RS @{thm eq_reflection}
          val ids_under_map = Thm.combination
            (Thm.reflexive (Thm.cterm_of ctxt map_column_at)) ids_equation
          val row_equation = Thm.transitive
            (Thm.transitive resolved_columns_meta ids_under_map)
            selected_equation
          val _ = check_equation "resolved row" row_term selected_columns row_equation
          val row_elapsed = Time.toMilliseconds (Time.- (Time.now (), row_started))
          val _ = profile_stage "row_projection" "done" (SOME row_elapsed)
          val _ = profile_stage "levels" "start" NONE
          val levels_started = Time.now ()
          val levels_equation = checked_level_schedule levels_term
          val levels = dest_nat_list "checker levels"
            (Thm.term_of (Thm.rhs_of levels_equation))
          val literal_levels = HOLogic.mk_list natT (map number levels)
          val _ = check_equation "checker levels" levels_term literal_levels levels_equation
          val levels_elapsed = Time.toMilliseconds (Time.- (Time.now (), levels_started))
          val _ = profile_stage "levels" "done" (SOME levels_elapsed)
          val checker_const = Const
            (@{const_name comma_semantic_b1_crt_partition_cofactor_checked},
              HOLogic.listT natT --> rowT --> boolT)
          val head_ct = Thm.cterm_of ctxt checker_const
          val prefix_equation = Thm.combination
            (Thm.reflexive head_ct) levels_equation
          val request_equation = Thm.combination prefix_equation row_equation
          val _ = profile_message (fn () => "B1 partition stage=state phase=start levels=" ^
            Int.toString (length levels) ^ " ids=" ^ Int.toString (length ids))
          val state_started = Time.now ()
          val state_equation = prove_state ids
          val state_elapsed = Time.toMilliseconds (Time.- (Time.now (), state_started))
          val _ = profile_message (fn () =>
            let val (states, vectors, _, _) = state_counts ()
            in "B1 partition stage=state phase=done elapsed_ms=" ^
              LargeInt.toString state_elapsed ^ " states=" ^ Int.toString states ^
              " vectors=" ^ Int.toString vectors ^
              " schedule_hits=" ^ Int.toString (!level_schedule_hits) ^
              " schedule_misses=" ^ Int.toString (!level_schedule_misses) ^
              state_work_summary () end)
          val equation = Thm.transitive request_equation state_equation
          val _ = check_equation "template checker" checker_request @{term True} equation
        in equation end
    in {prove_checker = prove_checker} end
end
