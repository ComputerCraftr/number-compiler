(* Canonical, narrowly scoped primitive CRT evaluation context.
   Catalogue selectors must run before these list equations are installed. *)
signature COMMA_SEMANTIC_B1_CRT_OPERATION_CONVERSION =
sig
  type value_status = {complete: bool, nodes: int}
  type checked_equation =
    {equation: thm, status: value_status, reused_rhs: bool, reused_closed: bool}
  type equation_checker =
    {check: term -> thm -> checked_equation, complete_value: term -> bool}
  type staged_result = {equation: thm, operands_unchanged: bool}
  val crt_operation_simp_rules: Proof.context -> thm list
  val apply_depth_simp_rules: Proof.context -> thm list
  val crt_operation_boundaries: thm list -> (string * thm list) list
  val crt_operation_base_patterns: term list
  val crt_operation_base_heads: string list
  val crt_operation_staged_heads: string list
  val crt_operation_lazy_function_heads: string list
  val small_closed_upt_context: Proof.context -> term -> Proof.context option
  val argument_at: int -> conv -> conv
  val natural_numeral: int -> term
  val reflect_boundaries: (string * thm list) list -> (string * thm list) list
  val make_staged_operation_converter:
    {context: Proof.context,
     boundaries: (string * thm list) list,
     staged_heads: string list, lazy_function_heads: string list,
     final_argument_stagers: (string * (cterm -> thm)) list,
     complete_value: term -> bool} ->
    cterm -> staged_result
  val operation_context: Proof.context -> Proof.context
  val selected_period_equation:
    {ctxt: Proof.context, context: Proof.context, period: cterm -> thm option,
     shape: term -> string} -> cterm -> thm
  val make_column_value_checker:
    Proof.context -> (term -> bool) -> term -> value_status
  val make_equation_checker_with_columns:
    Proof.context -> (term -> bool) -> equation_checker
  val bool_true_equation: Proof.context -> term -> thm -> thm
  val prove_column_at_admitted_header:
    Proof.context ->
      {request: term, dag: term, cid: term, lower: term, level: term,
       children: term, lookup: thm} -> thm
  val prove_nonfalse_from_step:
    Proof.context -> term -> term -> term -> thm -> thm
  val selected_paint_memo_spec:
    Proof.context -> {patterns: term list, roots: string list}
end

structure Comma_Semantic_B1_Selected_Contexts =
struct
  val source_scalar_rules =
    @{thms gcd_nat.simps nth_Cons' arith_simps arith_special rel_simps
      numeral_div_numeral numeral_mod_numeral}
  val source_action_rules =
    @{thms comma_finite_position.case comma_finite_move.case
      comma_fast_step.simps comma_round_crossing_def
      comma_source_continuation_shift.simps
      comma_semantic_b1_source_slot_action_code
      comma_semantic_b1_source_slot_action_width_def}
  val constructed_case_rules =
    @{thms comma_semantic_b1_crt_piece_ref.case
      comma_semantic_b1_crt_lift_ref.case
      comma_source_continuation_action.case}
  val constructed_case_congs =
    @{thms comma_semantic_b1_crt_piece_ref.case_cong_weak
      comma_semantic_b1_crt_lift_ref.case_cong_weak
      comma_source_continuation_action.case_cong_weak}
  val source_action_congs =
    @{thms let_weak_cong prod.case_cong_weak comma_decade_outcome.case_cong_weak
      comma_finite_move.case_cong_weak comma_finite_position.case_cong_weak
      comma_round_result.case_cong_weak sum.case_cong_weak
      comma_source_continuation_action.case_cong_weak}
  val offset_orbit_rules =
    @{thms comma_offset_orbit_def comma_digit_orbit_sum_def power2_eq_square
      of_nat_numeral of_nat_0 of_nat_1 zmod_zminus1_eq_if zmod_zminus2_eq_if}

  fun make ctxt operation_context arithmetic_rules endpoint_simproc =
    {slot_origins = fold Simplifier.add_cong constructed_case_congs
       (operation_context addsimps (constructed_case_rules @
         @{thms comma_semantic_b1_crt_constructed_slot_origins_def})),
     offset_orbit = Comma_Entry_Arithmetic.natural_context ctxt addsimps
       offset_orbit_rules,
     source_arithmetic = fold Simplifier.add_cong source_action_congs
       ((operation_context addsimps
           (arithmetic_rules @ source_scalar_rules @ source_action_rules)
           delsimps @{thms comma_decisive_sector_target.simps})
         |> Simplifier.add_proc endpoint_simproc)}
end

structure Comma_Semantic_B1_CRT_Operation_Conversion:
  COMMA_SEMANTIC_B1_CRT_OPERATION_CONVERSION =
struct
  (* The construction check uses this only on selected lift-slot scalars.
     Their period bound is 28; symbolic or wider ranges keep the old context. *)
  fun small_closed_upt_context ctxt term =
    let
      val upt_name = @{const_name upt}
      val natT = @{typ nat}
      fun inspect current =
        let val (head, args) = strip_comb current in
          (case head of
            Const (name, _) =>
              if name <> upt_name then inspect_children current
              else
                (case args of
                  [lower, upper] =>
                    let
                      val bounds = (try HOLogic.dest_number lower,
                        try HOLogic.dest_number upper)
                      val (seen_lower, safe_lower) = inspect lower
                      val (seen_upper, safe_upper) = inspect upper
                      val safe_bounds =
                        (case bounds of
                          (SOME (lowerT, lo), SOME (upperT, hi)) =>
                            lowerT = natT andalso upperT = natT andalso
                              hi >= lo andalso hi - lo <= 28
                        | _ => false)
                    in (true, safe_bounds andalso safe_lower andalso safe_upper) end
                | _ => (true, false))
          | _ => inspect_children current)
        end
      and inspect_children current =
        (case current of
          Abs (_, _, body) => inspect body
        | function $ argument =>
            let
              val (function_has, function_safe) = inspect function
              val (argument_has, argument_safe) = inspect argument
            in (function_has orelse argument_has, function_safe andalso argument_safe) end
        | _ => (false, true))
      val (found_upt, bounded) = inspect term
    in if found_upt andalso bounded then SOME (ctxt addsimps @{thms upt_rec}) else NONE end

  fun argument_at index conversion ct =
    if index = 0 then Conv.arg_conv conversion ct
    else Conv.fun_conv (argument_at (index - 1) conversion) ct

  fun natural_numeral value = HOLogic.mk_number @{typ nat} value

  fun list_shape term =
    (case strip_comb term of
      (Const (name, _), []) =>
        if name = @{const_name Nil} then SOME NONE else NONE
    | (Const (name, _), [head, tail]) =>
        if name = @{const_name Cons} then SOME (SOME (head, tail)) else NONE
    | _ => NONE)

  val operation_congs =
    @{thms option.case_cong_weak
      comma_semantic_b1_result.case_cong_weak
      comma_crt_column.case_cong_weak
      comma_crt_boolean_operation.case_cong_weak}

  fun crt_operation_simp_rules _ =
    @{thms comma_crt_period_def
      comma_crt_admitted.simps comma_crt_supported.simps(1)
      comma_crt_supported_node_short_circuit
      comma_crt_node_def comma_crt_node_cons
      comma_crt_negate.simps comma_crt_cofactor.simps
      comma_crt_apply_shortcut_def comma_crt_shifted_apply_shortcut_def
      comma_crt_cofactor_or_false_def comma_crt_shifted_cofactor_or_false_def
      comma_crt_boolean_value_def comma_crt_column.case
      comma_crt_result_at_def comma_crt_equiv_check_def
      comma_crt_apply_from_def comma_crt_apply_def
      comma_crt_apply_shifted_def comma_crt_apply_shifted_from.simps
      comma_crt_shift.simps rotate_drop_take drop_Nil take_Nil
      drop_Cons' take_Cons'
      comma_semantic_b1_weight_after_def
      option.inject option.distinct
      comma_crt_column.inject comma_crt_column.distinct
      comma_semantic_b1_result.inject comma_semantic_b1_result.distinct
      list.map list.case list.size list.inject list.distinct
      list_all_Nil_iff list_all_Cons_iff list_ex_Nil_iff list_ex_Cons_iff
      id_def List.map_filter_simps list.sel map_of.simps fun_upd_apply
      concat.simps append.simps filter.simps upt_rec nth_Cons' Let_def
      prod.case option.case fst_conv snd_conv case_prod_beta
      comma_semantic_b1_result.case comma_crt_boolean_operation.case
      comma_finite_move.case comma_finite_position.case comma_round_result.case}

  fun apply_depth_simp_rules ctxt =
    let
      val natT = @{typ nat}
      fun numeral n = HOLogic.mk_number natT n
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
        addsimps @{thms power_0 power_one_right power_numeral_even power_numeral_odd}
      fun specialize depth =
        Simplifier.simplify arithmetic
          (Drule.infer_instantiate ctxt
            [( ("remaining", 0), Thm.cterm_of ctxt (numeral depth))]
            @{thm comma_crt_apply_shifted_from.simps(2)})
    in map specialize (0 upto 3) end

  fun crt_operation_boundaries apply_depth_rules =
    [(@{const_name comma_crt_supported},
       @{thms comma_crt_supported.simps(1)
         comma_crt_supported_node_short_circuit}),
     (@{const_name comma_crt_apply_shifted},
       @{thms comma_crt_apply_shifted_def}),
     (@{const_name comma_crt_apply_shifted_from},
       @{thms comma_crt_apply_shifted_from.simps} @ apply_depth_rules),
     (@{const_name comma_crt_node},
       @{thms comma_crt_node_cons comma_crt_node_def}),
     (@{const_name comma_crt_cofactor}, @{thms comma_crt_cofactor.simps})]

  (* Exact memo roots shared by the occurrence and canonical CRT engines.
     Each pattern retains every semantic operand, so cache keys distinguish
     depth, shift, operation and both child columns. *)
  val crt_operation_base_patterns =
    [@{term "comma_crt_apply_shifted_from depth shift operation left right"},
     @{term "comma_crt_node level children"},
     @{term "comma_crt_cofactor level digit column"}]

  val crt_operation_base_heads =
    [@{const_name comma_crt_apply_shifted_from},
     @{const_name comma_crt_node},
     @{const_name comma_crt_cofactor}]

  (* Shared operand policies for the occurrence checker and the canonical
     fused power engine.  High-level occurrence predicates are deliberately
     absent: they are unfolded by their own checker while these primitive
     operations are admitted and memoized at their exact request boundary. *)
  val crt_operation_staged_heads =
    [@{const_name comma_crt_apply}, @{const_name comma_crt_apply_from},
     @{const_name comma_crt_apply_shifted},
     @{const_name comma_crt_apply_shifted_from},
     @{const_name comma_crt_admitted}, @{const_name comma_crt_supported},
     @{const_name comma_crt_equiv_check}, @{const_name comma_crt_negate},
     @{const_name comma_crt_group_rows}, @{const_name comma_crt_group_column},
     @{const_name comma_crt_group_insert}, @{const_name comma_crt_node},
     @{const_name comma_crt_cofactor}]

  val crt_operation_lazy_function_heads = []

  fun operation_context ctxt =
    let
      val rules = crt_operation_simp_rules ctxt @ apply_depth_simp_rules ctxt
    in fold Simplifier.add_cong operation_congs (ctxt addsimps rules) end

  fun selected_period_equation {ctxt, context, period, shape} cterm =
    let
      val request = Thm.term_of cterm
      val selected = Conv.arg_conv (Simplifier.rewrite context) cterm
      val overloaded = Axclass.overload_conv ctxt (Thm.rhs_of selected)
      val selected_overloaded = Thm.transitive selected overloaded
      val selected_ct = Thm.rhs_of selected_overloaded
      val selected_request = Thm.term_of selected_ct
      fun source_fields term =
        (case Term.strip_comb term of
          (Const (name, _), [source]) =>
            if name <> @{const_name comma_decisive_sector_period} then NONE
            else
              (case Term.strip_comb source of
                (Const (source_name, _), fields) =>
                  if member (op =) [@{const_name Comma_Entry}, @{const_name Comma_Near}]
                      source_name andalso length fields = 3 then SOME fields else NONE
              | _ => NONE)
        | _ => NONE)
      fun numeral_field field =
        (case try HOLogic.dest_number field of
          SOME (typ, _) => typ = @{typ nat}
        | NONE => false)
      val normalized =
        (case source_fields selected_request of
          SOME fields =>
            if List.all numeral_field fields then Thm.reflexive selected_ct
            else Simplifier.rewrite
              (Comma_Entry_Arithmetic.natural_context ctxt) selected_ct
        | NONE => Thm.reflexive selected_ct)
      val selected_source = Thm.transitive selected_overloaded normalized
      val selected_request = Thm.term_of (Thm.rhs_of selected_source)
    in
      (case period (Thm.rhs_of selected_source) of
        SOME equation =>
          let val theorem = Thm.transitive selected_source equation in
            if Thm.term_of (Thm.lhs_of theorem) aconv request then theorem
            else error "Selected source-period conversion changed its request"
          end
      | NONE => error
          ("B1 exact sector-period conversion failed after source selection: " ^
            shape selected_request))
    end

  type value_status = {complete: bool, nodes: int}
  type checked_equation =
    {equation: thm, status: value_status, reused_rhs: bool, reused_closed: bool}
  type equation_checker =
    {check: term -> thm -> checked_equation, complete_value: term -> bool}
  type staged_result = {equation: thm, operands_unchanged: bool}
  fun reflect_boundaries boundaries =
    map (fn (name, rules) =>
      (name, map (fn rule => rule RS @{thm eq_reflection}) rules)) boundaries

  (* Preserve operand-first evaluation; simplifying a parent before selecting
     its operands can expand both sides before the parent result is available. *)
  fun make_staged_operation_converter
      {context, boundaries, staged_heads, lazy_function_heads,
       final_argument_stagers, complete_value} =
    let
      val reflected = reflect_boundaries boundaries
      val column_type = @{typ comma_crt_column}
      (* Keep range recursion local to CRT primitives; the indexed geometry
         suffix stays opaque until its selected-row stager exposes one cell. *)
      val bounded_column_context = context addsimps
        @{thms upt_0 upt_Suc upt_rec upt_rec_numeral}
      val bounded_column_heads =
        [@{const_name comma_crt_supported}, @{const_name comma_crt_admitted},
         @{const_name comma_crt_node}, @{const_name comma_crt_cofactor},
         @{const_name comma_crt_apply}, @{const_name comma_crt_apply_from},
         @{const_name comma_crt_apply_shifted},
         @{const_name comma_crt_apply_shifted_from},
         @{const_name comma_crt_negate}, @{const_name comma_crt_equiv_check}]
      fun request_head request = Term.head_of request
      fun normalize_for request =
        let val bounded_request =
          (case request_head request of
            Const (name, _) => member (op =) bounded_column_heads name
          | _ => false)
        in Simplifier.full_rewrite
          (if bounded_request then bounded_column_context else context) end
      fun rules_for request =
        (case request_head request of
          Const (name, _) =>
            (case AList.lookup (op =) reflected name of
              SOME rules => rules
            | NONE => [])
        | _ => [])

      val slow_operation_reports = Unsynchronized.ref 0
      fun milliseconds started =
        Time.toMilliseconds (Time.- (Time.now (), started))

      fun constant_application name arity term =
        (case strip_comb term of
          (Const (head, _), arguments) =>
            if head = name andalso length arguments = arity
            then SOME arguments else NONE
        | _ => NONE)

      fun object_reflexivity term =
        Thm.reflexive (Thm.cterm_of context term) RS @{thm meta_eq_to_obj_eq}

      fun equality_value normalize equality =
        (case try HOLogic.dest_eq equality of
          SOME (left, right) =>
            if left aconv right then
              let
                val proposition = Thm.cterm_of context equality
                val rule = Drule.infer_instantiate context
                  [(("P", 0), proposition)] @{thm eqTrueI}
                val proof = object_reflexivity left
              in SOME (Thm.implies_elim rule proof RS @{thm eq_reflection}) end
            else
              let
                val reduced = normalize (Thm.cterm_of context equality)
                val result = Thm.term_of (Thm.rhs_of reduced)
              in if result aconv @{term True} orelse result aconv @{term False}
                 then SOME reduced else NONE end
        | NONE => NONE)

      fun list_all_term predicate items =
        Const (@{const_name list_all},
          fastype_of predicate --> fastype_of items --> @{typ bool}) $
          predicate $ items

      fun list_ex_term predicate items =
        Const (@{const_name list_ex},
          fastype_of predicate --> fastype_of items --> @{typ bool}) $
          predicate $ items

      val bool_root_rules = map_filter
        (try (fn rule => rule RS @{thm eq_reflection})) @{thms simp_thms}

      fun reduce_bool_root expected ct =
        let
          val conversion = Conv.rewrs_conv bool_root_rules ct
        in
          if Thm.term_of (Thm.rhs_of conversion) aconv expected then conversion
          else error "B1 Boolean root rewrite produced an unexpected result"
        end

      val list_all_cons = @{thm list_all_Cons_iff} RS @{thm eq_reflection}
      val list_all_nil = @{thm list_all_Nil_iff} RS @{thm eq_reflection}
      val list_ex_cons = @{thm list_ex_Cons_iff} RS @{thm eq_reflection}
      val list_ex_nil = @{thm list_ex_Nil_iff} RS @{thm eq_reflection}
      val node_cons = @{thm comma_crt_node_cons} RS @{thm eq_reflection}
      val support_node =
        @{thm comma_crt_supported_node_short_circuit} RS @{thm eq_reflection}
      val if_true = @{thm if_True} RS @{thm eq_reflection}
      val if_false = @{thm if_False} RS @{thm eq_reflection}

      fun list_all_conversion normalize predicate items =
        let
          val request = list_all_term predicate items
          val ct = Thm.cterm_of context request
        in
          (case list_shape items of
            SOME NONE => SOME (Conv.rewr_conv list_all_nil ct)
          | SOME (SOME (head, tail)) =>
              let
                val expanded = Conv.rewr_conv list_all_cons ct
                val tail_request = list_all_term predicate tail
                val head_request = predicate $ head
                val beta = Thm.beta_conversion true
                  (Thm.cterm_of context head_request)
                val comparison = Thm.term_of (Thm.rhs_of beta)
                val compared = equality_value normalize comparison
              in
                (case compared of
                  NONE => NONE
                | SOME comparison_conv =>
                    let
                      val after_head = argument_at 1
                        (Conv.rewr_conv comparison_conv) (Thm.rhs_of expanded)
                      val conjunction = Thm.term_of (Thm.rhs_of after_head)
                      val [head_value, _] = the (constant_application
                        @{const_name HOL.conj} 2 conjunction)
                      val truth =
                        if head_value aconv @{term True} then SOME true
                        else if head_value aconv @{term False} then SOME false
                        else NONE
                    in
                      (case truth of
                        NONE => NONE
                      | SOME true =>
                          let
                            val reduced = reduce_bool_root tail_request
                              (Thm.rhs_of after_head)
                            val rest = list_all_conversion normalize predicate tail
                          in Option.map (fn rest_conv =>
                            Thm.transitive expanded
                              (Thm.transitive after_head
                                (Thm.transitive reduced rest_conv))) rest end
                      | SOME false =>
                          let
                            val reduced = reduce_bool_root @{term False}
                              (Thm.rhs_of after_head)
                          in SOME (Thm.transitive expanded
                            (Thm.transitive after_head reduced)) end)
                    end)
              end
          | NONE => NONE)
        end

      fun list_ex_conversion normalize predicate items =
        let
          val request = list_ex_term predicate items
          val ct = Thm.cterm_of context request
        in
          (case list_shape items of
            SOME NONE => SOME (Conv.rewr_conv list_ex_nil ct)
          | SOME (SOME (head, tail)) =>
              let
                val expanded = Conv.rewr_conv list_ex_cons ct
                val tail_request = list_ex_term predicate tail
                val head_request = predicate $ head
                val beta = Thm.beta_conversion true
                  (Thm.cterm_of context head_request)
                val normalized_head = Thm.term_of (Thm.rhs_of beta)
                val head_conv = normalize (Thm.cterm_of context normalized_head)
                val head_value = Thm.term_of (Thm.rhs_of head_conv)
                val after_head = argument_at 1
                  (Conv.rewr_conv head_conv) (Thm.rhs_of expanded)
              in
                if head_value aconv @{term True} then
                  let
                    val reduced = reduce_bool_root @{term True}
                      (Thm.rhs_of after_head)
                  in SOME (Thm.transitive expanded
                    (Thm.transitive after_head reduced)) end
                else if head_value aconv @{term False} then
                  let
                    val reduced = reduce_bool_root tail_request
                      (Thm.rhs_of after_head)
                    val rest = list_ex_conversion normalize predicate tail
                  in Option.map (fn rest_conv =>
                    Thm.transitive expanded
                      (Thm.transitive after_head
                        (Thm.transitive reduced rest_conv))) rest end
                else NONE
              end
          | NONE => NONE)
        end

      fun smart_node normalize ct =
        (case constant_application @{const_name comma_crt_node} 2
            (Thm.term_of ct) of
          SOME [level, children] =>
            (case list_shape children of
              SOME (SOME (first, _)) =>
                let
                  val root = Conv.rewr_conv node_cons ct
                  val root_rhs = Thm.term_of (Thm.rhs_of root)
                in
                  (case constant_application @{const_name If} 3 root_rhs of
                    SOME [condition, _, _] =>
                      (case constant_application @{const_name list_all} 2 condition of
                        SOME [predicate, items] =>
                          (case list_all_conversion normalize predicate items of
                            SOME condition_conv =>
                              let
                                val truth = Thm.term_of
                                  (Thm.rhs_of condition_conv)
                                val if_condition = argument_at 2
                                  (Conv.rewr_conv condition_conv)
                                  (Thm.rhs_of root)
                                val branch_rule =
                                  if truth aconv @{term True} then if_true
                                  else if truth aconv @{term False} then if_false
                                  else error "B1 smart-node condition stayed open"
                                val branch = Conv.rewr_conv branch_rule
                                  (Thm.rhs_of if_condition)
                                val result = Thm.transitive root
                                  (Thm.transitive if_condition branch)
                                val expected = if truth aconv @{term True}
                                  then first
                                  else @{term "Comma_CRT_Node"} $ level $ children
                              in
                                if Thm.term_of (Thm.rhs_of result) aconv expected
                                then SOME result
                                else error "B1 smart-node selected an unexpected branch"
                              end
                          | NONE => NONE)
                      | NONE => NONE)
                  | NONE => NONE)
                end
            | _ => NONE)
        | _ => NONE)

      fun short_circuit_support normalize ct =
        (case constant_application @{const_name comma_crt_supported} 1
            (Thm.term_of ct) of
          SOME [column] =>
            (case strip_comb column of
              (Const (constructor, _), [_, _]) =>
                if constructor = @{const_name Comma_CRT_Node} then
                  let val root = Conv.rewr_conv support_node ct
                  in
                    (case constant_application @{const_name list_ex} 2
                        (Thm.term_of (Thm.rhs_of root)) of
                      SOME [predicate, items] =>
                        (case list_ex_conversion normalize predicate items of
                          SOME result => SOME (Thm.transitive root result)
                        | NONE => NONE)
                    | NONE => NONE)
                  end
                else NONE
            | _ => NONE)
        | _ => NONE)

      fun data_arguments normalize ct =
        let val term = Thm.term_of ct
        in
          if complete_value term then Conv.all_conv ct
          else
            (case term of
              _ $ _ => Conv.combination_conv (data_arguments normalize)
                (normalize_argument normalize) ct
            | _ => Conv.all_conv ct)
        end
      and normalize_argument normalize ct =
        let
          val term = Thm.term_of ct
          val constructor_root =
            (case (fastype_of term, Term.head_of term) of
              (Type (name, [_]), Const (head, _)) =>
                name = @{type_name list} andalso
                  member (op =) [@{const_name Nil}, @{const_name Cons}] head
            | (typ, Const (head, _)) => typ = column_type andalso
                member (op =) [@{const_name Comma_CRT_Bool},
                  @{const_name Comma_CRT_Node}] head
            | _ => false)
        in
          if complete_value term then Conv.all_conv ct
          else if constructor_root then data_arguments normalize ct
          else normalize ct
        end

      fun stage_operands normalize request ct =
        (case request_head request of
          Const (name, _) =>
            if name = @{const_name comma_crt_supported} then Conv.all_conv ct
            else (case AList.lookup (op =) final_argument_stagers name of
              SOME stage_final =>
                let
                  (* Normalize the completed accumulator as one exact request
                     before exposing the next cell; recursively normalizing
                     its arguments would rebuild the operational case/If result. *)
                  val stage_prefix = Conv.fun_conv
                    (Conv.arg_conv (normalize_argument normalize))
                  val prefix = stage_prefix ct
                  val final = Conv.arg_conv stage_final (Thm.rhs_of prefix)
                in Thm.transitive prefix final end
            | NONE => if member (op =) lazy_function_heads name then
              Conv.fun_conv (data_arguments normalize) ct
            else if member (op =) staged_heads name then data_arguments normalize ct
            else Conv.all_conv ct)
        | _ => Conv.all_conv ct)

      fun convert ct =
        let
          val request = Thm.term_of ct
          val normalize = normalize_for request
          val stage_started = Time.now ()
          val staged = stage_operands normalize request ct
          val stage_ms = milliseconds stage_started
          val staged_rhs = Thm.rhs_of staged
          val operands_unchanged = Thm.term_of staged_rhs aconv request
          val root_rules = rules_for request
          val root_started = Time.now ()
          val root_short_circuit =
            (case request_head request of
              Const (name, _) =>
                if name = @{const_name comma_crt_node} then
                  smart_node normalize staged_rhs
                else if name = @{const_name comma_crt_supported} then
                  short_circuit_support normalize staged_rhs
                else NONE
            | _ => NONE)
          val root_ms = milliseconds root_started
          val finish_started = Time.now ()
          val completed =
            (case root_short_circuit of
              SOME root => Thm.transitive staged root
            | NONE =>
                if null root_rules then Thm.transitive staged (normalize staged_rhs)
                else
                  let val root = Conv.try_conv (Conv.rewrs_conv root_rules) staged_rhs
                  in if Thm.is_reflexive root then
                       Thm.transitive staged (normalize staged_rhs)
                     else Thm.transitive staged
                       (Thm.transitive root (normalize (Thm.rhs_of root))) end)
          val finish_ms = milliseconds finish_started
          val total_ms = stage_ms + root_ms + finish_ms
          val operation_name = request_head request
          val operation_label =
            (case operation_name of
              Const (name, _) => Long_Name.base_name name
            | _ => "<non-constant>")
          val reportable =
            (case operation_name of
              Const (name, _) => member (op =)
                [@{const_name comma_crt_node},
                 @{const_name comma_crt_supported}] name
            | _ => false)
          val _ = if reportable andalso total_ms >= 20 andalso
              !slow_operation_reports < 10 then
            (slow_operation_reports := !slow_operation_reports + 1;
             Comma_Proof_Profile.report
               ("B1 CRT slow-root head=" ^ operation_label ^
                " stage_ms=" ^ LargeInt.toString stage_ms ^
                " root_ms=" ^ LargeInt.toString root_ms ^
                " finish_ms=" ^ LargeInt.toString finish_ms ^
                " total_ms=" ^ LargeInt.toString total_ms))
            else ()
        in {equation = completed, operands_unchanged = operands_unchanged}: staged_result end
    in convert end
  fun make_column_value_checker ctxt known_column =
    let
      val thy = Proof_Context.theory_of ctxt
      val mdd_name = Sign.intern_type thy "comma_crt_mdd"
      val control_name = Sign.intern_type thy "comma_crt_control"
      val mdd_leaf = Sign.intern_const thy "Comma_CRT_MDD_Leaf"
      val mdd_node = Sign.intern_const thy "Comma_CRT_MDD_Node"
      val control_live = Sign.intern_const thy "Comma_CRT_Control_Live"
      val control_stop = Sign.intern_const thy "Comma_CRT_Control_Stop"
      val control_invalid = Sign.intern_const thy "Comma_CRT_Control_Invalid"
      val nat_zero = Thm.term_of (Thm.rhs_of
        (Axclass.unoverload_conv ctxt
          (Thm.cterm_of ctxt @{term "0::nat"})))
      fun constructor name value =
        (case strip_comb value of
          (Const (head, _), arguments) =>
            if head = name then SOME arguments else NONE
        | _ => NONE)
      val column_cache = Synchronized.var
        "semantic_b1_column_value_subtrees" (Termtab.empty: bool Termtab.table)
      fun complete_nat value =
        if fastype_of value <> @{typ nat} then (false, 1)
        else if value aconv nat_zero then (true, 1)
        else
          (case try HOLogic.dest_number value of
            SOME (number_type, number) => (number_type = @{typ nat} andalso number >= 0, 1)
          | NONE =>
              (case constructor @{const_name Suc} value of
                SOME [predecessor] =>
                  let val (ok, count) = complete_nat predecessor
                  in (ok, count + 1) end
              | _ => (false, 1)))
      and complete_column_list value =
        if fastype_of value <> @{typ "comma_crt_column list"} then (false, 1)
        else
          (case constructor @{const_name Nil} value of
            SOME [] => (true, 1)
          | _ =>
              (case constructor @{const_name Cons} value of
                SOME [head, tail] =>
                  let
                    val (head_ok, head_count) = complete_column head
                    val (tail_ok, tail_count) = complete_column_list tail
                  in (head_ok andalso tail_ok, head_count + tail_count + 1) end
              | _ => (false, 1)))
      and complete_column value =
        (case Termtab.lookup (Synchronized.value column_cache) value of
          SOME valid => (valid, 0)
        | NONE =>
            let
              val result =
                if fastype_of value <> @{typ comma_crt_column} then (false, 1)
                else if known_column value then (true, 1)
                else
                  (case constructor @{const_name Comma_CRT_Bool} value of
                    SOME [flag] =>
                      ((flag aconv @{term True} orelse flag aconv @{term False}), 2)
                  | _ =>
                      (case constructor @{const_name Comma_CRT_Node} value of
                        SOME [level, children] =>
                          let
                            val (level_ok, level_count) = complete_nat level
                            val (children_ok, children_count) = complete_column_list children
                          in (level_ok andalso children_ok, 1 + level_count + children_count) end
                      | _ => (false, 1)))
              val _ = Synchronized.change column_cache (fn cache =>
                if Termtab.size cache < 65536 then
                  Termtab.update (value, #1 result) cache
                else cache)
            in result end)
      fun walk [] count = (true, count)
        | walk ((typ, value) :: rest) count =
            let
              val count' = count + 1
              fun continue children = walk (children @ rest) count'
              fun rejected () = (false, count')
            in
              if typ = @{typ bool} then
                if value aconv @{term True} orelse value aconv @{term False}
                then walk rest count' else rejected ()
              else if typ = @{typ nat} then
                (case try HOLogic.dest_number value of
                  SOME (number_type, number) =>
                    if number_type = @{typ nat} andalso number >= 0
                    then walk rest count' else rejected ()
                | NONE =>
                    if value aconv nat_zero then walk rest count'
                    else
                      (case constructor @{const_name Suc} value of
                        SOME [predecessor] =>
                          continue [(@{typ nat}, predecessor)]
                      | _ => rejected ()))
              else
                (case typ of
                  Type (name, [element]) =>
                    if name = @{type_name list} then
                      (case constructor @{const_name Nil} value of
                        SOME [] => walk rest count'
                      | _ =>
                          (case constructor @{const_name Cons} value of
                            SOME [head, tail] => continue
                              [(element, head), (typ, tail)]
                          | _ => rejected ()))
                    else if name = @{type_name option} then
                      (case constructor @{const_name None} value of
                        SOME [] => walk rest count'
                      | _ =>
                          (case constructor @{const_name Some} value of
                            SOME [payload] => continue [(element, payload)]
                          | _ => rejected ()))
                    else if name = mdd_name then
                      (case constructor mdd_leaf value of
                        SOME [leaf] => continue [(element, leaf)]
                      | _ =>
                          (case constructor mdd_node value of
                            SOME [level, children] => continue
                              [(@{typ nat}, level),
                               (Type (@{type_name list}, [typ]), children)]
                          | _ => rejected ()))
                    else rejected ()
                | Type (name, [left, right]) =>
                    if name = @{type_name prod} then
                      (case constructor @{const_name Pair} value of
                        SOME [first, second] => continue
                          [(left, first), (right, second)]
                      | _ => rejected ())
                    else rejected ()
                | Type (name, []) =>
                    if name = @{type_name comma_crt_column} then
                      let val (valid, visited) = complete_column value
                      in if valid then walk rest (count + visited) else rejected () end
                    else if name = @{type_name comma_semantic_b1_result} then
                      (case constructor @{const_name Comma_Semantic_B1_Live} value of
                        SOME [root] => continue [(@{typ nat}, root)]
                      | _ =>
                          (case constructor @{const_name Comma_Semantic_B1_Stop} value of
                            SOME [weight] => continue [(@{typ nat}, weight)]
                          | _ =>
                              (case constructor @{const_name Comma_Semantic_B1_Invalid} value of
                                SOME [] => walk rest count'
                              | _ => rejected ())))
                    else if name = control_name then
                      (case constructor control_live value of
                        SOME [root] => continue [(@{typ nat}, root)]
                      | _ =>
                          (case constructor control_stop value of
                            SOME [] => walk rest count'
                          | _ =>
                              (case constructor control_invalid value of
                                SOME [] => walk rest count'
                              | _ => rejected ())))
                    else if name = @{type_name comma_finite_position} then
                      (case constructor @{const_name Comma_Entry} value of
                        SOME [scale, delta, offset] => continue
                          [(@{typ nat}, scale), (@{typ nat}, delta),
                           (@{typ nat}, offset)]
                      | _ =>
                          (case constructor @{const_name Comma_Near} value of
                            SOME [scale, delta, headroom] => continue
                              [(@{typ nat}, scale), (@{typ nat}, delta),
                               (@{typ nat}, headroom)]
                          | _ => rejected ()))
                    else if name = @{type_name comma_source_continuation_action} then
                      (case constructor @{const_name Comma_Continuation_Goto} value of
                        SOME [source, shift] => continue
                          [(@{typ comma_finite_position}, source),
                           (@{typ nat}, shift)]
                      | _ =>
                          (case constructor @{const_name Comma_Continuation_Exit} value of
                            SOME [source, shift] => continue
                              [(@{typ comma_finite_position}, source),
                               (@{typ nat}, shift)]
                          | _ =>
                              (case constructor @{const_name Comma_Continuation_Fork} value of
                                SOME [scale, shift] => continue
                                  [(@{typ nat}, scale), (@{typ nat}, shift)]
                              | _ =>
                                  (case constructor @{const_name Comma_Continuation_Landmine} value of
                                    SOME [shift] => continue [(@{typ nat}, shift)]
                                  | _ =>
                                      (case constructor @{const_name Comma_Continuation_Invalid} value of
                                        SOME [] => walk rest count'
                                      | _ => rejected ())))))
                    else rejected ()
                | _ => rejected ())
            end
    in fn root =>
      let val (complete, nodes) = walk [(fastype_of root, root)] 0
      in {complete = complete, nodes = nodes}: value_status end
    end

  fun make_equation_checker_with_columns ctxt known_column =
    let
      fun make () =
        let
          val check_value = make_column_value_checker ctxt known_column
          val mdd_name = Sign.intern_type (Proof_Context.theory_of ctxt) "comma_crt_mdd"
          val completed_values = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
          val {validate = validate_equation, closed_reuse_hits} =
            Comma_Selected_List_Conversion.make_cached_equation_validator ()
          fun reusable_value value =
            (case fastype_of value of
              Type (name, []) => name = @{type_name comma_crt_column}
            | Type (name, [_]) => name = mdd_name
            | _ => false)
          fun validate request theorem =
            let
              val hits_before = closed_reuse_hits ()
              val checked = validate_equation request theorem
              val reused_closed = closed_reuse_hits () > hits_before
              val rhs = Thm.term_of (Thm.rhs_of checked)
              (* Check each theorem's authority first; the closedness and typed
                 constructor properties are exact-RHS facts and can then reuse. *)
              val reused_rhs = Termtab.defined (!completed_values) rhs
              val status =
                if reused_rhs then {complete = true, nodes = 0}: value_status
                else check_value rhs
              val _ = if not reused_rhs andalso #complete status andalso
                  reusable_value rhs andalso Termtab.size (!completed_values) < 8192
                then completed_values := Termtab.update (rhs, ()) (!completed_values)
                else ()
            in {equation = checked, status = status, reused_rhs = reused_rhs,
              reused_closed = reused_closed}: checked_equation
            end
          fun complete_value value = Termtab.defined (!completed_values) value
        in {check = validate, complete_value = complete_value}: equation_checker end

      val fixture_checker = make ()
      val fixture_validate = #check fixture_checker
      val first_request =
        @{term "comma_crt_node 0 [Comma_CRT_Bool True]"}
      val second_request =
        @{term "comma_crt_node 1 [Comma_CRT_Bool True]"}
      val expected_value = @{term "Comma_CRT_Bool True"}
      val fixture_context = ctxt addsimps @{thms comma_crt_node_def}
      val first_theorem = Simplifier.rewrite fixture_context
        (Thm.cterm_of ctxt first_request)
      val second_theorem = Simplifier.rewrite fixture_context
        (Thm.cterm_of ctxt second_request)
      val _ = if first_request aconv second_request then
          error "B1 exact completed-RHS fixture requests are not distinct"
        else ()
      val first_checked = fixture_validate first_request first_theorem
      val second_checked = fixture_validate second_request second_theorem
      val _ = if Thm.term_of (Thm.rhs_of (#equation first_checked)) aconv
          expected_value andalso
          Thm.term_of (Thm.rhs_of (#equation second_checked)) aconv expected_value andalso
          #complete (#status first_checked) andalso #complete (#status second_checked) andalso
          not (#reused_rhs first_checked) andalso #reused_rhs second_checked andalso
          not (#reused_closed first_checked) andalso #reused_closed second_checked andalso
          #nodes (#status second_checked) = 0
        then () else error "B1 exact completed-RHS reuse fixture failed"
      val forged_rejection = Exn.capture
        (fn () => fixture_validate second_request first_theorem) ()
      val _ =
        (case forged_rejection of
          Exn.Exn (ERROR message) =>
            if message = "selected-list conversion returned an open or mismatched theorem"
                andalso #reused_closed second_checked
            then () else error "B1 forged-theorem fixture failed for the wrong reason"
        | Exn.Exn failure => Exn.reraise failure
        | Exn.Res _ => error "B1 completed-RHS fixture accepted a forged theorem")
    in make () end
  fun selected_paint_memo_spec ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val roots = map (Sign.intern_const thy)
        ["comma_crt_mdd_paint_column", "comma_crt_mdd_node"]
      val patterns = map (Syntax.read_term ctxt)
        ["comma_crt_mdd_paint_column column current value",
         "comma_crt_mdd_node level children"]
    in {patterns = patterns, roots = roots} end

  fun bool_true_equation ctxt proposition proof =
    let
      val rule = Drule.infer_instantiate ctxt
        [(("P", 0), Thm.cterm_of ctxt proposition)] @{thm eqTrueI}
      val equation = Thm.implies_elim rule proof RS @{thm eq_reflection}
      val _ = if Thm.term_of (Thm.lhs_of equation) aconv proposition andalso
          Thm.term_of (Thm.rhs_of equation) aconv @{term True} andalso
          Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
          null (Thm.tpairs_of equation) then () else
            error "Boolean true equation changed its exact proposition"
    in equation end

  fun prove_column_at_admitted_header ctxt
      {request, dag, cid, lower, level, children, lookup} =
    let
      val theorem = Drule.infer_instantiate ctxt
        [(("dag", 0), Thm.cterm_of ctxt dag), (("cid", 0), Thm.cterm_of ctxt cid),
         (("level", 0), Thm.cterm_of ctxt level),
         (("children", 0), Thm.cterm_of ctxt children),
         (("lower", 0), Thm.cterm_of ctxt lower)]
        @{thm comma_semantic_b1_crt_column_at_admitted_at}
      val lookup_proof = lookup RS @{thm meta_eq_to_obj_eq}
      val with_lookup = Thm.implies_elim theorem lookup_proof
      val lower_bound = HOLogic.mk_binrel @{const_name less_eq} (lower, level)
      val bound_equation = Simplifier.rewrite
        (Comma_Entry_Arithmetic.natural_context ctxt)
        (Thm.cterm_of ctxt lower_bound)
      val _ = if Thm.term_of (Thm.rhs_of bound_equation) aconv @{term True}
        then () else error "B1 admission header bound did not reduce"
      val bound_prop_eq = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) bound_equation
      val bound_fact = Thm.equal_elim (Thm.symmetric bound_prop_eq) @{thm TrueI}
      val admitted = Thm.implies_elim with_lookup bound_fact
      val proposition = bool_true_equation ctxt request admitted
    in proposition end

  fun prove_nonfalse_from_step ctxt value false_column true_column value_step =
    let
      val proposition = HOLogic.mk_not (HOLogic.mk_eq (value, false_column))
      val stepped = Conv.arg_conv (Conv.fun_conv (Conv.arg_conv
        (Conv.rewr_conv value_step))) (Thm.cterm_of ctxt proposition)
      val body_ct = Thm.rhs_of value_step
      val body = Thm.term_of body_ct
      val body_fact = if body aconv true_column then
          @{thm comma_semantic_b1_crt_partition_true_nonfalse}
        else case strip_comb body of
          (Const (name, _), [_, _]) =>
            if name = @{const_name Comma_CRT_Node} then
              let
                val (node_level_ct, children_ct) = Thm.dest_comb body_ct
                val (_, level_ct) = Thm.dest_comb node_level_ct
              in Drule.infer_instantiate ctxt
                [(("level", 0), level_ct), (("children", 0), children_ct)]
                @{thm comma_semantic_b1_crt_partition_node_nonfalse} end
            else error "B1 non-false step produced an unsupported constructor"
        | _ => error "B1 non-false step did not produce a node or True"
      val reduced = Conv.rewr_conv (body_fact RS @{thm eq_reflection})
        (Thm.rhs_of stepped)
      val equation = Thm.transitive stepped reduced
      val _ = if Thm.term_of (Thm.lhs_of equation) aconv proposition andalso
          Thm.term_of (Thm.rhs_of equation) aconv @{term True} andalso
          Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
          null (Thm.tpairs_of equation) then () else
            error "B1 one-node non-false conversion changed its exact proposition"
      val proposition_equation = Thm.combination
        (Thm.reflexive (Thm.cterm_of ctxt @{term Trueprop})) equation
    in Thm.equal_elim (Thm.symmetric proposition_equation) @{thm TrueI} end
end
