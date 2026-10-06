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
  val reflect_boundaries: (string * thm list) list -> (string * thm list) list
  val make_staged_operation_converter:
    {context: Proof.context,
     boundaries: (string * thm list) list,
     staged_heads: string list, lazy_function_heads: string list,
     final_argument_stagers: (string * (cterm -> thm)) list,
     complete_value: term -> bool} ->
    cterm -> staged_result
  val make_indexed_zip_spine_stager:
    Proof.context ->
    {indexed_columns_def: thm, length_nil: thm, length_cons: thm} ->
    cterm -> thm
  val rewrite_conjuncts: (cterm -> thm) -> cterm -> thm
  val operation_context: Proof.context -> Proof.context
  val make_constructor_value_checker:
    Proof.context -> term -> value_status
  val make_equation_checker:
    Proof.context -> equation_checker
  val selected_paint_memo_spec:
    Proof.context -> {patterns: term list, roots: string list}
end

structure Comma_Semantic_B1_CRT_Operation_Conversion:
  COMMA_SEMANTIC_B1_CRT_OPERATION_CONVERSION =
struct
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

  type value_status = {complete: bool, nodes: int}
  type checked_equation =
    {equation: thm, status: value_status, reused_rhs: bool, reused_closed: bool}
  type equation_checker =
    {check: term -> thm -> checked_equation, complete_value: term -> bool}
  type staged_result = {equation: thm, operands_unchanged: bool}

  fun reflect_boundaries boundaries =
    map (fn (name, rules) =>
      (name, map (fn rule => rule RS @{thm eq_reflection}) rules)) boundaries

  (* Keep the proved operand-first policy in one owner.  Large parent
     operations must be normalized only after their admitted operands have
     been selected; blindly running the generated whole-program evaluator on
     the original term can expand both sides before the parent result exists. *)
  fun make_staged_operation_converter
      {context, boundaries, staged_heads, lazy_function_heads,
       final_argument_stagers, complete_value} =
    let
      val reflected = reflect_boundaries boundaries
      val column_type = @{typ comma_crt_column}
      (* CRT primitives may inspect finite period-sized lists made with upt.
         Keep range recursion local to those requests: the geometry fold's
         indexed suffix stays opaque until its selected-row stager exposes
         one cell. *)
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

      fun list_shape term =
        (case strip_comb term of
          (Const (name, _), []) =>
            if name = @{const_name Nil} then SOME NONE else NONE
        | (Const (name, _), [head, tail]) =>
            if name = @{const_name Cons} then SOME (SOME (head, tail)) else NONE
        | _ => NONE)

      fun argument_at index conversion ct =
        if index = 0 then Conv.arg_conv conversion ct
        else Conv.fun_conv (argument_at (index - 1) conversion) ct

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
                  (* The geometry-fold accumulator is itself a completed
                     column value.  Normalize that root as one exact request
                     before exposing the next indexed entry; recursively
                     normalizing only its arguments leaves case/If smart
                     constructor results operational and makes the next fold
                     step rebuild them. *)
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

  (* Expose one constructor of the indexed-column zip without simplifying its
     tail or the column payload.  This lets the recursive geometry fold own
     the list spine one cell at a time; ordinary simp on zip/upt traverses the
     complete suffix before the fold can memoize its child. *)
  fun make_indexed_zip_spine_stager ctxt
      {indexed_columns_def, length_nil, length_cons} =
    let
      val scalar_context = Comma_Entry_Arithmetic.natural_context ctxt addsimps
        @{thms pred_numeral_simps}
      val indexed_columns_rule = indexed_columns_def RS @{thm eq_reflection}
      val length_nil_rule = length_nil RS @{thm eq_reflection}
      val length_cons_rule = length_cons RS @{thm eq_reflection}
      val upt_rule = @{thm upt_rec} RS @{thm eq_reflection}
      val zip_nil_rule = @{thm zip_Nil} RS @{thm eq_reflection}
      val zip_right_nil_rule = @{thm zip.simps(1)} RS @{thm eq_reflection}
      val zip_cons_rule = @{thm zip_Cons_Cons} RS @{thm eq_reflection}
      val if_true_rule = @{thm if_True} RS @{thm eq_reflection}
      val if_false_rule = @{thm if_False} RS @{thm eq_reflection}

      fun args_of name arity ct =
        let val (head, args) = strip_comb (Thm.term_of ct)
        in
          (case head of
            Const (constant, _) =>
              if constant = name andalso length args = arity then args
              else error "B1 indexed-zip spine received a foreign application"
          | _ => error "B1 indexed-zip spine expected a constant application")
        end

      fun from_right index conversion ct =
        if index = 0 then Conv.arg_conv conversion ct
        else Conv.fun_conv (from_right (index - 1) conversion) ct

      fun list_shape term =
        (case strip_comb term of
          (Const (name, _), []) =>
            if name = @{const_name Nil} then SOME NONE else NONE
        | (Const (name, _), [head, tail]) =>
            if name = @{const_name Cons} then SOME (SOME (head, tail)) else NONE
        | _ => NONE)

      fun size_spine ct =
        let val [columns] = args_of @{const_name size} 1 ct
        in
          (case list_shape columns of
            SOME NONE => Conv.rewr_conv length_nil_rule ct
          | SOME (SOME _) =>
              let
                val root = Conv.rewr_conv length_cons_rule ct
                val tail = Conv.arg_conv size_spine (Thm.rhs_of root)
              in Thm.transitive root tail end
          | NONE => error "B1 indexed-zip length requires a literal list spine")
        end

      fun normalize_nat ct =
        let
          val term = Thm.term_of ct
          val structural =
            (case strip_comb term of
              (Const (name, _), [_]) =>
                if name = @{const_name size} then size_spine ct
                else Conv.all_conv ct
            | _ => Conv.all_conv ct)
          val arithmetic = Simplifier.rewrite scalar_context
            (Thm.rhs_of structural)
        in Thm.transitive structural arithmetic end

      fun expose_upt ct =
        (case list_shape (Thm.term_of ct) of
          SOME _ => Conv.all_conv ct
        | NONE =>
            let
              val [start, stop] = args_of @{const_name upt} 2 ct
              val start_eq = normalize_nat (Thm.cterm_of ctxt start)
              val start_step = from_right 1 (Conv.rewr_conv start_eq) ct
              val stop_eq = normalize_nat (Thm.cterm_of ctxt stop)
              val stop_step = from_right 0 (Conv.rewr_conv stop_eq)
                (Thm.rhs_of start_step)
              val prepared = Thm.transitive start_step stop_step
              val expanded = Conv.rewr_conv upt_rule (Thm.rhs_of prepared)
              val conditional = Thm.rhs_of expanded
              val [condition, _, _] = args_of @{const_name If} 3 conditional
              val condition_eq = Simplifier.rewrite scalar_context
                (Thm.cterm_of ctxt condition)
              val condition_step = from_right 2 (Conv.rewr_conv condition_eq)
                conditional
              val condition_value = Thm.term_of (Thm.rhs_of condition_eq)
              val branch_rule =
                if condition_value aconv @{term True} then if_true_rule
                else if condition_value aconv @{term False} then if_false_rule
                else error "B1 indexed-zip range condition did not normalize"
              val branch = Conv.rewr_conv branch_rule
                (Thm.rhs_of condition_step)
            in
              Thm.transitive prepared (Thm.transitive expanded
                (Thm.transitive condition_step branch))
            end)

      fun expose_zip ct =
        let val [left, right] = args_of @{const_name zip} 2 ct
        in
          (case list_shape right of
            SOME NONE => Conv.rewr_conv zip_right_nil_rule ct
          | SOME (SOME (_, _)) =>
              let
                val left_step = expose_upt
                  (Thm.cterm_of ctxt left)
                val with_left = from_right 1
                  (Conv.rewr_conv left_step) ct
                val [left_after, _] =
                  args_of @{const_name zip} 2 (Thm.rhs_of with_left)
              in
                (case list_shape left_after of
                  SOME NONE => Thm.transitive with_left
                    (Conv.rewr_conv zip_nil_rule (Thm.rhs_of with_left))
                | SOME (SOME _) => Thm.transitive with_left
                    (Conv.rewr_conv zip_cons_rule (Thm.rhs_of with_left))
                | NONE => error "B1 indexed-zip left spine stayed open")
              end
          | NONE =>
              (case list_shape left of
                SOME NONE => Conv.rewr_conv zip_nil_rule ct
              | _ => error "B1 indexed-zip right spine stayed open"))
        end

      fun expose_one ct =
        (case list_shape (Thm.term_of ct) of
          SOME _ => Conv.all_conv ct
        | NONE =>
            let
              val (head, arguments) = strip_comb (Thm.term_of ct)
            in
              (case head of
                Const (name, _) =>
                  if name = @{const_name comma_semantic_b1_crt_occurrence_indexed_columns}
                      andalso length arguments = 1 then
                    let val expanded = Conv.rewr_conv indexed_columns_rule ct
                    in Thm.transitive expanded (expose_zip (Thm.rhs_of expanded)) end
                  else if name = @{const_name zip} andalso length arguments = 2 then
                    expose_zip ct
                  else error "B1 geometry fold expected indexed columns or a list cell"
              | _ => error "B1 geometry fold entry spine has an unsupported shape")
            end)
    in expose_one end

  fun rewrite_conjuncts rewrite_leaf ct =
    (case try (HOLogic.dest_bin @{const_name HOL.conj} @{typ bool})
        (Thm.term_of ct) of
      SOME _ =>
        Conv.combination_conv
          (Conv.arg_conv (rewrite_conjuncts rewrite_leaf))
          (rewrite_conjuncts rewrite_leaf) ct
    | NONE => rewrite_leaf ct)

  fun make_constructor_value_checker ctxt =
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
                      (case constructor @{const_name Comma_CRT_Bool} value of
                        SOME [flag] => continue [(@{typ bool}, flag)]
                      | _ =>
                          (case constructor @{const_name Comma_CRT_Node} value of
                            SOME [level, children] => continue
                              [(@{typ nat}, level),
                               (@{typ "comma_crt_column list"}, children)]
                          | _ => rejected ()))
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
                    else rejected ()
                | _ => rejected ())
            end
    in fn root =>
      let val (complete, nodes) = walk [(fastype_of root, root)] 0
      in {complete = complete, nodes = nodes}: value_status end
    end

  fun make_equation_checker ctxt =
    let
      fun make () =
        let
          val check_value = make_constructor_value_checker ctxt
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
end
