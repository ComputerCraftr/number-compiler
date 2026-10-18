(* Production-shaped adversarial fixture for the shared Apply-DAG owner. *)
signature COMMA_SEMANTIC_B1_CRT_APPLY_DAG_PRODUCTION_FIXTURE =
sig
  type apply_owner =
   {convert: cterm -> thm option,
    stats: unit -> string,
    requests: unit -> int,
    recursive_certifications: unit -> int,
    cache_hits: unit -> int,
    retained_keys: unit -> int,
    fallbacks: unit -> int,
    derive_rejections: unit -> int,
    shortcut_applications: unit -> int}
  type column_authority =
   {known_column: term -> bool,
    column_value: int -> term,
    cofactor_transition: int * int * int -> {target_cid: int, theorem: thm},
    valid_column: term -> bool,
    normalize_column: cterm -> thm,
    reify_column: cterm -> thm}
  type column_comparison = {convert: cterm -> thm option, hits: unit -> int,
    misses: unit -> int, publications: unit -> int, resolutions: unit -> int}
  val check: Proof.context -> Proof.context -> apply_owner -> column_authority ->
    column_comparison -> unit
  val check_owner_fixtures: Proof.context -> apply_owner -> column_comparison ->
    (term -> thm -> bool) -> unit
end

structure Comma_Semantic_B1_CRT_Apply_DAG_Production_Fixture:
  COMMA_SEMANTIC_B1_CRT_APPLY_DAG_PRODUCTION_FIXTURE =
struct
  type apply_owner =
   {convert: cterm -> thm option,
    stats: unit -> string,
    requests: unit -> int,
    recursive_certifications: unit -> int,
    cache_hits: unit -> int,
    retained_keys: unit -> int,
    fallbacks: unit -> int,
    derive_rejections: unit -> int,
    shortcut_applications: unit -> int}
  type column_authority =
   {known_column: term -> bool,
    column_value: int -> term,
    cofactor_transition: int * int * int -> {target_cid: int, theorem: thm},
    valid_column: term -> bool,
    normalize_column: cterm -> thm,
    reify_column: cterm -> thm}
  type column_comparison = {convert: cterm -> thm option, hits: unit -> int,
    misses: unit -> int, publications: unit -> int, resolutions: unit -> int}

  fun check ctxt production_context owner authority comparison =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val applyT = @{typ
        "nat => nat => comma_crt_boolean_operation => comma_crt_column => comma_crt_column => comma_crt_column"}
      val and_op = Const (@{const_name Comma_CRT_And},
        @{typ comma_crt_boolean_operation})
      val or_op = Const (@{const_name Comma_CRT_Or},
        @{typ comma_crt_boolean_operation})
      val false_reference = #column_value authority 0
      val true_reference = #column_value authority 1
      val other_references = [#column_value authority 2, #column_value authority 3]
      val references = false_reference :: true_reference :: other_references
      val _ = if List.all (#known_column authority) references then ()
        else error "B1 production fixture lacks authenticated column references"
      val bool_column = Const (@{const_name Comma_CRT_Bool},
        @{typ bool} --> columnT)
      fun node_at level children = Const (@{const_name Comma_CRT_Node},
          natT --> HOLogic.listT columnT --> columnT) $
        HOLogic.mk_number natT level $ HOLogic.mk_list columnT children
      fun node children = node_at 0 children
      fun short_nat term =
        (case try HOLogic.dest_number term of
          SOME (_, value) => Int.toString value
        | NONE => "?")
      fun comparison_shape term =
        (case strip_comb term of
          (Const (name, _), arguments) =>
            if name = @{const_name comma_semantic_b1_crt_column_at} then
              (case arguments of [_, cid] => "column_at(" ^ short_nat cid ^ ")"
              | _ => "column_at/arity")
            else if name = @{const_name Comma_CRT_Node} then
              (case arguments of [level, children] =>
                "Node(level=" ^ short_nat level ^ ",width=" ^
                  (case try HOLogic.dest_list children of
                    SOME values => Int.toString (length values)
                  | NONE => "?") ^ ")"
              | _ => "Node/arity")
            else if name = @{const_name Comma_CRT_Bool} then
              (case arguments of [value] =>
                if value aconv @{term True} then "Bool(True)"
                else if value aconv @{term False} then "Bool(False)"
                else "Bool(?)"
              | _ => "Bool/arity")
            else Long_Name.base_name name ^ "/" ^ Int.toString (length arguments)
        | _ => "nonconstant")
      fun comparison_result left right =
        (case #convert comparison (Thm.cterm_of ctxt (HOLogic.mk_eq (left, right))) of
          SOME theorem =>
            let val rhs = Thm.term_of (Thm.rhs_of theorem)
            in
              if null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
                  null (Thm.tpairs_of theorem) andalso
                  null (Thm_Deps.all_oracles [theorem]) andalso
                  (rhs aconv @{term True} orelse rhs aconv @{term False})
              then SOME rhs else NONE
            end
        | NONE => NONE)
      val shared_reference_node = node
        [false_reference, false_reference, true_reference, true_reference]
      val shared_literal_node = node
        [bool_column $ @{term False}, false_reference, true_reference, true_reference]
      val shared_before_resolutions = #resolutions comparison ()
      val shared_first = comparison_result shared_reference_node shared_literal_node
      val shared_after_first_resolutions = #resolutions comparison ()
      val shared_hits_before_warm = #hits comparison ()
      val shared_second = comparison_result shared_reference_node shared_literal_node
      val shared_after_warm_resolutions = #resolutions comparison ()
      val shared_hits_after_warm = #hits comparison ()
      val first_difference_left = node
        [false_reference, true_reference, List.nth (other_references, 0),
         List.nth (other_references, 1)]
      val first_difference_right = node
        [true_reference, true_reference, List.nth (other_references, 0),
         List.nth (other_references, 1)]
      val first_difference_before_resolutions = #resolutions comparison ()
      val first_difference = comparison_result first_difference_left first_difference_right
      val first_difference_after_resolutions = #resolutions comparison ()
      val shared_hits_before_poison_check = #hits comparison ()
      val shared_after_difference =
        comparison_result shared_reference_node shared_literal_node
      val shared_after_difference_resolutions = #resolutions comparison ()
      val shared_hits_after_poison_check = #hits comparison ()
      val first_difference_hits_before_warm = #hits comparison ()
      val first_difference_warm = comparison_result
        first_difference_left first_difference_right
      val first_difference_after_warm_resolutions = #resolutions comparison ()
      val first_difference_hits_after_warm = #hits comparison ()
      val reverse_hits_before = #hits comparison ()
      val reverse_misses_before = #misses comparison ()
      val reverse_publications_before = #publications comparison ()
      val reverse_resolutions_before = #resolutions comparison ()
      val first_difference_reverse = comparison_result
        first_difference_right first_difference_left
      val reverse_hits_after = #hits comparison ()
      val reverse_misses_after = #misses comparison ()
      val reverse_publications_after = #publications comparison ()
      val reverse_resolutions_after = #resolutions comparison ()
      val comparison_fixtures = shared_first = SOME @{term True} andalso
        shared_second = SOME @{term True} andalso
        shared_after_first_resolutions > shared_before_resolutions andalso
        shared_after_warm_resolutions = shared_after_first_resolutions andalso
        shared_hits_after_warm > shared_hits_before_warm andalso
        first_difference = SOME @{term False} andalso
        shared_after_difference = SOME @{term True} andalso
        shared_after_difference_resolutions = first_difference_after_resolutions andalso
        shared_hits_after_poison_check > shared_hits_before_poison_check andalso
        first_difference_warm = SOME @{term False} andalso
        first_difference_after_resolutions - first_difference_before_resolutions = 2 andalso
        first_difference_after_warm_resolutions = first_difference_after_resolutions andalso
        first_difference_hits_after_warm > first_difference_hits_before_warm andalso
        first_difference_reverse = SOME @{term False} andalso
        reverse_hits_after > reverse_hits_before andalso
        reverse_misses_after = reverse_misses_before andalso
        reverse_publications_after = reverse_publications_before andalso
        reverse_resolutions_after = reverse_resolutions_before
      fun apply depth shift operation left right =
        Const (@{const_name comma_crt_apply_shifted_from}, applyT) $
          HOLogic.mk_number natT depth $ HOLogic.mk_number natT shift $
          operation $ left $ right
      val apply_comparison_left = node_at 1
        [false_reference, true_reference, false_reference]
      val apply_comparison_right = node_at 1
        [true_reference, true_reference, false_reference]
      val apply_comparison_request = apply 3 0 and_op
        apply_comparison_left apply_comparison_right
      val apply_comparison_before_requests = #requests owner ()
      val apply_comparison_before_fallbacks = #fallbacks owner ()
      val apply_comparison_before_rejections = #derive_rejections owner ()
      val apply_comparison_before_recursive = #recursive_certifications owner ()
      val apply_comparison = Simplifier.rewrite production_context
        (Thm.cterm_of ctxt apply_comparison_request)
      val apply_comparison_rhs = Thm.term_of (Thm.rhs_of apply_comparison)
      val expected_comparison_column = node_at 1
        [bool_column $ @{term False}, bool_column $ @{term True},
         bool_column $ @{term False}]
      val comparison_output_equality = comparison_result apply_comparison_rhs
        expected_comparison_column
      val evalT = @{typ "nat => comma_crt_column => bool"}
      fun eval_at phase column = Const (@{const_name comma_crt_eval}, evalT) $
        HOLogic.mk_number natT phase $ column
      val literal_comparison_column = node_at 1
        [bool_column $ @{term False}, bool_column $ @{term True},
         bool_column $ @{term False}]
      val comparison_true_request = eval_at 1 literal_comparison_column
      val comparison_false_request = eval_at 0 literal_comparison_column
      val comparison_last_request = eval_at 2 literal_comparison_column
      val comparison_true_oracle = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt comparison_true_request)
      val comparison_false_oracle = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt comparison_false_request)
      val comparison_last_oracle = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt comparison_last_request)
      val comparison_point_oracle =
        Thm.term_of (Thm.lhs_of comparison_true_oracle) aconv comparison_true_request andalso
        Thm.term_of (Thm.rhs_of comparison_true_oracle) aconv @{term True} andalso
        Thm.term_of (Thm.lhs_of comparison_false_oracle) aconv comparison_false_request andalso
        Thm.term_of (Thm.rhs_of comparison_false_oracle) aconv @{term False} andalso
        Thm.term_of (Thm.lhs_of comparison_last_oracle) aconv comparison_last_request andalso
        Thm.term_of (Thm.rhs_of comparison_last_oracle) aconv @{term False} andalso
        null (Thm.prems_of comparison_true_oracle) andalso
        null (Thm.hyps_of comparison_true_oracle) andalso
        null (Thm.tpairs_of comparison_true_oracle) andalso
        null (Thm_Deps.all_oracles [comparison_true_oracle]) andalso
        null (Thm.prems_of comparison_false_oracle) andalso
        null (Thm.hyps_of comparison_false_oracle) andalso
        null (Thm.tpairs_of comparison_false_oracle) andalso
        null (Thm_Deps.all_oracles [comparison_false_oracle]) andalso
        null (Thm.prems_of comparison_last_oracle) andalso
        null (Thm.hyps_of comparison_last_oracle) andalso
        null (Thm.tpairs_of comparison_last_oracle) andalso
        null (Thm_Deps.all_oracles [comparison_last_oracle])
      val comparison_lhs_exact =
        Thm.term_of (Thm.lhs_of apply_comparison) aconv apply_comparison_request
      val comparison_reified_matches =
        comparison_output_equality = SOME @{term True}
      val comparison_column_valid = #valid_column authority apply_comparison_rhs
      val comparison_theorem_clean = null (Thm.prems_of apply_comparison) andalso
        null (Thm.hyps_of apply_comparison) andalso
        null (Thm.tpairs_of apply_comparison) andalso
        null (Thm_Deps.all_oracles [apply_comparison])
      val comparison_owner_work =
        #requests owner () > apply_comparison_before_requests andalso
        #recursive_certifications owner () > apply_comparison_before_recursive andalso
        #fallbacks owner () = apply_comparison_before_fallbacks andalso
        #derive_rejections owner () = apply_comparison_before_rejections
      val apply_comparison_correct = comparison_lhs_exact andalso
        comparison_reified_matches andalso comparison_point_oracle andalso
        comparison_column_valid andalso comparison_theorem_clean andalso
        comparison_owner_work
      val scope = @{term "comma_crt_source_scope_column (28,27)"}
      val axis = @{term "comma_crt_source_axis_column 2 7 27"}
      (* The production wrapper starts at level 0 and descends all four
         cyclotomic coordinates.  A depth-1 call would start at level 3 and
         make this period-28 fixture exercise the default branch instead. *)
      val nested = apply 4 7 or_op axis false_reference
      (* Both the source scope and the nested axis contain phase 27 after the
         outer +7 transport: the level-2 clock has period 7.  The nested
         nonzero shift is erased by Or's false-right shortcut. *)
      val request = apply 4 7 and_op scope nested
      val before_fallbacks = #fallbacks owner ()
      val before_rejections = #derive_rejections owner ()
      val before_requests = #requests owner ()
      val before_recursive = #recursive_certifications owner ()
      val before_hits = #cache_hits owner ()
      val first = Simplifier.rewrite production_context (Thm.cterm_of ctxt request)
      val after_fallbacks = #fallbacks owner ()
      val after_rejections = #derive_rejections owner ()
      val after_requests = #requests owner ()
      val after_recursive = #recursive_certifications owner ()
      val first_rhs = Thm.term_of (Thm.rhs_of first)
      val oracle = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt request)
      val actual_named = #reify_column authority (Thm.rhs_of first)
      val oracle_named = #reify_column authority (Thm.rhs_of oracle)
      val evalT = @{typ "nat => comma_crt_column => bool"}
      val eval_at_27 = Const (@{const_name comma_crt_eval}, evalT) $
        HOLogic.mk_number natT 27 $ Thm.term_of (Thm.rhs_of oracle)
      val nonfalse_eval = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt eval_at_27)
      val nonfalse_eval_exact = Thm.term_of (Thm.lhs_of nonfalse_eval) aconv eval_at_27
      val nonfalse_eval_oracle_free = null (Thm_Deps.all_oracles [nonfalse_eval])
      val bool_leaf_eval_request = Const (@{const_name comma_crt_eval}, evalT) $
        HOLogic.mk_number natT 27 $ @{term "Comma_CRT_Bool True"}
      val bool_leaf_eval = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt bool_leaf_eval_request)
      val bool_leaf_code =
        Thm.term_of (Thm.lhs_of bool_leaf_eval) aconv bool_leaf_eval_request andalso
        Thm.term_of (Thm.rhs_of bool_leaf_eval) aconv @{term True} andalso
        null (Thm.prems_of bool_leaf_eval) andalso null (Thm.hyps_of bool_leaf_eval) andalso
        null (Thm.tpairs_of bool_leaf_eval) andalso
        null (Thm_Deps.all_oracles [bool_leaf_eval])
      val nonfalse_result = nonfalse_eval_exact andalso
        Thm.term_of (Thm.rhs_of nonfalse_eval) aconv @{term True} andalso
        null (Thm.prems_of nonfalse_eval) andalso null (Thm.hyps_of nonfalse_eval) andalso
        null (Thm.tpairs_of nonfalse_eval) andalso nonfalse_eval_oracle_free andalso
        bool_leaf_code
      fun excerpt term =
        let val rendered = XML.content_of (YXML.parse_body
              (Syntax.string_of_term ctxt term))
        in String.substring (rendered, 0, Int.min (512, String.size rendered)) end
      fun eval_probe term =
        (case try (fn () => Code_Simp.dynamic_conv ctxt
            (Thm.cterm_of ctxt
              (Const (@{const_name comma_crt_eval}, evalT) $
                HOLogic.mk_number natT 27 $ term))) () of
          SOME theorem => excerpt (Thm.term_of (Thm.rhs_of theorem))
        | NONE => "<conversion failed>")
      fun nonfalse_diagnostic () =
        "phase27 probes: scope=" ^ eval_probe scope ^
        " axis=" ^ eval_probe axis ^ " false_ref=" ^ eval_probe false_reference ^
        " nested=" ^ eval_probe nested ^ " raw_result=" ^
        excerpt (Thm.term_of (Thm.rhs_of nonfalse_eval))
      val second = Simplifier.rewrite production_context (Thm.cterm_of ctxt request)
      val after_warm_fallbacks = #fallbacks owner ()
      val after_warm_rejections = #derive_rejections owner ()
      val after_warm_recursive = #recursive_certifications owner ()
      val after_warm_hits = #cache_hits owner ()
      fun has_unresolved term =
        let
          val names = [@{const_name comma_crt_apply},
            @{const_name comma_crt_apply_from},
            @{const_name comma_crt_apply_shifted},
            @{const_name comma_crt_apply_shifted_from},
            @{const_name comma_crt_source_scope_column},
            @{const_name comma_crt_source_axis_column}]
          fun visit current =
            (case Term.head_of current of
              Const (name, _) => member (op =) names name
            | _ => false) orelse exists visit (Term.args_of current)
        in visit term end
      val normalize_column = #normalize_column authority
      fun literal_bool term =
        Term.head_of term = @{term True} orelse Term.head_of term = @{term False}
      fun check_cofactor_normalizer () =
        let
          fun request level digit shift column =
            if shift = 0 then Const (@{const_name comma_crt_cofactor_or_false},
              natT --> natT --> columnT --> columnT) $
                HOLogic.mk_number natT level $ HOLogic.mk_number natT digit $ column
            else Const (@{const_name comma_crt_shifted_cofactor_or_false},
              natT --> natT --> natT --> columnT --> columnT) $
                HOLogic.mk_number natT level $ HOLogic.mk_number natT digit $
                HOLogic.mk_number natT shift $ column
          fun transition_result (level, digit, cid) =
            let
              val {target_cid, theorem} = (#cofactor_transition authority)
                (level, digit, cid)
              val lhs = request level digit 0 (#column_value authority cid)
              val result = Thm.term_of (Thm.rhs_of theorem)
            in
              if target_cid >= 0 andalso Thm.term_of (Thm.lhs_of theorem) aconv lhs andalso
                  result aconv (#column_value authority target_cid) andalso
                  (#known_column authority) result andalso null (Thm.prems_of theorem) andalso
                  null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
                  null (Thm_Deps.all_oracles [theorem]) then result
              else error "B1 cofactor fixture received a malformed transition"
            end
          fun exact requested expected =
            let
              val theorem = normalize_column (Thm.cterm_of ctxt requested)
              val result = Thm.term_of (Thm.rhs_of theorem)
            in
              Thm.term_of (Thm.lhs_of theorem) aconv requested andalso
                result aconv expected andalso (#valid_column authority) result andalso
                null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
                null (Thm.tpairs_of theorem) andalso
                null (Thm_Deps.all_oracles [theorem])
            end
          val base = transition_result (0, 0, 2)
          val phase = transition_result (0, 1, 2)
          val other_source = transition_result (0, 1, 3)
          val other_clock = transition_result (1, 1, 2)
          val transported =
            [exact (request 0 0 0 (#column_value authority 2)) base,
             exact (request 0 0 4 (#column_value authority 2)) base,
             exact (request 0 0 1 (#column_value authority 2)) phase,
             exact (request 0 0 1 (#column_value authority 3)) other_source,
             exact (request 1 0 4 (#column_value authority 2)) other_clock]
          val literal_node = node_at 1
            [bool_column $ @{term False}, bool_column $ @{term True},
             bool_column $ @{term False}]
          val literal_fallback = exact (request 1 1 0 literal_node)
            (#column_value authority 1)
          val opaque = Free ("opaque_cofactor", columnT)
          val no_progress_refused =
            (case Exn.capture (fn () => normalize_column
                (Thm.cterm_of ctxt (request 0 0 0 opaque))) () of
              Exn.Res _ => false
            | Exn.Exn _ => true)
          val foreign_refused =
            (case strip_comb (#column_value authority 2) of
              (head as Const (_, _), [_, cid]) =>
                let
                  val foreign = head $ @{term Comma_B1_CRT_Column_DAG_Empty} $ cid
                in
                  (case Exn.capture (fn () => normalize_column
                      (Thm.cterm_of ctxt (request 0 0 1 foreign))) () of
                    Exn.Res _ => false
                  | Exn.Exn _ => true)
                end
            | _ => false)
        in
          if List.all (fn result => result) transported andalso literal_fallback andalso
              no_progress_refused andalso foreign_refused then ()
          else error "B1 source cofactor normalization fixture failed"
        end
      val _ = check_cofactor_normalizer ()
      val arithmetic_axis = @{term
        "comma_crt_source_axis_column (0+0) (2*2) (7 mod 4)"}
      val arithmetic_axis_equation = normalize_column
        (Thm.cterm_of ctxt arithmetic_axis)
      val arithmetic_axis_result = Thm.term_of
        (Thm.rhs_of arithmetic_axis_equation)
      val arithmetic_axis_valid =
        Thm.term_of (Thm.lhs_of arithmetic_axis_equation) aconv arithmetic_axis andalso
        #valid_column authority arithmetic_axis_result andalso
        null (Thm.prems_of arithmetic_axis_equation) andalso
        null (Thm.hyps_of arithmetic_axis_equation) andalso
        null (Thm.tpairs_of arithmetic_axis_equation) andalso
        null (Thm_Deps.all_oracles [arithmetic_axis_equation])
      fun eval_at phase column =
        Const (@{const_name comma_crt_eval}, evalT) $
          HOLogic.mk_number natT phase $ column
      fun oracle_true theorem request =
        Thm.term_of (Thm.lhs_of theorem) aconv request andalso
        Thm.term_of (Thm.rhs_of theorem) aconv @{term True} andalso
        null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso null (Thm_Deps.all_oracles [theorem])
      val arithmetic_axis_point = eval_at 3 arithmetic_axis
      val arithmetic_axis_point_theorem = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt arithmetic_axis_point)
      val arithmetic_axis_point_true =
        oracle_true arithmetic_axis_point_theorem arithmetic_axis_point
      val computed_boolean = Const (@{const_name Comma_CRT_Bool},
        @{typ bool} --> columnT) $ @{term "(7::nat) mod 4 = 3"}
      val computed_boolean_equation = normalize_column
        (Thm.cterm_of ctxt computed_boolean)
      val computed_boolean_result = Thm.term_of
        (Thm.rhs_of computed_boolean_equation)
      val computed_boolean_literal =
        (case strip_comb computed_boolean_result of
          (Const (name, _), [flag]) =>
            name = @{const_name Comma_CRT_Bool} andalso literal_bool flag
        | _ => false)
      val invalid_unselected_axis = @{term "comma_crt_source_axis_column 2 7 924"}
      val poisoned_axis = Const (@{const_name If},
        @{typ bool} --> columnT --> columnT --> columnT) $
        @{term "(7::nat) mod 4 = 3"} $ arithmetic_axis $ invalid_unselected_axis
      val poisoned_axis_equation = normalize_column (Thm.cterm_of ctxt poisoned_axis)
      val poisoned_axis_result = Thm.term_of (Thm.rhs_of poisoned_axis_equation)
      val poisoned_axis_selected =
        Thm.term_of (Thm.lhs_of poisoned_axis_equation) aconv poisoned_axis andalso
        #valid_column authority poisoned_axis_result andalso
        not (Term.exists_subterm (fn term =>
          (case Term.head_of term of
            Const (name, _) => name = @{const_name If} orelse
              name = @{const_name comma_crt_source_axis_column}
          | _ => false)) poisoned_axis_result)
      val poisoned_axis_point = eval_at 3 poisoned_axis
      val poisoned_axis_point_theorem = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt poisoned_axis_point)
      val poisoned_axis_point_true =
        oracle_true poisoned_axis_point_theorem poisoned_axis_point
      val scope22 = @{term "comma_crt_source_scope_column (22,21)"}
      val scope22_equation = normalize_column (Thm.cterm_of ctxt scope22)
      val scope22_result = Thm.term_of (Thm.rhs_of scope22_equation)
      val scope22_valid =
        Thm.term_of (Thm.lhs_of scope22_equation) aconv scope22 andalso
        #valid_column authority scope22_result andalso
        not (has_unresolved scope22_result) andalso
        null (Thm.prems_of scope22_equation) andalso
        null (Thm.hyps_of scope22_equation) andalso
        null (Thm.tpairs_of scope22_equation) andalso
        null (Thm_Deps.all_oracles [scope22_equation])
      val scope22_point = eval_at 21 scope22
      val scope22_point_theorem = Code_Simp.dynamic_conv ctxt
        (Thm.cterm_of ctxt scope22_point)
      val scope22_point_true = oracle_true scope22_point_theorem scope22_point
      val malformed_bool = Const (@{const_name Comma_CRT_Bool},
        @{typ bool} --> columnT) $ Free ("unclosed_flag", @{typ bool})
      val malformed_if = Const (@{const_name If},
        @{typ bool} --> columnT --> columnT --> columnT) $
        Free ("unclosed_guard", @{typ bool}) $ true_reference $ false_reference
      val rejects_nonliteral_bool = not (#valid_column authority malformed_bool)
      val rejects_unresolved_if = not (#valid_column authority malformed_if)
      val open_guard = Const (@{const_name If},
        @{typ bool} --> columnT --> columnT --> columnT) $
        Free ("fixture_guard", @{typ bool}) $ true_reference $ false_reference
      val open_guard_equation = normalize_column (Thm.cterm_of ctxt open_guard)
      val open_guard_refused = Thm.is_reflexive open_guard_equation
      fun check_closed_guard condition selects_true =
        let
          val invalid_unselected = @{term "comma_crt_source_axis_column 2 7 924"}
          val if_column = Const (@{const_name If},
            @{typ bool} --> columnT --> columnT --> columnT)
          val conditional = if selects_true then
              if_column $ condition $ true_reference $ invalid_unselected
            else if_column $ condition $ invalid_unselected $ true_reference
          val guarded_request = apply 4 7 and_op scope conditional
          val before_guard_fallbacks = #fallbacks owner ()
          val before_guard_rejections = #derive_rejections owner ()
          val before_guard_requests = #requests owner ()
          val before_guard_recursive = #recursive_certifications owner ()
          val before_guard_hits = #cache_hits owner ()
          val before_guard_shortcuts = #shortcut_applications owner ()
          val first_guard = Simplifier.rewrite production_context
            (Thm.cterm_of ctxt guarded_request)
          val after_guard_fallbacks = #fallbacks owner ()
          val after_guard_rejections = #derive_rejections owner ()
          val after_guard_requests = #requests owner ()
          val after_guard_recursive = #recursive_certifications owner ()
          val after_guard_hits = #cache_hits owner ()
          val after_guard_shortcuts = #shortcut_applications owner ()
          val guard_rhs = Thm.term_of (Thm.rhs_of first_guard)
          val guard_oracle = Code_Simp.dynamic_conv ctxt
            (Thm.cterm_of ctxt guarded_request)
          val actual_guard = #reify_column authority (Thm.rhs_of first_guard)
          val oracle_guard = #reify_column authority (Thm.rhs_of guard_oracle)
          fun certified theorem = null (Thm.prems_of theorem) andalso
            null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
            null (Thm_Deps.all_oracles [theorem])
          val exact_guard = Thm.term_of (Thm.lhs_of first_guard) aconv guarded_request andalso
            Thm.term_of (Thm.lhs_of guard_oracle) aconv guarded_request andalso
            Thm.term_of (Thm.rhs_of actual_guard) aconv Thm.term_of (Thm.rhs_of oracle_guard) andalso
            certified first_guard andalso certified guard_oracle andalso
            certified actual_guard andalso certified oracle_guard
          val point_request = Const (@{const_name comma_crt_eval}, evalT) $
            HOLogic.mk_number natT 27 $ Thm.term_of (Thm.rhs_of guard_oracle)
          val point = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt point_request)
          val exact_point = Thm.term_of (Thm.lhs_of point) aconv point_request andalso
            Thm.term_of (Thm.rhs_of point) aconv @{term True} andalso
            null (Thm.prems_of point) andalso null (Thm.hyps_of point) andalso
            null (Thm.tpairs_of point) andalso null (Thm_Deps.all_oracles [point])
          val selected_only = not (has_unresolved guard_rhs)
          val first_work = after_guard_requests > before_guard_requests andalso
            (after_guard_recursive > before_guard_recursive orelse
              after_guard_hits > before_guard_hits orelse
              after_guard_shortcuts > before_guard_shortcuts)
          val first_clean = after_guard_fallbacks = before_guard_fallbacks andalso
            after_guard_rejections = before_guard_rejections
          val second_guard = Simplifier.rewrite production_context
            (Thm.cterm_of ctxt guarded_request)
          val after_warm_fallbacks = #fallbacks owner ()
          val after_warm_rejections = #derive_rejections owner ()
          val after_warm_recursive = #recursive_certifications owner ()
          val after_warm_hits = #cache_hits owner ()
          val after_warm_shortcuts = #shortcut_applications owner ()
          val warm = not (Thm.is_reflexive second_guard) andalso
            after_warm_recursive = after_guard_recursive andalso
            after_warm_fallbacks = after_guard_fallbacks andalso
            after_warm_rejections = after_guard_rejections andalso
            (after_warm_hits > after_guard_hits orelse
              after_warm_shortcuts > after_guard_shortcuts)
        in exact_guard andalso exact_point andalso selected_only andalso first_work andalso
          first_clean andalso not (Thm.is_reflexive first_guard) andalso warm end
      val closed_true_guard = check_closed_guard
        @{term "(27::nat) mod 7 = 6"} true
      val closed_false_guard = check_closed_guard
        @{term "(27::nat) mod 7 = 5"} false
      fun named label value = label ^ "=" ^ Bool.toString value
      val exact_lhs = Thm.term_of (Thm.lhs_of first) aconv request
      val oracle_lhs = Thm.term_of (Thm.lhs_of oracle) aconv request
      val same_named_rhs = Thm.term_of (Thm.rhs_of actual_named) aconv
        Thm.term_of (Thm.rhs_of oracle_named)
      val result_type = fastype_of first_rhs = columnT
      val result_closed = not (Term.is_open first_rhs)
      val result_resolved = not (has_unresolved first_rhs)
      val theorem_closed = null (Thm.prems_of first) andalso
        null (Thm.hyps_of first) andalso null (Thm.tpairs_of first)
      val theorem_oracle_free = null (Thm_Deps.all_oracles [first])
      val exact_result = List.all I
        [exact_lhs, oracle_lhs, same_named_rhs, result_type, result_closed,
         result_resolved, theorem_closed, theorem_oracle_free]
      val column_at = @{const_name comma_semantic_b1_crt_column_at}
      val (dag, _) =
        (case Term.strip_comb false_reference of
          (Const (name, _), [dag, _]) =>
            if name = column_at then (dag, ())
            else error "B1 production fixture expected an owned column_at reference"
        | _ => error "B1 production fixture malformed its owned column reference")
      val dagT = fastype_of dag
      val unoverloaded_zero = Thm.term_of (Thm.rhs_of
        (Axclass.unoverload_conv ctxt
          (Thm.cterm_of ctxt (@{term "0::nat"}))))
      val unoverloaded_one = Const (@{const_name Suc}, natT --> natT) $
        unoverloaded_zero
      val column_at_const = Const (column_at, dagT --> natT --> columnT)
      val zero_reference = column_at_const $ dag $ unoverloaded_zero
      val one_reference = column_at_const $ dag $ unoverloaded_one
      (* Alternate closed Nat syntax is normalized by the exact converter
         before catalogue admission; the raw alias itself is not a catalogue
         identity. *)
      val unoverloaded_aliases_not_ids =
        not (#known_column authority zero_reference) andalso
        not (#known_column authority one_reference)
      val zero_reference_request = apply 0 0 and_op zero_reference one_reference
      val canonical_zero_reference = column_at_const $ dag $ HOLogic.mk_number natT 0
      val canonical_one_reference = column_at_const $ dag $ HOLogic.mk_number natT 1
      val canonical_zero_request = apply 0 0 and_op
        canonical_zero_reference canonical_one_reference
      val zero_reference_result_canonical = #convert owner
        (Thm.cterm_of ctxt canonical_zero_request)
      val zero_reference_recursive_after_canonical =
        #recursive_certifications owner ()
      val zero_reference_hits_before_alias = #cache_hits owner ()
      val zero_reference_keys_before_alias = #retained_keys owner ()
      val zero_reference_recursive_before_alias = #recursive_certifications owner ()
      val zero_reference_shortcuts_before_alias = #shortcut_applications owner ()
      val zero_reference_result = #convert owner
        (Thm.cterm_of ctxt zero_reference_request)
      val zero_reference_keys_after_alias = #retained_keys owner ()
      val zero_reference_recursive_after_alias = #recursive_certifications owner ()
      val zero_reference_hits_after_alias = #cache_hits owner ()
      val zero_reference_shortcuts_after_alias = #shortcut_applications owner ()
      val zero_reference_exact =
        (case (zero_reference_result, zero_reference_result_canonical) of
          (SOME theorem, SOME canonical_theorem) =>
            Thm.term_of (Thm.lhs_of theorem) aconv zero_reference_request andalso
            #valid_column authority (Thm.term_of (Thm.rhs_of theorem)) andalso
            Thm.term_of (Thm.rhs_of theorem) aconv
              Thm.term_of (Thm.rhs_of canonical_theorem) andalso
            null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso
            null (Thm_Deps.all_oracles [theorem]) andalso
            Thm.term_of (Thm.lhs_of canonical_theorem) aconv canonical_zero_request andalso
            null (Thm.prems_of canonical_theorem) andalso
            null (Thm.hyps_of canonical_theorem) andalso
            null (Thm.tpairs_of canonical_theorem) andalso
            null (Thm_Deps.all_oracles [canonical_theorem]) andalso
            zero_reference_keys_after_alias = zero_reference_keys_before_alias andalso
            zero_reference_recursive_after_alias = zero_reference_recursive_before_alias andalso
            zero_reference_recursive_after_alias = zero_reference_recursive_after_canonical andalso
            zero_reference_hits_after_alias > zero_reference_hits_before_alias andalso
            zero_reference_shortcuts_after_alias = zero_reference_shortcuts_before_alias
        | _ => false)
      val foreign = Const (column_at, dagT --> natT --> columnT) $
        Free ("foreign_fixture_dag", dagT) $ HOLogic.mk_number natT 0
      val outside = Const (column_at, dagT --> natT --> columnT) $
        dag $ HOLogic.mk_number natT 1000000
      val rejected_foreign = not (Option.isSome (#convert owner
        (Thm.cterm_of ctxt (apply 0 0 and_op foreign true_reference))))
      val rejected_outside = not (Option.isSome (#convert owner
        (Thm.cterm_of ctxt (apply 0 0 and_op outside true_reference))))
      val fresh_request = after_requests > before_requests
      val recursive_work = after_recursive > before_recursive
      val first_no_fallback = after_fallbacks = before_fallbacks
      val first_no_rejection = after_rejections = before_rejections
      val warm_nonreflexive = not (Thm.is_reflexive second)
      val warm_no_recursion = after_warm_recursive = after_recursive
      val warm_no_fallback = after_warm_fallbacks = after_fallbacks
      val warm_no_rejection = after_warm_rejections = after_rejections
      val warm_hit = after_warm_hits > before_hits
      val all_checks = exact_result andalso nonfalse_result andalso comparison_fixtures andalso
        apply_comparison_correct andalso
        arithmetic_axis_valid andalso computed_boolean_literal andalso
        arithmetic_axis_point_true andalso poisoned_axis_selected andalso
        poisoned_axis_point_true andalso scope22_valid andalso scope22_point_true andalso
        rejects_nonliteral_bool andalso
        rejects_unresolved_if andalso unoverloaded_aliases_not_ids andalso
        zero_reference_exact andalso
        closed_true_guard andalso closed_false_guard andalso open_guard_refused andalso
        not (Thm.is_reflexive first) andalso fresh_request andalso recursive_work andalso
        first_no_fallback andalso first_no_rejection andalso warm_nonreflexive andalso
        warm_no_recursion andalso warm_no_fallback andalso warm_no_rejection andalso
        warm_hit andalso rejected_foreign andalso rejected_outside
      fun failure_checks () = String.concatWith " "
        [named "exact_lhs" exact_lhs, named "oracle_lhs" oracle_lhs,
         named "column_comparison_first_difference_and_warm_cache" comparison_fixtures,
         named "column_comparison_actual_apply_owner" apply_comparison_correct,
         named "column_comparison_actual_lhs" comparison_lhs_exact,
         named "column_comparison_actual_reified_shape" comparison_reified_matches,
         named "column_comparison_point_oracle" comparison_point_oracle,
         named "column_comparison_actual_valid" comparison_column_valid,
         named "column_comparison_actual_clean" comparison_theorem_clean,
         named "column_comparison_actual_owner_work" comparison_owner_work,
         "actual_apply_shape=" ^ comparison_shape apply_comparison_rhs,
         "expected_apply_shape=" ^ comparison_shape expected_comparison_column,
         named "same_named_rhs" same_named_rhs, named "result_type" result_type,
         named "result_closed" result_closed, named "result_resolved" result_resolved,
         named "theorem_closed" theorem_closed,
         named "theorem_oracle_free" theorem_oracle_free,
         named "nonfalse_phase27" nonfalse_result,
         named "nonfalse_eval_exact" nonfalse_eval_exact,
         named "nonfalse_eval_oracle_free" nonfalse_eval_oracle_free,
         named "bool_leaf_code" bool_leaf_code,
         named "arithmetic_axis_valid" arithmetic_axis_valid,
         named "arithmetic_axis_point_true" arithmetic_axis_point_true,
         named "computed_boolean_literal" computed_boolean_literal,
         named "poisoned_axis_selected" poisoned_axis_selected,
         named "poisoned_axis_point_true" poisoned_axis_point_true,
         named "scope22_valid" scope22_valid,
         named "scope22_point_true" scope22_point_true,
         named "rejects_nonliteral_bool" rejects_nonliteral_bool,
         named "rejects_unresolved_if" rejects_unresolved_if,
         named "unoverloaded_aliases_not_ids" unoverloaded_aliases_not_ids,
         named "zero_reference_exact" zero_reference_exact,
         named "closed_true_guard" closed_true_guard,
         named "closed_false_guard" closed_false_guard,
         named "open_guard_refused" open_guard_refused,
         named "first_nonreflexive" (not (Thm.is_reflexive first)),
         named "fresh_request" fresh_request, named "recursive_work" recursive_work,
         named "first_no_fallback" first_no_fallback,
         named "first_no_rejection" first_no_rejection,
         named "warm_nonreflexive" warm_nonreflexive,
         named "warm_no_recursion" warm_no_recursion,
         named "warm_no_fallback" warm_no_fallback,
         named "warm_no_rejection" warm_no_rejection,
         named "warm_hit" warm_hit, named "foreign_rejected" rejected_foreign,
         named "outside_rejected" rejected_outside]
    in
      if all_checks
      then Comma_Proof_Profile.report
        ("B1 production source-scope Apply-DAG fixture period28=true nested=true " ^
         "depth4=true nonfalse_phase27=true exact_oracle=true warm_hit=true " ^
         "column_comparison_first_difference=true shared_reference_warm=true " ^
         "actual_apply_comparison=true request_local_fallbacks=0 " ^
         "request_local_rejections=0 foreign_and_out_of_range_refs_rejected=true " ^
         #stats owner ())
      else error ("B1 production source-scope Apply-DAG fixture failed: " ^
        failure_checks () ^ " " ^ nonfalse_diagnostic () ^ " " ^ #stats owner ())
    end
  fun check_owner_fixtures ctxt (isolated: apply_owner)
      (comparison: column_comparison) valid_theorem =
    let
      val natT = @{typ nat}
      val columnT = @{typ comma_crt_column}
      val applyT = @{typ "nat => nat => comma_crt_boolean_operation => comma_crt_column => comma_crt_column => comma_crt_column"}
      val apply_name = @{const_name comma_crt_apply_shifted_from}
      val nat_zero = Thm.term_of (Thm.rhs_of
        (Axclass.unoverload_conv ctxt (Thm.cterm_of ctxt @{term "0::nat"})))
      fun mk_apply depth shift operation left right =
        list_comb (Const (apply_name, applyT),
          [HOLogic.mk_number natT depth, HOLogic.mk_number natT shift,
           operation, left, right])
          val and_op = Const (@{const_name Comma_CRT_And},
            @{typ comma_crt_boolean_operation})
          val or_op = Const (@{const_name Comma_CRT_Or},
            @{typ comma_crt_boolean_operation})
          fun bool flag = Const (@{const_name Comma_CRT_Bool}, @{typ bool} --> columnT) $ flag
          fun request depth shift operation left right =
            mk_apply depth shift operation left right
          fun run term = #convert isolated (Thm.cterm_of ctxt term)
          val exact = request 0 0 and_op (bool @{term False}) (bool @{term True})
          val shortcuts_before_exact = #shortcut_applications isolated ()
          val hits_before_exact = #cache_hits isolated ()
          val first = run exact
          val after_first = #recursive_certifications isolated ()
          val shortcuts_after_first = #shortcut_applications isolated ()
          val second = run exact
          val after_second = #recursive_certifications isolated ()
          val shortcuts_after_second = #shortcut_applications isolated ()
          val hits_after_second = #cache_hits isolated ()
          val direct_unoverloaded_zero = Const (apply_name, applyT) $
            nat_zero $ nat_zero $ and_op $
            bool @{term False} $ bool @{term True}
          val before_zero_alias = #recursive_certifications isolated ()
          val hits_before_zero_alias = #cache_hits isolated ()
          val shortcuts_before_zero_alias = #shortcut_applications isolated ()
          val zero_alias_result = run direct_unoverloaded_zero
          val after_zero_alias = #recursive_certifications isolated ()
          val hits_after_zero_alias = #cache_hits isolated ()
          val shortcuts_after_zero_alias = #shortcut_applications isolated ()
          val changed_op = run (request 0 0 or_op (bool @{term False}) (bool @{term True}))
          val changed_shift = run (request 0 1 and_op (bool @{term False}) (bool @{term True}))
          val changed_column = run (request 0 0 and_op (bool @{term True}) (bool @{term True}))
          val symbolic = Const (apply_name, applyT) $
            Var (("depth", 0), natT) $ HOLogic.mk_number natT 0 $
            and_op $ bool @{term False} $ bool @{term True}
          val malformed = run symbolic
          val forged = Thm.reflexive (Thm.cterm_of ctxt (bool @{term False}))
          val exact_rhs =
            (case first of
              SOME theorem => Thm.term_of (Thm.rhs_of theorem)
            | NONE => error "B1 shifted-apply fixture did not produce a theorem")
          val _ = if Option.isSome second andalso Option.isSome changed_op andalso
            Option.isSome changed_shift andalso Option.isSome changed_column andalso
            Option.isSome zero_alias_result andalso
            shortcuts_after_first = shortcuts_before_exact + 1 andalso
            shortcuts_after_second = shortcuts_after_first andalso
            hits_after_second > hits_before_exact andalso
            after_first = before_zero_alias andalso after_second = after_first andalso
            after_zero_alias = before_zero_alias andalso
            hits_after_zero_alias > hits_before_zero_alias andalso
            shortcuts_after_zero_alias = shortcuts_before_zero_alias andalso
            not (Option.isSome malformed) andalso
            exact_rhs aconv (bool @{term False})
            then () else error "B1 shifted-apply DAG shape/reuse fixture failed"
          val _ = if not (valid_theorem exact forged) then ()
            else error "B1 shifted-apply fixture accepted a forged theorem"
          val child_values = map bool
            [@{term False}, @{term True}, @{term False}, @{term True},
             @{term True}, @{term False}, @{term True}, @{term False},
             @{term False}, @{term True}, @{term False}]
          val child_list = HOLogic.mk_list columnT child_values
          val level_three = Const (@{const_name Comma_CRT_Node},
            natT --> fastype_of child_list --> columnT) $
            HOLogic.mk_number natT 3 $ child_list
          val powered = request 1 1 and_op level_three level_three
          val powered_first = run powered
          val powered_certified = #recursive_certifications isolated ()
          val powered_second = run powered
          val powered_cached = #recursive_certifications isolated ()
          fun mk_suc value = Const (@{const_name Suc}, natT --> natT) $ value
          val unoverloaded_one = mk_suc nat_zero
          val unoverloaded_three = mk_suc (mk_suc unoverloaded_one)
          val level_three_alias = Const (@{const_name Comma_CRT_Node},
            natT --> fastype_of child_list --> columnT) $
            unoverloaded_three $ child_list
          val powered_alias = Const (apply_name, applyT) $
            unoverloaded_one $ unoverloaded_one $ and_op $
            level_three_alias $ level_three_alias
          val alias_result = run powered_alias
          val alias_cached = #recursive_certifications isolated ()
          val shifted_outer = Const (@{const_name comma_crt_apply_shifted},
            @{typ "comma_crt_boolean_operation => nat => comma_crt_column => comma_crt_column => comma_crt_column"}) $
            and_op $ unoverloaded_one $ level_three_alias $ level_three_alias
          val outer_result = run shifted_outer
          val _ = if Option.isSome powered_first andalso Option.isSome powered_second andalso
              powered_certified > after_second andalso powered_cached = powered_certified andalso
              Option.isSome alias_result andalso alias_cached = powered_cached andalso
              Option.isSome outer_result then ()
            else error "B1 shifted-apply recursive/wrapper fixture failed"
          val report = #stats isolated ()
          val _ = if after_first = 0 andalso after_second = after_first andalso
            #shortcut_applications isolated () >= 3 andalso
            String.isSubstring "apply_dag_fallbacks=1" report then ()
            else error "B1 shifted-apply fixture missed its reuse/fallback accounting"

          (* The same template geometry and terminal source action may be
             presented with distinct bindings.  The arithmetic action proof
             above is reusable, but compact admission must still transport
             the exact binding: a stale descriptor and a self-consistent but
             wrong result label are both rejected by the local coverage
             premise. *)
          val finite_positionT = @{typ comma_finite_position}
          val resultT = @{typ comma_semantic_b1_result}
          val occurrenceT = @{typ comma_semantic_b1_crt_occurrence}
          val referenceT = @{typ comma_semantic_b1_crt_lift_ref}
          val lift_descriptorT = @{typ comma_semantic_b1_crt_lift_descriptor}
          val source = @{term "Comma_Near 9 0 19 :: comma_finite_position"}
          val sources = HOLogic.mk_list finite_positionT [source]
          val geometry = @{term "[[Comma_CRT_Bool True]] :: comma_crt_column list list"}
          val stop_eight = @{term "Comma_Semantic_B1_Stop 8"}
          val live_zero = @{term "Comma_Semantic_B1_Live 0"}
          val terminal_ref = @{term "Comma_B1_Lift_Terminal_Ref 0 0"}
          val refs_row = HOLogic.mk_list referenceT [terminal_ref]
          val refs = HOLogic.mk_list (HOLogic.listT referenceT) [refs_row]
          val no_lifts = HOLogic.mk_list lift_descriptorT []
          val descriptorT = HOLogic.mk_prodT (natT,
            HOLogic.mk_prodT (natT, HOLogic.listT resultT))
          fun descriptor result = HOLogic.mk_prod (HOLogic.mk_number natT 0,
            HOLogic.mk_prod (HOLogic.mk_number natT 0,
              HOLogic.mk_list resultT [result]))
          fun occurrence result =
            let
              val result_free = Free ("binding_result", resultT)
              val template = @{term
                "\<lparr>comma_semantic_b1_crt_occurrence_columns =
                    [Comma_CRT_Bool True],
                  comma_semantic_b1_crt_occurrence_rebase = 0,
                  comma_semantic_b1_crt_occurrence_beta = [binding_result]\<rparr>"}
            in Term.subst_free [(result_free, result)] template end
          fun occurrence_at result =
            let
              val selected = occurrence result
              val some = Const (@{const_name Some},
                occurrenceT --> @{typ "comma_semantic_b1_crt_occurrence option"})
            in Abs ("index", natT, some $ selected) end
          val compact_head = @{const_name comma_semantic_b1_crt_compact_occurrence_check}
          val compactT = Sign.the_const_type (Proof_Context.theory_of ctxt) compact_head
          fun compact occurrence_result descriptor_result =
            let
              val args = [geometry, sources, occurrence_at occurrence_result,
                HOLogic.mk_list descriptorT [descriptor descriptor_result], refs,
                no_lifts, HOLogic.mk_number natT 0]
            in list_comb (Const (compact_head, compactT), args) end
          fun exact_boolean expected proposition =
            let
              val theorem = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt proposition)
              val rhs = Thm.term_of (Thm.rhs_of theorem)
            in Thm.term_of (Thm.lhs_of theorem) aconv proposition andalso
              rhs aconv expected andalso
              null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem) andalso
              null (Thm_Deps.all_oracles [theorem]) end
          val valid_binding = exact_boolean @{term True}
            (compact stop_eight stop_eight)
          val stale_binding = exact_boolean @{term False}
            (compact stop_eight live_zero)
          val wrong_result_binding = exact_boolean @{term False}
            (compact live_zero live_zero)
          val _ = if valid_binding andalso stale_binding andalso
              wrong_result_binding then ()
            else error "B1 compact occurrence binding reuse/rejection fixture failed"

          (* A nonconstant child column makes the occurrence rebase observable.
             The parent is a one-slot Goto source; the child action's exact
             source and result labels stay fixed while the published rebase
             changes.  The second negative also changes the child rebase and
             its corresponding net shift together, so descriptor consistency
             holds and local result-column coverage is what rejects it. *)
          val columnT = @{typ comma_crt_column}
          val column_listT = HOLogic.listT columnT
          val quarter = @{term
            "Comma_CRT_Node 0 [Comma_CRT_Bool True, Comma_CRT_Bool False,
              Comma_CRT_Bool False, Comma_CRT_Bool False]"}
          val quarter_columns = HOLogic.mk_list columnT [quarter]
          val templates = HOLogic.mk_list column_listT [quarter_columns]
          val goto_sources = @{term
            "[Comma_Entry 2 0 80, Comma_Near 1 0 2] :: comma_finite_position list"}
          val empty_refs = HOLogic.mk_list referenceT []
          val goto_ref = @{term "Comma_B1_Lift_Goto_Ref 0 0 0"}
          val goto_refs = HOLogic.mk_list referenceT [goto_ref]
          val goto_refs_table = HOLogic.mk_list (HOLogic.listT referenceT)
            [empty_refs, goto_refs]
          val zero = HOLogic.mk_number natT 0
          fun occurrence_with rebase result =
            let
              val columns_free = Free ("rebased_columns", column_listT)
              val rebase_free = Free ("occurrence_rebase", natT)
              val result_free = Free ("occurrence_result", resultT)
              val template = @{term
                "\<lparr>comma_semantic_b1_crt_occurrence_columns = rebased_columns,
                  comma_semantic_b1_crt_occurrence_rebase = occurrence_rebase,
                  comma_semantic_b1_crt_occurrence_beta = [occurrence_result]\<rparr>"}
            in Term.subst_free
              [(columns_free, quarter_columns),
               (rebase_free, HOLogic.mk_number natT rebase),
               (result_free, result)] template end
          fun occurrence_function child_rebase parent_rebase =
            let
              val child = occurrence_with child_rebase live_zero
              val parent = occurrence_with parent_rebase live_zero
              val optionT = Type (@{type_name option}, [occurrenceT])
              val eq_nat = Const (@{const_name HOL.eq}, natT --> natT --> @{typ bool}) $
                Bound 0 $ zero
              val some = Const (@{const_name Some}, occurrenceT --> optionT)
              val conditional = Const (@{const_name If},
                @{typ bool} --> optionT --> optionT --> optionT) $
                  eq_nat $ (some $ child) $ (some $ parent)
            in Abs ("occurrence_index", natT, conditional) end
          fun occurrence_descriptor rebase =
            HOLogic.mk_prod (zero, HOLogic.mk_prod
              (HOLogic.mk_number natT rebase, HOLogic.mk_list resultT [live_zero]))
          val goto_descriptorT = HOLogic.mk_prodT (natT,
            HOLogic.mk_prodT (natT, HOLogic.listT resultT))
          fun goto_descriptors child_rebase parent_rebase =
            HOLogic.mk_list goto_descriptorT
              [occurrence_descriptor child_rebase,
               occurrence_descriptor parent_rebase]
          val lift_make = Const
            (@{const_name comma_semantic_b1_crt_lift_descriptor.make},
             natT --> natT --> natT --> natT --> lift_descriptorT)
          fun goto_lift_descriptor net_shift = list_comb (lift_make,
            [HOLogic.mk_number natT 1, zero, zero,
             HOLogic.mk_number natT net_shift])
          fun goto_compact child_rebase parent_rebase net_shift =
            let
              val args = [templates, goto_sources,
                occurrence_function child_rebase parent_rebase,
                goto_descriptors child_rebase parent_rebase, goto_refs_table,
                HOLogic.mk_list lift_descriptorT [goto_lift_descriptor net_shift],
                HOLogic.mk_number natT 1]
            in list_comb (Const (compact_head, compactT), args) end
          val nontrivial_shift_valid = exact_boolean @{term True}
            (goto_compact 0 0 0)
          val wrong_parent_rebase = exact_boolean @{term False}
            (goto_compact 0 1 0)
          val wrong_child_net_shift = exact_boolean @{term False}
            (goto_compact 1 0 1)
          val _ = if nontrivial_shift_valid andalso wrong_parent_rebase andalso
              wrong_child_net_shift then ()
            else error "B1 compact occurrence failed shifted-geometry rebase rejection"
          val _ = Comma_Proof_Profile.report
            ("B1 occurrence split DAG fixture distinct_bindings=true " ^
              "warm_certifications_reused=true authenticated_refs=true " ^
              "foreign_refs_rejected=true shifted_geometry=true " ^
              "wrong_parent_rebase_rejected=true wrong_child_net_shift_rejected=true " ^
              #stats isolated ())
          val _ = Comma_Semantic_B1_CRT_Apply_Shortcut_Fixture.check ctxt
            {convert = #convert isolated,
             recursive_certifications = #recursive_certifications isolated,
             fallbacks = #fallbacks isolated,
             derive_rejections = #derive_rejections isolated,
             shortcut_applications = #shortcut_applications isolated,
             cache_hits = #cache_hits isolated,
             retained_keys = #retained_keys isolated}
            {convert = #convert comparison}
        in () end


  end
