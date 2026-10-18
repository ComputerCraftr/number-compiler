(* Exercise the right-support quotient through the real Apply-DAG memo. *)
structure Comma_Semantic_B1_Apply_Clock_DAG_Fixture =
struct
  fun check_owned_reference_reification ctxt =
    let
      val natT = HOLogic.natT
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val columnT = @{typ comma_crt_column}
      val dag = @{term Comma_B1_CRT_Column_DAG_Empty}
      val at = Const (@{const_name comma_semantic_b1_crt_column_at},
        dagT --> natT --> columnT)
      val owned = at $ dag $ HOLogic.mk_number natT 2
      val foreign = at $ dag $
        HOLogic.mk_number natT 3
      val poison_calls = Unsynchronized.ref 0
      fun poison _ =
        (poison_calls := !poison_calls + 1;
         error "B1 known-reference reifier poison was reached")
      val theorem = Comma_Semantic_B1_Source_Column_Normalizer.reify_known_reference
        (fn term => term aconv owned) poison (Thm.cterm_of ctxt owned)
      val fallback_calls = Unsynchronized.ref 0
      fun fallback ct =
        (fallback_calls := !fallback_calls + 1; Thm.reflexive ct)
      val foreign_theorem =
        Comma_Semantic_B1_Source_Column_Normalizer.reify_known_reference
          (fn term => term aconv owned) fallback (Thm.cterm_of ctxt foreign)
      val exact_owned = Thm.term_of (Thm.lhs_of theorem) aconv owned andalso
        Thm.term_of (Thm.rhs_of theorem) aconv owned andalso
        Thm.is_reflexive theorem andalso null (Thm.prems_of theorem) andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
        null (Thm_Deps.all_oracles [theorem]) andalso !poison_calls = 0
      val foreign_falls_through = !fallback_calls = 1 andalso
        Thm.term_of (Thm.lhs_of foreign_theorem) aconv foreign andalso
        Thm.term_of (Thm.rhs_of foreign_theorem) aconv foreign
    in
      if exact_owned andalso foreign_falls_through then ()
      else error "B1 known-reference reification fast-path fixture failed"
    end

  fun check_reflexive_comparison ctxt =
    let
      val natT = HOLogic.natT
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      val columnT = @{typ comma_crt_column}
      val dag = @{term Comma_B1_CRT_Column_DAG_Empty}
      val at = Const (@{const_name comma_semantic_b1_crt_column_at},
        dagT --> natT --> columnT)
      val owned = at $ dag $ HOLogic.mk_number natT 2
      val foreign = at $ dag $ HOLogic.mk_number natT 3
      val comparison = Comma_Semantic_B1_Column_Lookup_Cache.make_column_comparison
        ctxt (Comma_Entry_Arithmetic.natural_context ctxt) columnT
        {valid_column = (fn term => term aconv owned),
         known_column = (fn term => term aconv owned),
         resolve_column = K NONE,
         valid_step = (fn _ => fn _ => false)}
      fun request term = HOLogic.mk_eq (term, term)
      fun stats () = (#hits comparison (), #misses comparison (),
        #publications comparison (), #resolutions comparison ())
      val before_owned = stats ()
      val owned_request = request owned
      val owned_result = #convert comparison (Thm.cterm_of ctxt owned_request)
      val after_owned = stats ()
      val exact_true =
        (case owned_result of
          SOME theorem => Thm.term_of (Thm.lhs_of theorem) aconv owned_request andalso
            Thm.term_of (Thm.rhs_of theorem) aconv @{term True} andalso
            null (Thm.prems_of theorem) andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso
            null (Thm_Deps.all_oracles [theorem])
        | NONE => false)
      val foreign_request = request foreign
      val foreign_result = #convert comparison (Thm.cterm_of ctxt foreign_request)
      val after_foreign = stats ()
      val foreign_rejected = is_none foreign_result andalso
        #3 after_foreign = #3 after_owned andalso
        #4 after_foreign = #4 after_owned
    in
      if exact_true andalso before_owned = after_owned andalso foreign_rejected then ()
      else error "B1 reflexive column comparison fixture failed"
    end

  fun check ctxt =
    let
      val _ = check_owned_reference_reification ctxt
      val _ = check_reflexive_comparison ctxt
      val natT = HOLogic.natT
      val boolT = HOLogic.boolT
      val columnT = @{typ comma_crt_column}
      val operationT = @{typ comma_crt_boolean_operation}
      fun numeral n = HOLogic.mk_number natT n
      fun bool value =
        Const (@{const_name Comma_CRT_Bool}, boolT --> columnT) $ value
      fun node level children =
        Const (@{const_name Comma_CRT_Node},
          natT --> HOLogic.listT columnT --> columnT) $
          numeral level $ HOLogic.mk_list columnT children
      val false_column = bool @{term False}
      val true_column = bool @{term True}
      val left_children = [true_column, false_column, true_column]
      val right_children = List.tabulate (11, fn index =>
        if index mod 2 = 0 then false_column else true_column)
      val left = node 1 left_children
      val right = node 3 right_children
      val values = [(0, false_column), (1, true_column), (2, left), (3, right)]
      val ids = fold (fn (cid, value) => Termtab.update (value, cid))
        values Termtab.empty
      val by_id = Inttab.make values
      fun column_value cid =
        (case Inttab.lookup by_id cid of
          SOME value => value
        | NONE => error "B1 clock-DAG fixture requested a foreign CID")
      fun column_id value = Termtab.lookup ids value
      fun node_info cid =
        (case cid of
          2 => SOME (1, map (fn value => the (column_id value)) left_children)
        | 3 => SOME (3, map (fn value => the (column_id value)) right_children)
        | _ => NONE)
      fun cofactor_target level digit cid =
        if cid < 2 then cid
        else
          (case node_info cid of
            SOME (node_level, children) =>
              if node_level < level then 0
              else if level < node_level then cid
              else List.nth (children, digit)
          | NONE => error "B1 clock-DAG fixture lost a node")
      val cofactor = Const (@{const_name comma_crt_cofactor_or_false},
        natT --> natT --> columnT --> columnT)
      fun cofactor_transition (level, digit, cid) =
        let
          val target_cid = cofactor_target level digit cid
          val request = cofactor $ numeral level $ numeral digit $ column_value cid
          val goal = HOLogic.mk_Trueprop
            (HOLogic.mk_eq (request, column_value target_cid))
          val object_equality = Goal.prove ctxt [] [] goal
            (fn {context, ...} => simp_tac
              (Comma_Entry_Arithmetic.natural_context context addsimps
                (@{thms comma_crt_cofactor.simps comma_crt_cofactor_or_false_def
                  option.case comma_crt_period_def list.map list.size nth_Cons'
                  nth_Cons_0})) 1)
          val theorem = object_equality RS @{thm eq_reflection}
        in {target_cid = target_cid, theorem = theorem} end
      fun prove_admitted (lower, cid) =
        let
          val proposition = Const
            (@{const_name comma_crt_admitted}, natT --> columnT --> boolT) $
            numeral lower $ column_value cid
          val goal = HOLogic.mk_Trueprop proposition
        in Goal.prove ctxt [] [] goal
          (fn {context, ...} => simp_tac
            (Comma_Entry_Arithmetic.natural_context context addsimps
              (@{thms comma_crt_admitted.simps comma_crt_period_def list.size
                nth_Cons' nth_Cons_0
                list_all_Cons_iff list_all_Nil_iff})) 1)
        end
      val authority: Comma_Semantic_B1_CRT_Apply_DAG.column_authority =
        {known_column = (fn value => Option.isSome (column_id value)),
         column_id = column_id,
         column_value = column_value,
         cofactor_node_level = (fn cid => Option.map #1 (node_info cid)),
         prove_admitted = prove_admitted,
         resolve_column = K NONE,
         cofactor_transition = cofactor_transition,
         reify_column = Thm.reflexive}
      val broken_admission_authority:
          Comma_Semantic_B1_Apply_Depth_Quotient.authority =
        {known_column = (fn value => Option.isSome (column_id value)),
         column_id = column_id,
         column_value = column_value,
         cofactor_node_level = (fn cid => Option.map #1 (node_info cid)),
         prove_admitted = (fn _ => error "fixture poison: admitted proof producer failed")}
      val poison_owner =
        Comma_Semantic_B1_Apply_Depth_Quotient.make ctxt broken_admission_authority
      val recognized_admission_failure_surfaces =
        ((ignore (#right_support poison_owner right); false) handle ERROR _ => true)
      val unsupported_column =
        Const (@{const_name Comma_CRT_Bool}, boolT --> columnT) $ Free ("opaque", boolT)
      val unsupported_stays_unrecognized =
        is_none (#right_support poison_owner unsupported_column)
      val right_admission = prove_admitted (3, 3)
      val exact_right_admission =
        Thm.prop_of right_admission aconv
          (HOLogic.mk_Trueprop
            (Const (@{const_name comma_crt_admitted}, natT --> columnT --> boolT) $
              numeral 3 $ right)) andalso
        null (Thm.prems_of right_admission) andalso null (Thm.hyps_of right_admission)
      val _ = if exact_right_admission andalso recognized_admission_failure_surfaces andalso
          unsupported_stays_unrecognized then ()
        else error ("B1 mixed-level fixture admission checks failed: exact=" ^
          Bool.toString exact_right_admission ^ ", poison=" ^
          Bool.toString recognized_admission_failure_surfaces ^ ", unsupported=" ^
          Bool.toString unsupported_stays_unrecognized)
      val owner = Comma_Semantic_B1_CRT_Apply_DAG.make ctxt authority
      val operation = Const (@{const_name Comma_CRT_And}, operationT)
      fun request shift = list_comb
        (Const (@{const_name comma_crt_apply_shifted_from},
          natT --> natT --> operationT --> columnT --> columnT --> columnT),
         [numeral 3, numeral shift, operation, left, right])
      val first_request = request 1
      val second_request = request 12
      fun convert term = #convert owner (Thm.cterm_of ctxt term)
      val recursive_before = #recursive_certifications owner ()
      val first = convert first_request
      val after_first = #recursive_certifications owner ()
      val stats_after_first = #stats owner ()
      val hits_before_second = #cache_hits owner ()
      val second = convert second_request
      val after_second = #recursive_certifications owner ()
      val hits_after_second = #cache_hits owner ()
      val stats_after_second = #stats owner ()
      fun exact request theorem =
        (case theorem of
          SOME result => Thm.term_of (Thm.lhs_of result) aconv request andalso
            null (Thm.prems_of result) andalso null (Thm.hyps_of result) andalso
            null (Thm.tpairs_of result) andalso
            null (Thm_Deps.all_oracles [result])
        | NONE => false)
      val same_result = (case (first, second) of
        (SOME a, SOME b) =>
          Thm.term_of (Thm.rhs_of a) aconv Thm.term_of (Thm.rhs_of b)
      | _ => false)
      val warm_hit = after_first > recursive_before andalso
        after_second = after_first andalso
        hits_after_second = hits_before_second + 1
      val first_exact = exact first_request first
      val second_exact = exact second_request second
      val _ = if first_exact andalso second_exact andalso same_result andalso warm_hit
        then ()
        else error ("B1 mixed-level right-quotient DAG cache fixture failed: " ^
          "first=" ^ Bool.toString first_exact ^
          ", second=" ^ Bool.toString second_exact ^
          ", same_result=" ^ Bool.toString same_result ^
          ", warm=" ^ Bool.toString warm_hit ^
          ", recursive=" ^ Int.toString recursive_before ^ "/" ^
            Int.toString after_first ^ "/" ^ Int.toString after_second ^
          ", hits=" ^ Int.toString hits_before_second ^ "/" ^
            Int.toString hits_after_second ^
          ", exact_right_admission=" ^ Bool.toString exact_right_admission ^
          ", stats_first={" ^ stats_after_first ^ "}" ^
          ", stats_second={" ^ stats_after_second ^ "}")
    in () end
end
