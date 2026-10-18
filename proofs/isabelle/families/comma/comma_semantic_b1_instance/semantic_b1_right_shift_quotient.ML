(* A context-owned Boolean-Apply quotient justified by an admitted right column.
   The left operand is never shifted, so its clocks do not constrain this key. *)
structure Comma_Semantic_B1_Right_Shift_Quotient =
struct
  type owner =
   {rewrite: int -> int -> int -> thm -> cterm -> int * thm,
    retained_rules: unit -> int,
    rule_hits: unit -> int,
    rule_builds: unit -> int,
    check_fixture: unit -> unit}

  fun check_bounds lower depth shift =
    if lower >= 0 andalso lower <= 4 andalso depth >= 0 andalso depth <= 4 andalso
        shift >= 0 andalso shift < 924
    then ()
    else error "B1 right-support shift request is outside admitted bounds"

  fun make ctxt =
    let
      val natT = HOLogic.natT
      val boolT = HOLogic.boolT
      val columnT = @{typ comma_crt_column}
      val operationT = @{typ comma_crt_boolean_operation}
      fun numeral value = HOLogic.mk_number natT value
      val nat_mod = Const (@{const_name modulo}, natT --> natT --> natT)
      val nat_eq = Const (@{const_name HOL.eq}, natT --> natT --> boolT)
      val bool_eq = Const (@{const_name HOL.eq}, boolT --> boolT --> boolT)
      val nat_le = Const (@{const_name less_eq}, natT --> natT --> boolT)
      val admitted = Const (@{const_name comma_crt_admitted}, natT --> columnT --> boolT)
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
        addsimps @{thms comma_crt_apply_suffix_period_def}
      val rules = Synchronized.var
        "semantic_b1_right_shift_rules" (Inttab.empty: thm Inttab.table)
      val right_rules = Synchronized.var
        "semantic_b1_right_shift_right_rules" (Termtab.empty: thm Termtab.table)
      val right_rule_capacity = 65536
      val rule_hits = Synchronized.var "semantic_b1_right_shift_rule_hits" 0
      val rule_builds = Synchronized.var "semantic_b1_right_shift_rule_builds" 0
      val right_rule_hits = Synchronized.var "semantic_b1_right_shift_right_rule_hits" 0
      val right_rule_builds = Synchronized.var "semantic_b1_right_shift_right_rule_builds" 0

      fun expected_admission lower right =
        HOLogic.mk_Trueprop (admitted $ numeral lower $ right)

      fun make_rule lower depth shift =
        let
          val period = Vector.sub (Comma_Semantic_B1_Clock_Shift_Common.periods,
            4 - lower)
          val representative =
            Comma_Semantic_B1_Clock_Shift_Common.canonical_period_shift period shift
          val lower_term = numeral lower
          val depth_term = numeral depth
          val shift_term = numeral shift
          val representative_term = numeral representative
          fun zero_residue value =
            nat_eq $ (nat_mod $ value $ numeral 924) $ numeral 0
          val depth_bound = nat_le $ depth_term $ numeral 4
          val support_bound = nat_le $ lower_term $ numeral 4
          val same_zero_branch = bool_eq $
            zero_residue shift_term $ zero_residue representative_term
          val instantiated = Drule.infer_instantiate ctxt
            [( ("lower", 0), Thm.cterm_of ctxt lower_term),
             (("depth", 0), Thm.cterm_of ctxt depth_term),
             (("shift", 0), Thm.cterm_of ctxt shift_term),
             (("shift'", 0), Thm.cterm_of ctxt representative_term)]
            @{thm comma_crt_apply_shifted_from_right_suffix_period_equiv}
          val after_depth = Thm.implies_elim instantiated
            (Comma_Semantic_B1_Clock_Shift_Common.prove_ground ctxt arithmetic depth_bound)
          val after_support = Thm.implies_elim after_depth
            (Comma_Semantic_B1_Clock_Shift_Common.prove_ground ctxt arithmetic support_bound)
          val after_zero = Thm.implies_elim after_support
            (Comma_Semantic_B1_Clock_Shift_Common.prove_ground ctxt arithmetic same_zero_branch)
          val (admission_premise, suffix_premise) =
            (case Thm.prems_of after_zero of
              [admission, suffix] => (admission, suffix)
            | _ => error "B1 right-support rule changed its premise order")
          val suffix_first = Thm.permute_prems 0 1 after_zero
          val _ = if Thm.prems_of suffix_first = [suffix_premise, admission_premise]
            then () else error "B1 right-support premise rotation changed its order"
          val suffix_fact = Comma_Semantic_B1_Clock_Shift_Common.prove_ground
            ctxt arithmetic (HOLogic.dest_Trueprop suffix_premise)
          val discharged_suffix = Thm.implies_elim suffix_first suffix_fact
          val conditional = discharged_suffix RS @{thm eq_reflection}
        in
          if Thm.nprems_of conditional = 1 andalso
              null (Thm.hyps_of conditional) andalso null (Thm.tpairs_of conditional) andalso
              null (Thm_Deps.all_oracles [conditional])
          then conditional
          else error "B1 right-support rule retained foreign premises"
        end

      fun rule_key lower depth shift =
        (lower * 5 + depth) * 924 + shift

      fun rule_for lower depth shift =
        let
          val key = rule_key lower depth shift
        in
          (case Inttab.lookup (Synchronized.value rules) key of
            SOME theorem =>
              (Synchronized.change rule_hits (fn count => count + 1); theorem)
          | NONE =>
              let
                val theorem = make_rule lower depth shift
                val _ = Synchronized.change rule_builds (fn count => count + 1)
                val (selected, inserted) =
                  Synchronized.change_result rules (fn table =>
                    (case Inttab.lookup table key of
                      SOME existing => ((existing, false), table)
                    | NONE => ((theorem, true), Inttab.update (key, theorem) table)))
                val _ = if inserted then () else
                  Synchronized.change rule_hits (fn count => count + 1)
              in selected end)
        end

      fun admission_variable lower theorem =
        let
          fun malformed premise =
            error ("B1 right-shift rule has a malformed admission premise: " ^
              Syntax.string_of_term ctxt premise)
        in
          (case Thm.prems_of theorem of
            [premise] =>
              (case Term.strip_comb (HOLogic.dest_Trueprop premise) of
                (Const (name, _), [premise_lower, Var (variable, variable_type)]) =>
                  if name = @{const_name comma_crt_admitted} andalso
                      premise_lower aconv numeral lower andalso
                      variable_type = columnT
                  then variable
                  else malformed premise
              | _ => malformed premise)
          | _ => error "B1 right-shift rule does not have one admission premise")
        end

      fun right_rule lower depth shift right admission =
        let
          val key = HOLogic.mk_prod (numeral lower,
            HOLogic.mk_prod (numeral depth,
              HOLogic.mk_prod (numeral shift, right)))
          val expected = expected_admission lower right
        in
          (case Termtab.lookup (Synchronized.value right_rules) key of
            SOME theorem =>
              let
                val _ = Synchronized.change right_rule_hits (fn count => count + 1)
              in if Thm.nprems_of theorem = 0 andalso
                  null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
              then theorem
              else error "B1 cached right-shift equation is not closed" end
          | NONE =>
              let
                val base = rule_for lower depth shift
                val right_variable = admission_variable lower base
                val conditional = Drule.infer_instantiate ctxt
                  [(right_variable, Thm.cterm_of ctxt right)] base
                val _ = if Thm.prems_of conditional = [expected] andalso
                    null (Thm.hyps_of conditional) andalso null (Thm.tpairs_of conditional)
                  then () else error "B1 right-shift rule specialized to another column"
                val theorem = Thm.implies_elim conditional admission
                val _ = if Thm.nprems_of theorem = 0 andalso
                    null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
                  then () else error "B1 right-shift equation retained its admission"
                val (selected, _, already_present) = Synchronized.change_result right_rules
                  (fn table =>
                    (case Termtab.lookup table key of
                      SOME existing => ((existing, false, true), table)
                    | NONE =>
                        if Termtab.size table < right_rule_capacity
                        then ((theorem, true, false), Termtab.update (key, theorem) table)
                        else ((theorem, false, false), table)))
                val _ = Synchronized.change right_rule_builds (fn count => count + 1)
                val _ = if already_present then
                    Synchronized.change right_rule_hits (fn count => count + 1)
                  else ()
              in selected end)
        end

      fun rewrite lower depth shift admission request_ct =
        let
          val _ = check_bounds lower depth shift
          val request = Thm.term_of request_ct
          val (head, args) = Term.strip_comb request
          val period = Vector.sub (Comma_Semantic_B1_Clock_Shift_Common.periods,
            4 - lower)
          val representative =
            Comma_Semantic_B1_Clock_Shift_Common.canonical_period_shift period shift
          val apply_name = @{const_name comma_crt_apply_shifted_from}
          val _ =
            (case (head, args) of
              (Const (name, _), [request_depth, request_shift, _, _, right]) =>
                if name = apply_name andalso
                    request_depth aconv numeral depth andalso
                    request_shift aconv numeral shift andalso
                    Thm.prop_of admission aconv expected_admission lower right
                then ()
                else error "B1 right-support rule does not match its request or admission"
            | _ => error "B1 right-support conversion requires a saturated Apply request")
          (* The depth authority audits each newly issued admission proof with
             its shared incremental oracle certifier. Recheck its exact
             proposition and closedness here without repeating that transitive
             proof-graph walk for every matrix request. *)
          val _ = if Thm.nprems_of admission = 0 andalso
              null (Thm.hyps_of admission) andalso null (Thm.tpairs_of admission)
            then () else error "B1 right-support admission is not a clean certificate"
          val theorem =
            if representative = shift then Thm.reflexive request_ct
            else
              let
                val (_, [_, _, _, _, right]) = Term.strip_comb request
                val equation = right_rule lower depth shift right admission
              in Conv.rewr_conv equation request_ct end
          val expected_rhs =
            (case Term.strip_comb request of
              (Const (name, T), [request_depth, _, operation, left, right]) =>
                list_comb (Const (name, T),
                  [request_depth, numeral representative, operation, left, right])
            | _ => error "B1 right-support conversion changed its request shape")
          val _ = if Thm.term_of (Thm.lhs_of theorem) aconv request andalso
              Thm.term_of (Thm.rhs_of theorem) aconv expected_rhs andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem)
            then () else error "B1 right-support conversion changed its exact request"
        in (representative, theorem) end

      fun column flag =
        Const (@{const_name Comma_CRT_Bool}, HOLogic.boolT --> columnT) $ flag
      fun node level children =
        Const (@{const_name Comma_CRT_Node}, natT --> HOLogic.listT columnT --> columnT) $
          numeral level $ HOLogic.mk_list columnT children
      fun apply depth shift operation left right =
        list_comb (Const (@{const_name comma_crt_apply_shifted_from},
          natT --> natT --> operationT --> columnT --> columnT --> columnT),
          [numeral depth, numeral shift, operation, left, right])

      fun check_fixture () =
        let
          val left = node 1 (map column [@{term True}, @{term False}, @{term True}])
          val right = node 3 (map column
            [@{term False}, @{term True}, @{term False}, @{term True}, @{term True},
             @{term False}, @{term True}, @{term False}, @{term True}, @{term False},
             @{term True}])
          val operation = Const (@{const_name Comma_CRT_And}, operationT)
          val admission_prop = expected_admission 3 right
          val admission = Goal.prove ctxt [] [] admission_prop
            (fn {context, ...} => simp_tac
              (Comma_Entry_Arithmetic.natural_context context addsimps
                (@{thms comma_crt_admitted.simps comma_crt_period_def list.size
                   nth_Cons' nth_Cons_0
                   list_all_Cons_iff list_all_Nil_iff})) 1)
          val first_request = apply 3 1 operation left right
          val second_request = apply 3 12 operation left right
          val zero_request = apply 3 0 operation left right
          val positive_period_request = apply 3 11 operation left right
          val (first_shift, first) = rewrite 3 3 1 admission
            (Thm.cterm_of ctxt first_request)
          val (second_shift, second) = rewrite 3 3 12 admission
            (Thm.cterm_of ctxt second_request)
          val right_rule_hits_before = Synchronized.value right_rule_hits
          val _ = rewrite 3 3 12 admission (Thm.cterm_of ctxt second_request)
          val right_rule_warm_hit =
            Synchronized.value right_rule_hits = right_rule_hits_before + 1
          val (zero_shift, zero_theorem) = rewrite 3 3 0 admission
            (Thm.cterm_of ctxt zero_request)
          val (period_shift, period_theorem) = rewrite 3 3 11 admission
            (Thm.cterm_of ctxt positive_period_request)
          val wrong_admission = Goal.prove ctxt [] []
            (expected_admission 3 (column @{term False}))
            (fn {context, ...} => simp_tac
              (put_simpset HOL_basic_ss context addsimps
                [@{thm comma_crt_admitted.simps(1)}]) 1)
          val wrong_admission_rejected =
            ((ignore (rewrite 3 3 12 wrong_admission
                (Thm.cterm_of ctxt second_request)); false)
              handle ERROR _ => true)
          val zero_branch_preserved = zero_shift = 0 andalso period_shift = 11 andalso
            Thm.term_of (Thm.rhs_of zero_theorem) aconv zero_request andalso
            Thm.term_of (Thm.rhs_of period_theorem) aconv positive_period_request andalso
            not (Thm.term_of (Thm.rhs_of zero_theorem) aconv
              Thm.term_of (Thm.rhs_of period_theorem))
          val _ = if first_shift = 1 andalso second_shift = 1 andalso
              Thm.term_of (Thm.lhs_of first) aconv first_request andalso
              Thm.term_of (Thm.lhs_of second) aconv second_request andalso
              Thm.term_of (Thm.rhs_of first) aconv Thm.term_of (Thm.rhs_of second) andalso
              null (Thm_Deps.all_oracles [first, second, admission]) andalso
              right_rule_warm_hit andalso wrong_admission_rejected andalso
              zero_branch_preserved
            then () else error "B1 asymmetric right-support alias fixture failed"
        in () end
    in
      {rewrite = rewrite,
       retained_rules = fn () => Inttab.size (Synchronized.value rules) +
         Termtab.size (Synchronized.value right_rules),
       rule_hits = fn () => Synchronized.value rule_hits +
         Synchronized.value right_rule_hits,
       rule_builds = fn () => Synchronized.value rule_builds +
         Synchronized.value right_rule_builds,
       check_fixture = check_fixture}
    end
end
