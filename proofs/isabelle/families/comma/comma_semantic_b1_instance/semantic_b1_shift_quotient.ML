(* Context-owned scalar transport for the checked CRT suffix-clock quotient. *)
structure Comma_Semantic_B1_Clock_Shift_Common =
struct
  val periods = Vector.fromList [1, 11, 77, 231, 924]

  fun canonical_period_shift period shift =
    if period <= 0 orelse shift < 0 then
      error "B1 clock-shift representative is outside its scalar bounds"
    else
      let val residue = shift mod period in
        if shift = 0 then 0 else if residue = 0 then period else residue
      end

  fun prove_ground ctxt arithmetic proposition =
    let
      val goal = HOLogic.mk_Trueprop proposition
      val theorem = Goal.prove ctxt [] [] goal
        (fn _ => simp_tac arithmetic 1)
    in
      if Thm.prop_of theorem aconv goal andalso Thm.nprems_of theorem = 0 andalso
          null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem) andalso
          null (Thm_Deps.all_oracles [theorem])
      then theorem
      else error "B1 clock-shift arithmetic fact was not certified exactly"
    end
end

structure Comma_Semantic_B1_Shift_Quotient =
struct
  fun check_bounds depth shift =
    if depth >= 0 andalso depth <= 4 andalso shift >= 0 andalso shift < 924
    then ()
    else error "B1 suffix-shift request is outside the admitted scalar bounds"
  fun canonical_shift depth shift =
    let
      val _ = check_bounds depth shift
      val period = Vector.sub (Comma_Semantic_B1_Clock_Shift_Common.periods, depth)
    in Comma_Semantic_B1_Clock_Shift_Common.canonical_period_shift period shift end

  fun make ctxt =
    let
      val natT = HOLogic.natT
      val boolT = HOLogic.boolT
      fun numeral value = HOLogic.mk_number natT value
      val nat_mod = Const (@{const_name modulo}, natT --> natT --> natT)
      val nat_eq = Const (@{const_name HOL.eq}, natT --> natT --> boolT)
      val bool_eq = Const (@{const_name HOL.eq}, boolT --> boolT --> boolT)
      val nat_le = Const (@{const_name less_eq}, natT --> natT --> boolT)
      val suffix_period = Const
        (@{const_name comma_crt_apply_suffix_period}, natT --> natT)
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
        addsimps @{thms comma_crt_apply_suffix_period_def}
      val rules = Synchronized.var
        "semantic_b1_suffix_shift_rules" (Inttab.empty: thm Inttab.table)
      val rule_hits = Synchronized.var "semantic_b1_suffix_shift_rule_hits" 0
      val rule_builds = Synchronized.var "semantic_b1_suffix_shift_rule_builds" 0

      fun prove_ground proposition =
        Comma_Semantic_B1_Clock_Shift_Common.prove_ground ctxt arithmetic proposition

      fun make_rule depth shift =
        let
          val representative = canonical_shift depth shift
          val depth_term = numeral depth
          val shift_term = numeral shift
          val representative_term = numeral representative
          fun zero_residue value =
            nat_eq $ (nat_mod $ value $ numeral 924) $ numeral 0
          val depth_bound = nat_le $ depth_term $ numeral 4
          val same_zero_branch = bool_eq $
            zero_residue shift_term $ zero_residue representative_term
          val period = suffix_period $ depth_term
          val same_suffix = nat_eq $
            (nat_mod $ shift_term $ period) $
            (nat_mod $ representative_term $ period)
          val instantiated = Drule.infer_instantiate ctxt
            [(("depth", 0), Thm.cterm_of ctxt depth_term),
             (("shift", 0), Thm.cterm_of ctxt shift_term),
             (("shift'", 0), Thm.cterm_of ctxt representative_term)]
            @{thm comma_crt_apply_shifted_from_suffix_equiv}
          val bound_fact = prove_ground depth_bound
          val zero_fact = prove_ground same_zero_branch
          val suffix_fact = prove_ground same_suffix
          val result = instantiated
            |> (fn theorem => Thm.implies_elim theorem bound_fact)
            |> (fn theorem => Thm.implies_elim theorem zero_fact)
            |> (fn theorem => Thm.implies_elim theorem suffix_fact)
          val proposition = Thm.prop_of result
        in
          if Thm.nprems_of result = 0 andalso null (Thm.hyps_of result) andalso
              null (Thm.tpairs_of result) andalso
              null (Thm_Deps.all_oracles [result])
          then result RS @{thm eq_reflection}
          else error ("B1 suffix-shift rule retained assumptions: " ^
            Syntax.string_of_term ctxt proposition)
        end

      fun rule_for depth shift =
        let
          val _ = check_bounds depth shift
          val key = depth * 924 + shift
        in
          (case Inttab.lookup (Synchronized.value rules) key of
            SOME theorem =>
              (Synchronized.change rule_hits (fn count => count + 1); theorem)
          | NONE =>
              let
                val theorem = make_rule depth shift
                val _ = Synchronized.change rule_builds (fn count => count + 1)
                val (selected, inserted) =
                  Synchronized.change_result rules (fn table =>
                    (case Inttab.lookup table key of
                      SOME existing => ((existing, false), table)
                    | NONE =>
                        ((theorem, true), Inttab.update (key, theorem) table)))
                val _ = if inserted then () else
                  Synchronized.change rule_hits (fn count => count + 1)
              in
                selected
              end)
        end

      fun rewrite depth shift request_ct =
        let
          val request = Thm.term_of request_ct
          val (head, args) = strip_comb request
          val representative = canonical_shift depth shift
          val expected_head = Const
            (@{const_name comma_crt_apply_shifted_from}, fastype_of head)
          val _ =
            (case (head, args) of
              (Const (name, _), [request_depth, request_shift, _, _, _]) =>
                if name = @{const_name comma_crt_apply_shifted_from} andalso
                    request_depth aconv numeral depth andalso
                    request_shift aconv numeral shift then ()
                else error "B1 suffix-shift conversion does not match its parsed scalars"
            | _ => error "B1 suffix-shift conversion requires a saturated apply request")
          val theorem = if representative = shift then Thm.reflexive request_ct
            else Conv.rewr_conv (rule_for depth shift) request_ct
          val _ = if representative = shift then () else
            let
              val expected = list_comb (expected_head,
                [numeral depth, numeral representative] @ List.drop (args, 2))
              val lhs = Thm.term_of (Thm.lhs_of theorem)
              val rhs = Thm.term_of (Thm.rhs_of theorem)
            in
              if lhs aconv request andalso rhs aconv expected andalso
                  Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
                  null (Thm.tpairs_of theorem)
              then () else error "B1 suffix-shift transport changed its exact request"
            end
        in (representative, theorem) end
    in
      {rewrite = rewrite,
       retained_rules = fn () => Inttab.size (Synchronized.value rules),
       rule_hits = fn () => Synchronized.value rule_hits,
       rule_builds = fn () => Synchronized.value rule_builds}
    end

  type application_owner =
   {convert: cterm -> thm option,
    cache_hits: unit -> int,
    recursive_certifications: unit -> int}

  fun check_application ctxt (owner: application_owner) =
    let
      val natT = HOLogic.natT
      val boolT = HOLogic.boolT
      val columnT = @{typ comma_crt_column}
      val operationT = @{typ comma_crt_boolean_operation}
      val applyT = natT --> natT --> operationT --> columnT --> columnT --> columnT
      fun numeral value = HOLogic.mk_number natT value
      fun bool_column value =
        Const (@{const_name Comma_CRT_Bool}, boolT --> columnT) $ value
      fun apply depth shift operation left right =
        list_comb (Const (@{const_name comma_crt_apply_shifted_from}, applyT),
          [numeral depth, numeral shift, operation, left, right])
      fun invalid work =
        ((work (); false) handle ERROR _ => true)
      val boundary_cases =
        [(0, 0, 0), (0, 1, 1), (0, 923, 1),
         (1, 0, 0), (1, 11, 11), (1, 22, 11),
         (2, 0, 0), (2, 77, 77), (2, 154, 77),
         (3, 0, 0), (3, 231, 231), (3, 462, 231),
         (4, 0, 0), (4, 1, 1), (4, 923, 923)]
      val boundaries_ok = List.all (fn (depth, shift, expected) =>
        canonical_shift depth shift = expected) boundary_cases
      val invalid_scalars_rejected =
        invalid (fn () => canonical_shift (~1) 0) andalso
        invalid (fn () => canonical_shift 5 0) andalso
        invalid (fn () => canonical_shift 1 (~1)) andalso
        invalid (fn () => canonical_shift 1 924)

      val right_digits = map bool_column
        [@{term False}, @{term False}, @{term True}, @{term True},
         @{term False}, @{term True}, @{term False}, @{term False},
         @{term True}, @{term True}, @{term False}]
      val right = Const (@{const_name Comma_CRT_Node},
          natT --> HOLogic.listT columnT --> columnT) $
        numeral 3 $ HOLogic.mk_list columnT right_digits
      val left = bool_column @{term True}
      val and_op = Const (@{const_name Comma_CRT_And}, operationT)
      val first_request = apply 1 1 and_op left right
      val second_request = apply 1 12 and_op left right
      fun run request = #convert owner (Thm.cterm_of ctxt request)
      fun clean request theorem =
        (case theorem of
          SOME checked => Thm.term_of (Thm.lhs_of checked) aconv request andalso
            null (Thm.prems_of checked) andalso null (Thm.hyps_of checked) andalso
            null (Thm.tpairs_of checked) andalso
            null (Thm_Deps.all_oracles [checked])
        | NONE => false)
      val recursive_before = #recursive_certifications owner ()
      val first = run first_request
      val recursive_after_first = #recursive_certifications owner ()
      val hits_before_second = #cache_hits owner ()
      val second = run second_request
      val recursive_after_second = #recursive_certifications owner ()
      val hits_after_second = #cache_hits owner ()
      val exact_original_lhs = clean first_request first andalso
        clean second_request second
      val equal_rhs = (case (first, second) of
        (SOME left_theorem, SOME right_theorem) =>
          Thm.term_of (Thm.rhs_of left_theorem) aconv
            Thm.term_of (Thm.rhs_of right_theorem)
      | _ => false)
      val warm_alias_hit = hits_after_second = hits_before_second + 1 andalso
        recursive_after_second = recursive_after_first andalso
        recursive_after_first > recursive_before
      val _ = if boundaries_ok andalso invalid_scalars_rejected andalso
          exact_original_lhs andalso equal_rhs andalso warm_alias_hit then ()
        else error ("B1 suffix-shift fixture failed: boundaries=" ^
          Bool.toString boundaries_ok ^ ", invalid=" ^
          Bool.toString invalid_scalars_rejected ^ ", exact_lhs=" ^
          Bool.toString exact_original_lhs ^ ", equal_rhs=" ^
          Bool.toString equal_rhs ^ ", warm_alias=" ^ Bool.toString warm_alias_hit)
    in () end
end

(* A checked column may be constant in one or more leading CRT coordinates.
   Drop only those unused Apply levels; unknown literal trees stay unchanged. *)
structure Comma_Semantic_B1_Apply_Depth_Quotient =
struct
  type authority =
   {known_column: term -> bool,
    column_id: term -> int option,
    column_value: int -> term,
    cofactor_node_level: int -> int option,
    (* `prove_admitted` returns an exact, clean fact whose proof graph has
       already passed the column owner's shared incremental oracle audit. *)
    prove_admitted: int * int -> thm}

  fun make ctxt (authority: authority) =
    let
      val natT = HOLogic.natT
      val columnT = @{typ comma_crt_column}
      val applyT = @{typ
        "nat => nat => comma_crt_boolean_operation => comma_crt_column => comma_crt_column => comma_crt_column"}
      fun numeral n = HOLogic.mk_number natT n
      fun apply depth shift operation left right =
        list_comb (Const (@{const_name comma_crt_apply_shifted_from}, applyT),
          [numeral depth, numeral shift, operation, left, right])
      fun admitted lower column =
        Const (@{const_name comma_crt_admitted}, natT --> columnT --> HOLogic.boolT) $
          numeral lower $ column
      val specialization_simpset = Comma_Entry_Arithmetic.natural_context ctxt
      val unused_level_theorem =
        @{thm comma_crt_apply_shifted_from_skip_unused_level}
      val depth_facts = Vector.fromList (map (fn depth =>
        Goal.prove ctxt [] []
          (HOLogic.mk_Trueprop
            (Const (@{const_name less}, natT --> natT --> HOLogic.boolT) $
              numeral depth $ numeral 4))
          (fn {context, ...} => simp_tac
            (Comma_Entry_Arithmetic.natural_context context) 1))
        (0 upto 3))
      fun specialize_depth depth =
        let
          val theorem = Drule.infer_instantiate ctxt
            [(("depth", 0), Thm.cterm_of ctxt (numeral depth))]
            unused_level_theorem
          val theorem = Thm.implies_elim theorem (Vector.sub (depth_facts, depth))
          val theorem = Simplifier.full_simplify specialization_simpset theorem
          val _ = if Thm.nprems_of theorem = 2 andalso
              null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
            then () else error "B1 unused-level specialized theorem changed shape"
        in theorem end
      val depth_rules = Vector.fromList (map specialize_depth (0 upto 3))
      val bool_admissions = Symtab.make (maps (fn lower =>
        map (fn (name, flag) =>
          let
            val column = Const (@{const_name Comma_CRT_Bool}, HOLogic.boolT --> columnT) $ flag
            val request = admitted lower column
            val fact = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop request)
              (fn {context, ...} => simp_tac
                (put_simpset HOL_basic_ss context addsimps
                  [@{thm comma_crt_admitted.simps(1)}]) 1)
          in (Int.toString lower ^ ":" ^ name, (request, fact)) end)
          [("false", @{term False}), ("true", @{term True})]) (1 upto 4))
      val admissions = Synchronized.var
        "semantic_b1_unused_level_admissions" (Termtab.empty: thm Termtab.table)
      val admission_capacity = 65536
      val strips = Synchronized.var "semantic_b1_unused_level_strips" 0
      val transport_rules = Synchronized.var
        "semantic_b1_unused_level_transport_rules" (Termtab.empty: thm Termtab.table)
      val transport_capacity = 65536
      val transport_rule_hits = Synchronized.var
        "semantic_b1_unused_level_transport_rule_hits" 0
      val transport_rule_builds = Synchronized.var
        "semantic_b1_unused_level_transport_rule_builds" 0
      val transport_capacity_refusals = Synchronized.var
        "semantic_b1_unused_level_transport_capacity_refusals" 0

      fun check_fact expected theorem check_oracles =
        if Thm.prop_of theorem aconv (HOLogic.mk_Trueprop expected) andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso
            (not check_oracles orelse null (Thm_Deps.all_oracles [theorem]))
        then theorem
        else error "B1 unused-level admission authority changed its exact premise"

      val _ = Vector.app (fn theorem =>
        if Thm.nprems_of theorem = 2 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso
            null (Thm_Deps.all_oracles [theorem])
        then () else error "B1 unused-level depth rule is not certified") depth_rules
      val _ = List.app (fn (_, (expected, theorem)) =>
        ignore (check_fact expected theorem true)) (Symtab.dest bool_admissions)
      fun cache_admission expected theorem =
        let
          (* The authority producer audits each newly generated proof through
             its shared serial-set certifier before returning it.  Preserve
             our exact proposition/cleanliness check here without traversing
             the same transitive proof graph again. *)
          val checked = check_fact expected theorem false
          val (selected, inserted) = Synchronized.change_result admissions
            (fn cache =>
              (case Termtab.lookup cache expected of
                SOME existing => ((existing, false), cache)
              | NONE =>
                  if Termtab.size cache < admission_capacity then
                    ((checked, true), Termtab.update (expected, checked) cache)
                  else ((checked, false), cache)))
          val _ = if inserted then () else ignore (check_fact expected selected false)
        in selected end

      fun literal_fact lower column flag =
        let
          val expected = admitted lower column
          val key = Int.toString lower ^ ":" ^
            (if flag aconv @{term True} then "true" else "false")
        in
          (case Symtab.lookup bool_admissions key of
            SOME (request, theorem) =>
              if request aconv expected then check_fact expected theorem false
              else error "B1 cached Boolean admission changed its request"
          | NONE => error "B1 literal Boolean admission was not prebuilt")
        end

      fun admission lower column =
        let val expected = admitted lower column in
          (case Termtab.lookup (Synchronized.value admissions) expected of
            SOME theorem => SOME (check_fact expected theorem false)
          | NONE =>
              (case #column_id authority column of
                SOME cid =>
                  let
                    val level = #cofactor_node_level authority cid
                    val terminal = cid < 2 andalso is_none level
                    val level_ok = (case level of SOME value => lower <= value
                      | NONE => terminal)
                    val exact_owner = #known_column authority column andalso
                      column aconv #column_value authority cid
                  in
                    if not (level_ok andalso exact_owner) then NONE
                    else
                      let
                        val theorem = #prove_admitted authority (lower, cid)
                      in SOME (cache_admission expected theorem) end
                  end
              | NONE =>
                  (case strip_comb column of
                    (Const (name, _), [flag]) =>
                      if name = @{const_name Comma_CRT_Bool} andalso
                          (flag aconv @{term True} orelse flag aconv @{term False})
                      then SOME (literal_fact lower column flag) else NONE
                  | _ => NONE)))
        end

      fun right_support column =
        let
          fun admitted_support lower =
            Option.map (fn theorem => (lower, theorem)) (admission lower column)
        in
          (case #column_id authority column of
            SOME cid =>
              (case #cofactor_node_level authority cid of
                SOME lower =>
                  if lower >= 0 andalso lower <= 4
                  then admitted_support lower else NONE
              | NONE => if cid < 2 then admitted_support 4 else NONE)
          | NONE => admitted_support 4)
        end

      fun transport_key depth left right =
        HOLogic.mk_prod (numeral depth, HOLogic.mk_prod (left, right))

      fun transport_rule_shape depth left right theorem =
        let
          fun parts term =
            (case strip_comb term of
              (Const (name, _), [depth_term, shift, operation, lhs, rhs]) =>
                SOME (name, depth_term, shift, operation, lhs, rhs)
            | _ => NONE)
          val lhs = Thm.term_of (Thm.lhs_of theorem)
          val rhs = Thm.term_of (Thm.rhs_of theorem)
        in
          (case (parts lhs, parts rhs) of
            (SOME (lhs_name, lhs_depth, shift, operation, lhs_left, lhs_right),
             SOME (rhs_name, rhs_depth, rhs_shift, rhs_operation, rhs_left, rhs_right)) =>
              lhs_name = @{const_name comma_crt_apply_shifted_from} andalso
              rhs_name = @{const_name comma_crt_apply_shifted_from} andalso
              lhs_depth aconv numeral (depth + 1) andalso
              rhs_depth aconv numeral depth andalso
              Term.is_Var shift andalso fastype_of shift = natT andalso
              shift aconv rhs_shift andalso Term.is_Var operation andalso
              fastype_of operation = @{typ comma_crt_boolean_operation} andalso
              operation aconv rhs_operation andalso
              lhs_left aconv left andalso rhs_left aconv left andalso
              lhs_right aconv right andalso rhs_right aconv right andalso
              length (Term.add_vars lhs []) = 2 andalso
              Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
              null (Thm.tpairs_of theorem)
          | _ => false)
        end

      fun make_transport_rule depth left right left_fact right_fact =
        let
          val theorem = Drule.infer_instantiate ctxt
            [(("left", 0), Thm.cterm_of ctxt left),
             (("right", 0), Thm.cterm_of ctxt right)]
            (Vector.sub (depth_rules, depth))
          val result = theorem
            |> (fn fact => Thm.implies_elim fact left_fact)
            |> (fn fact => Thm.implies_elim fact right_fact)
            |> (fn fact => fact RS @{thm eq_reflection})
        in
          if transport_rule_shape depth left right result then result
          else error "B1 unused-level parametric transport theorem changed shape"
        end

      fun transport_rule depth left right left_fact right_fact =
        let
          val key = transport_key depth left right
        in
          (case Termtab.lookup (Synchronized.value transport_rules) key of
            SOME theorem =>
              (Synchronized.change transport_rule_hits (fn count => count + 1);
               theorem)
          | NONE =>
              let
                val theorem = make_transport_rule depth left right left_fact right_fact
                val _ = Synchronized.change transport_rule_builds (fn count => count + 1)
                val (selected, inserted, refused) =
                  Synchronized.change_result transport_rules (fn cache =>
                    (case Termtab.lookup cache key of
                      SOME existing => ((existing, false, false), cache)
                    | NONE =>
                        if Termtab.size cache < transport_capacity then
                          ((theorem, true, false), Termtab.update (key, theorem) cache)
                        else ((theorem, false, true), cache)))
                val _ = if inserted orelse refused then ()
                  else Synchronized.change transport_rule_hits (fn count => count + 1)
                val _ = if refused then
                    Synchronized.change transport_capacity_refusals (fn count => count + 1)
                  else ()
              in selected end)
        end

      fun skip depth shift operation left right request_ct =
        if depth <= 0 then NONE
        else
          let
            val smaller = depth - 1
            val lower = 4 - smaller
          in
            (case (admission lower left, admission lower right) of
              (SOME left_fact, SOME right_fact) =>
                let
                  val theorem = transport_rule smaller left right left_fact right_fact
                  val result = Conv.rewr_conv theorem request_ct
                  val lhs = apply depth shift operation left right
                  val rhs = apply smaller shift operation left right
                in
                  if Thm.term_of (Thm.lhs_of result) aconv lhs andalso
                      Thm.term_of (Thm.rhs_of result) aconv rhs andalso
                      Thm.nprems_of result = 0 andalso null (Thm.hyps_of result) andalso
                      null (Thm.tpairs_of result)
                  then SOME result
                  else error "B1 unused-level theorem changed its exact Apply request"
                end
            | _ => NONE)
          end

      fun reduce depth shift operation left right request_ct =
        let
          val _ = if depth >= 0 andalso depth <= 4 andalso
              shift >= 0 andalso shift < 924
            then () else error "B1 unused-level Apply request is outside its bounds"
          fun loop 0 current equation count = (0, current, equation, count)
            | loop current_depth current equation count =
                (case skip current_depth shift operation left right current of
                  NONE => (current_depth, current, equation, count)
                | SOME step =>
                    let
                      val lhs = apply current_depth shift operation left right
                      val rhs = apply (current_depth - 1) shift operation left right
                      val _ = if Thm.term_of (Thm.lhs_of step) aconv lhs andalso
                          Thm.term_of (Thm.rhs_of step) aconv rhs then ()
                        else error "B1 unused-level conversion changed its exact request"
                    in loop (current_depth - 1) (Thm.rhs_of step)
                      (Thm.transitive equation step) (count + 1) end)
          val (depth', request', theorem, count) =
            loop depth request_ct (Thm.reflexive request_ct) 0
        in (depth', request', theorem, count) end

      fun record count = if count = 0 then () else
        Synchronized.change strips (fn n => n + count)

      fun check_fixture {convert, recursive_certifications, cache_hits,
          root_exposures} =
        let
          fun candidate cid =
            let val reference = #column_value authority cid in
              if not (#known_column authority reference) then NONE
              else (case #cofactor_node_level authority cid of
                SOME level => if level > 0 andalso
                    #column_id authority reference = SOME cid
                  then SOME cid else NONE
              | NONE => NONE)
            end
          val ids = map_filter candidate (2 upto 64)
          val (left_id, right_id) =
            (case ids of
              left_id :: right_id :: _ => (left_id, right_id)
            | _ => error "B1 unused-level fixture has no admitted node pair")
          val left = #column_value authority left_id
          val right = #column_value authority right_id
          val operation = Const (@{const_name Comma_CRT_And},
            @{typ comma_crt_boolean_operation})
          val high = apply 4 922 operation left right
          val (depth', reduced, equation, count) = reduce 4 922 operation left right
            (Thm.cterm_of ctxt high)
          val probe = make ctxt authority
          val probe_reduce = #reduce probe
          val probe_builds_before = #transport_rule_builds probe ()
          val probe_hits_before = #transport_rule_hits probe ()
          val (probe_depth, probe_reduced, probe_equation, probe_count) =
            probe_reduce 4 922 operation left right (Thm.cterm_of ctxt high)
          val probe_builds_after_first = #transport_rule_builds probe ()
          val probe_hits_after_first = #transport_rule_hits probe ()
          val alternate_operation = Const (@{const_name Comma_CRT_Or},
            @{typ comma_crt_boolean_operation})
          val alternate_shift = 921
          val alternate_high = apply 4 alternate_shift alternate_operation left right
          val (alternate_depth, alternate_reduced, alternate_equation, alternate_count) =
            probe_reduce 4 alternate_shift alternate_operation left right
              (Thm.cterm_of ctxt alternate_high)
          val probe_hits_after_alternate = #transport_rule_hits probe ()
          val probe_builds_after_alternate = #transport_rule_builds probe ()
          val expected = apply depth' 922 operation left right
          val exact_equation = Thm.term_of (Thm.lhs_of equation) aconv high andalso
            Thm.term_of (Thm.rhs_of equation) aconv expected andalso
            Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
            null (Thm.tpairs_of equation) andalso Thm.term_of reduced aconv expected
          val probe_expected = apply probe_depth 922 operation left right
          val probe_exact_equation =
            Thm.term_of (Thm.lhs_of probe_equation) aconv high andalso
            Thm.term_of (Thm.rhs_of probe_equation) aconv probe_expected andalso
            Thm.nprems_of probe_equation = 0 andalso
            null (Thm.hyps_of probe_equation) andalso
            null (Thm.tpairs_of probe_equation) andalso
            Thm.term_of probe_reduced aconv probe_expected
          val alternate_expected = apply alternate_depth alternate_shift
            alternate_operation left right
          val alternate_exact_equation =
            Thm.term_of (Thm.lhs_of alternate_equation) aconv alternate_high andalso
            Thm.term_of (Thm.rhs_of alternate_equation) aconv alternate_expected andalso
            Thm.nprems_of alternate_equation = 0 andalso
            null (Thm.hyps_of alternate_equation) andalso
            null (Thm.tpairs_of alternate_equation) andalso
            Thm.term_of alternate_reduced aconv alternate_expected
          val parametric_reuse = count > 0 andalso alternate_count = count andalso
            probe_count = count andalso
            probe_builds_after_first - probe_builds_before = count andalso
            probe_hits_after_first = probe_hits_before andalso
            probe_builds_after_alternate = probe_builds_after_first andalso
            probe_hits_after_alternate - probe_hits_after_first = count
          val literal_node = Const (@{const_name Comma_CRT_Node},
            natT --> HOLogic.listT columnT --> columnT) $ numeral 0 $
            HOLogic.mk_list columnT (map (fn flag =>
              Const (@{const_name Comma_CRT_Bool}, HOLogic.boolT --> columnT) $ flag)
              [@{term False}, @{term True}, @{term False}, @{term True}])
          val (opaque_depth, _, opaque_equation, opaque_count) = reduce 4 922
            operation literal_node right
            (Thm.cterm_of ctxt (apply 4 922 operation literal_node right))
          val opaque_fallback = opaque_depth = 4 andalso opaque_count = 0 andalso
            Thm.is_reflexive opaque_equation
          val before_recursion = recursive_certifications ()
          val before_hits = cache_hits ()
          val before_exposures = root_exposures ()
          val before_strips = Synchronized.value strips
          val first = convert (Thm.cterm_of ctxt high)
          val after_first = recursive_certifications ()
          val after_first_exposures = root_exposures ()
          val after_strips = Synchronized.value strips
          val low = apply depth' 922 operation left right
          val second = convert (Thm.cterm_of ctxt low)
          val after_second = recursive_certifications ()
          val after_hits = cache_hits ()
          val after_second_exposures = root_exposures ()
          fun clean lhs theorem = Thm.term_of (Thm.lhs_of theorem) aconv lhs andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) andalso null (Thm_Deps.all_oracles [theorem])
          val exact_lhs = (case first of SOME theorem => clean high theorem | NONE => false)
            andalso (case second of SOME theorem => clean low theorem | NONE => false)
          val equal_rhs = (case (first, second) of
            (SOME a, SOME b) => Thm.term_of (Thm.rhs_of a) aconv Thm.term_of (Thm.rhs_of b)
          | _ => false)
          val warm = after_first > before_recursion andalso after_strips > before_strips andalso
            after_first_exposures > before_exposures andalso
            after_second = after_first andalso after_hits > before_hits andalso
            after_second_exposures = after_first_exposures
        in
          if count > 0 andalso exact_equation andalso probe_exact_equation andalso
              alternate_exact_equation andalso
              parametric_reuse andalso opaque_fallback andalso
              exact_lhs andalso equal_rhs andalso warm then ()
          else error ("B1 unused-level quotient production fixture failed: exact=" ^
            Bool.toString exact_equation ^ ", probe=" ^
            Bool.toString probe_exact_equation ^ ", alternate=" ^
            Bool.toString alternate_exact_equation ^ ", parametric=" ^
            Bool.toString parametric_reuse ^ ", opaque=" ^
            Bool.toString opaque_fallback ^ ", exact_lhs=" ^
            Bool.toString exact_lhs ^ ", equal_rhs=" ^ Bool.toString equal_rhs ^
            ", warm=" ^ Bool.toString warm)
        end
    in {reduce = reduce, record = record, admission = admission,
        right_support = right_support, strips = fn () => Synchronized.value strips,
        transport_rule_hits = fn () => Synchronized.value transport_rule_hits,
        transport_rule_builds = fn () => Synchronized.value transport_rule_builds,
        transport_capacity_refusals = fn () => Synchronized.value transport_capacity_refusals,
        retained_transport_rules = fn () => Termtab.size (Synchronized.value transport_rules),
        check_fixture = check_fixture}
    end
end
