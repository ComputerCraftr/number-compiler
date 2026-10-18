(* Proof-producing normalization of the finite source-axis grammar used by
   generated B1 actions.  The accepted heads and scalar bounds are explicit;
   generated applications return to the shared apply-DAG owner. *)
signature COMMA_SEMANTIC_B1_SOURCE_COLUMN_NORMALIZER =
sig
  val reify_known_reference: (term -> bool) -> (cterm -> thm) -> cterm -> thm
  val check_digit_equation_cache: Proof.context -> unit
  val make: Proof.context ->
    {known_column: term -> bool,
     valid_column: term -> bool,
     column_value: int -> term,
     nat_value: term -> int option,
     normalize_scalars: cterm -> thm option,
     cofactor_transition: int * int * int -> {target_cid: int, theorem: thm},
     open_column_reference: cterm -> thm,
     reify_column: cterm -> thm,
     convert: (cterm -> thm option) Unsynchronized.ref} ->
    {normalize: cterm -> thm, stats: unit -> string}
end

structure Comma_Semantic_B1_Source_Column_Normalizer:
  COMMA_SEMANTIC_B1_SOURCE_COLUMN_NORMALIZER =
struct
  fun reify_known_reference known_column reify_column ct =
    if known_column (Thm.term_of ct) then Thm.reflexive ct
    else reify_column ct

  fun make_cofactor_equation_cache ctxt name build =
    let
      val natT = HOLogic.natT
      val columnT = @{typ comma_crt_column}
      fun numeral value = HOLogic.mk_number natT value
      val nat_plus = Const (@{const_name plus}, natT --> natT --> natT)
      val nat_mod = Const (@{const_name modulo}, natT --> natT --> natT)
      val period = Const (@{const_name comma_crt_period}, natT --> natT)
      val nat_cofactor = Const (@{const_name comma_crt_cofactor_or_false},
        natT --> natT --> columnT --> columnT)
      val nat_shifted_cofactor = Const
        (@{const_name comma_crt_shifted_cofactor_or_false},
          natT --> natT --> natT --> columnT --> columnT)
      type equations = {arithmetic: thm, transport: thm}
      val cache: equations Comma_Semantic_B1_Term_LRU.cache =
        Comma_Semantic_B1_Term_LRU.make name 8192
      val builds = Synchronized.var (name ^ "_builds") 0
      fun expression level digit shift =
        nat_mod $ (nat_plus $ numeral digit $ numeral shift) $ (period $ numeral level)
      fun key level digit shift = HOLogic.mk_prod (numeral level,
        HOLogic.mk_prod (numeral digit, numeral shift))
      fun check_arithmetic level digit shift effective check_oracles theorem =
        let
          val expected_lhs = expression level digit shift
          val expected_rhs = numeral effective
          val exact = Thm.term_of (Thm.lhs_of theorem) aconv expected_lhs andalso
            Thm.term_of (Thm.rhs_of theorem) aconv expected_rhs
          val clean = Thm.nprems_of theorem = 0 andalso
            null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
          val oracle_free = not check_oracles orelse
            null (Thm_Deps.all_oracles [theorem])
        in
          if fastype_of expected_lhs = natT andalso exact andalso clean andalso oracle_free
          then theorem
          else error "B1 cached cofactor digit equation changed its exact arithmetic"
        end
      fun shifted_request level digit shift column =
        nat_shifted_cofactor $ numeral level $ numeral digit $ numeral shift $ column
      fun unshifted_request level effective column =
        nat_cofactor $ numeral level $ numeral effective $ column
      fun check_transport level digit shift effective check_oracles theorem =
        let
          val column = Var ((name ^ "_cofactor_column", 0), columnT)
          val expected_lhs = shifted_request level digit shift column
          val expected_rhs = unshifted_request level effective column
          val exact = Thm.term_of (Thm.lhs_of theorem) aconv expected_lhs andalso
            Thm.term_of (Thm.rhs_of theorem) aconv expected_rhs
          val clean = Thm.nprems_of theorem = 0 andalso
            null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)
          val oracle_free = not check_oracles orelse
            null (Thm_Deps.all_oracles [theorem])
        in
          if exact andalso clean andalso oracle_free then theorem
          else error "B1 cached cofactor bridge changed its schematic-column endpoints"
        end
      fun make_transport level digit shift effective arithmetic =
        let
          val column = Var ((name ^ "_cofactor_column", 0), columnT)
          val request = shifted_request level digit shift column
          val unfold = Conv.rewr_conv
            (@{thm comma_crt_shifted_cofactor_or_false_as_cofactor}
              RS @{thm eq_reflection}) (Thm.cterm_of ctxt request)
          val digit_equation = Comma_Semantic_B1_Column_Lookup_Cache.argument_at 1
            (Conv.rewr_conv arithmetic) (Thm.rhs_of unfold)
          val bridge = Thm.transitive unfold digit_equation
        in check_transport level digit shift effective true bridge end
      fun get level digit shift effective =
        let val cache_key = key level digit shift in
          (case Comma_Semantic_B1_Term_LRU.lookup cache cache_key of
            SOME equations =>
              {arithmetic = check_arithmetic level digit shift effective false
                  (#arithmetic equations),
               transport = check_transport level digit shift effective false
                  (#transport equations)}
          | NONE =>
              let
                val arithmetic = check_arithmetic level digit shift effective true
                  (build (expression level digit shift))
                val transport = make_transport level digit shift effective arithmetic
                val equations = {arithmetic = arithmetic, transport = transport}
                val _ = Comma_Semantic_B1_Term_LRU.insert_completed cache cache_key equations
                val _ = Synchronized.change builds (fn count => count + 1)
              in equations end)
        end
    in
      {get = get, builds = fn () => Synchronized.value builds,
       hits = fn () => Comma_Semantic_B1_Term_LRU.hits cache,
       evictions = fn () => Comma_Semantic_B1_Term_LRU.evictions cache,
       refusals = fn () => Comma_Semantic_B1_Term_LRU.refusals cache}
    end

  fun check_digit_equation_cache ctxt =
    let
      val context = (Comma_Entry_Arithmetic.natural_context ctxt) addsimps
        @{thms comma_crt_period_def nth_Cons' nth_Cons_0}
      val poisoned = Unsynchronized.ref false
      val poison_calls = Unsynchronized.ref 0
      fun build expression =
        if !poisoned then
          (poison_calls := !poison_calls + 1;
           error "B1 cofactor digit cache fixture builder poison")
        else Simplifier.rewrite context (Thm.cterm_of ctxt expression)
      val cache = make_cofactor_equation_cache ctxt
        "source_column_digit_fixture" build
      val cold = #get cache 0 2 2 0
      val other_clock = #get cache 1 2 2 1
      val _ = poisoned := true
      val warm = #get cache 0 2 2 0
      val second_source_warm = #get cache 0 2 2 0
      fun exact lhs rhs theorem =
        Thm.term_of (Thm.lhs_of theorem) aconv lhs andalso
        Thm.term_of (Thm.rhs_of theorem) aconv rhs andalso
        Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem) andalso null (Thm_Deps.all_oracles [theorem])
      val natT = HOLogic.natT
      val columnT = @{typ comma_crt_column}
      val dagT = @{typ comma_semantic_b1_crt_column_dag}
      fun numeral value = HOLogic.mk_number natT value
      val nat_plus = Const (@{const_name plus}, natT --> natT --> natT)
      val nat_mod = Const (@{const_name modulo}, natT --> natT --> natT)
      val period = Const (@{const_name comma_crt_period}, natT --> natT)
      fun lhs level shift = nat_mod $
        (nat_plus $ numeral 2 $ numeral shift) $ (period $ numeral level)
      val cold_exact = exact (lhs 0 2) (numeral 0) (#arithmetic cold)
      val changed_clock_exact = exact (lhs 1 2) (numeral 1) (#arithmetic other_clock)
      val column_at = Const (@{const_name comma_semantic_b1_crt_column_at},
        dagT --> natT --> columnT)
      val dag = @{term Comma_B1_CRT_Column_DAG_Empty}
      val source_left = column_at $ dag $ numeral 2
      val source_right = column_at $ dag $ numeral 3
      fun shifted column = Const (@{const_name comma_crt_shifted_cofactor_or_false},
          natT --> natT --> natT --> columnT --> columnT) $
        numeral 0 $ numeral 2 $ numeral 2 $ column
      fun unshifted column = Const (@{const_name comma_crt_cofactor_or_false},
          natT --> natT --> columnT --> columnT) $ numeral 0 $ numeral 0 $ column
      fun bridge_is_exact column theorem =
        let
          val converted = Conv.rewr_conv (#transport theorem)
            (Thm.cterm_of ctxt (shifted column))
        in exact (shifted column) (unshifted column) converted end
      val shared_bridge_reuse = bridge_is_exact source_left warm andalso
        bridge_is_exact source_right second_source_warm
      val warm_reuse = exact (lhs 0 2) (numeral 0) (#arithmetic warm) andalso
        Thm.prop_of (#transport warm) aconv Thm.prop_of (#transport second_source_warm) andalso
        #builds cache () = 2 andalso #hits cache () = 2 andalso
        #evictions cache () = 0 andalso #refusals cache () = 0 andalso shared_bridge_reuse
      val wrong_effective_rejected =
        (case Exn.capture (fn () => #get cache 0 2 2 1) () of
          Exn.Res _ => false
        | Exn.Exn _ => true)
      val changed_shift_rejected =
        (case Exn.capture (fn () => #get cache 0 2 3 1) () of
          Exn.Res _ => false
        | Exn.Exn _ => true)
      val _ = poisoned := false
      val changed_shift_retry = #get cache 0 2 3 1
      val retry_exact = exact (lhs 0 3) (numeral 1) (#arithmetic changed_shift_retry) andalso
        #builds cache () = 3
    in
      if cold_exact andalso changed_clock_exact andalso warm_reuse andalso
          wrong_effective_rejected andalso changed_shift_rejected andalso
          !poison_calls = 1 andalso retry_exact then ()
      else error "B1 shared cofactor bridge cache fixture failed"
    end

  fun make bounded_context
      {known_column, valid_column, column_value, nat_value, normalize_scalars,
       cofactor_transition,
       open_column_reference, reify_column, convert} =
    let
      val columnT = @{typ comma_crt_column}
      val source_periods = [1, 2, 3, 6, 22, 28]
      val clock_periods = Vector.fromList [4, 3, 7, 11]
      val cache = Synchronized.var "semantic_b1_source_column_equations"
        (Termtab.empty: thm Termtab.table)
      val source_refusals = Synchronized.var "semantic_b1_source_column_refusals" 0
      val cache_capacity = 4096
      val recursive_apply_defs = @{thms comma_crt_apply_def
        comma_crt_apply_from_def comma_crt_apply_shifted_def
        comma_crt_apply_shifted_from.simps}
      val source_scope_context =
        bounded_context delsimps recursive_apply_defs
        addsimps @{thms comma_crt_source_scope_column_def comma_crt_period_def
          prod.case if_True if_False}
      val source_axis_context =
        (bounded_context delsimps recursive_apply_defs)
        addsimps @{thms comma_crt_source_axis_column_def comma_crt_period_def
          upt_0 upt_Suc upt_rec
          upt_rec_numeral list.map list_all_Nil_iff list_all_Cons_iff
          prod.case if_True if_False}
      val cofactor_shift_context =
        (Comma_Entry_Arithmetic.natural_context bounded_context)
        addsimps @{thms comma_crt_period_def nth_Cons' nth_Cons_0}
      val cofactor_equation_cache = make_cofactor_equation_cache bounded_context
        "source_column_cofactor_equation"
        (fn expression => Simplifier.rewrite cofactor_shift_context
          (Thm.cterm_of bounded_context expression))
      fun cofactor_equation_stats () =
        "apply_dag_cofactor_equation_builds=" ^
          Int.toString (#builds cofactor_equation_cache ()) ^
        " apply_dag_cofactor_equation_hits=" ^
          Int.toString (#hits cofactor_equation_cache ()) ^
        " apply_dag_cofactor_equation_evictions=" ^
          Int.toString (#evictions cofactor_equation_cache ()) ^
        " apply_dag_cofactor_equation_refusals=" ^
          Int.toString (#refusals cofactor_equation_cache ())

      fun source_head term =
        (case strip_comb term of
          (Const (name, _), _) =>
            member (op =) [@{const_name comma_crt_source_scope_column},
              @{const_name comma_crt_source_axis_column}] name
        | _ => false)

      fun admitted_source term =
        (case strip_comb term of
          (Const (name, _), [level, divisor, residue]) =>
            if name <> @{const_name comma_crt_source_axis_column} then false
            else
              (case (nat_value level, nat_value divisor, nat_value residue) of
                (SOME l, SOME d, SOME r) =>
                  if l >= 4 then false
                  else
                    let val period = Vector.sub (clock_periods, l)
                    in d > 0 andalso d <= period andalso period mod d = 0 andalso
                      r < 924 end
              | _ => false)
          | (Const (name, _), [scope]) =>
            if name <> @{const_name comma_crt_source_scope_column} then false
            else
              (case try HOLogic.dest_prod scope of
                SOME (period, residue) =>
                  (case (nat_value period, nat_value residue) of
                    (SOME p, SOME r) => member (op =) source_periods p andalso r < p
                  | _ => false)
              | NONE => false)
          | _ => false)

      fun source_refusal_reason term =
        (case strip_comb term of
          (Const (name, _), [level, divisor, residue]) =>
            if name <> @{const_name comma_crt_source_axis_column} then
              "unexpected-source-head"
            else
              (case (nat_value level, nat_value divisor, nat_value residue) of
                (SOME l, SOME d, SOME r) =>
                  if l >= 4 then "axis-level-bound"
                  else
                    let val period = Vector.sub (clock_periods, l)
                    in if d <= 0 orelse d > period orelse period mod d <> 0 then
                         "axis-divisor-domain"
                       else if r >= 924 then "axis-residue-bound"
                       else "axis-domain"
                    end
              | _ => "axis-numeral-normalization")
        | (Const (name, _), [scope]) =>
            if name <> @{const_name comma_crt_source_scope_column} then
              "unexpected-source-head"
            else
              (case try HOLogic.dest_prod scope of
                SOME (period, residue) =>
                  (case (nat_value period, nat_value residue) of
                    (SOME p, SOME r) =>
                      if not (member (op =) source_periods p) then
                        "scope-period-domain"
                      else if r >= p then "scope-residue-bound"
                      else "scope-domain"
                  | _ => "scope-numeral-normalization")
              | NONE => "scope-pair-normalization")
        | _ => "source-shape")

      fun report_source_refusal term reason =
        let val count = Synchronized.change_result source_refusals
          (fn previous => (previous + 1, previous + 1))
        in if count <= 8 then
          Comma_Proof_Profile.report
            ("B1 source-column admission refusal: " ^ reason ^ " " ^
              (case strip_comb term of
                (Const (name, _), [level, divisor, residue]) =>
                  if name = @{const_name comma_crt_source_axis_column} then
                    "level=" ^ (case nat_value level of
                      SOME n => Int.toString n | NONE => "?") ^
                    ",divisor=" ^ (case nat_value divisor of
                      SOME n => Int.toString n | NONE => "?") ^
                    ",residue=" ^ (case nat_value residue of
                      SOME n => Int.toString n | NONE => "?")
                  else "source-head=" ^ Long_Name.base_name name
              | (Const (name, _), [_]) =>
                  "source-head=" ^ Long_Name.base_name name
              | _ => "source-head=other"))
        else () end

      (* An If operand can be part of the published source grammar.  Reduce
         only a closed guard and transport its exact Boolean equation under
         the guard position; the unselected branch is never normalized. *)
      fun selected_closed_if ct =
        (case strip_comb (Thm.term_of ct) of
          (Const (name, _), [condition, _, _]) =>
            if name <> @{const_name If} orelse fastype_of condition <> @{typ bool} orelse
                Term.is_open condition orelse not (null (Term.add_frees condition [])) orelse
                not (null (Term.add_vars condition [])) then NONE
            else SOME (Comma_Semantic_B1_Column_Lookup_Cache.choose_closed_if
              bounded_context bounded_context
              ("B1 source-column normalizer expected an If node",
               "B1 source-column guard did not normalize to a Boolean",
               "B1 source-column normalizer encountered a malformed If") ct)
        | _ => NONE)

      fun closed theorem = null (Thm.prems_of theorem) andalso
        null (Thm.hyps_of theorem) andalso null (Thm.tpairs_of theorem)

      fun literal_bool term =
        Term.head_of term = @{term True} orelse Term.head_of term = @{term False}

      fun normalize_scalar ct =
        (case normalize_scalars ct of
          SOME theorem => theorem
        | NONE => Thm.reflexive ct)

      val reify_if_needed = reify_known_reference known_column reify_column

      fun is_column_reference term =
        (case strip_comb term of
          (Const (name, _), [_, _]) =>
            name = @{const_name comma_semantic_b1_crt_column_at} andalso
              fastype_of term = columnT
        | _ => false)

      fun is_node_column term =
        (case strip_comb term of
          (Const (name, _), [_, _]) =>
            name = @{const_name Comma_CRT_Node} andalso
              fastype_of term = columnT
        | _ => false)

      fun normalize_bool_column ct =
        (case strip_comb (Thm.term_of ct) of
          (Const (name, _), [flag]) =>
            if name <> @{const_name Comma_CRT_Bool} orelse
                fastype_of flag <> @{typ bool} orelse Term.is_open flag orelse
                not (null (Term.add_frees flag [])) orelse
                not (null (Term.add_vars flag []))
            then Conv.all_conv ct
            else
              let
                val equation = Simplifier.rewrite bounded_context
                  (Thm.cterm_of bounded_context flag)
                val selected = Thm.term_of (Thm.rhs_of equation)
              in
                if literal_bool selected andalso closed equation
                then Conv.arg_conv (Conv.rewr_conv equation) ct
                else Conv.all_conv ct
              end
        | _ => Conv.all_conv ct)

      fun complete_column term =
        fastype_of term = columnT andalso not (Term.is_open term) andalso
          valid_column term

      fun cached_source request =
        (case Termtab.lookup (Synchronized.value cache) request of
          SOME theorem =>
            if closed theorem andalso Thm.term_of (Thm.lhs_of theorem) aconv request andalso
                complete_column (Thm.term_of (Thm.rhs_of theorem))
            then SOME theorem
            else error "B1 source-column equation cache is malformed"
        | NONE => NONE)

      fun publish_source request theorem =
        Synchronized.change_result cache (fn facts =>
          case Termtab.lookup facts request of
            SOME existing => (existing, facts)
          | NONE =>
              if Termtab.size facts >= cache_capacity then (theorem, facts)
              else (theorem, Termtab.update (request, theorem) facts))

      fun normalize_source ct =
        let
          val request = Thm.term_of ct
        in
          (case cached_source request of
            SOME theorem => theorem
          | NONE =>
              (case normalize_scalars ct of
                NONE =>
                  (report_source_refusal request "scalar-normalization-failed";
                   Thm.reflexive ct)
              | SOME scalar_equation =>
                  let
                    val scalar_ct = Thm.rhs_of scalar_equation
                    val canonical_request = Thm.term_of scalar_ct
                  in
                    if not (admitted_source canonical_request) then
                      (report_source_refusal canonical_request
                        (source_refusal_reason canonical_request);
                       Thm.reflexive ct)
                    else
                      let
                        val source_context =
                          (case Term.head_of canonical_request of
                            Const (name, _) =>
                              if name = @{const_name comma_crt_source_scope_column}
                              then source_scope_context else source_axis_context
                          | _ => source_axis_context)
                        val unfolded = Simplifier.rewrite source_context scalar_ct
                        val unfolded_term = Thm.term_of (Thm.rhs_of unfolded)
                        val _ = if unfolded_term aconv canonical_request then
                          raise TERM ("B1 source-column unfolding made no progress",
                            [canonical_request]) else ()
                        val normalized = normalize_expression (Thm.rhs_of unfolded)
                        val reified = reify_if_needed (Thm.rhs_of normalized)
                        val theorem = Thm.transitive scalar_equation
                          (Thm.transitive unfolded (Thm.transitive normalized reified))
                        val result = Thm.term_of (Thm.rhs_of theorem)
                      in
                        if not (Thm.term_of (Thm.rhs_of unfolded) aconv canonical_request) andalso
                           closed theorem andalso Thm.term_of (Thm.lhs_of theorem) aconv request andalso
                           complete_column result
                        then
                          let
                            val selected = publish_source request theorem
                            val selected_result = Thm.term_of (Thm.rhs_of selected)
                          in
                            if closed selected andalso
                               Thm.term_of (Thm.lhs_of selected) aconv request andalso
                               complete_column selected_result then selected
                            else error "B1 source-column publication raced with a malformed equation"
                          end
                        else raise TERM ("B1 source-column normalization rejected", [request])
                      end
                  end))
        end

      and normalize_expression ct =
        let
          val request = Thm.term_of ct
          val head = Term.head_of request
          val is_apply =
            (case head of
              Const (name, _) => member (op =)
                [@{const_name comma_crt_apply}, @{const_name comma_crt_apply_from},
                 @{const_name comma_crt_apply_shifted},
                 @{const_name comma_crt_apply_shifted_from}] name
            | _ => false)
        in
          if source_head request then
            normalize_source ct
          else if known_column request then Thm.reflexive ct
          else if is_column_reference request then
            Comma_Semantic_B1_Column_Lookup_Cache.argument_at
              0 normalize_scalar ct
          else if is_node_column request then
            let
              val level = Comma_Semantic_B1_Column_Lookup_Cache.argument_at
                1 normalize_scalar ct
              val children = Comma_Semantic_B1_Column_Lookup_Cache.argument_at
                0 normalize_expression (Thm.rhs_of level)
              val row = Thm.transitive level children
            in Thm.transitive row (reify_if_needed (Thm.rhs_of row)) end
          else if (case strip_comb request of
                (Const (name, _), [flag]) => name = @{const_name Comma_CRT_Bool} andalso
                  literal_bool flag
              | _ => false)
          then Thm.reflexive ct
          else if is_apply then
            (case !convert ct of SOME theorem => theorem | NONE => Thm.reflexive ct)
          else if (case strip_comb request of
              (Const (name, _), [_]) => name = @{const_name Comma_CRT_Bool}
            | _ => false) then
            normalize_bool_column ct
          else if (case head of
              Const (name, _) => name = @{const_name If}
            | _ => false) then
            (case selected_closed_if ct of
              SOME theorem => Thm.transitive theorem
                (normalize_expression (Thm.rhs_of theorem))
            | NONE => Thm.reflexive ct)
          else if (case head of
              Const (name, _) => member (op =)
                [@{const_name comma_crt_cofactor_or_false},
                 @{const_name comma_crt_shifted_cofactor_or_false}] name
            | _ => false) then
            normalize_cofactor ct
          else
            (case request of
              _ $ _ => Conv.combination_conv normalize_expression
                normalize_expression ct
            | _ => Thm.reflexive ct)
        end

      and normalize_cofactor ct =
        let
          val (head, arguments) = strip_comb (Thm.term_of ct)
          val name = (case head of Const (constant, _) => constant | _ => "")
          val (level_index, digit_index, shift_index) =
            if name = @{const_name comma_crt_cofactor_or_false}
            then (2, 1, NONE) else (3, 2, SOME 1)
          val _ = if length arguments = (case shift_index of NONE => 3 | SOME _ => 4)
            then () else raise TERM ("malformed CRT cofactor", [Thm.term_of ct])
          val level = Comma_Semantic_B1_Column_Lookup_Cache.argument_at
            level_index normalize_scalar ct
          val digit = Comma_Semantic_B1_Column_Lookup_Cache.argument_at
            digit_index normalize_scalar (Thm.rhs_of level)
          val shifted =
            (case shift_index of
              NONE => digit
            | SOME index => Thm.transitive digit
                (Comma_Semantic_B1_Column_Lookup_Cache.argument_at
                  index normalize_scalar (Thm.rhs_of digit)))
          val column = Comma_Semantic_B1_Column_Lookup_Cache.argument_at
            0 normalize_expression (Thm.rhs_of shifted)
          val canonical_request = Thm.term_of (Thm.rhs_of column)
          fun reference_cid term =
            (case strip_comb term of
              (Const (reference_name, _), [_, cid_term]) =>
                if reference_name = @{const_name comma_semantic_b1_crt_column_at} andalso
                    known_column term then nat_value cid_term
                else NONE
            | _ => NONE)
          fun transitioned (level_term, digit_term, shift_term, column_term) =
            (case (nat_value level_term, nat_value digit_term,
                   reference_cid column_term) of
              (SOME level_value, SOME digit_value, SOME cid) =>
                let
                  val radix = if level_value >= 0 andalso level_value < 4
                    then Vector.sub (clock_periods, level_value) else 0
                  val effective_digit = (case shift_term of
                      NONE => digit_value
                    | SOME shift_value =>
                        (case nat_value shift_value of
                          SOME amount =>
                            if radix > 0 then
                              ((digit_value mod radix) + (amount mod radix)) mod radix
                            else ~1
                        | NONE => ~1))
                in
                  if radix = 0 orelse effective_digit < 0 orelse
                      effective_digit >= radix then NONE
                  else
                    let
                      val request =
                        Const (@{const_name comma_crt_cofactor_or_false},
                          @{typ nat} --> @{typ nat} --> columnT --> columnT) $
                        HOLogic.mk_number @{typ nat} level_value $
                        HOLogic.mk_number @{typ nat} effective_digit $
                        column_term
                      val {target_cid, theorem = transition} =
                        cofactor_transition (level_value, effective_digit, cid)
                      val transition_lhs = Thm.term_of (Thm.lhs_of transition)
                      val transition_rhs = Thm.term_of (Thm.rhs_of transition)
                      val target_valid = target_cid >= 0 andalso
                        transition_rhs aconv column_value target_cid andalso
                        known_column transition_rhs
                    in
                      if not (closed transition) orelse
                          not (transition_lhs aconv request) orelse
                          not target_valid then NONE
                      else
                        let
                          val argument_equation = Thm.transitive level
                            (Thm.transitive shifted column)
                          val selected_input = Thm.term_of (Thm.rhs_of argument_equation)
                          val unshifted_request = request
                          val shift_bridge =
                            (case shift_term of
                              NONE => Thm.reflexive (Thm.cterm_of bounded_context selected_input)
                            | SOME amount =>
                                let
                                  val digit_shift =
                                    (case nat_value amount of
                                      SOME value => value
                                    | NONE => raise TERM
                                        ("normalized cofactor shift is not a numeral", [amount]))
                                  val {transport = bridge_rule, ...} =
                                    #get cofactor_equation_cache level_value
                                      digit_value digit_shift effective_digit
                                  val bridge = Conv.rewr_conv bridge_rule
                                    (Thm.cterm_of bounded_context selected_input)
                                in
                                  if Thm.term_of (Thm.rhs_of bridge) aconv unshifted_request
                                  then bridge
                                  else raise TERM
                                    ("shifted cofactor did not reduce to its admitted transition",
                                      [selected_input, unshifted_request])
                                end)
                          val translated = Thm.transitive argument_equation shift_bridge
                        in SOME (Thm.transitive translated transition) end
                    end
                end
            | _ => NONE)
          val transition_result =
            (case strip_comb canonical_request of
              (_, [level_term, digit_term, column_term]) =>
                transitioned (level_term, digit_term, NONE, column_term)
            | (_, [level_term, digit_term, shift_term, column_term]) =>
                transitioned (level_term, digit_term, SOME shift_term, column_term)
            | _ => NONE)
          val theorem =
            (case transition_result of
              SOME theorem => theorem
            | NONE =>
                let
                  val exposed = Comma_Semantic_B1_Column_Lookup_Cache.argument_at
                    0 open_column_reference (Thm.rhs_of column)
                  val reduced = Simplifier.rewrite bounded_context (Thm.rhs_of exposed)
                  val exposed_request = Thm.term_of (Thm.rhs_of exposed)
                  val reduced_request = Thm.term_of (Thm.rhs_of reduced)
                  val _ = if reduced_request aconv exposed_request orelse
                      reduced_request aconv canonical_request then
                    raise TERM ("CRT cofactor fallback made no progress",
                      [canonical_request]) else ()
                  val normalized = normalize_expression (Thm.rhs_of reduced)
                  val reified = reify_if_needed (Thm.rhs_of normalized)
                in Thm.transitive level
                  (Thm.transitive shifted
                    (Thm.transitive column
                      (Thm.transitive exposed (Thm.transitive reduced
                        (Thm.transitive normalized reified))))) end)
          val result = Thm.term_of (Thm.rhs_of theorem)
        in
          if closed theorem andalso
              Thm.term_of (Thm.lhs_of theorem) aconv Thm.term_of ct andalso
              fastype_of result = columnT andalso
              complete_column result then theorem
          else raise TERM ("CRT cofactor did not normalize to an admitted column",
            [Thm.term_of ct, result])
        end
    in {normalize = normalize_expression, stats = cofactor_equation_stats} end
end
