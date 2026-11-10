(* Shared proof-producing arithmetic for a single decisive endpoint.  The
   caller supplies its existing kernel context; this owner never constructs a
   second kernel or evaluates a complete B1 trajectory. *)
structure Comma_Decisive_Endpoint_Kernel =
struct
  fun make ctxt kernel_context =
    let
      val natT = @{typ nat}
      val intT = @{typ int}
      fun nat n = HOLogic.mk_number natT n
      val profiling = getenv "COMMA_PROFILE_LOG" <> ""
      fun closed term =
        null (Term.add_frees term []) andalso null (Term.add_vars term []) andalso
          not (Term.is_open term)
      fun schematic pattern = Term.map_aterms
        (fn Free (name, typ) => Var ((name, 0), typ) | atom => atom) pattern
      fun constructor_args name term =
        (case Term.strip_comb term of
          (Const (actual, _), args) => if actual = name then SOME args else NONE
        | _ => NONE)
      fun exact_numeral typ term =
        (case try HOLogic.dest_number term of
          SOME (actual, _) => actual = typ
        | NONE => false)
      fun exact_integer term =
        exact_numeral intT term orelse
          (case Term.strip_comb term of
            (Const (name, _), [magnitude]) =>
              name = @{const_name uminus} andalso exact_numeral intT magnitude
          | _ => false)
      fun complete_value term = complete_at (fastype_of term) term
      and complete_at typ term =
        fastype_of term = typ andalso
        (if typ = natT then exact_numeral typ term
         else if typ = intT then exact_integer term
         else
           case typ of
             Type (name, [leftT, rightT]) =>
               if name = @{type_name prod} then
                 (case constructor_args @{const_name Pair} term of
                   SOME [left, right] =>
                     complete_at leftT left andalso complete_at rightT right
                 | _ => false)
               else false
           | Type (name, [elementT]) =>
               if name = @{type_name option} then
                 (case constructor_args @{const_name None} term of
                   SOME [] => true
                 | _ =>
                     (case constructor_args @{const_name Some} term of
                       SOME [element] => complete_at elementT element
                     | _ => false))
               else false
           | Type (name, []) =>
               if name = @{type_name comma_finite_position} then
                 (case constructor_args @{const_name Comma_Entry} term of
                   SOME [scale, delta, offset] =>
                     List.all (complete_at natT) [scale, delta, offset]
                 | _ =>
                     (case constructor_args @{const_name Comma_Near} term of
                       SOME [scale, delta, headroom] =>
                         List.all (complete_at natT) [scale, delta, headroom]
                     | _ => false))
               else false
           | _ => false)
      val complete_value_regression =
        let
          val near_value = @{term "Comma_Near"} $ nat 1 $ nat 2 $ nat 3
          val partial_near = @{term "Comma_Near"} $
            @{term "comma_core_primary (1::nat)"} $ nat 2 $ nat 3
          val triple_value = HOLogic.mk_prod (nat 1, HOLogic.mk_prod (nat 2, nat 3))
          val triple_type = fastype_of triple_value
          val option_type = Type (@{type_name option}, [triple_type])
          val some_triple = Const (@{const_name Some}, triple_type --> option_type) $
            triple_value
          val negative_int = HOLogic.mk_number intT (~3)
        in
          complete_value (nat 7) andalso complete_value negative_int andalso
          complete_value near_value andalso complete_value (HOLogic.mk_prod (nat 1, nat 2)) andalso
          complete_value some_triple andalso
          not (complete_value (@{term "1 + (2::nat)"})) andalso
          not (complete_value (@{term "comma_core_primary (1::nat)"})) andalso
          not (complete_value (@{term
            "comma_decisive_entry_clock_key_with_core
              (comma_cyclotomic_clock_of 0) 1 0 23"})) andalso
          not (complete_value partial_near)
        end
      val _ = if complete_value_regression then ()
        else error "Endpoint complete-value guard regression failed"
      fun require_closed_equation request theorem =
        let val result = Thm.term_of (Thm.rhs_of theorem) in
          if Thm.term_of (Thm.lhs_of theorem) aconv request andalso closed result andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) then
            if complete_value result then theorem
            else error ("Endpoint equation has an incomplete closed result: " ^
              Syntax.string_of_term ctxt request ^ " = " ^ Syntax.string_of_term ctxt result)
          else error "Endpoint equation has the wrong owner or open authority"
        end
      (* These are closed local arithmetic requests, not whole B1/round
         evaluations. Closed arithmetic equations supply kernel equalities;
         the exact source term remains the cache authority. *)
      val local_arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      (* Separate the selected fast-period table read from the small core
         projection.  The recursive gcd equations are used only for a selected
         P, then memoized by P rather than re-run for each source spelling. *)
      val source_period_context = put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps
        @{thms comma_decisive_sector_period_def comma_finite_position.case}
      val fast_period_context = local_arithmetic |> Simplifier.add_simps
        @{thms comma_finite_period_fast_def nth_Cons'}
      val core_period_context = local_arithmetic |> Simplifier.add_simps
        @{thms comma_core_primary_def comma_core_modulus_def
          comma_core_period_def gcd_nat.simps}
      val admitted_context = local_arithmetic |> Simplifier.add_simps
        @{thms comma_round_admitted.simps}
      fun instantiate_index theorem variable n =
        Simplifier.simplify local_arithmetic
          (Drule.infer_instantiate ctxt
            [((variable, 0), Thm.cterm_of ctxt (nat n))] theorem)
      val port_steps = map
        (instantiate_index @{thm comma_port_weighted_trace.simps(2)} "n") (0 upto 8)
      val displacement_steps = map
        (instantiate_index @{thm comma_period_displacement_succ} "j") (0 upto 8)
      val endpoint_context = kernel_context |> Simplifier.add_simps
        (@{thms comma_decisive_sector_period_def comma_decisive_sector_target.simps
          comma_decisive_entry_clock_key_def
          comma_decisive_entry_clock_key_with_core_def
          comma_decisive_entry_clock_key_from_core_residue_def
          comma_cyclotomic_clock_core_value_def comma_core_primary_def
          comma_core_modulus_def comma_core_seed_def comma_core_period_def
          comma_recursive_core_residue_def comma_core_halfcycle_def comma_core_seven_def
          comma_cyclotomic_clock_projection insert_iff empty_iff
          comma_entry_diagonal_def comma_entry_diagonal_endpoint_def
          comma_diagonal_headroom_def comma_offset_orbit_def
          comma_digit_orbit_sum_def power2_eq_square
          comma_entry_port_refined_locator_def comma_entry_port_seed_def
          comma_entry_port_row_def comma_entry_port_orbit_def
          comma_entry_port_position_def comma_entry_port_potential_def
          comma_port_action_power_trace comma_port_weighted_locator_def
          comma_port_weighted_trace.simps(1) comma_port_next_def
          comma_port_previous_def comma_port_dwell_def comma_port_low_def
          comma_port_cycle_length_def comma_compiled_cycle_length_facts
          comma_compiled_period_facts comma_entry_port_displacement_zero
          comma_phase_digit_def gcd_nat.simps option.map option.case option.sel
          List.find.simps list.size nth_Cons' upt_rec Let_def prod.case
          fst_conv snd_conv case_prod_beta}
         @ port_steps @ displacement_steps)
      val boundaries =
        [(@{term "comma_offset_orbit x"}, @{thms comma_offset_orbit_def}),
         (@{term "comma_decisive_sector_period source"},
            @{thms comma_decisive_sector_period_def}),
         (@{term "comma_decisive_sector_target r source"},
            @{thms comma_decisive_sector_target.simps}),
         (@{term "comma_decisive_entry_clock_key clock f x"},
            @{thms comma_decisive_entry_clock_key_def}),
         (@{term "comma_decisive_entry_clock_key_with_core clock f x c"},
            @{thms comma_decisive_entry_clock_key_with_core_def}),
         (@{term "comma_core_primary P"}, @{thms comma_core_primary_def}),
         (@{term "comma_core_modulus P"}, @{thms comma_core_modulus_def}),
         (@{term "comma_core_seed P"}, @{thms comma_core_seed_def}),
         (@{term "comma_core_period c"}, @{thms comma_core_period_def}),
         (@{term "comma_recursive_core_residue c t"},
            @{thms comma_recursive_core_residue_def}),
         (@{term "comma_entry_port_refined_locator f d eta"},
            @{thms comma_entry_port_refined_locator_def}),
         (@{term "comma_entry_port_potential f d"},
            @{thms comma_entry_port_potential_def}),
         (@{term "comma_port_weighted_trace f d n"},
            @{thms comma_port_weighted_trace.simps(1)} @ port_steps)]
      val endpoint_heads = map (Term.head_of o #1) boundaries
      val endpoint_evaluator = Unsynchronized.ref endpoint_context
      val active = Unsynchronized.ref (Termtab.empty: unit Termtab.table)
      val endpoint_memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val period_memo = Unsynchronized.ref
        (Termtab.empty: (int * thm * thm * Proof.context) Termtab.table)
      val fast_period_memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val core_period_memo = Unsynchronized.ref
        (Termtab.empty: (int * thm) Termtab.table)
      val fast_period_hits = Unsynchronized.ref 0
      val fast_period_misses = Unsynchronized.ref 0
      val core_period_hits = Unsynchronized.ref 0
      val core_period_misses = Unsynchronized.ref 0
      val endpoint_hits = Unsynchronized.ref 0
      val endpoint_misses = Unsynchronized.ref 0
      val target_calls = Unsynchronized.ref 0
      val target_hits = Unsynchronized.ref 0
      val target_misses = Unsynchronized.ref 0
      val target_inclusive_ms = Unsynchronized.ref (0: LargeInt.int)
      val clock_key_calls = Unsynchronized.ref 0
      val clock_key_hits = Unsynchronized.ref 0
      val clock_key_misses = Unsynchronized.ref 0
      val clock_key_inclusive_ms = Unsynchronized.ref (0: LargeInt.int)
      val core_scalar_calls = Unsynchronized.ref 0
      val core_scalar_hits = Unsynchronized.ref 0
      val core_scalar_misses = Unsynchronized.ref 0
      val core_scalar_inclusive_ms = Unsynchronized.ref (0: LargeInt.int)
      val locator_hits = Unsynchronized.ref 0
      val locator_misses = Unsynchronized.ref 0
      val direct_entry_hits = Unsynchronized.ref 0
      val target_period_rebases = Unsynchronized.ref 0
      fun is_locator request = Term.head_of request =
        Term.head_of @{term "comma_entry_port_refined_locator f d eta"}
      fun is_target request = Term.head_of request =
        Term.head_of @{term "comma_decisive_sector_target r source"}
      fun is_clock_key request = Term.head_of request =
        Term.head_of @{term "comma_decisive_entry_clock_key clock f x"}
      fun is_core_scalar request =
        (case Term.head_of request of
          Const (name, _) => member (op =)
            [@{const_name comma_core_modulus}, @{const_name comma_core_seed},
             @{const_name comma_core_period}] name
        | _ => false)

      (* Keep admission authority exact, but avoid rebuilding a goal/tactic
         context for every source.  A closed rewrite to True is the theorem
         used by equal_elim; any other result fails closed. *)
      fun exact_admission source =
        let
          val request = HOLogic.mk_Trueprop (@{term comma_round_admitted} $ source)
          val equation = Simplifier.rewrite admitted_context (Thm.cterm_of ctxt request)
        in
          if Thm.term_of (Thm.lhs_of equation) aconv request andalso
              Thm.term_of (Thm.rhs_of equation) aconv @{prop True} andalso
              Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
              null (Thm.tpairs_of equation) then
            let val admitted = Thm.equal_elim (Thm.symmetric equation) @{thm TrueI}
            in if Thm.prop_of admitted aconv request then SOME admitted else NONE end
          else NONE
        end

      fun checked_rewrite context request =
        let val equation = Simplifier.rewrite context (Thm.cterm_of ctxt request) in
          if Thm.term_of (Thm.lhs_of equation) aconv request andalso
              Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
              null (Thm.tpairs_of equation) then SOME equation else NONE
        end

      fun require_stage stage result =
        (case result of SOME value => value
        | NONE => error ("Canonical period conversion failed at " ^ stage))

      fun prove_true context request =
        let
          val _ = HOLogic.dest_Trueprop request
          val equation = Simplifier.rewrite context (Thm.cterm_of ctxt request)
        in
          if Thm.term_of (Thm.lhs_of equation) aconv request andalso
              Thm.term_of (Thm.rhs_of equation) aconv @{prop True} andalso
              Thm.nprems_of equation = 0 andalso null (Thm.hyps_of equation) andalso
              null (Thm.tpairs_of equation) then
            SOME (Thm.equal_elim (Thm.symmetric equation) @{thm TrueI})
          else NONE
        end

      val recognized_period_inputs =
        [60,80,100,120,140,210,220,230,240,260,270,280,290,460,480,520,540]

      fun selected_fast_period f d =
        let val request = @{term comma_finite_period_fast} $ f $ d in
          (case Termtab.lookup (!fast_period_memo) request of
            SOME equation => (fast_period_hits := !fast_period_hits + 1;
              SOME equation)
          | NONE =>
              let
                val _ = fast_period_misses := !fast_period_misses + 1
              in
                (case checked_rewrite fast_period_context request of
                  SOME equation =>
                    (case try HOLogic.dest_number (Thm.term_of (Thm.rhs_of equation)) of
                      SOME (typ, value) =>
                        if typ = natT andalso member (op =) recognized_period_inputs value then
                          (if Termtab.size (!fast_period_memo) < 128 then
                             fast_period_memo := Termtab.update (request, equation)
                               (!fast_period_memo) else ();
                           SOME equation)
                        else NONE
                    | NONE => NONE)
                | NONE => NONE)
              end)
        end

      fun selected_core_period p =
        let
          val request = @{term comma_core_period} $
            (@{term comma_core_modulus} $ p)
        in
          (case Termtab.lookup (!core_period_memo) p of
            SOME answer => (core_period_hits := !core_period_hits + 1; SOME answer)
          | NONE =>
              let
                val _ = core_period_misses := !core_period_misses + 1
              in
                (case checked_rewrite core_period_context request of
                  SOME equation =>
                    (case try HOLogic.dest_number (Thm.term_of (Thm.rhs_of equation)) of
                      SOME (typ, value) =>
                        if typ = natT andalso value > 0 andalso value <= 924 then
                          (if Termtab.size (!core_period_memo) < 32 then
                             core_period_memo := Termtab.update
                               (p, (value, equation)) (!core_period_memo) else ();
                           SOME (value, equation))
                        else NONE
                    | NONE => NONE)
                | NONE => NONE)
              end)
        end

      fun selected_source_period source =
        let
          val request = @{term comma_decisive_sector_period} $ source
          val source_equation = require_stage "source constructor normalization"
            (checked_rewrite source_period_context request)
          val source_rhs = Thm.term_of (Thm.rhs_of source_equation)
          fun finish equation =
            let val result = Thm.transitive source_equation equation in
              SOME (require_closed_equation request result)
            end
        in
          (case constructor_args @{const_name Comma_Near} source of
            SOME [_, _, _] =>
              (case try HOLogic.dest_number source_rhs of
                SOME (typ, value) => if typ = natT andalso value = 1 then
                  SOME (require_closed_equation request source_equation) else NONE
              | NONE => error "Canonical period conversion left a nonnumeral Near period")
          | _ =>
              (case constructor_args @{const_name Comma_Entry} source of
                SOME [f, _, x] =>
                  (case (try HOLogic.dest_number f, try HOLogic.dest_number x) of
                    (SOME (ft, fv), SOME (xt, xv)) =>
                      if ft <> natT orelse xt <> natT orelse fv < 1 orelse fv > 9 orelse
                          xv < 0 orelse xv > 98 then
                        error "Canonical period conversion received an admitted Entry outside its numeral bounds"
                      else
                        let
                          val mod_request = Term.subst_atomic
                            [(Free ("x", natT), x)] @{term "(x::nat) mod 10"}
                          val mod_equation = require_stage "offset modulo selection"
                            (checked_rewrite local_arithmetic mod_request)
                          val d = Thm.term_of (Thm.rhs_of mod_equation)
                          val d_number = try HOLogic.dest_number d
                          val expected_source_rhs = @{term comma_core_period} $
                            (@{term comma_core_modulus} $
                              (@{term comma_finite_period_fast} $ f $ mod_request))
                        in
                          if not (source_rhs aconv expected_source_rhs) then
                            error "Canonical period source normalization changed its selected table request"
                          else
                            (case (d_number, selected_fast_period f d) of
                              (SOME (dt, dv), SOME fast_equation) =>
                                if dt <> natT orelse dv < 0 orelse dv > 9 then
                                  error "Canonical period offset selector was not a decimal numeral"
                                else
                                  (case try HOLogic.dest_number
                                      (Thm.term_of (Thm.rhs_of fast_equation)) of
                                    SOME (pt, pv) =>
                                      if pt <> natT then
                                        error "Canonical fast-period selector returned a non-natural"
                                      else
                                        let
                                          val p = HOLogic.mk_number natT pv
                                          val core_request = @{term comma_core_period} $
                                            (@{term comma_core_modulus} $ p)
                                          val selected_fast = Thm.transitive
                                            (Thm.combination
                                              (Thm.reflexive (Thm.cterm_of ctxt
                                                (@{term comma_finite_period_fast} $ f)))
                                              mod_equation)
                                            fast_equation
                                          val selected_core = Thm.combination
                                            (Thm.reflexive (Thm.cterm_of ctxt
                                              @{term comma_core_modulus})) selected_fast
                                          val selected_period = Thm.combination
                                            (Thm.reflexive (Thm.cterm_of ctxt
                                              @{term comma_core_period})) selected_core
                                        in
                                          if Thm.term_of (Thm.lhs_of selected_period)
                                              aconv source_rhs then
                                            (case selected_core_period p of
                                              SOME (_, core_equation) =>
                                                if Thm.term_of (Thm.lhs_of core_equation)
                                                    aconv core_request then
                                                  finish (Thm.transitive selected_period
                                                    core_equation)
                                                else NONE
                                            | NONE =>
                                                error "Canonical core-period lookup failed for selected P")
                                          else error "Canonical period equality did not compose at the selected P"
                                        end
                                  | NONE => error "Canonical fast-period lookup returned no numeral")
                            | _ => error "Canonical fast-period table selection failed")
                        end
                    | _ => error "Canonical admitted Entry source has nonnumeral f or offset")
              | _ => error "Canonical admitted source has an unsupported constructor"))
        end

      fun target_period source =
        (case Termtab.lookup (!period_memo) source of
          SOME answer => SOME answer
        | NONE =>
            (case exact_admission source of
            NONE => NONE
            | SOME admitted =>
                (case selected_source_period source of
                    SOME equation =>
                      (case try HOLogic.dest_number (Thm.term_of (Thm.rhs_of equation)) of
                        SOME (typ, value) =>
                          if typ = natT andalso value > 0 andalso value <= 924 then
                            let
                              val congruence_context = local_arithmetic |> Simplifier.add_simps [equation]
                              val answer = (value, equation, admitted, congruence_context)
                              val _ = if Termtab.size (!period_memo) < 8192 then
                                  period_memo := Termtab.update (source, answer) (!period_memo)
                                else ()
                            in SOME answer end
                          else NONE
                      | NONE => NONE)
                  | NONE => NONE)))

      fun period_conversion ct =
        let val request = Thm.term_of ct in
          (case request of
            Const (name, _) $ source =>
              if name = @{const_name comma_decisive_sector_period} then
                (case target_period source of
                  SOME (_, equation, _, _) =>
                    SOME (require_closed_equation request equation)
                | NONE => NONE)
              else NONE
          | _ => NONE)
        end

      val period_cache_regression =
        let
          val source0 = @{term "Comma_Entry (1::nat) 0 0"}
          val source_offset10 = @{term "Comma_Entry (1::nat) 0 10"}
          val source_delta = @{term "Comma_Entry (1::nat) 7 0"}
          val before_fast = !fast_period_hits
          val before_core = !core_period_hits
          fun answer source =
            (case exact_admission source of
              NONE => error "Period-cache regression source admission failed"
            | SOME expected_admitted =>
              (case target_period source of
              SOME (value, equation, admitted, _) =>
                let
                  val request = @{term comma_decisive_sector_period} $ source
                  val admission = HOLogic.mk_Trueprop (@{term comma_round_admitted} $ source)
                  val _ = if Thm.term_of (Thm.lhs_of equation) aconv request andalso
                      Thm.prop_of admitted aconv admission andalso
                      Thm.prop_of expected_admitted aconv admission then ()
                    else error "Period-cache regression changed source authority"
                in SOME (value, equation) end
              | NONE => error "Period-cache regression exact target_period cache path failed"
              ))
          val first = answer source0
          val second = answer source_offset10
          val third = answer source_delta
        in
          (case (first, second, third) of
            (SOME (left, _), SOME (right, _), SOME (delta_value, _)) =>
              left = right andalso left = delta_value andalso
                !fast_period_hits >= before_fast + 2 andalso
                !core_period_hits >= before_core + 2
          | _ => false)
        end
      val _ = if period_cache_regression then ()
        else error "Canonical source-period cache regression failed"

      fun reduced_target_equation request r source =
        (case try HOLogic.dest_number r of
          NONE => NONE
        | SOME (typ, value) =>
            if typ <> natT orelse value < 0 then NONE
            else
              (case target_period source of
                NONE => NONE
              | SOME (period, period_equation, admitted, congruence_context) =>
                  let
                    val reduced = HOLogic.mk_number natT
                      (value mod period)
                  in
                    if r aconv reduced then NONE
                    else
                      let
                        val reduced_request =
                          @{term comma_decisive_sector_target} $ reduced $ source
                        val instance = Drule.infer_instantiate ctxt
                          [(("r", 0), Thm.cterm_of ctxt r),
                           (("s", 0), Thm.cterm_of ctxt reduced),
                           (("source", 0), Thm.cterm_of ctxt source)]
                          @{thm comma_decisive_sector_target_period}
                        val _ = if Thm.nprems_of instance = 2 then ()
                          else error "Sector-target period theorem changed shape"
                        val admitted_premise = Thm.term_of (Thm.cprem_of instance 1)
                        val same_premise = Thm.term_of (Thm.cprem_of instance 2)
                        val _ = if Thm.prop_of admitted aconv admitted_premise then ()
                          else error "Cached source admission does not match period theorem"
                        val same_result = prove_true congruence_context same_premise
                      in
                        (case same_result of
                          NONE => NONE
                        | SOME congruent =>
                            let
                              val target_period = Thm.implies_elim
                                (Thm.implies_elim instance admitted) congruent
                              val target_rebase = mk_meta_eq target_period
                              val _ = if Thm.term_of (Thm.lhs_of target_rebase) aconv request andalso
                                  Thm.term_of (Thm.rhs_of target_rebase) aconv reduced_request
                                then () else error
                                  "Sector-target period theorem changed its endpoints"
                              val _ = target_period_rebases := !target_period_rebases + 1
                            in SOME (reduced_request, target_rebase) end)
                      end
                  end)
        )
      fun direct_entry_equation ct =
        let
          val request = Thm.term_of ct
          fun admitted_numbers f x =
            (case (try HOLogic.dest_number f, try HOLogic.dest_number x) of
              (SOME (ft, fv), SOME (xt, xv)) =>
                ft = natT andalso xt = natT andalso
                  1 <= fv andalso fv <= 9 andalso 0 <= xv andalso xv <= 98
            | _ => false)
        in
          (case request of
            Const (name, _) $ r $
              (Const (constructor, constructorT) $ f $ delta $ x) =>
                if name = @{const_name comma_decisive_sector_target} andalso
                    constructor = @{const_name Comma_Entry} andalso
                    admitted_numbers f x
                then
                  let
                    val instance = Drule.infer_instantiate ctxt
                      [(("r",0), Thm.cterm_of ctxt r),
                       (("f",0), Thm.cterm_of ctxt f),
                       (("delta",0), Thm.cterm_of ctxt delta),
                       (("x",0), Thm.cterm_of ctxt x)]
                      @{thm comma_decisive_entry_target_diagonal}
                    val _ = if Thm.nprems_of instance = 1 then ()
                      else error "Direct Entry projection has unexpected premises"
                    val premise = Thm.cprem_of instance 1
                    val source = Const (constructor, constructorT) $ f $ delta $ x
                    val admitted = the (exact_admission source)
                    val _ = if Thm.prop_of admitted aconv Thm.term_of premise then ()
                      else error "Direct Entry admission changed its exact source"
                  in SOME (Thm.implies_elim instance admitted) end
                else NONE
          | _ => NONE)
        end
      fun endpoint ct =
        let val request = Thm.term_of ct in
          if not (closed request) orelse
            not (member (op =) endpoint_heads (Term.head_of request)) orelse
            Termtab.defined (!active) request then NONE
          else
            let
              val target_request = is_target request
              val _ = if target_request then target_calls := !target_calls + 1 else ()
              val clock_key_request = is_clock_key request
              val _ = if clock_key_request then
                clock_key_calls := !clock_key_calls + 1 else ()
              val core_scalar_request = is_core_scalar request
              val _ = if core_scalar_request then
                core_scalar_calls := !core_scalar_calls + 1 else ()
            in SOME (case Termtab.lookup (!endpoint_memo) request of
            SOME theorem => (endpoint_hits := !endpoint_hits + 1;
              if target_request then target_hits := !target_hits + 1 else ();
              if clock_key_request then clock_key_hits := !clock_key_hits + 1 else ();
              if core_scalar_request then core_scalar_hits := !core_scalar_hits + 1 else ();
              if is_locator request then locator_hits := !locator_hits + 1 else ();
              theorem)
          | NONE =>
              let
                val _ = endpoint_misses := !endpoint_misses + 1
                val _ = if target_request then target_misses := !target_misses + 1 else ()
                val _ = if clock_key_request then
                  clock_key_misses := !clock_key_misses + 1 else ()
                val _ = if core_scalar_request then
                  core_scalar_misses := !core_scalar_misses + 1 else ()
                val _ = if is_locator request then
                  locator_misses := !locator_misses + 1 else ()
                val started = Time.now ()
                val rules = #2 (the (find_first
                  (fn (pattern, _) => Term.head_of pattern = Term.head_of request) boundaries))
                val _ = active := Termtab.update (request, ()) (!active)
                val attempt = Exn.capture (fn () =>
                  let
                    fun finish root =
                      let
                        val children = Simplifier.full_rewrite
                          (!endpoint_evaluator) (Thm.rhs_of root)
                      in require_closed_equation request
                        (Thm.transitive root children) end
                    fun direct_or_rewrite () =
                      (case direct_entry_equation ct of
                        SOME direct =>
                          let
                            val theorem = finish (direct RS @{thm eq_reflection})
                            val _ = direct_entry_hits := !direct_entry_hits + 1
                          in theorem end
                      | NONE =>
                          let
                            val root = Conv.rewrs_conv
                              (map (fn rule => rule RS @{thm eq_reflection}) rules) ct
                          in finish root end)
                  in
                    (case request of
                      Const (name, _) $ source =>
                        if name = @{const_name comma_decisive_sector_period} then
                          (case target_period source of
                            SOME (_, equation, _, _) =>
                              require_closed_equation request equation
                          | NONE =>
                              if is_some (exact_admission source) then
                                error "Admitted source-period bridge failed"
                              else direct_or_rewrite ())
                        else direct_or_rewrite ()
                    | Const (name, _) $ r $ source =>
                        if name = @{const_name comma_decisive_sector_target} then
                          (case reduced_target_equation request r source of
                            SOME (reduced_request, target_rebase) =>
                              (case endpoint (Thm.cterm_of ctxt reduced_request) of
                                SOME reduced =>
                                  let
                                    val theorem = Thm.transitive target_rebase reduced
                                  in require_closed_equation request theorem end
                              | NONE => error "Reduced sector target was not evaluable")
                          | NONE => direct_or_rewrite ())
                        else direct_or_rewrite ()
                    | _ => direct_or_rewrite ())
                  end) ()
                val _ = active := Termtab.delete request (!active)
                val theorem = Exn.release attempt
                val duration = Time.toMilliseconds (Time.- (Time.now (), started))
                val _ = if target_request then
                    target_inclusive_ms := !target_inclusive_ms + duration else ()
                val _ = if clock_key_request then
                    clock_key_inclusive_ms := !clock_key_inclusive_ms + duration else ()
                val _ = if core_scalar_request then
                    core_scalar_inclusive_ms := !core_scalar_inclusive_ms + duration else ()
                val _ = if profiling andalso duration > 100 then Comma_Fast_Kernel.report
                  ("compact_endpoint_ms=" ^ LargeInt.toString duration ^
                    " request=" ^ XML.content_of
                      (YXML.parse_body (Syntax.string_of_term ctxt request))) else ()
                val value = Thm.term_of (Thm.rhs_of theorem)
                val _ = if closed value andalso not (request aconv value) then ()
                  else error "Compact endpoint arithmetic did not reduce a closed request"
                val _ = if Termtab.size (!endpoint_memo) < 8192 then
                    endpoint_memo := Termtab.update (request, theorem) (!endpoint_memo)
                  else ()
              in theorem end)
            end
        end

      val endpoint_proc = Simplifier.make_simproc ctxt
        {name = "comma_compact_endpoint_arithmetic", kind = Simplifier.Simproc,
         lhss = map (schematic o #1) boundaries,
         proc = fn _ => fn _ => endpoint, identifier = []}
      val _ = endpoint_evaluator :=
        (endpoint_context |> Simplifier.del_simps (maps #2 boundaries)
          |> Simplifier.add_proc endpoint_proc)

      fun stats () = "endpoint_hits=" ^ Int.toString (!endpoint_hits) ^
          " endpoint_misses=" ^ Int.toString (!endpoint_misses) ^
          " target_calls=" ^ Int.toString (!target_calls) ^
          " target_hits=" ^ Int.toString (!target_hits) ^
          " target_misses=" ^ Int.toString (!target_misses) ^
          " target_inclusive_ms=" ^ LargeInt.toString (!target_inclusive_ms) ^
          " clock_key_calls=" ^ Int.toString (!clock_key_calls) ^
          " clock_key_hits=" ^ Int.toString (!clock_key_hits) ^
          " clock_key_misses=" ^ Int.toString (!clock_key_misses) ^
          " clock_key_inclusive_ms=" ^ LargeInt.toString (!clock_key_inclusive_ms) ^
          " core_scalar_calls=" ^ Int.toString (!core_scalar_calls) ^
          " core_scalar_hits=" ^ Int.toString (!core_scalar_hits) ^
          " core_scalar_misses=" ^ Int.toString (!core_scalar_misses) ^
          " core_scalar_inclusive_ms=" ^ LargeInt.toString (!core_scalar_inclusive_ms) ^
          " locator_hits=" ^ Int.toString (!locator_hits) ^
          " locator_misses=" ^ Int.toString (!locator_misses) ^
          " direct_entry_hits=" ^ Int.toString (!direct_entry_hits) ^
          " target_period_rebases=" ^ Int.toString (!target_period_rebases) ^
          " fast_period_hits=" ^ Int.toString (!fast_period_hits) ^
          " fast_period_misses=" ^ Int.toString (!fast_period_misses) ^
          " core_period_hits=" ^ Int.toString (!core_period_hits) ^
          " core_period_misses=" ^ Int.toString (!core_period_misses)
    in {context = !endpoint_evaluator, simproc = endpoint_proc,
        period = period_conversion,
        rewrite = endpoint, stats = stats,
        endpoint_hits = fn () => !endpoint_hits,
        target_period_rebases = fn () => !target_period_rebases,
        direct_entry_hits = fn () => !direct_entry_hits,
        direct_entry_probe = direct_entry_equation} end
end
