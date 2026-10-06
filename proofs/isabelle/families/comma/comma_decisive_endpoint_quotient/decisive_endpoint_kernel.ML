(* Shared proof-producing arithmetic for a single decisive endpoint.  The
   caller supplies its existing kernel context; this owner never constructs a
   second kernel or evaluates a complete B1 trajectory. *)
structure Comma_Decisive_Endpoint_Kernel =
struct
  fun make ctxt kernel_context =
    let
      val natT = @{typ nat}
      fun nat n = HOLogic.mk_number natT n
      val profiling = getenv "COMMA_PROFILE_LOG" <> ""
      fun closed term =
        null (Term.add_frees term []) andalso null (Term.add_vars term []) andalso
          not (Term.is_open term)
      fun schematic pattern = Term.map_aterms
        (fn Free (name, typ) => Var ((name, 0), typ) | atom => atom) pattern
      fun capture_optional operation argument =
        (case Exn.capture operation argument of
          Exn.Res result => SOME result
        | Exn.Exn failure =>
            if Exn.is_interrupt failure then Exn.reraise failure else NONE)
      fun require_closed_equation request theorem =
        let val result = Thm.term_of (Thm.rhs_of theorem) in
          if Thm.term_of (Thm.lhs_of theorem) aconv request andalso closed result andalso
            Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
            null (Thm.tpairs_of theorem) then theorem
          else error "Endpoint equation has the wrong owner or open authority"
        end
      (* These are closed local arithmetic requests, not whole B1/round
         evaluations. Closed arithmetic equations supply kernel equalities;
         the exact source term remains the cache authority. *)
      val local_arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
      fun instantiate_index theorem variable n =
        Simplifier.simplify local_arithmetic
          (Drule.infer_instantiate ctxt
            [((variable, 0), Thm.cterm_of ctxt (nat n))] theorem)
      val port_steps = map
        (instantiate_index @{thm comma_port_weighted_trace.simps(2)} "n") (0 upto 8)
      val displacement_steps = map
        (instantiate_index @{thm comma_period_displacement_succ} "j") (0 upto 8)
      val endpoint_context = kernel_context addsimps
        (@{thms comma_decisive_sector_period_def comma_decisive_sector_target.simps
          comma_decisive_entry_clock_key_def comma_core_primary_def
          comma_core_modulus_def comma_core_seed_def comma_core_period_def
          comma_recursive_core_residue_def comma_core_halfcycle_def comma_core_seven_def
          comma_cyclotomic_clock_projection insert_iff empty_iff
          comma_entry_diagonal_def comma_entry_diagonal_endpoint_def
          comma_diagonal_headroom_def
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
        [(@{term "comma_decisive_sector_period source"},
            @{thms comma_decisive_sector_period_def}),
         (@{term "comma_decisive_sector_target r source"},
            @{thms comma_decisive_sector_target.simps}),
         (@{term "comma_core_primary P"}, @{thms comma_core_primary_def}),
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
        (Termtab.empty: (int * thm * thm) Termtab.table)
      val endpoint_hits = Unsynchronized.ref 0
      val endpoint_misses = Unsynchronized.ref 0
      val locator_hits = Unsynchronized.ref 0
      val locator_misses = Unsynchronized.ref 0
      val direct_entry_hits = Unsynchronized.ref 0
      val target_period_rebases = Unsynchronized.ref 0
      fun is_locator request = Term.head_of request =
        Term.head_of @{term "comma_entry_port_refined_locator f d eta"}

      (* Normalize only the first sector target, for which a checked period
         theorem exists.  The endpoint round itself is intentionally left at
         its original phase: recursive successors can have a different
         sector period. Cache the admission and checked period equation by
         exact source. *)
      fun target_period source =
        (case Termtab.lookup (!period_memo) source of
          SOME answer => SOME answer
        | NONE =>
            let
              val admitted_request = @{term comma_round_admitted} $ source
              val admitted_result = capture_optional (fn () => Goal.prove ctxt [] []
                (HOLogic.mk_Trueprop admitted_request)
                (fn {context, ...} => simp_tac
                  (Comma_Entry_Arithmetic.natural_context context addsimps
                    @{thms comma_round_admitted.simps}) 1)) ()
            in
              (case admitted_result of
                NONE => NONE
              | SOME admitted =>
                let
                  val request = @{term comma_decisive_sector_period} $ source
                  val equation_result = capture_optional (fn () =>
                    Simplifier.rewrite endpoint_context (Thm.cterm_of ctxt request)) ()
                in
                  (case equation_result of
                    NONE => NONE
                  | SOME equation =>
                    let
                      val valid_equation =
                        Thm.term_of (Thm.lhs_of equation) aconv request andalso
                        null (Thm.hyps_of equation) andalso
                        null (Thm.tpairs_of equation) andalso
                        Thm.nprems_of equation = 0 andalso
                        closed (Thm.term_of (Thm.rhs_of equation))
                    in
                      if not valid_equation then
                        error "Sector-period conversion returned open authority"
                      else
                        (case try HOLogic.dest_number (Thm.term_of (Thm.rhs_of equation)) of
                          SOME (typ, value) =>
                            if typ = natT andalso value > 0 andalso
                                value <= 924 then
                              let
                                val answer = (value, equation, admitted)
                                val _ = if Termtab.size (!period_memo) < 8192 then
                                    period_memo := Termtab.update (source, answer)
                                      (!period_memo)
                                  else ()
                              in SOME answer end
                            else NONE
                        | NONE => NONE)
                    end)
                end)
            end)

      fun reduced_target_equation request r source =
        (case try HOLogic.dest_number r of
          NONE => NONE
        | SOME (typ, value) =>
            if typ <> natT orelse value < 0 then NONE
            else
              (case target_period source of
                NONE => NONE
              | SOME (period, period_equation, admitted) =>
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
                        val same_result = capture_optional (fn () => Goal.prove ctxt [] []
                          same_premise
                          (fn {context, ...} => simp_tac
                            (Comma_Entry_Arithmetic.natural_context context addsimps
                              [period_equation]) 1)) ()
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
              (Const (constructor, _) $ f $ delta $ x) =>
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
                    val admitted = Goal.prove ctxt [] [] (Thm.term_of premise)
                      (fn _ => simp_tac (local_arithmetic addsimps
                        @{thms comma_round_admitted.simps}) 1)
                  in SOME (Thm.implies_elim instance admitted) end
                else NONE
          | _ => NONE)
        end
      fun endpoint ct =
        let val request = Thm.term_of ct in
          if not (closed request) orelse
            not (member (op =) endpoint_heads (Term.head_of request)) orelse
            Termtab.defined (!active) request then NONE
          else SOME (case Termtab.lookup (!endpoint_memo) request of
            SOME theorem => (endpoint_hits := !endpoint_hits + 1;
              if is_locator request then locator_hits := !locator_hits + 1 else ();
              theorem)
          | NONE =>
              let
                val _ = endpoint_misses := !endpoint_misses + 1
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
                      Const (name, _) $ r $ source =>
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

      val endpoint_proc = Simplifier.make_simproc ctxt
        {name = "comma_compact_endpoint_arithmetic", kind = Simplifier.Simproc,
         lhss = map (schematic o #1) boundaries,
         proc = fn _ => fn _ => endpoint, identifier = []}
      val _ = endpoint_evaluator :=
        (endpoint_context delsimps (maps #2 boundaries)
          |> Simplifier.add_proc endpoint_proc)

      fun stats () = "endpoint_hits=" ^ Int.toString (!endpoint_hits) ^
          " endpoint_misses=" ^ Int.toString (!endpoint_misses) ^
          " locator_hits=" ^ Int.toString (!locator_hits) ^
          " locator_misses=" ^ Int.toString (!locator_misses) ^
          " direct_entry_hits=" ^ Int.toString (!direct_entry_hits) ^
          " target_period_rebases=" ^ Int.toString (!target_period_rebases)
    in {context = !endpoint_evaluator, simproc = endpoint_proc,
        rewrite = endpoint, stats = stats,
        endpoint_hits = fn () => !endpoint_hits,
        target_period_rebases = fn () => !target_period_rebases,
        direct_entry_hits = fn () => !direct_entry_hits,
        direct_entry_probe = direct_entry_equation} end
end
