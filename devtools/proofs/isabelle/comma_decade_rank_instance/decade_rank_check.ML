structure Comma_Decade_Rank_Check =
struct
  val numeral_context = Comma_Entry_Arithmetic.numeral_context

  fun canonical_term ctxt term = Thm.term_of (Thm.rhs_of
    (Simplifier.rewrite (numeral_context ctxt) (Thm.cterm_of ctxt term)))

  fun canonical_theorem ctxt theorem =
    Simplifier.simplify (numeral_context ctxt) theorem

  fun timed elapsed failed f x =
    let
      val start = Time.now ()
      val result = Exn.capture f x
      val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), start))
      val _ = if Exn.is_exn result then failed := !failed + 1 else ()
    in Exn.release result end

  (* Select before simplifying: normalizing the complete candidate list for
     every lookup would turn a constant-depth table into quadratic work. *)
  fun make_lookup ctxt codes_def rank_def =
    let
      val scalar = numeral_context ctxt
      val arithmetic = Simplifier.rewrite (Comma_Entry_Arithmetic.natural_context ctxt)
      val root = if can Logic.dest_equals (Thm.prop_of codes_def)
        then codes_def else codes_def RS @{thm eq_reflection}
      val root_term = Thm.term_of (Thm.lhs_of root)
      val memo = Unsynchronized.ref (Termtab.empty: thm Termtab.table)
      val lookups = Unsynchronized.ref 0
      val hits = Unsynchronized.ref 0
      val internal_publications = Unsynchronized.ref 0
      val leaf_evaluations = Unsynchronized.ref 0
      val retained = Unsynchronized.ref 0
      val peak_retained = Unsynchronized.ref 0
      val evicted = Unsynchronized.ref 0
      val elapsed = Unsynchronized.ref Time.zeroTime
      val failed = Unsynchronized.ref 0
      fun nth ct =
        let
          val normalized = Conv.arg_conv arithmetic ct
          val equation = Conv.rewr_conv (@{thm nth_Cons'} RS @{thm eq_reflection}) (Thm.rhs_of normalized)
          val condition = Conv.fun_conv (Conv.fun_conv (Conv.arg_conv arithmetic))
            (Thm.rhs_of equation)
          val reduced = (Conv.rewr_conv (@{thm if_True} RS @{thm eq_reflection}) else_conv
            Conv.rewr_conv (@{thm if_False} RS @{thm eq_reflection})) (Thm.rhs_of condition)
          val first = Thm.transitive normalized
            (Thm.transitive equation (Thm.transitive condition reduced))
          val (head, _) = strip_comb (Thm.term_of (Thm.rhs_of first))
        in
          if (case head of Const (name, _) => name = @{const_name nth} | _ => false) then
            Thm.transitive first (nth (Thm.rhs_of first)) else first
        end
      fun lookup ct =
        let
          val key = Thm.term_of ct
          val _ = lookups := !lookups + 1
        in
          (case Termtab.lookup (!memo) key of
            SOME result => (hits := !hits + 1; result)
          | NONE =>
              let
                val result = if key aconv root_term then root else
                  let
                    val transported = Conv.fun_conv (Conv.arg_conv lookup) ct
                  in Thm.transitive transported (nth (Thm.rhs_of transported)) end
                val _ = if fastype_of key = @{typ nat} then
                    leaf_evaluations := !leaf_evaluations + 1
                  else
                    let
                      val _ = if !retained < 8192 then () else
                        (evicted := !evicted + !retained;
                         memo := Termtab.empty; retained := 0)
                      val _ = memo := Termtab.update (key, result) (!memo)
                      val _ = retained := !retained + 1
                      val _ = peak_retained := Int.max (!peak_retained, !retained)
                    in internal_publications := !internal_publications + 1 end
              in result end)
        end
      fun rank_unmeasured raw_state =
        let
          val state = canonical_term ctxt raw_state
          val rank_head = case HOLogic.dest_eq
              (HOLogic.dest_Trueprop (Thm.prop_of rank_def)) of
            (Const (name, _) $ _, _) => Const (name, fastype_of state --> @{typ nat})
          | _ => error "Expected unary candidate rank definition"
          val opened = Simplifier.rewrite
            (scalar addsimps [rank_def] addsimps @{thms comma_decade_state.case})
            (Thm.cterm_of ctxt (rank_head $ state))
          val indices = arithmetic (Thm.rhs_of opened)
          val selected = lookup (Thm.rhs_of indices)
        in Thm.transitive opened (Thm.transitive indices selected)
          RS @{thm meta_eq_to_obj_eq} end
      val rank = timed elapsed failed rank_unmeasured
      fun stats () = {lookups = !lookups, hits = !hits,
        internal_publications = !internal_publications,
        leaf_evaluations = !leaf_evaluations, retained_internal = !retained,
        peak_retained_internal = !peak_retained, evicted_internal = !evicted,
        retained_leaf_equations = 0, elapsed_ms = Time.toMilliseconds (!elapsed), failed_work = !failed}
    in (rank, stats) end

  fun check ctxt {rank, rank_lookup, lookup_work, phases, generation} =
    let
      val _ = if phases >= 0 andalso phases <= 924 then ()
        else error "Invalid decade rank phase count"
      val (observe, stats) = Comma_Round_Witness.make_decade_observation_owned ctxt
        {generation = generation,
          current_generation = fn () => getenv "NUMBER_COMPILER_PROOF_GENERATION"}
      val comparison_ms = Unsynchronized.ref Time.zeroTime
      val comparison_failures = Unsynchronized.ref 0
      val aggregation_ms = Unsynchronized.ref Time.zeroTime
      val aggregation_failures = Unsynchronized.ref 0
      val checked_rows = Unsynchronized.ref 0
      val started = Time.now ()
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun state r x = @{term Comma_Decade} $ nat r $ nat x
      fun predicate s = @{term comma_decade_observed_rank_step} $ rank $ s
      val normalize = canonical_theorem ctxt
      val peak_roots_per_batch = Unsynchronized.ref 0
      fun aggregate p count get =
        let
          fun join ((lo, mid, left), (mid', hi, right)) =
            if mid <> mid' then error "Nonadjacent decade rank intervals" else
              (lo, hi, timed aggregation_ms aggregation_failures
                (fn () => @{thm comma_rank_interval_append} OF [left, right]) ())
          fun push item [] = [item]
            | push (item as (lo, hi, _)) (prior as ((lo', hi', _) :: rest)) =
                if hi - lo = hi' - lo' then push (join (hd prior, item)) rest
                else item :: prior
          fun add i stack =
            let
              val checked = get i
              val singleton = timed aggregation_ms aggregation_failures
                (fn () => normalize (Drule.infer_instantiate ctxt
                  [(("P", 0), Thm.cterm_of ctxt p),
                   (("a", 0), Thm.cterm_of ctxt (nat i))]
                  @{thm comma_rank_interval_singleton} OF [checked])) ()
              val result = push (i, i + 1, singleton) stack
              val _ = peak_roots_per_batch := Int.max (!peak_roots_per_batch, length result)
            in result end
          val stack = fold add (0 upto (count - 1)) []
          val interval = case stack of
            [] => Drule.infer_instantiate ctxt
              [(("P", 0), Thm.cterm_of ctxt p),
               (("a", 0), Thm.cterm_of ctxt (nat 0))] @{thm comma_rank_interval_empty}
          | latest :: earlier => #3 (fold (fn older => fn acc => join (older, acc)) earlier latest)
        in timed aggregation_ms aggregation_failures
          (fn () => @{thm comma_rank_interval_zero_prefix} OF [interval]) () end
      val arithmetic = Comma_Entry_Arithmetic.natural_context ctxt
        addsimps @{thms comma_decade_admitted.simps}
      fun prove_boolean proposition =
        let
          val conversion = Simplifier.rewrite arithmetic
            (Thm.cterm_of ctxt (HOLogic.mk_Trueprop proposition))
          val _ = if Thm.term_of (Thm.rhs_of conversion) aconv @{prop True}
            then () else error "Decade rank arithmetic premise did not reduce to True"
        in Thm.equal_elim (Thm.symmetric conversion) @{thm TrueI} end
      fun rank_rule theorem = Drule.infer_instantiate ctxt
        [(("rank", 0), Thm.cterm_of ctxt rank)] theorem
      fun equation_value theorem = snd (HOLogic.dest_eq
        (HOLogic.dest_Trueprop (Thm.prop_of theorem)))
      fun row r x =
        let
          val observation = canonical_theorem ctxt (observe r x)
          val source = canonical_term ctxt (state r x)
          val result = equation_value observation
          val (head, arguments) = strip_comb result
          val proof = case (head, arguments) of
            (Const (name, _), [raw_target]) =>
              if name = @{const_name Comma_Decade_Continue} then
                let
                  val target = canonical_term ctxt raw_target
                  val source_rank = rank_lookup source
                  val target_rank = rank_lookup target
                in timed comparison_ms comparison_failures (fn () =>
                  rank_rule @{thm comma_observed_rank_continue_valuesI} OF
                    [observation, prove_boolean (@{term comma_decade_admitted} $ target),
                     target_rank, source_rank,
                     prove_boolean (@{term "less :: nat => nat => bool"} $
                       equation_value target_rank $ equation_value source_rank)]) () end
              else if name = @{const_name Comma_Decade_Landmine} then
                timed comparison_ms comparison_failures (fn () =>
                  rank_rule @{thm comma_observed_rank_landmineI} OF [observation]) ()
              else error "Unexpected decade rank unary outcome"
          | (Const (name, _), [_, _]) =>
              if name = @{const_name Comma_Decade_Fork} then
                timed comparison_ms comparison_failures (fn () =>
                  rank_rule @{thm comma_observed_rank_forkI} OF [observation]) ()
              else error "Unexpected decade rank binary outcome"
          | _ => error "Invalid decade rank outcome"
          val _ = if Thm.prop_of proof aconv HOLogic.mk_Trueprop (predicate source)
              andalso Thm.nprems_of proof = 0 andalso null (Thm.hyps_of proof)
            then () else error "Open or differently bound decade rank row"
          val _ = checked_rows := !checked_rows + 1
        in proof end
      fun phase r =
        let
          val p = Abs ("x", @{typ nat}, predicate
            (@{term Comma_Decade} $ nat r $ Bound 0))
          val result = aggregate p 91 (row r)
          val observed = stats ()
          val progress = "Decade rank progress: phases=" ^ Int.toString (r + 1) ^
            " checked_rows=" ^ Int.toString (!checked_rows) ^ " elapsed_ms=" ^
            LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started))) ^
            " observation_ms=" ^ LargeInt.toString (#observation_milliseconds observed) ^
            " lookup_ms=" ^ LargeInt.toString (lookup_work ()) ^
            " comparison_ms=" ^ LargeInt.toString (Time.toMilliseconds (!comparison_ms)) ^
            " aggregation_ms=" ^ LargeInt.toString (Time.toMilliseconds (!aggregation_ms)) ^
            " entry_conversions=" ^ Int.toString (#entry_conversions observed) ^
            " near_conversions=" ^ Int.toString (#near_conversions observed)
          val _ = Output.physical_stderr (progress ^ "\n")
          (* Isabelle may retain process output until session completion. This
             optional diagnostic sink preserves completed-phase measurements
             on watchdog termination; it is never read as proof evidence. *)
          val progress_path = getenv "NUMBER_COMPILER_RANK_PROGRESS"
          val _ = if progress_path = "" then () else
            File.append (Path.explode progress_path) (progress ^ "\n")
        in result end
      val p = Abs ("r", @{typ nat}, HOLogic.mk_all ("x", @{typ nat},
        HOLogic.mk_imp ((@{term "less :: nat => nat => bool"} $ Bound 0 $ nat 91),
          predicate (@{term Comma_Decade} $ Bound 1 $ Bound 0))))
      val rectangle = aggregate p phases phase
      val final_stats = stats ()
      val _ = if #control_reconstructions final_stats = 0 andalso
          #weighted_exports final_stats = 0 andalso
          #terminal_payloads final_stats = 0 then ()
        else error "Rank checker evaluated an undemanded weighted consumer"
      val audit_started = Time.now ()
      val _ = if null (Thm_Deps.all_oracles [rectangle]) then ()
        else error "Decade rank rectangle depends on an oracle"
      val audit_ms = Time.toMilliseconds (Time.- (Time.now (), audit_started))
      val _ = if getenv "NUMBER_COMPILER_PROOF_GENERATION" = generation then ()
        else error "Decade rank generation changed during final audit"
    in (rectangle, {observation = final_stats, checked_rows = !checked_rows,
      peak_roots_per_batch = !peak_roots_per_batch, audit_ms = audit_ms,
      comparison_ms = Time.toMilliseconds (!comparison_ms), comparison_failures = !comparison_failures,
      aggregation_ms = Time.toMilliseconds (!aggregation_ms), aggregation_failures = !aggregation_failures}) end
end
