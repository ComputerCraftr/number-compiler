(* Proof-producing local evaluator. No recursive round equation is in the
   evaluator simpset; recursive calls only compose already checked local steps. *)
structure Comma_Round_Witness =
struct
  fun numeral n = HOLogic.mk_number @{typ nat} n
  fun entry f d x = @{term Comma_Entry} $ numeral f $ numeral d $ numeral x
  fun rhs th = Thm.term_of (Thm.rhs_of th)
  fun object_eq th = th RS @{thm meta_eq_to_obj_eq}

  fun mentions_round th = Term.exists_subterm
    (fn Const (name, _) => name = @{const_name comma_round_close}
      | _ => false) (Thm.prop_of th)

  fun round_rules ctxt =
    #simps (Simplifier.dest_ss (Simplifier.simpset_of ctxt))
    |> filter (fn (_, th) => mentions_round th)

  fun evaluator ctxt =
    let
      val arithmetic = ctxt
        |> fold Simplifier.del_simp
          @{thms comma_round_close.simps comma_weighted_step_def
            comma_near_germ.simps comma_round_control_germ.simps}
      (* Function-package domain rewrites may also mention round_close.
         Quarantine every such inherited dependency, not only its equation. *)
      val inherited = round_rules arithmetic
      val _ = if null inherited then () else warning
        ("round witness: quarantined round-dependent arithmetic rewrites: " ^
          commas (map (fn (_, th) => fst (Thm.get_name_hint th)) inherited))
    in arithmetic
      |> fold (Simplifier.del_simp o snd) inherited
      |> fold Simplifier.add_simp @{thms comma_finite_guard_extra_def Let_def}
    end

  fun memo_certified require_generation certify {hit, miss} table key compute =
    (require_generation ();
     case Termtab.lookup (!table) key of
       SOME th => (hit (); th)
     | NONE =>
         let val _ = miss ()
             val th = compute ()
             val _ = certify th
             val _ = require_generation ()
         in table := Termtab.update (key, th) (!table); th end)

  fun make_engine_owned ctxt {generation, current_generation} =
    let
      (* Invalidation revokes this entire owner. The caller must drop/replace
         the returned closures to release their local tables and audit cache;
         retaining an invalid owner cannot confer publication authority. *)
      val invalidated = Unsynchronized.ref false
      fun require_generation () =
        if !invalidated then error "Round witness owner was invalidated"
        else if current_generation () = generation then ()
        else (invalidated := true;
          error "Round witness source generation changed; discard the entire owner")
      val _ = require_generation ()
      val _ = warning "round witness: evaluator setup"
      val local_ctxt = evaluator ctxt
      val _ = warning "round witness: evaluator ready"
      val recursive_rules = round_rules local_ctxt
      val _ = if null recursive_rules then ()
        else error ("Round closure rewrite remained in local evaluator: " ^
          commas (map (fn (_, th) => fst (Thm.get_name_hint th)) recursive_rules))
      val (certify, certificate_stats) = Comma_Entry_Arithmetic.make_certifier ctxt
      val diagnostic_steps = Unsynchronized.ref 0
      val entry_conversions = Unsynchronized.ref 0
      val near_conversions = Unsynchronized.ref 0
      val entry_conversion_elapsed = Unsynchronized.ref Time.zeroTime
      val near_conversion_elapsed = Unsynchronized.ref Time.zeroTime
      val near_steps = Unsynchronized.ref Termtab.empty
      val near_germs = Unsynchronized.ref Termtab.empty
      val germ_hits = Unsynchronized.ref 0
      val germ_misses = Unsynchronized.ref 0
      val entry_steps = Unsynchronized.ref Termtab.empty
      val current_phase = Unsynchronized.ref (NONE: int option)
      val entry_rules = Unsynchronized.ref Termtab.empty
      val entry_moduli = Unsynchronized.ref Inttab.empty
      val entry_hits = Unsynchronized.ref 0
      val entry_misses = Unsynchronized.ref 0
      val predicate_facts = Unsynchronized.ref Termtab.empty
      val predicate_hits = Unsynchronized.ref 0
      val predicate_misses = Unsynchronized.ref 0
      val predicate_evictions = Unsynchronized.ref 0
      val predicate_retained = Unsynchronized.ref 0
      val sector_compositions = Unsynchronized.ref 0
      val round_exports = Unsynchronized.ref 0
      val max_sector_compositions = Unsynchronized.ref 0
      val round_elapsed = Unsynchronized.ref Time.zeroTime
      val request_elapsed = Unsynchronized.ref Time.zeroTime
      val short_keys = Unsynchronized.ref 0
      val key_elapsed = Unsynchronized.ref Time.zeroTime
      val composition_elapsed = Unsynchronized.ref Time.zeroTime
      fun measured elapsed f x =
        let val start = Time.now (); val result = Exn.capture f x
          val _ = elapsed := Time.+ (!elapsed, Time.- (Time.now (), start))
        in Exn.release result end
      fun compose rule facts = measured composition_elapsed (fn () => rule OF facts) ()
      val numeral_ctxt = Comma_Entry_Arithmetic.numeral_context ctxt
      fun normalize_numeral_fact th = Simplifier.full_simplify numeral_ctxt th
      fun memo table key compute =
        memo_certified require_generation certify
          {hit = fn () => (), miss = fn () => ()} table key compute
      fun counted_memo hits misses table key compute =
        memo_certified require_generation certify
          {hit = fn () => hits := !hits + 1,
           miss = fn () => misses := !misses + 1} table key compute
      fun number term = snd (HOLogic.dest_number term)
        handle TERM _ => HOLogic.dest_nat term
      fun value th = number (rhs th)
      fun period_item th =
        let val (_, [f, d]) = strip_comb (Thm.term_of (Thm.lhs_of th))
        in (10 * number f + number d, (value th, th)) end
      fun short_item th =
        let val (_, [p]) = strip_comb (Thm.term_of (Thm.lhs_of th))
        in (number p, (value th, th)) end
      val period_data = Inttab.make (map period_item @{thms comma_compiled_period_facts})
      val cycle_data = Inttab.make (map short_item @{thms comma_compiled_cycle_length_facts})
      val short_data = Inttab.make (map short_item @{thms comma_compiled_short_period_facts})
      val (compiled_arithmetic, power_invocations) =
        Comma_Entry_Arithmetic.conversion local_ctxt certify
        {periods = @{thms comma_compiled_period_facts},
         short_periods = @{thms comma_compiled_short_period_facts},
         powers = @{thms comma_compiled_power_facts}}
      val step_ctxt = (put_simpset HOL_basic_ss ctxt
        |> Simplifier.add_cong @{thm if_weak_cong}) addsimps
        @{thms comma_entry_control_formula comma_near_control_formula Let_def}
      val headroom_ctxt = put_simpset HOL_basic_ss ctxt addsimps
        @{thms comma_finite_headroom_def Let_def}
      (* Composition consumes proved germ equations only. Inheriting the global
         simpset here reopens arithmetic and source semantics for cached effects;
         numeral normalization and exact structural equations are sufficient. *)
      val composition_ctxt = numeral_ctxt addsimps
        @{thms numeral_plus_numeral add_numeral_special add_0_left add_0_right}
      (* Closed Near arithmetic has no sequence semantics. In particular it must
         not search the imported comma/cylinder simplification collection. *)
      val near_arithmetic_ctxt = Comma_Entry_Arithmetic.natural_context ctxt
      val shift_ctxt = near_arithmetic_ctxt addsimps
        @{thms comma_shift_move.simps comma_shift_position.simps}
      fun local_conversion ct =
        let
          val first = Simplifier.rewrite step_ctxt ct
          val near = (case strip_comb (Thm.term_of ct) of
              (_, [_, source]) => head_of source = @{term Comma_Near}
            | _ => false)
        in if near then
          (* Near has no Entry headroom or modular power. Do not traverse its
             conditional expression twice with unrelated Entry conversions. *)
          Thm.transitive first (Simplifier.rewrite near_arithmetic_ctxt (Thm.rhs_of first))
        else
          let
            val headroom = Simplifier.rewrite headroom_ctxt (Thm.rhs_of first)
            val table = compiled_arithmetic (Thm.rhs_of headroom)
            val arithmetic = Simplifier.rewrite local_ctxt (Thm.rhs_of table)
          in Thm.transitive first (Thm.transitive headroom
            (Thm.transitive table arithmetic)) end
        end
      fun rewrite t =
        let
          val trace = !diagnostic_steps < 3
          val _ = diagnostic_steps := !diagnostic_steps + 1
          val _ = if trace then warning ("round witness: local start " ^
            Syntax.string_of_term ctxt t) else ()
          val (_, [_, source]) = strip_comb t
          val near = head_of source = @{term Comma_Near}
          val calls = if near then near_conversions else entry_conversions
          val elapsed = if near then near_conversion_elapsed else entry_conversion_elapsed
          val _ = calls := !calls + 1
          val th = measured elapsed local_conversion (Thm.cterm_of ctxt t)
          val _ = if trace then warning ("round witness: local done " ^
            Thm.string_of_thm ctxt th) else ()
        in th end
      fun prove_true proposition =
        let
          val _ = require_generation ()
          val cached = Termtab.defined (!predicate_facts) proposition
          val _ = if cached orelse !predicate_retained < 8192 then ()
            else (predicate_evictions := !predicate_evictions + !predicate_retained;
              predicate_facts := Termtab.empty; predicate_retained := 0)
          val result = counted_memo predicate_hits predicate_misses predicate_facts proposition (fn () =>
          let val equation = Simplifier.rewrite local_ctxt
              (Thm.cterm_of ctxt proposition)
          in if rhs equation aconv @{term True}
            then object_eq equation RS @{thm eqTrueE}
            else error "Entry transport bound did not normalize to True" end)
          val _ = if cached then () else predicate_retained := !predicate_retained + 1
        in result end
      fun entry_rule f = memo entry_rules f (fn () =>
        @{thm comma_finite_entry_short_phase_shift} OF
          [prove_true (HOLogic.mk_binrel @{const_name less_eq} (numeral 1, f)),
           prove_true (HOLogic.mk_binrel @{const_name less_eq} (f, numeral 9))])
      fun modulus_fact f digit period_fact short_fact =
        let val _ = require_generation ()
            val index = 10 * f + digit
        in case Inttab.lookup (!entry_moduli) index of
          SOME th => th
        | NONE =>
            let
              val term = @{term comma_short_period} $
                (@{term comma_finite_period} $ numeral f $ numeral digit)
              val first = Conv.arg_conv (Conv.rewr_conv period_fact)
                (Thm.cterm_of ctxt term)
              val th = certify (Thm.transitive first short_fact)
              val _ = require_generation ()
              val _ = entry_moduli := Inttab.update (index, th) (!entry_moduli)
            in th end
        end
      fun entry_step r source ct =
        let
          (* This lookup is untrusted indexing only. The checked phase reduction
             below must compose to this exact representative or the call fails. *)
          val (_, [f_term, delta_term, offset_term]) = strip_comb source
          val f = number f_term
          val delta = number delta_term
          val offset = number offset_term
          val digit = offset mod 10
          val (p, period_fact) = the (Inttab.lookup period_data (10 * f + digit))
          val (period, short_fact) = the (Inttab.lookup short_data p)
          val key = (number r + delta) mod period
          val request = @{term comma_finite_step} $ numeral key $ entry f 0 offset
          val local_fact = counted_memo entry_hits entry_misses entry_steps request
            (fn () => rewrite request)
          val modulus = modulus_fact f digit period_fact short_fact
          val canonical = Simplifier.rewrite numeral_ctxt ct
          val transported = Conv.rewr_conv
            (entry_rule (numeral f) RS @{thm eq_reflection}) (Thm.rhs_of canonical)
          fun arithmetic ct' =
            let val th = Simplifier.rewrite near_arithmetic_ctxt ct'
            in Thm.transitive th (Simplifier.rewrite numeral_ctxt (Thm.rhs_of th)) end
          fun reduce_modulus ct' =
            let
              val digit_eq = Conv.arg_conv (Conv.arg_conv arithmetic) ct'
              val table_eq = Conv.rewr_conv modulus (Thm.rhs_of digit_eq)
            in Thm.transitive digit_eq table_eq end
          fun reduce_key ct' =
            let
              val mod_eq = Conv.arg_conv reduce_modulus ct'
              val reduced = arithmetic (Thm.rhs_of mod_eq)
              val _ = if rhs reduced aconv numeral key then ()
                else error "Untrusted short-phase key disagrees with certified reduction"
            in Thm.transitive mod_eq reduced end
          val _ = short_keys := !short_keys + 1
          val key_eq = measured key_elapsed
            (Conv.arg_conv (Conv.fun_conv (Conv.arg_conv reduce_key)))
            (Thm.rhs_of transported)
          val applied = Conv.arg_conv (Conv.rewr_conv local_fact) (Thm.rhs_of key_eq)
          val shifted = Simplifier.rewrite shift_ctxt (Thm.rhs_of applied)
        in certify (Thm.transitive canonical (Thm.transitive transported
          (Thm.transitive key_eq (Thm.transitive applied shifted)))) end
      fun step r source =
        let
          val _ = require_generation ()
          val _ = if head_of source = @{term Comma_Entry} then ()
            else error "Only Entry discovery may use the Entry arithmetic owner"
          val request = @{term comma_finite_step} $
            (HOLogic.mk_binop @{const_name modulo} (r, numeral 924)) $ source
        in entry_step r source (Thm.cterm_of ctxt request) end
      fun unexpected r source result = error
        ("Local evaluator did not prove an admitted finite move: phase " ^
          Syntax.string_of_term ctxt r ^ "; source " ^
          Syntax.string_of_term ctxt source ^ "; result " ^
          Syntax.string_of_term ctxt result)
      fun is_near source =
        (case head_of source of
          Const (name, _) => name = @{const_name Comma_Near}
        | _ => false)
      val germ_ctxt = composition_ctxt addsimps
        @{thms comma_finite_move.case comma_finite_position.case prod.case Let_def}
      (* Prove one compact (count, terminal-headroom) equation per Near class.
         Recursive arithmetic is discharged here once; round proofs consume the
         generic germ-refinement theorem, never its internal transition rows. *)
      fun near_germ source_f source_h =
        let
          val request = @{term comma_near_germ} $ source_f $ source_h
          val authority = Simplifier.rewrite numeral_ctxt (Thm.cterm_of ctxt request)
          val key = rhs authority
          val (_, [f, h]) = strip_comb key
          val cached = counted_memo germ_hits germ_misses near_germs key (fn () =>
          let
            val source = @{term Comma_Near} $ f $ numeral 0 $ h
            val request = @{term comma_finite_step} $ numeral 0 $ source
            val move = memo near_steps request (fn () => rewrite request)
            val tail = (case strip_comb (rhs move) of
                (Const (name, _), [target]) =>
                  if name = @{const_name Comma_Next} andalso is_near target then
                    let val (_, [g, delta, j]) = strip_comb target
                        val _ = if number g = number f andalso number delta = 0 then ()
                          else error "Near germ changed its sector or absolute delta"
                    in [near_germ f j] end
                  else []
              | _ => [])
            val unfolded = Conv.rewr_conv
              (@{thm comma_near_germ.simps} RS @{thm eq_reflection})
              (Thm.cterm_of ctxt key)
            (* The arithmetic owner may spell one as Suc 0 while the
               function equation uses numeral one. Normalize both sides of
               closed certificates before adding them as exact rewrites. *)
            val facts = map normalize_numeral_fact (move :: tail)
            val normalized = Simplifier.rewrite
              (germ_ctxt addsimps facts) (Thm.rhs_of unfolded)
            val _ = HOLogic.dest_prod (rhs normalized)
          in Thm.transitive unfolded normalized end)
        in Thm.transitive authority cached end
      val terminal_payloads = Unsynchronized.ref Termtab.empty
      val terminal_hits = Unsynchronized.ref 0
      val terminal_misses = Unsynchronized.ref 0
      val weighted_exports = Unsynchronized.ref 0
      val scalar_normalizations = Unsynchronized.ref 0
      val normalization_calls = Unsynchronized.ref 0
      val normalization_elapsed = Unsynchronized.ref Time.zeroTime
      val selector_calls = Unsynchronized.ref 0
      val selector_elapsed = Unsynchronized.ref Time.zeroTime
      val compatibility_calls = Unsynchronized.ref 0
      val compatibility_elapsed = Unsynchronized.ref Time.zeroTime
      val payload_ctxt = composition_ctxt addsimps
        @{thms simp_thms if_True if_False arith_simps rel_simps of_nat_numeral
          comma_event_kind.distinct prod.case Let_def option.case list.map append.simps
          comma_finite_position.case comma_weighted_move.case
          comma_weighted_germ.select_convs comma_weight_expression.select_convs
          comma_terminal_payload.select_convs
          comma_sector_germ_def comma_sector_weighted_germ_def
          comma_terminal_payload_weighted_def comma_event_target.simps
          comma_weight_then_def
          comma_chart_then_coefficients comma_guard_pullback.simps
          comma_form_pullback.simps comma_prefix_chart.simps
          comma_occurrence_guards.simps comma_lift_event_guard.simps}
      (* Proof normalization keeps the semantic predicates opaque. It can only
         rewrite certified payload equations and concrete record selectors. *)
      val proof_ctxt = put_simpset HOL_basic_ss ctxt addsimps
        @{thms simp_thms comma_weighted_germ.select_convs
          comma_weight_expression.select_convs comma_terminal_payload.select_convs
          comma_weighted_germ_then_source comma_germ_then_target comma_germ_then_controls
          add_0_left add_0_right numeral_plus_numeral add_numeral_special}
      fun instantiate rule bindings = Drule.infer_instantiate ctxt
        (map (fn (name, term) => ((name, 0), Thm.cterm_of ctxt term)) bindings) rule
      fun normalize_payload rules facts term =
        (normalization_calls := !normalization_calls + 1;
         certify (measured normalization_elapsed
           (Simplifier.rewrite (payload_ctxt addsimps (rules @ facts)))
           (Thm.cterm_of ctxt term)))
      fun normalize_proof facts theorem =
        (normalization_calls := !normalization_calls + 1;
         certify (measured normalization_elapsed
           (Simplifier.full_simplify (proof_ctxt addsimps facts)) theorem))
      fun leaf_selector selector record =
        (selector_calls := !selector_calls + 1;
         certify (measured selector_elapsed (Simplifier.rewrite proof_ctxt)
           (Thm.cterm_of ctxt (selector $ record))))
      type checked_germ = {value: term, refinement: thm, frontier: thm option,
        source_equation: thm, target_equation: thm}
      fun checked_leaf value refinement frontier : checked_germ =
        {value=value, refinement=refinement, frontier=frontier,
         source_equation=leaf_selector
           @{term "germ_source :: comma_weighted_germ => comma_finite_position"} value,
         target_equation=leaf_selector
           @{term "germ_target :: comma_weighted_germ => comma_finite_position"} value}
      fun weighted_sector r source : checked_germ =
        let
          val _ = require_generation ()
          val _ = sector_compositions := !sector_compositions + 1
          val (germ, extra) = if is_near source then
              let val (_, [f, _, h]) = strip_comb source
              in (near_germ f h, []) end
            else
              let
                val move = normalize_numeral_fact (step r source)
                val (_, [target]) = strip_comb (rhs move)
                val (_, [f, _, h]) = strip_comb target
                val weighted = compose @{thm comma_entry_weight_from_control}
                  [object_eq move]
                (* Only this finite scalar cycle length is evaluated here;
                   the exact weight retains its absolute delta symbolically. *)
                val (_, length) = the (Inttab.lookup cycle_data (number f))
                val (_, [_, _, x]) = strip_comb source
                val period_request = @{term comma_finite_period} $ f $
                  HOLogic.mk_binop @{const_name modulo} (x, numeral 10)
                val digit = Conv.arg_conv (fn ct =>
                  let val evaluated = Simplifier.rewrite local_ctxt ct
                  in Thm.transitive evaluated
                    (Simplifier.rewrite numeral_ctxt (Thm.rhs_of evaluated)) end)
                  (Thm.cterm_of ctxt period_request)
                val (_, [_, d]) = strip_comb (rhs digit)
                val (_, period) = the (Inttab.lookup period_data (10 * number f + number d))
                val exact_period = Thm.transitive digit period
              in (near_germ f h, [weighted, length, exact_period]) end
          val request = @{term comma_sector_weighted_germ} $ r $ source
          val equation = normalize_payload [] (germ :: extra) request
          fun consequence rule = normalize_proof [equation]
            (instantiate rule [("r", r), ("source", source)])
        in checked_leaf (rhs equation)
          (consequence @{thm comma_sector_occurrence_certificate})
          (SOME (consequence @{thm comma_sector_weighted_germ_frontier})) end
      fun terminal_move r terminal =
        let
          val (_, [_, delta, _]) = strip_comb terminal
          val request = @{term comma_finite_step} $ r $ terminal
          val transport = Conv.rewr_conv
            (@{thm comma_round_witness_near_transport} RS @{thm eq_reflection})
            (Thm.cterm_of ctxt request)
          val (_, [_, normalized]) = strip_comb (rhs transport)
          val normalization = Simplifier.rewrite numeral_ctxt (Thm.cterm_of ctxt normalized)
          val canonical_key = rhs normalization
          val cached = (case Termtab.lookup (!near_steps) canonical_key of
              SOME proof => normalize_numeral_fact proof
            | NONE => error "Terminal payload requested an undiscovered Near event")
          val local_fact = Thm.transitive normalization cached
          val applied = Conv.arg_conv (Conv.rewr_conv local_fact) (Thm.rhs_of transport)
          val shifted = Simplifier.rewrite
            (germ_ctxt addsimps @{thms comma_shift_move.simps comma_shift_position.simps})
            (Thm.rhs_of applied)
          val move = Thm.transitive transport (Thm.transitive applied shifted)
        in certify move end
      fun terminal_payload r terminal =
        let
          val (_, [f, delta, h]) = strip_comb terminal
          val key = @{term comma_terminal_event_germ} $ numeral 0 $ f $ delta $ h
          val canonical = counted_memo terminal_hits terminal_misses terminal_payloads key (fn () =>
            let
              val move = terminal_move (numeral 0) terminal
              val _ = scalar_normalizations := !scalar_normalizations + 1
              val digit = certify (measured composition_elapsed
                (Simplifier.rewrite local_ctxt)
                (Thm.cterm_of ctxt (Term.betapply (@{term "\<lambda>h::nat. (10-h mod 10) mod 10"}, h))))
              val powers = (case strip_comb (rhs move) of
                  (Const (next, _), [target]) =>
                    (case strip_comb target of
                      (Const (tag, _), [_, e, _]) =>
                        if next = @{const_name Comma_Next} andalso tag = @{const_name Comma_Entry}
                        then let
                          val gain = number e - number delta
                          val _ = if gain = 0 orelse gain = 1 then ()
                            else error "Terminal chart has an inadmissible exponent gain"
                          val request = Term.betapply (Term.betapply (@{term "\<lambda>e d::nat. (10::int)^(e-d)"}, e), delta)
                          val _ = scalar_normalizations := !scalar_normalizations + 1
                        in [certify (measured composition_elapsed
                          (Simplifier.rewrite (local_ctxt addsimps @{thms power_0 power_Suc}))
                          (Thm.cterm_of ctxt request))] end else []
                    | _ => [])
                | _ => [])
            in normalize_payload
              @{thms comma_terminal_event_germ_def comma_move_kind.simps
                comma_event_action.simps comma_event_guards.simps
                comma_event_units.simps comma_event_wall_def comma_event_false_def}
              (move :: digit :: powers) key end)
          val actual = @{term comma_terminal_payload_at} $ r $ terminal
          (* Phase erasure is intentionally one-shot. Its zero-phase
             instance rewrites a term to itself, so it must never enter a
             recursive simplifier. The canonical payload is already checked. *)
          val unfolded = Conv.rewr_conv
            (@{thm comma_terminal_payload_at.simps(1)} RS @{thm eq_reflection})
            (Thm.cterm_of ctxt actual)
          val erased = Conv.rewr_conv
            (@{thm comma_terminal_event_phase_erase} RS @{thm eq_reflection})
            (Thm.rhs_of unfolded)
          val result = Conv.rewr_conv canonical (Thm.rhs_of erased)
        in certify (Thm.transitive unfolded (Thm.transitive erased result)) end
      fun join r (left: checked_germ) (right: checked_germ) : checked_germ =
        let
          val _ = require_generation ()
          (* Composition and its complete certificate stay symbolic. Cached
             selector equations prove compatibility without traversing either
             previously built prefix or its guards/weight records. *)
          val action = @{term comma_weighted_germ_then} $ #value left $ #value right
          val _ = compatibility_calls := !compatibility_calls + 1
          val compatible = measured compatibility_elapsed (fn () =>
            object_eq (Thm.transitive (#target_equation left)
              (Thm.symmetric (#source_equation right)))) ()
          fun combine rule first second = certify
            (compose rule [first, second, compatible])
          val refinement = combine @{thm comma_occurrence_certificate_then}
            (#refinement left) (#refinement right)
          val frontier = (case (#frontier left, #frontier right) of
              (SOME A, SOME B) => SOME (combine @{thm comma_weighted_germ_frontier_then} A B)
            | _ => NONE)
          fun inherited_selector selector rule cached =
            (selector_calls := !selector_calls + 1;
             certify (measured selector_elapsed (fn () =>
               let val lifted = Conv.rewr_conv (rule RS @{thm eq_reflection})
                 (Thm.cterm_of ctxt (selector $ action))
               in Thm.transitive lifted cached end) ()))
          val source_equation = inherited_selector
            @{term "germ_source :: comma_weighted_germ => comma_finite_position"}
            @{thm comma_weighted_germ_then_source} (#source_equation left)
          val target_equation = inherited_selector
            @{term "germ_target :: comma_weighted_germ => comma_finite_position"}
            @{thm comma_germ_then_target} (#target_equation right)
        in {value=action, refinement=refinement, frontier=frontier,
          source_equation=source_equation, target_equation=target_equation} end
      fun round_once r source =
        let
          fun loop current count accumulated =
            let
              val _ = if count < 9 then () else
                error "Weighted round exceeded the admitted nine-sector budget"
              val sector = weighted_sector r current
              val prefix = (case accumulated of NONE => sector
                | SOME previous => join r previous sector)
              val terminal = rhs (#target_equation prefix)
              val payload = terminal_payload r terminal
              val payload_request = @{term comma_terminal_payload_at} $ r $ terminal
              val move_request = @{term "terminal_move :: comma_terminal_payload => comma_finite_move"} $ payload_request
              val move = normalize_payload [] [payload] move_request
              val (_, [f, _, _]) = strip_comb terminal
              val kind_request = @{term comma_move_kind} $ f $ move_request
              val kind = normalize_payload @{thms comma_move_kind.simps} [payload] kind_request
              val event_request = @{term comma_terminal_weighted_germ} $ r $ terminal
              val projection = Conv.rewr_conv
                (@{thm comma_terminal_payload_projection[symmetric]} RS @{thm eq_reflection})
                (Thm.cterm_of ctxt event_request)
              val event_value = normalize_payload [] [payload] (rhs projection)
              val event_equation = Thm.transitive projection event_value
              val event_certificate = normalize_proof [event_equation]
                (instantiate @{thm comma_terminal_occurrence_certificate}
                  [("r", r), ("source", terminal)])
              val event = checked_leaf (rhs event_equation) event_certificate NONE
              fun stop rule more =
                let
                  val terminal_stop = compose rule (object_eq move :: more)
                  val frontier = the (#frontier prefix)
                  val finish = Simplifier.full_simplify proof_ctxt
                    (compose @{thm comma_weighted_germ_frontier_stop} [frontier])
                  val answer = certify (compose finish [terminal_stop])
                  val complete = join r prefix event
                  val _ = max_sector_compositions :=
                    Int.max (!max_sector_compositions, count + 1)
                in (answer, complete) end
            in (case strip_comb (rhs move) of
                (Const (name, _), [target]) =>
                  if name = @{const_name Comma_Next} then
                    if rhs kind aconv @{term Comma_Power_Event} then
                      stop @{thm comma_terminal_power_stop} [object_eq kind]
                    else
                      let
                        val ordinary = normalize_payload [] [kind]
                          (HOLogic.mk_not (HOLogic.mk_eq
                            (kind_request, @{term Comma_Power_Event})))
                        val proof = compose @{thm comma_terminal_ordinary_frontier}
                          [object_eq move, object_eq ordinary RS @{thm eqTrueE}]
                        val frontier = normalize_proof [event_equation] proof
                        val continuing : checked_germ = {value = #value event,
                          refinement = #refinement event, frontier = SOME frontier,
                          source_equation = #source_equation event,
                          target_equation = #target_equation event}
                      in loop target (count + 1) (SOME (join r prefix continuing)) end
                  else if name = @{const_name Comma_Landmine} then
                    stop @{thm comma_terminal_landmine_stop} []
                  else unexpected r terminal (rhs move)
              | (Const (name, _), [_, _]) =>
                  if name = @{const_name Comma_Fork} then
                    stop @{thm comma_terminal_fork_stop} []
                  else unexpected r terminal (rhs move)
              | _ => unexpected r terminal (rhs move))
            end
        in loop source 0 NONE end
      fun close_source_inner phase source =
        let
          val _ = require_generation ()
          val _ = current_phase := SOME phase
          val r = numeral phase
          val admission = prove_true (@{term comma_round_admitted} $ source)
          val (equation, complete) = measured round_elapsed (round_once r) source
          val _ = if Thm.term_of (Thm.lhs_of (equation RS @{thm eq_reflection})) aconv
              (@{term comma_round_close} $ r $ source) then ()
            else error "Weighted round lost its exact occurrence binding"
          val _ = if rhs (#source_equation complete) aconv source then ()
            else error "Weighted payload lost the requested source occurrence"
          val expected = HOLogic.mk_Trueprop
            (@{term comma_occurrence_certificate} $ r $ #value complete)
          val _ = if Thm.prop_of (#refinement complete) aconv expected then ()
            else error "Weighted certificate belongs to another payload or phase"
          val _ = certify (#refinement complete)
          val _ = require_generation ()
          val _ = round_exports := !round_exports + 1
          val _ = weighted_exports := !weighted_exports + 1
        in {equation = equation, payload = #value complete,
          refinement = #refinement complete, admission = admission} end

      (* Full request accounting includes admission, the bounded forward fold,
         final source/certificate checks and failures. The existing five-second
         diagnostic remains scoped to the forward fold itself. *)
      fun close_source phase source = measured request_elapsed
        (close_source_inner phase) source

      val observation_exports = Unsynchronized.ref 0
      val control_reconstructions = Unsynchronized.ref 0
      val decade_observation_exports = Unsynchronized.ref 0
      val observation_sectors = Unsynchronized.ref 0
      val observation_max_sectors = Unsynchronized.ref 0
      val observation_links = Unsynchronized.ref 0
      val observation_elapsed = Unsynchronized.ref Time.zeroTime
      val observation_normalizations = Unsynchronized.ref 0
      val observation_normalization_elapsed = Unsynchronized.ref Time.zeroTime
      val observation_ctxt = composition_ctxt addsimps
        @{thms simp_thms if_True if_False arith_simps rel_simps
          comma_event_kind.distinct comma_move_kind.simps
          comma_finite_position.case comma_finite_move.case prod.case Let_def
          comma_shift_move.simps comma_shift_position.simps}
      fun observation_equation facts term =
        (observation_normalizations := !observation_normalizations + 1;
         certify (measured observation_normalization_elapsed
           (Simplifier.rewrite (observation_ctxt addsimps facts)) (Thm.cterm_of ctxt term)))
      val observation_sector_cache = Unsynchronized.ref
        (Termtab.empty: (term * thm) Termtab.table)
      val observation_sector_hits = Unsynchronized.ref 0
      val observation_sector_misses = Unsynchronized.ref 0
      val observation_sector_retained = Unsynchronized.ref 0
      val observation_sector_peak = Unsynchronized.ref 0
      val observation_sector_evictions = Unsynchronized.ref 0
      val observation_sector_failures = Unsynchronized.ref 0
      fun build_observation_sector r source =
        let
          val (germ, facts) = if is_near source then
              let val (_, [f, _, h]) = strip_comb source
              in (near_germ f h, []) end
            else
              let
                val move = normalize_numeral_fact (step r source)
                val (_, [target]) = strip_comb (rhs move)
                val (_, [f, _, h]) = strip_comb target
              in (near_germ f h, [move]) end
          val request = @{term comma_sector_control} $ r $ source
          val unfolded = Conv.rewr_conv
            (@{thm comma_sector_control_evaluation} RS @{thm eq_reflection})
            (Thm.cterm_of ctxt request)
          val evaluated = observation_equation (germ :: facts) (rhs unfolded)
          val sector = Thm.transitive unfolded evaluated
          val (_, terminal) = HOLogic.dest_prod (rhs sector)
          (* The publication boundary below checks this link once, after its
             exact source/target binding has been validated. *)
          val link = compose @{thm comma_observation_sector} [object_eq sector]
        in (terminal, link) end
      fun observation_sector r source =
        let
          val _ = require_generation ()
          val _ = observation_sectors := !observation_sectors + 1
          (* Exact occurrence identity is indispensable here: sharing a local
             Near/Entry arithmetic fact does not identify its phase or source. *)
          val key = HOLogic.mk_prod (r, source)
        in case Termtab.lookup (!observation_sector_cache) key of
          SOME result => (observation_sector_hits := !observation_sector_hits + 1; result)
        | NONE =>
            let
              val _ = observation_sector_misses := !observation_sector_misses + 1
              val attempted = Exn.capture (fn () =>
                let
                  val result as (terminal, link) = build_observation_sector r source
                  val (head, arguments) = strip_comb
                    (HOLogic.dest_Trueprop (Thm.prop_of link))
                  val _ = (case arguments of [phase, _, origin, target] =>
                    if head aconv @{term comma_observation_link} andalso phase aconv r
                        andalso origin aconv source andalso target aconv terminal then ()
                    else error "Sector observation lost its exact phase/source binding"
                  | _ => error "Malformed sector observation certificate")
                  val _ = certify link
                  val _ = require_generation ()
                in result end) ()
              val _ = if Exn.is_exn attempted then
                observation_sector_failures := !observation_sector_failures + 1 else ()
              val result = Exn.release attempted
              val _ = if !observation_sector_retained < 8192 then () else
                (observation_sector_evictions := !observation_sector_evictions +
                   !observation_sector_retained;
                 observation_sector_cache := Termtab.empty; observation_sector_retained := 0)
              val _ = observation_sector_cache := Termtab.update (key, result)
                (!observation_sector_cache)
              val _ = observation_sector_retained := !observation_sector_retained + 1
              val _ = observation_sector_peak := Int.max
                (!observation_sector_peak, !observation_sector_retained)
            in result end
        end
      fun observation_join A B =
        (observation_links := !observation_links + 1;
         observation_normalizations := !observation_normalizations + 1;
         certify (measured observation_normalization_elapsed
           (Simplifier.full_simplify composition_ctxt)
           (compose @{thm comma_observation_link_then} [A, B])))
      fun observe_once r source admission =
        let
          fun loop current count accumulated =
            let
              val _ = if count < 9 then () else
                error "Observation exceeded the proved nine-sector bound"
              val _ = observation_max_sectors := Int.max (!observation_max_sectors, count+1)
              val (terminal, sector) = observation_sector r current
              val prefix = (case accumulated of NONE => sector
                | SOME previous => observation_join previous sector)
              val phase = HOLogic.mk_binop @{const_name modulo} (r, numeral 924)
              val move = terminal_move phase terminal
              val (_, [f, _, _]) = strip_comb terminal
              val kind_request = @{term comma_move_kind} $ f $ rhs move
              val kind = observation_equation [] kind_request
              fun stop rule more =
                let
                  val stopped = compose rule (object_eq move :: more)
                  val observed = certify
                    (compose @{thm comma_observation_finish} [prefix, admission, stopped])
                in {observation=observed, admission=admission} end
            in (case strip_comb (rhs move) of
                (Const (name, _), [target]) =>
                  if name = @{const_name Comma_Next} then
                    if rhs kind aconv @{term Comma_Power_Event} then
                      stop @{thm comma_observation_power} [object_eq kind]
                    else
                      let
                        val ordinary = observation_equation [kind]
                          (HOLogic.mk_not (HOLogic.mk_eq
                            (kind_request, @{term Comma_Power_Event})))
                        val edge = certify (compose @{thm comma_observation_ordinary}
                          [object_eq move, object_eq ordinary RS @{thm eqTrueE}])
                      in loop target (count+1) (SOME (observation_join prefix edge)) end
                  else if name = @{const_name Comma_Landmine} then
                    stop @{thm comma_observation_landmine} []
                  else unexpected r terminal (rhs move)
              | (Const (name, _), [_, _]) =>
                  if name = @{const_name Comma_Fork} then
                    stop @{thm comma_observation_fork} []
                  else unexpected r terminal (rhs move)
              | _ => unexpected r terminal (rhs move))
            end
        in loop source 0 NONE end
      fun observe_source_inner phase source =
        let
          val _ = require_generation ()
          val _ = current_phase := SOME phase
          val r = numeral phase
          val admission = prove_true (@{term comma_round_admitted} $ source)
          val result = observe_once r source admission
          val _ = if Thm.term_of (Thm.lhs_of (#observation result RS @{thm eq_reflection}))
              aconv (@{term comma_round_observation} $ r $ source) then ()
            else error "Observation lost its weighted-owner projection binding"
          val _ = require_generation ()
          val _ = observation_exports := !observation_exports + 1
        in result end
      fun observe_source phase source = measured observation_elapsed
        (observe_source_inner phase) source

      (* Only legacy control-equation consumers request this conversion.
         Rank consumers keep the weighted constructor's observation theorem. *)
      fun observe_control_source phase source = measured observation_elapsed (fn () =>
        let
          val result = observe_source_inner phase source
          val equation = certify (compose @{thm comma_observation_close}
            [#admission result, #observation result])
          val _ = require_generation ()
          val _ = control_reconstructions := !control_reconstructions + 1
        in {equation=equation, observation= #observation result,
          admission= #admission result} end) ()

      fun observe_decade phase offset = measured observation_elapsed (fn () =>
        let
          val _ = if 0 <= phase andalso phase < 924 andalso
              0 <= offset andalso offset <= 90 then ()
            else error "Decade observation is outside the admitted finite domain"
          val result = observe_source_inner phase (entry 1 0 offset)
          val decoded = compose @{thm comma_decade_observed_from_round}
            [#observation result]
          val decoded_eq = decoded RS @{thm eq_reflection}
          val result_eq = Simplifier.rewrite
            (near_arithmetic_ctxt addsimps @{thms comma_decade_decode.simps
              comma_decade_root_admitted_entry})
            (Thm.rhs_of decoded_eq)
          val equation = certify (object_eq (Thm.transitive decoded_eq result_eq))
          val expected = @{term comma_decade_observed_control} $
            (@{term Comma_Decade} $ numeral phase $ numeral offset)
          val _ = if Thm.term_of (Thm.lhs_of (equation RS @{thm eq_reflection}))
              aconv expected then () else error "Decade observation lost its source"
          val _ = require_generation ()
          val _ = decade_observation_exports := !decade_observation_exports + 1
        in equation end) ()

      fun stats () =
        (require_generation ();
         {decade_observation_exports = !decade_observation_exports,
         control_reconstructions = !control_reconstructions,
         predicate_hits = !predicate_hits, predicate_misses = !predicate_misses,
         predicate_retained = !predicate_retained,
         predicate_evictions = !predicate_evictions,
         entry_conversions = !entry_conversions,
         near_conversions = !near_conversions,
         entry_conversion_milliseconds = Time.toMilliseconds (!entry_conversion_elapsed),
         near_conversion_milliseconds = Time.toMilliseconds (!near_conversion_elapsed),
         observation_sectors = !observation_sectors,
         observation_sector_hits = !observation_sector_hits,
         observation_sector_misses = !observation_sector_misses,
         observation_sector_retained = !observation_sector_retained,
         observation_sector_peak = !observation_sector_peak,
         observation_sector_evictions = !observation_sector_evictions,
         observation_sector_failures = !observation_sector_failures,
         observation_max_sectors = !observation_max_sectors,
         observation_links = !observation_links,
         selector_calls = !selector_calls,
         selector_milliseconds = Time.toMilliseconds (!selector_elapsed),
         compatibility_calls = !compatibility_calls,
         compatibility_milliseconds = Time.toMilliseconds (!compatibility_elapsed),
         observation_normalizations = !observation_normalizations,
         observation_normalization_milliseconds = Time.toMilliseconds (!observation_normalization_elapsed),
         observation_exports = !observation_exports,
         observation_milliseconds = Time.toMilliseconds (!observation_elapsed),
         normalization_calls = !normalization_calls,
         normalization_milliseconds = Time.toMilliseconds (!normalization_elapsed),
         weighted_exports = !weighted_exports,
         scalar_normalizations = !scalar_normalizations,
         terminal_payloads = Termtab.size (!terminal_payloads),
         terminal_hits = !terminal_hits, terminal_misses = !terminal_misses,
         near_steps = Termtab.size (!near_steps),
         entry_steps = Termtab.size (!entry_steps),
         near_germs = Termtab.size (!near_germs),
         germ_hits = !germ_hits, germ_misses = !germ_misses,
         sector_compositions = !sector_compositions,
         max_sector_compositions = !max_sector_compositions,
         round_exports = !round_exports,
         round_milliseconds = Time.toMilliseconds (!round_elapsed),
         request_milliseconds = Time.toMilliseconds (!request_elapsed),
         retained_rounds = 0, entry_rules = Termtab.size (!entry_rules),
         power_facts = length @{thms comma_compiled_power_facts},
         current_phase = !current_phase, oracle_audit = certificate_stats (),
         representative_hits = !entry_hits, representative_misses = !entry_misses,
         short_key_reductions = !short_keys, power_invocations = power_invocations (),
         short_key_milliseconds = Time.toMilliseconds (!key_elapsed),
         composition_milliseconds = Time.toMilliseconds (!composition_elapsed)})
    in {source=close_source, observe=observe_source,
      control=observe_control_source, decade=observe_decade, stats=stats} end

  fun make_source_owned ctxt authority =
    let val engine = make_engine_owned ctxt authority
    in (#source engine, #stats engine) end

  fun make_observer_source_owned ctxt authority =
    let val engine = make_engine_owned ctxt authority
    in (#control engine, #stats engine) end

  fun make_round_observation_owned ctxt authority =
    let val engine = make_engine_owned ctxt authority
    in (fn phase => fn offset => #observation
      (#observe engine phase (entry 1 0 offset)), #stats engine) end

  fun make_observer_owned ctxt authority =
    let val (observe, stats) = make_observer_source_owned ctxt authority
    in (fn phase => fn offset => #equation (observe phase (entry 1 0 offset)), stats) end

  fun make_decade_observation_owned ctxt authority =
    let val engine = make_engine_owned ctxt authority
    in (#decade engine, #stats engine) end

  fun make_owned ctxt authority =
    let val (close, stats) = make_source_owned ctxt authority
    in (fn phase => fn offset => #equation (close phase (entry 1 0 offset)), stats) end

  (* The captured Isabelle context is immutable. The runner owns the source
     fingerprint envelope; this token is only its generation authority, not a
     filesystem watcher. No file is read or hashed on an arithmetic cache hit. *)
  fun make ctxt =
    let
      val token = getenv "NUMBER_COMPILER_PROOF_GENERATION"
      val local_generation = "context-owner-" ^ string_of_int (serial ())
      fun current_generation () =
        let val current = getenv "NUMBER_COMPILER_PROOF_GENERATION"
        in if current = "" then local_generation else current end
      val generation = if token = "" then local_generation else token
    in make_owned ctxt {generation = generation,
      current_generation = current_generation} end
end
