theory Comma_Round_Witness
  imports Comma_Entry_Arithmetic.Comma_Entry_Arithmetic Comma_Decade_Observation
begin

text \<open>Local equations are kernel-checked and composed in one forward
weighted-germ fold. The loop retains transported chart guards, symbolic weights,
a closed all-exponent occurrence certificate and the exact round frontier.
The terminal event closes that frontier once; no recursive control replay or
suffix-history cache is used. Global finite-quotient classification and future
branch safety remain separate obligations.\<close>

lemma comma_round_witness_near_transport:
  "comma_finite_step r (Comma_Near f delta h) =
    comma_shift_move delta (comma_finite_step 0 (Comma_Near f 0 h))"
  using comma_near_step_delta_transport[of r f 0 delta h 0] by simp

lemma comma_round_witness_cross_shape_regression:
  "comma_finite_step 5 (Comma_Near 9 0 3) =
      Comma_Next (Comma_Entry 1 1 68)"
  "comma_round_crossing (Comma_Near 9 0 3) (Comma_Entry 1 1 68)"
  "\<not> comma_round_crossing (Comma_Entry 1 1 68) (Comma_Entry 1 1 68)"
  by (simp_all add: comma_near_control_formula comma_round_crossing_def Let_def)

lemma comma_germ_then_target:
  "germ_target (comma_weighted_germ_then A B) = germ_target B"
  by (simp add: comma_weighted_germ_then_def)

lemma comma_germ_then_controls:
  "germ_controls (comma_weighted_germ_then A B) = germ_controls A + germ_controls B"
  by (simp add: comma_weighted_germ_then_def)

lemma comma_germ_then_weight:
  "germ_weight (comma_weighted_germ_then A B) =
    comma_weight_then (germ_weight A) (germ_weight B)"
  by (simp add: comma_weighted_germ_then_def)

ML_file "round_witness.ML"

ML \<open>
  val comma_round_smoke =
  let
    val comma_failed_memo = Unsynchronized.ref Termtab.empty;
    val (comma_smoke_certify, _) = Comma_Entry_Arithmetic.make_certifier @{context};
    val comma_memo_key = @{term "(0::nat)"};
    val comma_memo_hits = Unsynchronized.ref 0;
    val comma_memo_misses = Unsynchronized.ref 0;
    val comma_memo_observe =
      {hit = fn () => comma_memo_hits := !comma_memo_hits + 1,
       miss = fn () => comma_memo_misses := !comma_memo_misses + 1};
    val _ = (case Exn.capture (fn () => Comma_Round_Witness.memo_certified
        (fn () => ()) comma_smoke_certify comma_memo_observe comma_failed_memo comma_memo_key
        (fn () => Thm.assume @{cprop True})) () of
        Exn.Exn (ERROR _) => ()
      | _ => error "Hypothesis-bearing theorem was accepted into memo");
    val _ = if Termtab.is_empty (!comma_failed_memo) then ()
      else error "Failed certification polluted the memo";
    val _ = Comma_Round_Witness.memo_certified (fn () => ()) comma_smoke_certify
      comma_memo_observe comma_failed_memo comma_memo_key (fn () => Thm.reflexive @{cterm "(0::nat)"});
    val _ = if Termtab.size (!comma_failed_memo) = 1 then ()
      else error "Certified memo insertion failed after rejected publication";
    val _ = Comma_Round_Witness.memo_certified (fn () => ())
      (fn _ => error "Memo hit repeated theorem certification") comma_memo_observe
      comma_failed_memo comma_memo_key (fn () => error "Memo hit repeated construction");
    val _ = if !comma_memo_hits = 1 andalso !comma_memo_misses = 2 then ()
      else error "Memo hit/miss counters do not match actual lookups";
    val comma_smoke_generation = Unsynchronized.ref 1;
    val (comma_source_smoke_close, comma_round_smoke_stats) =
      Comma_Round_Witness.make_source_owned @{context}
        {generation = 1, current_generation = fn () => !comma_smoke_generation};
    fun comma_round_smoke_close phase offset = #equation
      (comma_source_smoke_close phase (Comma_Round_Witness.entry 1 0 offset));
    val comma_source_smoke = comma_source_smoke_close 5 (Comma_Round_Witness.entry 1 0 3);
    val comma_round_smoke = #equation comma_source_smoke;
    val _ = if Thm.nprems_of comma_round_smoke = 0 andalso
        null (Thm.hyps_of comma_round_smoke) then ()
      else error "Round witness smoke has undischarged premises";
    val comma_cache_prior = comma_round_smoke_stats ();
    val comma_round_shifted_smoke = comma_round_smoke_close 929 3;
    val comma_cache_after = comma_round_smoke_stats ();
    val _ = if #representative_misses comma_cache_prior =
        #representative_misses comma_cache_after andalso
        #power_invocations comma_cache_prior = #power_invocations comma_cache_after andalso
        #representative_hits comma_cache_prior < #representative_hits comma_cache_after
      then () else error "Short-phase cache missed an equivalent phase";
    val _ = if #predicate_misses comma_cache_prior = #predicate_misses comma_cache_after
        andalso #predicate_hits comma_cache_prior < #predicate_hits comma_cache_after then ()
      else error "Repeated source admission was recomputed or lost its memo binding";
    val _ = if Thm.term_of (Thm.lhs_of
        (comma_round_shifted_smoke RS @{thm eq_reflection})) aconv
          @{term "comma_round_close 929 (Comma_Entry 1 0 3)"} andalso
        Thm.nprems_of comma_round_shifted_smoke = 0 andalso
        null (Thm.hyps_of comma_round_shifted_smoke) andalso
        null (Thm_Deps.all_oracles [comma_round_shifted_smoke])
      then () else error "Shifted smoke lost its original source or proof closure";
    val comma_delta_prior = comma_round_smoke_stats ();
    val comma_delta_source = Comma_Round_Witness.entry 1 924 3;
    val comma_delta_smoke = comma_source_smoke_close 5 comma_delta_source;
    val comma_delta_after = comma_round_smoke_stats ();
    val _ = if #representative_misses comma_delta_prior = #representative_misses comma_delta_after
        andalso #representative_hits comma_delta_prior < #representative_hits comma_delta_after
      then () else error "Absolute-delta transport rediscovered its control arithmetic";
    val _ = if Thm.term_of (Thm.lhs_of (#equation comma_delta_smoke RS @{thm eq_reflection}))
        aconv @{term "comma_round_close 5 (Comma_Entry 1 924 3)"}
      then () else error "Occurrence delta was erased from requested source";
    val comma_selector_context = put_simpset HOL_basic_ss @{context} |> Simplifier.add_simps
      @{thms comma_weighted_germ.select_convs comma_weight_expression.select_convs
        comma_germ_then_weight comma_weight_then_def append.simps};
    fun comma_weight_deltas payload =
      let
        val request = @{term "weight_entries :: comma_weight_expression => comma_chart_weight list"} $ (@{term "germ_weight :: comma_weighted_germ => comma_weight_expression"} $ payload);
        val equation = Simplifier.rewrite comma_selector_context
          (Thm.cterm_of @{context} request);
        fun delta term =
          let val (_, [_, d, _, _]) = strip_comb term
          in snd (HOLogic.dest_number d) end;
      in map delta (HOLogic.dest_list (Thm.term_of (Thm.rhs_of equation))) end;
    val comma_delta_zero = comma_weight_deltas (#payload comma_source_smoke);
    val comma_delta_large = comma_weight_deltas (#payload comma_delta_smoke);
    val _ = if not (null comma_delta_zero) andalso length comma_delta_zero = length comma_delta_large
        andalso forall (fn d => d=0) comma_delta_zero
        andalso forall (fn d => d=924) comma_delta_large
      then () else error "Symbolic literal weights lost their absolute exponent gain";
    val _ = List.app (fn th => if Thm.nprems_of th=0 andalso null (Thm.hyps_of th)
        andalso null (Thm_Deps.all_oracles [th]) then ()
      else error "Weighted occurrence certificate is open or oracle-dependent")
      [#refinement comma_source_smoke, #refinement comma_delta_smoke,
       #admission comma_source_smoke, #admission comma_delta_smoke];
    val (comma_observe, comma_observe_stats) = Comma_Round_Witness.make_observer_source_owned
      @{context} {generation=1, current_generation=fn () => !comma_smoke_generation};
    val comma_observed = comma_observe 5 (Comma_Round_Witness.entry 1 0 3);
    val comma_observation_compare_context = put_simpset HOL_basic_ss @{context} |> Simplifier.add_simps
      @{thms One_nat_def[symmetric] Suc_1 Suc_numeral add_num_simps
        add_0_left add_0_right numeral_plus_numeral add_numeral_special
        comma_germ_then_controls comma_weighted_germ.select_convs};
    fun comma_same_observation label actual expected =
      let
        val left = Simplifier.full_simplify comma_observation_compare_context actual;
        val right = Simplifier.full_simplify comma_observation_compare_context expected;
      in if Thm.prop_of left aconv Thm.prop_of right then ()
        else error (label ^ "\nActual: " ^ Thm.string_of_thm @{context} left ^
          "\nExpected: " ^ Thm.string_of_thm @{context} right) end;
    val _ = comma_same_observation "Projected observation disagrees with full weighted owner"
      (#equation comma_observed) comma_round_smoke;
    val comma_sector_before_shift = comma_observe_stats ();
    val comma_observed_shift = comma_observe 929 (Comma_Round_Witness.entry 1 0 3);
    val _ = comma_same_observation "Projected observation lost phase authority"
      (#equation comma_observed_shift) comma_round_shifted_smoke;
    val comma_projection_stats = comma_observe_stats ();
    val _ = if #weighted_exports comma_projection_stats=0 andalso
        #terminal_payloads comma_projection_stats=0 andalso
        #normalization_calls comma_projection_stats=0 andalso
        #observation_exports comma_projection_stats=2 then ()
      else error "Projected observation eagerly constructed weighted payloads";
    val _ = if #observation_sector_misses comma_projection_stats >
        #observation_sector_misses comma_sector_before_shift then ()
      else error "Sector cache confused distinct absolute phases";
    val comma_repeated_observation = comma_observe 5 (Comma_Round_Witness.entry 1 0 3);
    val comma_sector_repeated = comma_observe_stats ();
    val _ = comma_same_observation "Sector cache changed a repeated observation"
      (#equation comma_repeated_observation) (#equation comma_observed);
    val _ = if #observation_sector_hits comma_sector_repeated >
        #observation_sector_hits comma_projection_stats andalso
        #observation_sector_misses comma_sector_repeated =
        #observation_sector_misses comma_projection_stats then ()
      else error "Repeated observation did not reuse exact completed sectors";
    val _ = comma_observe 5 (Comma_Round_Witness.entry 1 0 4);
    val comma_sector_changed = comma_observe_stats ();
    val _ = if #observation_sector_misses comma_sector_changed >
        #observation_sector_misses comma_sector_repeated then ()
      else error "Sector cache reused a different source occurrence";
    val (comma_decade_observe, comma_decade_stats) =
      Comma_Round_Witness.make_decade_observation_owned @{context}
        {generation=1, current_generation=fn () => !comma_smoke_generation};
    val comma_decade_fact = comma_decade_observe 5 3;
    val _ = if Thm.prop_of comma_decade_fact aconv
        @{prop "comma_decade_observed_control (Comma_Decade 5 3) =
          Comma_Decade_Continue (Comma_Decade 6 68)"} andalso
        Thm.nprems_of comma_decade_fact=0 andalso null (Thm.hyps_of comma_decade_fact)
        andalso null (Thm_Deps.all_oracles [comma_decade_fact]) then ()
      else error ("Direct decade observation lost its exact closed outcome: " ^
        Thm.string_of_thm @{context} comma_decade_fact);
    val comma_decade_snapshot = comma_decade_stats ();
    val _ = if #decade_observation_exports comma_decade_snapshot=1 andalso
        #control_reconstructions comma_decade_snapshot=0 andalso
        #weighted_exports comma_decade_snapshot=0 andalso
        #terminal_payloads comma_decade_snapshot=0 andalso
        #normalization_calls comma_decade_snapshot=0 then ()
      else error "Direct decade observation reconstructed an unrequested consumer";
    val _ = (case Exn.capture (fn () => comma_decade_observe 924 3) () of
        Exn.Exn (ERROR _) => ()
      | _ => error "Decade observer admitted a foreign phase");
    val _ = writeln (Thm.string_of_thm @{context} comma_round_smoke);
    val _ = writeln (@{make_string} (comma_round_smoke_stats ()));
    val _ = if null (Thm_Deps.all_oracles [comma_round_smoke]) then ()
      else error "Round witness smoke depends on an oracle";
    val _ = comma_smoke_generation := 2;
    val _ = (case Exn.capture (fn () => comma_round_smoke_close 5 3) () of
        Exn.Exn (ERROR _) => ()
      | _ => error "Invalidated round owner published a cache-backed theorem");
    val _ = (case Exn.capture (fn () => comma_observe 5 (Comma_Round_Witness.entry 1 0 3)) () of
        Exn.Exn (ERROR _) => ()
      | _ => error "Invalidated observation owner published a theorem");
    val _ = (case Exn.capture (fn () => comma_decade_observe 5 3) () of
        Exn.Exn (ERROR _) => ()
      | _ => error "Invalidated decade owner published a theorem");
    val _ = comma_smoke_generation := 1;
    val _ = (case Exn.capture comma_round_smoke_stats () of
        Exn.Exn (ERROR _) => ()
      | _ => error "Invalidated owner recovered authority when generation reverted");
    val (comma_fresh_close, comma_fresh_stats) = Comma_Round_Witness.make_owned @{context}
      {generation = 1, current_generation = fn () => !comma_smoke_generation};
    val _ = if #representative_misses (comma_fresh_stats ()) = 0 then ()
      else error "Fresh evaluator inherited another owner's memo";
    val _ = comma_fresh_close 5 3;
    val _ = if #representative_misses (comma_fresh_stats ()) > 0 then ()
      else error "Fresh evaluator did not recompute its own arithmetic";
  in comma_round_smoke end;
\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_entry_control_formula comma_round_witness_near_transport
      comma_sector_occurrence_certificate comma_terminal_occurrence_certificate
      comma_occurrence_certificate_then comma_weighted_germ_frontier_then
      comma_weighted_germ_frontier_stop comma_round_germ_control_refines})
    then () else error "Round witness composition depends on an oracle";
\<close>

local_setup \<open>fn lthy => #2 (Local_Theory.note
  ((Binding.name "comma_round_smoke", []), [comma_round_smoke]) lthy)\<close>

end
