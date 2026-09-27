val (comma_round_phase_slice, comma_export_phase_metrics) =
let
  val comma_slice_generation = getenv "NUMBER_COMPILER_PROOF_GENERATION";
  val (comma_slice_close, comma_slice_stats) = Comma_Round_Witness.make_round_observation_owned @{context}
    {generation = comma_slice_generation,
      current_generation = fn () => getenv "NUMBER_COMPILER_PROOF_GENERATION"};
  val comma_phase_initial_stats = comma_slice_stats ();
  val comma_phase_five_timer = Timing.start ();
  val comma_phase_five_normalizer = put_simpset HOL_basic_ss @{context} addsimps
    @{thms One_nat_def[symmetric] Suc_1 Suc_numeral add_num_simps};

  fun comma_phase_five_check (offset, expected) =
    let
      val actual = comma_slice_close comma_round_candidate_phase offset RS @{thm eq_reflection}
      val (control_left, right) = HOLogic.dest_eq (HOLogic.dest_Trueprop expected)
      val (head, arguments) = strip_comb control_left
      val _ = if head aconv @{term comma_round_close} andalso length arguments = 2
        then () else error "Unexpected phase candidate observation shape"
      val left = list_comb (@{term comma_round_observation}, arguments)
      val expected_observation = HOLogic.mk_Trueprop (HOLogic.mk_eq (left, right))
      val _ = if Thm.term_of (Thm.lhs_of actual) aconv left then ()
        else error "Phase slice source/index mismatch"
      val actual_result = Simplifier.rewrite comma_phase_five_normalizer
        (Thm.rhs_of actual)
      val expected_result = Simplifier.rewrite comma_phase_five_normalizer
        (Thm.cterm_of @{context} right)
      val checked = Thm.transitive actual (Thm.transitive actual_result
        (Thm.symmetric expected_result)) RS @{thm meta_eq_to_obj_eq}
      val _ = if Thm.prop_of checked aconv expected_observation andalso
          Thm.nprems_of checked = 0 andalso null (Thm.hyps_of checked)
        then () else error "Phase slice is not the exact closed candidate equation"
    in checked end;

  val _ = if length comma_round_phase_candidates = 91 then ()
    else error "Phase slice must cover every offset 0 through 90";
  val comma_round_phase_slice =
    map_index comma_phase_five_check comma_round_phase_candidates;
  val _ = warning ("Comma phase slice 91-offset check: " ^
    Timing.message (Timing.result comma_phase_five_timer));
  val _ = warning ("Comma phase slice caches: " ^
    @{make_string} (comma_slice_stats ()));

  (* Snapshot while the owner still has generation authority. The exported
     formatter retains only immutable measurements, never evaluator closures. *)
  val comma_phase_final_stats = comma_slice_stats ();
val _ = if #control_reconstructions comma_phase_final_stats = 0 andalso
    #weighted_exports comma_phase_final_stats = 0 andalso
    #terminal_payloads comma_phase_final_stats = 0 andalso
    #normalization_calls comma_phase_final_stats = 0
  then () else error "Rank observation constructed a full weighted payload";
  fun comma_export_phase_metrics final_audit =
    let
      val stats = comma_phase_final_stats
      val initial = comma_phase_initial_stats
      val oracle = #oracle_audit stats
      val initial_oracle = #oracle_audit initial
      val total = Timing.result comma_phase_five_timer
      fun count key value = key ^ "=" ^ Int.toString value ^ "\n"
      fun millis key value = key ^ "=" ^ LargeInt.toString value ^ "\n"
      val generation = comma_slice_generation
      val _ = if getenv "NUMBER_COMPILER_PROOF_GENERATION" = generation then ()
        else error "Proof generation changed after phase construction; metrics export refused"
      val _ = if forall (fn c => Char.isPrint c andalso c <> #"=")
          (String.explode generation) then ()
        else error "Invalid proof-generation token in metrics"
      val text =
        "proof_generation=" ^ (if generation = "" then "unbound" else generation) ^ "\n" ^
        "germ_scope=weighted_constructor_control_projection\n" ^
        "full_sector_round_weight_refinement=generic_weighted_round_theorem\n" ^
        "guard_pullback_compositions=unavailable\n" ^
        "guard_family_before_reduction=unavailable\n" ^
        "guard_family_after_reduction=unavailable\n" ^
        count "phase" comma_round_candidate_phase ^
        count "states" (length comma_round_phase_slice) ^
        millis "elapsed_ms" (Time.toMilliseconds (#elapsed total)) ^
        millis "cpu_ms" (Time.toMilliseconds (#cpu total)) ^
        millis "final_audit_ms" (Time.toMilliseconds final_audit) ^
        count "initial_entry_representatives" (#entry_steps initial) ^
        count "final_entry_representatives" (#entry_steps stats) ^
        count "representative_hits" (#representative_hits stats - #representative_hits initial) ^
        count "representative_misses" (#representative_misses stats - #representative_misses initial) ^
        count "short_key_reductions" (#short_key_reductions stats - #short_key_reductions initial) ^
        count "power_invocations" (#power_invocations stats - #power_invocations initial) ^
      count "entry_conversions" (#entry_conversions stats - #entry_conversions initial) ^
      count "near_conversions" (#near_conversions stats - #near_conversions initial) ^
      millis "entry_conversion_ms" (#entry_conversion_milliseconds stats - #entry_conversion_milliseconds initial) ^
      millis "near_conversion_ms" (#near_conversion_milliseconds stats - #near_conversion_milliseconds initial) ^
        count "initial_near_steps" (#near_steps initial) ^
        count "final_near_steps" (#near_steps stats) ^
        count "initial_near_germs" (#near_germs initial) ^
        count "final_near_germs" (#near_germs stats) ^
        count "near_germ_hits" (#germ_hits stats - #germ_hits initial) ^
        count "near_germ_misses" (#germ_misses stats - #germ_misses initial) ^
        count "weighted_sector_compositions" (#sector_compositions stats - #sector_compositions initial) ^
        count "max_weighted_sector_compositions" (#max_sector_compositions stats) ^
        count "round_exports" (#round_exports stats - #round_exports initial) ^
        count "control_reconstructions" (#control_reconstructions stats - #control_reconstructions initial) ^
        count "weighted_exports" (#weighted_exports stats - #weighted_exports initial) ^
      count "observation_exports" (#observation_exports stats - #observation_exports initial) ^
      count "observation_sectors" (#observation_sectors stats - #observation_sectors initial) ^
      count "observation_max_sectors" (#observation_max_sectors stats) ^
      count "observation_links" (#observation_links stats - #observation_links initial) ^
      count "observation_normalizations" (#observation_normalizations stats - #observation_normalizations initial) ^
      millis "observation_evaluation_ms" (#observation_milliseconds stats - #observation_milliseconds initial) ^
      millis "observation_normalization_ms" (#observation_normalization_milliseconds stats - #observation_normalization_milliseconds initial) ^
      count "field_projections" (#selector_calls stats - #selector_calls initial) ^
      millis "field_projection_ms" (#selector_milliseconds stats - #selector_milliseconds initial) ^
      count "join_compatibility_normalizations" (#compatibility_calls stats - #compatibility_calls initial) ^
      millis "join_compatibility_ms" (#compatibility_milliseconds stats - #compatibility_milliseconds initial) ^
        count "terminal_payloads" (#terminal_payloads stats) ^
        count "terminal_hits" (#terminal_hits stats - #terminal_hits initial) ^
        count "terminal_misses" (#terminal_misses stats - #terminal_misses initial) ^
        count "scalar_normalizations" (#scalar_normalizations stats - #scalar_normalizations initial) ^
        count "owner_memo_retained_rounds" (#retained_rounds stats) ^
        count "slice_retained_equations" (length comma_round_phase_slice) ^
        millis "weighted_round_fold_ms" (#round_milliseconds stats - #round_milliseconds initial) ^
        millis "weighted_request_ms" (#request_milliseconds stats - #request_milliseconds initial) ^
        count "normalization_calls" (#normalization_calls stats - #normalization_calls initial) ^
        millis "normalization_ms" (#normalization_milliseconds stats - #normalization_milliseconds initial) ^
        millis "short_key_ms" (#short_key_milliseconds stats - #short_key_milliseconds initial) ^
        millis "round_composition_ms" (#composition_milliseconds stats - #composition_milliseconds initial) ^
        count "oracle_calls" (#calls oracle - #calls initial_oracle) ^
        count "oracle_failed_calls" (#failed_calls oracle - #failed_calls initial_oracle) ^
        count "initial_oracle_nodes" (#nodes initial_oracle) ^
        count "final_oracle_nodes" (#nodes oracle) ^
        millis "incremental_oracle_ms" (#milliseconds oracle - #milliseconds initial_oracle)
    in Export.export @{theory} (Path.explode_binding0 "comma-phase-metrics.txt")
      [XML.Text text] end;

in (comma_round_phase_slice, comma_export_phase_metrics) end;
