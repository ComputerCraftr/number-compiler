theory Double_Reverse_Joint_Lineage_Endpoint
  imports Double_Reverse_Joint_Lineage_Power
begin

text \<open>This layer connects the proved finite cyclic action fold to its exact
source endpoint and the complete binary observer.  The source-cycle theorem
remains separate from the endpoint application, so temporal powering is only
used after the ring and port phase recurrence has been established.\<close>

theorem double_reverse_ring_lineage_cycle_fold_exact_endpoint:
  assumes nonempty: "word \<noteq> []"
      and decimal:
        "double_reverse_ring_decimal
          (double_reverse_ring_inward_run cycle_start word)"
      and cycle:
        "double_reverse_ring_eventual_cycle cycle_start temporal_period word"
      and temporal: "temporal_period dvd joint_period"
      and spatial: "length word dvd joint_period"
      and joint_positive: "0 < joint_period"
      and extent: "cycle_start + copies * joint_period \<le> total_steps"
  shows "double_reverse_f5_apply
      (double_reverse_ring_lineage_cycle_fold word output_position total_steps
        cycle_start joint_period copies)
      (double_reverse_ring_digit
        (double_reverse_ring_inward_run cycle_start word)
        (output_position + total_steps - cycle_start) mod 5) =
    double_reverse_ring_digit
      (double_reverse_ring_inward_run
        (cycle_start + copies * joint_period) word)
      (output_position + total_steps - cycle_start - copies * joint_period) mod 5"
  using extent
proof (induction copies)
  case 0
  then show ?case
    by (simp add: double_reverse_f5_apply_def double_reverse_f5_identity_def
        double_reverse_f5_multiplier_def)
next
  case (Suc copies)
  have current_extent:
    "cycle_start + copies * joint_period + joint_period \<le> total_steps"
    using Suc.prems by (simp add: algebra_simps)
  have old_extent:
    "cycle_start + copies * joint_period \<le> total_steps"
    using current_extent joint_positive by arith
  have current_row:
    "double_reverse_ring_inward_run (cycle_start + copies * joint_period) word =
      double_reverse_ring_inward_run cycle_start word"
    using double_reverse_ring_eventual_shift_periodic
      [OF cycle dvd_mult[OF temporal], of 0]
    by simp
  have current_decimal:
    "double_reverse_ring_decimal
      (double_reverse_ring_inward_run (cycle_start + copies * joint_period) word)"
    using current_row decimal by (simp only: current_row decimal)
  have input_coordinate:
    "output_position + total_steps - (cycle_start + copies * joint_period) =
      output_position + total_steps - cycle_start - copies * joint_period"
    using old_extent by arith
  have output_coordinate:
    "output_position + total_steps - (cycle_start + copies * joint_period) -
        joint_period =
      output_position + total_steps - cycle_start - Suc copies * joint_period"
    using current_extent by (simp add: algebra_simps; arith)
  have segment:
    "double_reverse_f5_apply
        (double_reverse_ring_lineage_segment_action word output_position
          total_steps (cycle_start + copies * joint_period) joint_period)
        (double_reverse_ring_digit
          (double_reverse_ring_inward_run (cycle_start + copies * joint_period) word)
          (output_position + total_steps - (cycle_start + copies * joint_period)) mod 5) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + copies * joint_period + joint_period) word)
        (output_position + total_steps - (cycle_start + copies * joint_period) -
          joint_period) mod 5"
    by (rule double_reverse_ring_lineage_segment_refines_endpoint
      [OF nonempty current_decimal current_extent])
  have induction:
    "double_reverse_f5_apply
        (double_reverse_ring_lineage_cycle_fold word output_position total_steps
          cycle_start joint_period copies)
        (double_reverse_ring_digit
          (double_reverse_ring_inward_run cycle_start word)
          (output_position + total_steps - cycle_start) mod 5) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + copies * joint_period) word)
        (output_position + total_steps - cycle_start - copies * joint_period) mod 5"
    by (rule Suc.IH[OF old_extent])
  let ?previous_action =
    "double_reverse_ring_lineage_cycle_fold word output_position total_steps
      cycle_start joint_period copies"
  let ?segment_action =
    "double_reverse_ring_lineage_segment_action word output_position total_steps
      (cycle_start + copies * joint_period) joint_period"
  let ?initial_residue =
    "double_reverse_ring_digit (double_reverse_ring_inward_run cycle_start word)
      (output_position + total_steps - cycle_start) mod 5"
  let ?current_residue =
    "double_reverse_ring_digit
      (double_reverse_ring_inward_run (cycle_start + copies * joint_period) word)
      (output_position + total_steps - (cycle_start + copies * joint_period)) mod 5"
  let ?target_residue =
    "double_reverse_ring_digit
      (double_reverse_ring_inward_run (cycle_start + Suc copies * joint_period) word)
      (output_position + total_steps - cycle_start - Suc copies * joint_period) mod 5"
  have previous:
    "double_reverse_f5_apply ?previous_action ?initial_residue = ?current_residue"
  proof -
    have coordinate:
      "output_position + total_steps - cycle_start - copies * joint_period =
        output_position + total_steps - (cycle_start + copies * joint_period)"
      using input_coordinate[symmetric] .
    have input_transport:
      "double_reverse_ring_digit
          (double_reverse_ring_inward_run (cycle_start + copies * joint_period) word)
          (output_position + total_steps - cycle_start - copies * joint_period) mod 5 =
        double_reverse_ring_digit
          (double_reverse_ring_inward_run (cycle_start + copies * joint_period) word)
          (output_position + total_steps - (cycle_start + copies * joint_period)) mod 5"
      by (rule arg_cong[where f="\<lambda>index.
        double_reverse_ring_digit
          (double_reverse_ring_inward_run (cycle_start + copies * joint_period) word)
          index mod 5", OF coordinate])
    show ?thesis
      by (rule trans[OF induction input_transport])
  qed
  have transported:
    "double_reverse_f5_apply ?segment_action
        (double_reverse_f5_apply ?previous_action ?initial_residue) =
      double_reverse_f5_apply ?segment_action ?current_residue"
    by (rule arg_cong[where f="double_reverse_f5_apply ?segment_action",
        OF previous])
  have next_start:
    "cycle_start + copies * joint_period + joint_period =
      cycle_start + Suc copies * joint_period"
    by (simp add: algebra_simps)
  have next_row:
    "double_reverse_ring_inward_run
        (cycle_start + copies * joint_period + joint_period) word =
      double_reverse_ring_inward_run
        (cycle_start + Suc copies * joint_period) word"
    by (rule arg_cong[where f="\<lambda>start.
      double_reverse_ring_inward_run start word", OF next_start])
  have segment_row_transport:
    "double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + copies * joint_period + joint_period) word)
        (output_position + total_steps - (cycle_start + copies * joint_period) -
          joint_period) mod 5 =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + Suc copies * joint_period) word)
        (output_position + total_steps - (cycle_start + copies * joint_period) -
          joint_period) mod 5"
    by (rule arg_cong[where f="\<lambda>row.
      double_reverse_ring_digit row
        (output_position + total_steps - (cycle_start + copies * joint_period) -
          joint_period) mod 5", OF next_row])
  have segment_index_transport:
    "double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + Suc copies * joint_period) word)
        (output_position + total_steps - (cycle_start + copies * joint_period) -
          joint_period) mod 5 = ?target_residue"
    by (rule arg_cong[where f="\<lambda>index.
      double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + Suc copies * joint_period) word)
        index mod 5", OF output_coordinate])
  have segment_to_target:
    "double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + copies * joint_period + joint_period) word)
        (output_position + total_steps - (cycle_start + copies * joint_period) -
          joint_period) mod 5 = ?target_residue"
    by (rule trans[OF segment_row_transport segment_index_transport])
  have completed:
    "double_reverse_f5_apply
        (double_reverse_f5_then ?previous_action ?segment_action)
        ?initial_residue = ?target_residue"
  proof -
    have composition:
      "double_reverse_f5_apply
          (double_reverse_f5_then ?previous_action ?segment_action)
          ?initial_residue =
        double_reverse_f5_apply ?segment_action
          (double_reverse_f5_apply ?previous_action ?initial_residue)"
      by (rule double_reverse_f5_apply_then)
    have step:
      "double_reverse_f5_apply ?segment_action
          (double_reverse_f5_apply ?previous_action ?initial_residue) =
        ?target_residue"
      by (rule trans[OF transported])
        (rule trans[OF segment segment_to_target])
    show ?thesis by (rule trans[OF composition step])
  qed
  show ?case using completed
    by (simp only: double_reverse_ring_lineage_cycle_fold.simps completed)
qed

theorem double_reverse_ring_lineage_cycle_fold_applies_power:
  fixes output_position residue :: nat
  assumes nonempty: "word \<noteq> []"
      and cycle:
        "double_reverse_ring_eventual_cycle cycle_start temporal_period word"
      and temporal: "temporal_period dvd joint_period"
      and spatial: "length word dvd joint_period"
      and joint_positive: "0 < joint_period"
      and extent: "cycle_start + copies * joint_period \<le> total_steps"
  shows
  "double_reverse_f5_apply
      (double_reverse_ring_lineage_cycle_fold word output_position total_steps
        cycle_start joint_period copies) residue =
    double_reverse_f5_repeated_residue
      (double_reverse_ring_lineage_segment_action word output_position
        total_steps cycle_start joint_period)
      copies
      residue"
proof -
  have action:
    "double_reverse_ring_lineage_cycle_fold word output_position total_steps
        cycle_start joint_period copies =
      double_reverse_f5_action_power
        (double_reverse_ring_lineage_segment_action word output_position
          total_steps cycle_start joint_period) copies"
    by (rule double_reverse_ring_lineage_cycle_fold_power
      [OF nonempty cycle temporal spatial joint_positive extent])
  show ?thesis
    using action double_reverse_f5_action_power_exact[of
      "double_reverse_ring_lineage_segment_action word output_position
        total_steps cycle_start joint_period" copies residue]
    by (simp only: action double_reverse_f5_action_power_exact)
qed

theorem double_reverse_ring_lineage_powered_endpoint_exact:
  assumes nonempty: "word \<noteq> []"
      and decimal:
        "double_reverse_ring_decimal
          (double_reverse_ring_inward_run cycle_start word)"
      and cycle:
        "double_reverse_ring_eventual_cycle cycle_start temporal_period word"
      and temporal: "temporal_period dvd joint_period"
      and spatial: "length word dvd joint_period"
      and joint_positive: "0 < joint_period"
      and extent: "cycle_start + copies * joint_period \<le> total_steps"
  shows "double_reverse_f5_apply
      (double_reverse_f5_action_power
        (double_reverse_ring_lineage_segment_action word output_position
          total_steps cycle_start joint_period) copies)
      (double_reverse_ring_digit
        (double_reverse_ring_inward_run cycle_start word)
        (output_position + total_steps - cycle_start) mod 5) =
    double_reverse_ring_digit
      (double_reverse_ring_inward_run
        (cycle_start + copies * joint_period) word)
      (output_position + total_steps - cycle_start - copies * joint_period) mod 5"
proof -
  have fold_power:
    "double_reverse_ring_lineage_cycle_fold word output_position total_steps
        cycle_start joint_period copies =
      double_reverse_f5_action_power
        (double_reverse_ring_lineage_segment_action word output_position
          total_steps cycle_start joint_period) copies"
    by (rule double_reverse_ring_lineage_cycle_fold_power
      [OF nonempty cycle temporal spatial joint_positive extent])
  have endpoint:
    "double_reverse_f5_apply
        (double_reverse_ring_lineage_cycle_fold word output_position total_steps
          cycle_start joint_period copies)
        (double_reverse_ring_digit
          (double_reverse_ring_inward_run cycle_start word)
          (output_position + total_steps - cycle_start) mod 5) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + copies * joint_period) word)
        (output_position + total_steps - cycle_start - copies * joint_period) mod 5"
    by (rule double_reverse_ring_lineage_cycle_fold_exact_endpoint
      [OF nonempty decimal cycle temporal spatial joint_positive extent])
  show ?thesis using fold_power endpoint by (simp only: fold_power)
qed

theorem double_reverse_ring_lineage_binary_loop_endpoint_exact:
  fixes output_position :: nat
  assumes nonempty: "word \<noteq> []"
      and decimal:
        "double_reverse_ring_decimal
          (double_reverse_ring_inward_run cycle_start word)"
      and cycle:
        "double_reverse_ring_eventual_cycle cycle_start temporal_period word"
      and temporal: "temporal_period dvd joint_period"
      and spatial: "length word dvd joint_period"
      and joint_positive: "0 < joint_period"
      and extent:
        "cycle_start + copies * joint_period \<le> total_steps"
      and binary_loop:
        "transfer_binary_loop_reaches
          (Id,
            double_reverse_f5_action_graph
              (double_reverse_ring_lineage_segment_action word output_position
                total_steps cycle_start joint_period),
            copies)
          (accumulator, current, 0)"
  defines "initial_digit \<equiv>
      double_reverse_ring_digit
        (double_reverse_ring_inward_run cycle_start word)
        (output_position + total_steps - cycle_start)"
  shows
    "(double_reverse_f5_observer_origin (initial_digit mod 5),
       double_reverse_f5_advance_observer
         (double_reverse_f5_action_power
           (double_reverse_ring_lineage_segment_action word output_position
             total_steps cycle_start joint_period) copies)
         (double_reverse_f5_observer_origin (initial_digit mod 5)))
        \<in> accumulator"
    "double_reverse_f5_residue_value
       (double_reverse_f5_observer_residue
         (double_reverse_f5_advance_observer
           (double_reverse_f5_action_power
             (double_reverse_ring_lineage_segment_action word output_position
               total_steps cycle_start joint_period) copies)
             (double_reverse_f5_observer_origin (initial_digit mod 5)))) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + copies * joint_period) word)
        (output_position + total_steps - cycle_start - copies * joint_period)
        mod 5"
    "double_reverse_f5_offset
        (double_reverse_f5_action_power
          (double_reverse_ring_lineage_segment_action word output_position
            total_steps cycle_start joint_period) copies) mod 5 =
      double_reverse_f5_weighted_phase_sum
        (double_reverse_f5_action_power
          (double_reverse_ring_lineage_segment_action word output_position
            total_steps cycle_start joint_period) copies)"
proof -
  let ?action =
    "double_reverse_ring_lineage_segment_action word output_position
      total_steps cycle_start joint_period"
  let ?origin = "double_reverse_f5_observer_origin (initial_digit mod 5)"
  let ?result = "double_reverse_f5_advance_observer
      (double_reverse_f5_action_power ?action copies) ?origin"
  have binary_observer: "(?origin, ?result) \<in> accumulator"
    by (rule double_reverse_f5_binary_loop_complete_observer[OF binary_loop])
  have endpoint:
    "double_reverse_f5_apply (double_reverse_f5_action_power ?action copies)
        (initial_digit mod 5) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + copies * joint_period) word)
        (output_position + total_steps - cycle_start - copies * joint_period)
        mod 5"
    unfolding initial_digit_def
    by (rule double_reverse_ring_lineage_powered_endpoint_exact
      [OF nonempty decimal cycle temporal spatial joint_positive extent])
  have source_weighted:
    "double_reverse_f5_offset ?action mod 5 =
      double_reverse_f5_weighted_phase_sum ?action"
    unfolding double_reverse_ring_lineage_segment_action_def Let_def
    by (rule double_reverse_f5_open_trace_offset_weighted)
  have powered_weighted:
    "double_reverse_f5_offset
        (double_reverse_f5_action_power ?action copies) mod 5 =
      double_reverse_f5_weighted_phase_sum
        (double_reverse_f5_action_power ?action copies)"
    by (rule double_reverse_f5_action_power_weighted_phase_exact
      [OF source_weighted])
  have initial_decode:
    "double_reverse_f5_residue_value
        (double_reverse_f5_residue_of_value (initial_digit mod 5)) =
      initial_digit mod 5"
  proof -
    have decoded:
      "double_reverse_f5_residue_value
          (double_reverse_f5_residue_of_value (initial_digit mod 5)) =
        (initial_digit mod 5) mod 5"
      by (rule double_reverse_f5_value_roundtrip)
    show ?thesis using decoded by (simp only: mod_mod_trivial)
  qed
  have result_decode:
    "double_reverse_f5_residue_value
        (double_reverse_f5_residue_of_value
          (double_reverse_f5_apply
            (double_reverse_f5_action_power ?action copies)
            (initial_digit mod 5))) =
      double_reverse_f5_apply
        (double_reverse_f5_action_power ?action copies)
        (initial_digit mod 5)"
  proof -
    have decoded:
      "double_reverse_f5_residue_value
          (double_reverse_f5_residue_of_value
            (double_reverse_f5_apply
              (double_reverse_f5_action_power ?action copies)
              (initial_digit mod 5))) =
        double_reverse_f5_apply
          (double_reverse_f5_action_power ?action copies)
          (initial_digit mod 5) mod 5"
      by (rule double_reverse_f5_value_roundtrip)
    show ?thesis
      using decoded
      by (simp only: double_reverse_f5_apply_def mod_mod_trivial)
  qed
  have observed_endpoint:
    "double_reverse_f5_residue_value
        (double_reverse_f5_observer_residue ?result) =
      double_reverse_f5_apply
        (double_reverse_f5_action_power ?action copies)
        (initial_digit mod 5)"
    by (simp only: double_reverse_f5_advance_observer_def
        double_reverse_f5_observer_origin_def
        double_reverse_f5_observer_state.select_convs
        initial_decode result_decode)
  show "(?origin, ?result) \<in> accumulator"
    by (rule binary_observer)
  show "double_reverse_f5_residue_value
      (double_reverse_f5_observer_residue ?result) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run
          (cycle_start + copies * joint_period) word)
        (output_position + total_steps - cycle_start - copies * joint_period)
        mod 5"
    by (rule trans[OF observed_endpoint endpoint])
  show "double_reverse_f5_offset
      (double_reverse_f5_action_power ?action copies) mod 5 =
      double_reverse_f5_weighted_phase_sum
        (double_reverse_f5_action_power ?action copies)"
    by (rule powered_weighted)
qed

ML \<open>
  val checked = @{thms double_reverse_ring_lineage_cycle_fold_exact_endpoint
    double_reverse_ring_lineage_cycle_fold_applies_power
    double_reverse_ring_lineage_powered_endpoint_exact
    double_reverse_ring_lineage_binary_loop_endpoint_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse lineage endpoint depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse lineage endpoint proof" else ();
\<close>

end
