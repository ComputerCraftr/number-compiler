theory Comma_Semantic_B1_CRT_Local_Cover_Candidate
  imports Comma_Semantic_B1_CRT_Local_Cover
begin

theorem comma_semantic_b1_crt_lift_local_cover_candidate_matches:
  fixes sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and templates :: "comma_crt_column list list"
    and children :: "comma_finite_position \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and source :: comma_finite_position
    and parent :: comma_semantic_b1_crt_occurrence
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
  assumes witness:
      "comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
        occurrence_descriptors templates source parent refs descriptors"
    and parent_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed parent"
    and referenced_children_wellformed:
      "\<And>slot child_index lift_cid child. slot < length refs \<Longrightarrow>
        refs ! slot = Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
        occurrence_at child_index = Some child \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed child"
    and children_resolve:
      "\<And>i. i < length sources \<Longrightarrow>
        children (sources ! i) = occurrence_at i"
  shows "comma_semantic_b1_crt_occurrence_candidate_matches children source parent"
proof -
  let ?period = "comma_decisive_sector_period source"
  have source_base: "source = comma_source_continuation_base source"
    and source_admitted: "comma_round_admitted source"
    and refs_length: "length refs = ?period"
    and refs_slots:
      "map comma_semantic_b1_crt_lift_ref_slot refs = [0..<length refs]"
    and slots_valid:
      "list_all (comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
        occurrence_descriptors templates source parent refs descriptors)
        [0..<length refs]"
    using witness by (auto simp: comma_semantic_b1_crt_lift_local_cover_witness_def)
  have source_period_base:
      "comma_decisive_sector_period (comma_source_continuation_base source)
        \<in> comma_semantic_b1_crt_source_periods"
    by (rule comma_semantic_b1_generated_source_period_six[OF source_admitted])
  have source_period: "?period \<in> comma_semantic_b1_crt_source_periods"
    using source_period_base source_base by simp
  have period_positive: "0 < ?period"
    using source_period by (auto simp: comma_semantic_b1_crt_source_periods_def)
  show ?thesis
    unfolding comma_semantic_b1_crt_occurrence_candidate_matches_def
  proof (intro allI impI)
    fix clock :: nat
    assume clock_bound: "clock < 924"
    let ?slot = "clock mod ?period"
    let ?ref = "refs ! ?slot"
    have slot_bound: "?slot < ?period" using period_positive by simp
    have ref_bound: "?slot < length refs" using slot_bound refs_length by simp
    have slots_at:
        "(map comma_semantic_b1_crt_lift_ref_slot refs) ! ?slot =
          [0..<length refs] ! ?slot"
      by (rule arg_cong[OF refs_slots, where f="\<lambda>xs. xs ! ?slot"])
    have ref_slot:
        "comma_semantic_b1_crt_lift_ref_slot ?ref = ?slot"
      using slots_at ref_bound by (simp add: nth_map nth_upt)
    have slot_member: "?slot \<in> set [0..<length refs]"
      using ref_bound by simp
    have selected_slot_valid:
        "comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
          occurrence_descriptors templates source parent refs descriptors ?slot"
      using slots_valid slot_member by (simp add: list_all_iff)
    have base_slot_valid:
        "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
          occurrence_descriptors templates source parent refs descriptors ?slot"
      using selected_slot_valid
      by (simp add: comma_semantic_b1_crt_lift_local_slot_valid_def)
    show "comma_semantic_b1_crt_occurrence_lookup parent clock =
      comma_semantic_b1_crt_occurrence_local_step children source clock"
    proof (cases "\<exists>child shift.
        comma_semantic_b1_source_slot_action source ?slot =
          Comma_Continuation_Goto child shift")
      case True
      then obtain child shift where action:
          "comma_semantic_b1_source_slot_action source ?slot =
            Comma_Continuation_Goto child shift"
        by blast
      obtain child_index lift_cid where reference:
          "?ref = Comma_B1_Lift_Goto_Ref ?slot child_index lift_cid"
        using base_slot_valid ref_slot ref_bound slot_bound action source_base
        by (cases ?ref)
          (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
            split: option.splits)
      have child_present: "occurrence_at child_index \<noteq> None"
        using base_slot_valid reference action source_base ref_bound slot_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
            split: option.splits prod.splits)
      obtain child_occurrence where child_at:
          "occurrence_at child_index = Some child_occurrence"
        using child_present by (cases "occurrence_at child_index") auto
      have index_bound: "child_index < length sources"
        using base_slot_valid reference action source_base ref_bound slot_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def)
      have child_wellformed:
          "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
        by (rule referenced_children_wellformed
          [OF ref_bound reference child_at])
      have source_child:
          "sources ! child_index = comma_source_continuation_base child"
        using base_slot_valid reference action child_at source_base ref_bound slot_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
            split: option.splits prod.splits)
      have decrease:
          "shift = 0 \<and> child = comma_source_continuation_base child \<and>
           comma_round_admitted child \<and>
           9-comma_sector_number child < 9-comma_sector_number source"
        by (rule comma_semantic_b1_crt_occurrence_goto_decreases
          [OF source_base source_admitted slot_bound action])
      have source_child_eq: "sources ! child_index = child"
        using source_child decrease by simp
      have resolved_child:
          "children child = Some child_occurrence"
        using children_resolve[OF index_bound] child_at source_child_eq by simp
      have selected_slot: "clock mod ?period = ?slot" by simp
      have parent_lookup:
          "comma_semantic_b1_crt_occurrence_lookup parent clock =
            comma_semantic_b1_crt_occurrence_lookup child_occurrence
              ((clock + shift) mod 924)"
        by (rule comma_semantic_b1_crt_lift_local_goto_lookup
          [OF source_base source_period slot_bound ref_bound
            selected_slot reference action selected_slot_valid child_at child_wellformed
            parent_wellformed clock_bound])
      have local_step:
          "comma_semantic_b1_crt_occurrence_local_step children source clock =
            comma_semantic_b1_crt_occurrence_lookup child_occurrence
              ((clock + shift) mod 924)"
        using clock_bound action resolved_child selected_slot
        by (simp add: comma_semantic_b1_crt_occurrence_local_step_def)
      show ?thesis using parent_lookup local_step by simp
    next
      case False
      obtain result where terminal:
          "comma_semantic_b1_terminal_action_result
            (comma_semantic_b1_source_slot_action source ?slot) = Some result"
        using comma_semantic_b1_terminal_action_result_present[OF False] by blast
      obtain parent_index where reference:
          "?ref = Comma_B1_Lift_Terminal_Ref ?slot parent_index"
        using base_slot_valid ref_slot ref_bound slot_bound terminal source_base
        by (cases ?ref)
          (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
            split: option.splits comma_source_continuation_action.splits)
      have selected_ref: "refs ! ?slot = ?ref" by simp
      have selected_slot: "clock mod ?period = ?slot" by simp
      have base_slot_bound:
          "?slot < comma_decisive_sector_period (comma_source_continuation_base source)"
        using slot_bound source_base by simp
      have base_selected_slot:
          "clock mod comma_decisive_sector_period
             (comma_source_continuation_base source) = ?slot"
        using selected_slot source_base by simp
      have parent_lookup:
          "comma_semantic_b1_crt_occurrence_lookup parent clock = Some result"
        by (rule comma_semantic_b1_crt_lift_local_terminal_lookup
          [OF source_base source_period_base base_slot_bound ref_bound base_selected_slot reference
            selected_ref _ terminal selected_slot_valid parent_wellformed clock_bound])
          simp
      have local_step:
          "comma_semantic_b1_crt_occurrence_local_step children source clock =
            Some result"
        using clock_bound terminal selected_slot
        by (cases "comma_semantic_b1_source_slot_action source ?slot")
          (auto simp: comma_semantic_b1_crt_occurrence_local_step_def
            split: comma_source_continuation_action.splits)
      show ?thesis using parent_lookup local_step by simp
    qed
  qed
qed

ML \<open>Comma_Proof_Profile.report "Local cover stage=candidate-matches proof passed"\<close>

ML \<open>
  val _ = Thm.consolidate @{thms
    comma_semantic_b1_crt_lift_local_cover_rejects_truncated_refs
    comma_semantic_b1_crt_lift_local_terminal_lookup
    comma_semantic_b1_crt_lift_local_goto_lookup
    comma_semantic_b1_crt_lift_local_cover_candidate_matches}
  val _ = Comma_Local_Cover_Checkpoints.report "Local cover stage=candidate-matches"
\<close>


ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_semantic_b1_crt_find_result_index_sound
    comma_semantic_b1_crt_local_parent_column_some
    comma_semantic_b1_crt_local_piece_covered_sound
    comma_semantic_b1_crt_local_columns_disjoint_at
    comma_semantic_b1_crt_local_parent_lookup_from_column
    comma_semantic_b1_crt_local_piece_lookup
    comma_semantic_b1_crt_lift_local_cover_rejects_truncated_refs
    comma_semantic_b1_crt_lift_local_terminal_lookup
    comma_semantic_b1_crt_lift_local_goto_lookup
    comma_semantic_b1_crt_lift_local_cover_candidate_matches
  }) then ()
  else error "Comma_Semantic_B1_CRT_Local_Cover local oracle audit failed"
\<close>
end
