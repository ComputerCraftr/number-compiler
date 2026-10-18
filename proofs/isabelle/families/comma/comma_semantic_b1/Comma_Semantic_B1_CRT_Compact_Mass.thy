theory Comma_Semantic_B1_CRT_Compact_Mass
  imports Comma_Semantic_B1_CRT_Compact_Refinement
    Comma_Semantic_B1_CRT_Constructor_Mass
    Comma_Semantic_B1_CRT_Cover_Mass
begin

text \<open>
The compact occurrence certificate gives pointwise parent coverage.  A
terminal slot selects its result column directly; a goto slot transports a
covered child column through its authenticated lift.  Template mass then
turns that coverage into the occurrence partition without rebuilding the
per-result construction-piece table.
\<close>

lemma comma_semantic_b1_crt_compact_occurrence_shifted_coverage:
  fixes templates :: "comma_crt_column list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and lift_refs :: "comma_semantic_b1_crt_lift_ref list list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and index phase :: nat
    and parent :: comma_semantic_b1_crt_occurrence
  assumes checked:
      "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
        occurrence_descriptors lift_refs lift_descriptors index"
    and occurrence: "occurrence_at index = Some parent"
    and earlier_wellformed:
      "\<And>child_index child. child_index < index \<Longrightarrow>
        occurrence_at child_index = Some child \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed child"
    and phase_bound: "phase < 924"
  shows "\<exists>parent_index <
      length (comma_semantic_b1_crt_occurrence_columns parent).
    comma_crt_eval phase
      (comma_crt_shift (comma_semantic_b1_crt_occurrence_rebase parent)
        (comma_semantic_b1_crt_occurrence_columns parent ! parent_index))"
proof -
  let ?source = "sources!index"
  let ?refs = "lift_refs!index"
  let ?period = "comma_decisive_sector_period ?source"
  have refs_bound: "index < length lift_refs"
    using checked
    by (auto simp: comma_semantic_b1_crt_compact_occurrence_check_def
        split: if_splits option.splits)
  have exposed:
      "?source = comma_source_continuation_base ?source \<and>
       comma_round_admitted ?source \<and>
       comma_semantic_b1_crt_occurrence_binding_check parent \<and>
       (fst (occurrence_descriptors!index) < length templates \<and>
        fst (snd (occurrence_descriptors!index)) =
          comma_semantic_b1_crt_occurrence_rebase parent \<and>
        snd (snd (occurrence_descriptors!index)) =
          comma_semantic_b1_crt_occurrence_beta parent \<and>
        comma_semantic_b1_crt_occurrence_columns parent =
          templates ! fst (occurrence_descriptors!index)) \<and>
       list_all comma_crt_supported
         (comma_semantic_b1_crt_occurrence_columns parent) \<and>
       comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
         occurrence_descriptors templates ?source parent ?refs lift_descriptors \<and>
       list_all (\<lambda>slot. case ?refs!slot of
          Comma_B1_Lift_Terminal_Ref ref_slot _ \<Rightarrow> ref_slot = slot
        | Comma_B1_Lift_Goto_Ref ref_slot child_index _ \<Rightarrow>
            ref_slot = slot \<and> child_index < index)
          [0..<length ?refs]"
    by (rule comma_semantic_b1_crt_compact_occurrence_check_exposes
      [OF checked occurrence])
  have normalized: "?source = comma_source_continuation_base ?source"
    and source_admitted: "comma_round_admitted ?source"
    and witness:
      "comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
        occurrence_descriptors templates ?source parent ?refs lift_descriptors"
    and refs_order:
      "list_all (\<lambda>slot. case ?refs!slot of
          Comma_B1_Lift_Terminal_Ref ref_slot _ \<Rightarrow> ref_slot = slot
        | Comma_B1_Lift_Goto_Ref ref_slot child_index _ \<Rightarrow>
            ref_slot = slot \<and> child_index < index)
          [0..<length ?refs]"
    using exposed by blast+
  have source_period_base:
      "comma_decisive_sector_period (comma_source_continuation_base ?source)
        \<in> comma_semantic_b1_crt_source_periods"
    by (rule comma_semantic_b1_generated_source_period_six[OF source_admitted])
  have source_period: "?period \<in> comma_semantic_b1_crt_source_periods"
    using source_period_base normalized by simp
  have period_positive: "0 < ?period"
    using source_period by (auto simp: comma_semantic_b1_crt_source_periods_def)
  have refs_length: "length ?refs = ?period"
    using witness normalized
    by (auto simp: comma_semantic_b1_crt_lift_local_cover_witness_def)
  have slots_valid:
      "list_all (comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
        occurrence_descriptors templates ?source parent ?refs lift_descriptors)
        [0..<length ?refs]"
    using witness by (auto simp: comma_semantic_b1_crt_lift_local_cover_witness_def)
  let ?slot = "phase mod ?period"
  have slot_bound: "?slot < ?period" using period_positive by simp
  have ref_bound: "?slot < length ?refs" using slot_bound refs_length by simp
  have slot_member: "?slot \<in> set [0..<length ?refs]"
    using ref_bound by simp
  have slot_valid:
      "comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
        occurrence_descriptors templates ?source parent ?refs lift_descriptors ?slot"
    using slots_valid slot_member by (simp add: list_all_iff)
  have base_slot_valid:
      "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
        occurrence_descriptors templates ?source parent ?refs lift_descriptors ?slot"
    using slot_valid
    by (simp add: comma_semantic_b1_crt_lift_local_slot_valid_def)
  have slots_equation:
      "map comma_semantic_b1_crt_lift_ref_slot ?refs = [0..<length ?refs]"
    using witness by (auto simp: comma_semantic_b1_crt_lift_local_cover_witness_def)
  have selected_slot:
      "phase mod comma_decisive_sector_period
          (comma_source_continuation_base ?source) = ?slot"
    using normalized by simp
  have selected_slot_source:
      "phase mod comma_decisive_sector_period ?source = ?slot"
    using normalized selected_slot by simp
  have base_slot_bound:
      "?slot < comma_decisive_sector_period
        (comma_source_continuation_base ?source)"
    using slot_bound normalized by simp
  have ref_slot: "comma_semantic_b1_crt_lift_ref_slot (?refs!?slot) = ?slot"
  proof -
    have nth_slots:
        "(map comma_semantic_b1_crt_lift_ref_slot ?refs)!?slot =
          [0..<length ?refs]!?slot"
      by (rule arg_cong[OF slots_equation, where f="\<lambda>xs. xs!?slot"])
    show ?thesis using nth_slots ref_bound by (simp add: nth_map nth_upt)
  qed
  show ?thesis
  proof (cases "\<exists>child shift. comma_semantic_b1_source_slot_action
      ?source ?slot = Comma_Continuation_Goto child shift")
    case True
    then obtain child shift where action:
        "comma_semantic_b1_source_slot_action ?source ?slot =
          Comma_Continuation_Goto child shift"
      by blast
    obtain child_index lift_cid where reference:
        "?refs!?slot = Comma_B1_Lift_Goto_Ref ?slot child_index lift_cid"
      using base_slot_valid ref_slot ref_bound slot_bound action normalized
      by (cases "?refs!?slot")
        (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
          split: option.splits prod.splits)
    have selected_order:
        "case ?refs!?slot of
          Comma_B1_Lift_Terminal_Ref ref_slot _ \<Rightarrow> ref_slot = ?slot
        | Comma_B1_Lift_Goto_Ref ref_slot child_index _ \<Rightarrow>
            ref_slot = ?slot \<and> child_index < index"
      using refs_order slot_member unfolding list_all_iff by blast
    have order_facts: "child_index < index"
      using selected_order by (simp add: reference)
    have child_present: "occurrence_at child_index \<noteq> None"
      using base_slot_valid reference action normalized ref_bound slot_bound
      by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
          split: option.splits prod.splits)
    then obtain child_occurrence where child_at:
        "occurrence_at child_index = Some child_occurrence"
      by (cases "occurrence_at child_index") auto
    have child_wellformed:
        "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
      by (rule earlier_wellformed[OF order_facts child_at])
    obtain parent_index result where parent_index:
        "parent_index < length (comma_semantic_b1_crt_occurrence_columns parent)"
      and active:
        "comma_crt_eval phase
          (comma_crt_shift (comma_semantic_b1_crt_occurrence_rebase parent)
            (comma_semantic_b1_crt_occurrence_columns parent ! parent_index))"
      using comma_semantic_b1_crt_lift_local_goto_parent_active
        [OF normalized source_period slot_bound ref_bound selected_slot_source reference
          action slot_valid child_at child_wellformed phase_bound]
      by blast
    show ?thesis using parent_index active by blast
  next
    case False
    then obtain result where terminal:
        "comma_semantic_b1_terminal_action_result
          (comma_semantic_b1_source_slot_action ?source ?slot) = Some result"
      using comma_semantic_b1_terminal_action_result_present[OF False] by blast
    have slot_action:
        "comma_semantic_b1_source_slot_action ?source ?slot =
          comma_semantic_b1_source_slot_action ?source ?slot"
      by simp
    obtain parent_index where reference:
        "?refs!?slot = Comma_B1_Lift_Terminal_Ref ?slot parent_index"
      using base_slot_valid ref_slot ref_bound slot_bound terminal normalized
      by (cases "?refs!?slot")
        (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
          split: option.splits prod.splits comma_source_continuation_action.splits)
    have reference_refl:
        "Comma_B1_Lift_Terminal_Ref ?slot parent_index =
          Comma_B1_Lift_Terminal_Ref ?slot parent_index"
      by simp
    obtain selected where selected:
        "selected < length (comma_semantic_b1_crt_occurrence_columns parent)"
      and active:
        "comma_crt_eval phase
          (comma_crt_shift (comma_semantic_b1_crt_occurrence_rebase parent)
            (comma_semantic_b1_crt_occurrence_columns parent ! selected))"
      using comma_semantic_b1_crt_lift_local_terminal_parent_active
        [OF normalized source_period_base base_slot_bound ref_bound selected_slot
          reference_refl reference slot_action terminal slot_valid phase_bound]
      by blast
    show ?thesis using selected active by blast
  qed
qed

lemma comma_semantic_b1_crt_compact_occurrence_raw_coverage:
  fixes templates :: "comma_crt_column list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and lift_refs :: "comma_semantic_b1_crt_lift_ref list list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and index :: nat
    and parent :: comma_semantic_b1_crt_occurrence
  assumes checked:
      "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
        occurrence_descriptors lift_refs lift_descriptors index"
    and occurrence: "occurrence_at index = Some parent"
    and earlier_wellformed:
      "\<And>child_index child. child_index < index \<Longrightarrow>
        occurrence_at child_index = Some child \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed child"
    and parent_admitted:
      "list_all (comma_crt_admitted 0)
        (comma_semantic_b1_crt_occurrence_columns parent)"
  shows "\<forall>phase<924. \<exists>column_index <
      length (comma_semantic_b1_crt_occurrence_columns parent).
    comma_crt_eval phase
      (comma_semantic_b1_crt_occurrence_columns parent ! column_index)"
proof (intro allI impI)
  fix target :: nat
  assume target_bound: "target < 924"
  let ?rebase = "comma_semantic_b1_crt_occurrence_rebase parent"
  let ?phase = "(target + comma_semantic_b1_inverse_shift ?rebase) mod 924"
  have phase_rebase: "(?phase + ?rebase) mod 924 = target"
    using comma_semantic_b1_inverse_shift_cancel_right[of target ?rebase]
      target_bound by simp
  have phase_bound: "?phase < 924" by simp
  have shifted_coverage:
      "\<exists>column_index < length (comma_semantic_b1_crt_occurrence_columns parent).
        comma_crt_eval ?phase
          (comma_crt_shift ?rebase
            (comma_semantic_b1_crt_occurrence_columns parent ! column_index))"
  proof (rule comma_semantic_b1_crt_compact_occurrence_shifted_coverage
      [OF checked occurrence _ phase_bound])
    fix child_index child
    assume child_lt: "child_index < index"
      and child_at: "occurrence_at child_index = Some child"
    show "comma_semantic_b1_crt_occurrence_wellformed child"
      by (rule earlier_wellformed[OF child_lt child_at])
  qed
  obtain column_index where column_bound:
      "column_index < length (comma_semantic_b1_crt_occurrence_columns parent)"
    and shifted_active:
      "comma_crt_eval ?phase
        (comma_crt_shift ?rebase
          (comma_semantic_b1_crt_occurrence_columns parent ! column_index))"
    using shifted_coverage by blast
  have selected_admitted:
      "comma_crt_admitted 0
        (comma_semantic_b1_crt_occurrence_columns parent ! column_index)"
    using parent_admitted column_bound nth_mem[OF column_bound]
    by (auto simp: list_all_iff)
  have shifted_refines:
      "comma_crt_eval ?phase
        (comma_crt_shift ?rebase
          (comma_semantic_b1_crt_occurrence_columns parent ! column_index)) =
       comma_crt_eval (?phase + ?rebase)
          (comma_semantic_b1_crt_occurrence_columns parent ! column_index)"
    by (rule comma_crt_shift_refines[OF selected_admitted])
  have periodic:
      "comma_crt_eval ((?phase + ?rebase) mod 924)
          (comma_semantic_b1_crt_occurrence_columns parent ! column_index) =
       comma_crt_eval (?phase + ?rebase)
          (comma_semantic_b1_crt_occurrence_columns parent ! column_index)"
    by (rule comma_crt_eval_periodic[OF selected_admitted])
  have active:
      "comma_crt_eval target
        (comma_semantic_b1_crt_occurrence_columns parent ! column_index)"
    using shifted_active shifted_refines periodic phase_rebase by simp
  show "\<exists>column_index <
      length (comma_semantic_b1_crt_occurrence_columns parent).
    comma_crt_eval target
      (comma_semantic_b1_crt_occurrence_columns parent ! column_index)"
    using column_bound active by blast
qed

lemma comma_semantic_b1_crt_compact_occurrences_wellformed_from_mass:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and lift_refs :: "comma_semantic_b1_crt_lift_ref list list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
  assumes table_admitted: "list_all (comma_crt_admitted 0) columns"
    and descriptor_extent: "length occurrence_descriptors = length sources"
    and used_template_masses:
      "list_all (comma_semantic_b1_crt_template_mass_certified
        columns templates template_column_ids)
        (remdups (map fst occurrence_descriptors))"
    and compact:
      "list_all (\<lambda>index.
        comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
          occurrence_descriptors lift_refs lift_descriptors index)
        [0..<length sources]"
  shows "\<forall>index<length sources. \<forall>parent.
    occurrence_at index = Some parent \<longrightarrow>
    comma_semantic_b1_crt_occurrence_wellformed parent"
proof -
  have used_mass_at:
      "\<And>index. index < length sources \<Longrightarrow>
        comma_semantic_b1_crt_template_mass_certified columns templates
          template_column_ids (fst (occurrence_descriptors!index))"
    by (rule comma_semantic_b1_crt_used_template_masses_cover_sources
      [OF descriptor_extent used_template_masses])
  have all_wellformed:
      "\<forall>index<length sources. \<forall>parent.
        occurrence_at index = Some parent \<longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed parent"
  proof (rule allI)
    fix index
    show "index < length sources \<longrightarrow>
        (\<forall>parent. occurrence_at index = Some parent \<longrightarrow>
          comma_semantic_b1_crt_occurrence_wellformed parent)"
    proof (induction index rule: less_induct)
      case (less index)
      show ?case
      proof
        assume index_source: "index < length sources"
        show "\<forall>parent. occurrence_at index = Some parent \<longrightarrow>
            comma_semantic_b1_crt_occurrence_wellformed parent"
        proof (intro allI impI)
          fix parent assume parent_at: "occurrence_at index = Some parent"
        have check:
            "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
              occurrence_descriptors lift_refs lift_descriptors index"
        proof -
          have member: "index \<in> set [0..<length sources]"
            using index_source by simp
          show ?thesis using compact member by (auto simp: list_all_iff)
        qed
        have exposed:
            "sources!index = comma_source_continuation_base (sources!index) \<and>
             comma_round_admitted (sources!index) \<and>
             comma_semantic_b1_crt_occurrence_binding_check parent \<and>
             (fst (occurrence_descriptors!index) < length templates \<and>
              fst (snd (occurrence_descriptors!index)) =
                comma_semantic_b1_crt_occurrence_rebase parent \<and>
              snd (snd (occurrence_descriptors!index)) =
                comma_semantic_b1_crt_occurrence_beta parent \<and>
              comma_semantic_b1_crt_occurrence_columns parent =
                templates ! fst (occurrence_descriptors!index)) \<and>
             list_all comma_crt_supported
               (comma_semantic_b1_crt_occurrence_columns parent) \<and>
             comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
               occurrence_descriptors templates (sources!index) parent (lift_refs!index)
               lift_descriptors \<and>
             list_all (\<lambda>slot. case (lift_refs!index)!slot of
                Comma_B1_Lift_Terminal_Ref ref_slot _ \<Rightarrow> ref_slot = slot
              | Comma_B1_Lift_Goto_Ref ref_slot child_index _ \<Rightarrow>
                  ref_slot = slot \<and> child_index < index)
                [0..<length (lift_refs!index)]"
          by (rule comma_semantic_b1_crt_compact_occurrence_check_exposes
            [OF check parent_at])
        obtain template_cid where template_cid:
            "template_cid = fst (occurrence_descriptors!index)"
          by blast
        have mass:
            "comma_semantic_b1_crt_template_mass_certified columns templates
              template_column_ids template_cid"
          using used_mass_at[OF index_source] template_cid by simp
        have mass_facts:
            "template_cid < length templates \<and>
             template_cid < length template_column_ids \<and>
             comma_semantic_b1_crt_column_ids_resolve columns
               (template_column_ids!template_cid) (templates!template_cid) \<and>
             sum_list (map comma_semantic_b1_crt_column_mass
               (templates!template_cid))=924"
          using mass by (simp add: comma_semantic_b1_crt_template_mass_certified_def)
        have resolved:
            "comma_semantic_b1_crt_column_ids_resolve columns
              (template_column_ids!template_cid) (templates!template_cid)"
          using mass_facts by blast
        have mapped_admitted:
            "list_all (comma_crt_admitted 0)
              (map (\<lambda>cid. columns!cid) (template_column_ids!template_cid))"
          by (rule comma_semantic_b1_crt_column_ids_resolve_preserves_list_all
            [OF table_admitted resolved])
        have resolved_map:
            "map (\<lambda>cid. columns!cid) (template_column_ids!template_cid) =
              templates!template_cid"
          by (rule comma_semantic_b1_crt_column_ids_resolve_map[OF resolved])
        have template_admitted:
            "list_all (comma_crt_admitted 0) (templates!template_cid)"
          using mapped_admitted by (simp add: resolved_map)
        have parent_template:
            "comma_semantic_b1_crt_occurrence_columns parent = templates!template_cid"
          using exposed template_cid by blast
        have parent_admitted:
            "list_all (comma_crt_admitted 0)
              (comma_semantic_b1_crt_occurrence_columns parent)"
          using template_admitted parent_template by simp
        have parent_covered:
            "\<forall>phase<924. \<exists>column_index <
              length (comma_semantic_b1_crt_occurrence_columns parent).
              comma_crt_eval phase
                (comma_semantic_b1_crt_occurrence_columns parent ! column_index)"
        proof (rule comma_semantic_b1_crt_compact_occurrence_raw_coverage
          [OF check parent_at _ parent_admitted])
          fix child_index child
          assume child_lt: "child_index < index"
            and child_at: "occurrence_at child_index = Some child"
          have child_index_bound: "child_index < length sources"
            by (rule less_trans[OF child_lt index_source])
          show "comma_semantic_b1_crt_occurrence_wellformed child"
            using less.IH[OF child_lt] child_index_bound child_at by blast
        qed
        have template_mass:
            "sum_list (map comma_semantic_b1_crt_column_mass
              (comma_semantic_b1_crt_occurrence_columns parent))=924"
          using mass by (simp add: comma_semantic_b1_crt_template_mass_certified_def
              parent_template template_cid)
        have parent_partition:
            "comma_semantic_b1_crt_cells_partition {..<924}
              (map comma_crt_set
                (comma_semantic_b1_crt_occurrence_columns parent))"
          by (rule comma_semantic_b1_crt_cells_partition_from_eval_cover_mass
            [OF parent_admitted parent_covered template_mass])
        have binding:
            "comma_semantic_b1_crt_occurrence_binding_check parent"
          using exposed by blast
        have supported:
            "list_all comma_crt_supported
              (comma_semantic_b1_crt_occurrence_columns parent)"
          using exposed by blast
        show "comma_semantic_b1_crt_occurrence_wellformed parent"
          by (rule comma_semantic_b1_crt_occurrence_wellformed_from_partition
            [OF binding parent_admitted supported parent_partition])
        qed
      qed
    qed
  qed
  show ?thesis by (rule all_wellformed)
qed

ML \<open>
  val checked = @{thms
    comma_semantic_b1_crt_compact_occurrence_shifted_coverage
    comma_semantic_b1_crt_compact_occurrence_raw_coverage
    comma_semantic_b1_crt_compact_occurrences_wellformed_from_mass};
  val _ = Thm.consolidate checked;
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Compact B1 mass refinement has oracle dependencies";
  val _ = Comma_Proof_Profile.report
    "Semantic B1 compact mass stage=wellformed-from-local-cover-and-template-mass";
\<close>

end
