theory Comma_Semantic_B1_CRT_Occurrence_Bounds
  imports Comma_Semantic_B1_CRT_Slot_Certificates
begin

ML \<open>Comma_Proof_Profile.report "Constructed occurrence bound stage=entered"\<close>

lemma comma_semantic_b1_crt_template_geometry_certified_partition:
  assumes certified:
    "comma_semantic_b1_crt_template_geometry_certified columns templates
      template_column_ids template_cid"
  shows "comma_semantic_b1_crt_cells_partition {..<924}
      (map comma_crt_set (templates!template_cid))"
proof -
  have partition_certified:
      "comma_semantic_b1_crt_columns_partition_certified
        (templates!template_cid)"
    using certified
    by (auto simp: comma_semantic_b1_crt_template_geometry_certified_def)
  show ?thesis
    by (rule comma_semantic_b1_crt_columns_partition_certified_sound
      [OF partition_certified])
qed

lemma comma_semantic_b1_crt_occurrence_wellformed_from_template_geometry:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids :: "nat list list"
    and template_cid :: nat
    and occurrence :: comma_semantic_b1_crt_occurrence
  assumes binding:
      "comma_semantic_b1_crt_occurrence_binding_check occurrence"
    and template_geometry:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids template_cid"
    and occurrence_columns:
      "comma_semantic_b1_crt_occurrence_columns occurrence =
        templates!template_cid"
    and supported:
      "list_all comma_crt_supported
        (comma_semantic_b1_crt_occurrence_columns occurrence)"
  shows "comma_semantic_b1_crt_occurrence_wellformed occurrence"
proof -
  have binding_facts:
      "comma_semantic_b1_crt_occurrence_rebase occurrence < 924 \<and>
       length (comma_semantic_b1_crt_occurrence_columns occurrence) =
         length (comma_semantic_b1_crt_occurrence_beta occurrence) \<and>
       comma_semantic_b1_crt_occurrence_columns occurrence \<noteq> []"
    using binding
    by (simp add: comma_semantic_b1_crt_occurrence_binding_check_def)
  have admitted_template:
      "list_all (comma_crt_admitted 0) (templates!template_cid)"
    using template_geometry
    by (auto simp: comma_semantic_b1_crt_template_geometry_certified_def
        comma_semantic_b1_crt_columns_partition_certified_def)
  have admitted_occurrence:
      "list_all (comma_crt_admitted 0)
        (comma_semantic_b1_crt_occurrence_columns occurrence)"
    using admitted_template occurrence_columns by simp
  have cells_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set
          (comma_semantic_b1_crt_occurrence_columns occurrence))"
    using comma_semantic_b1_crt_template_geometry_certified_partition
      [OF template_geometry] occurrence_columns by simp
  have covered:
      "comma_semantic_b1_crt_occurrence_covered
        (comma_semantic_b1_crt_occurrence_columns occurrence)"
  proof -
    let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
    let ?cells = "map comma_crt_set ?columns"
    have cover:
        "\<forall>phase\<in>{..<924}. \<exists>index<length ?cells. phase\<in>?cells!index"
      using cells_partition
      by (auto simp: comma_semantic_b1_crt_cells_partition_def)
    show ?thesis
      unfolding comma_semantic_b1_crt_occurrence_covered_def
        comma_semantic_b1_crt_occurrence_indexed_columns_def
    proof (intro allI impI)
      fix phase :: nat
      assume phase: "phase < 924"
      obtain index where index_bound: "index < length ?cells"
        and phase_cell: "phase \<in> ?cells!index"
        using cover phase by blast
      have column_bound: "index < length ?columns"
        using index_bound by simp
      have entry:
          "(index, ?columns!index) \<in> set (zip [0..<length ?columns] ?columns)"
        using column_bound by (auto simp: in_set_conv_nth nth_zip)
      have phase_column: "phase \<in> comma_crt_set (?columns!index)"
        using phase_cell column_bound by (simp add: nth_map)
      show "\<exists>entry\<in>set (zip [0..<length ?columns] ?columns).
          phase \<in> comma_crt_set (snd entry)"
      proof
        show "(index, ?columns!index) \<in>
            set (zip [0..<length ?columns] ?columns)"
          by (rule entry)
        show "phase \<in> comma_crt_set (snd (index, ?columns!index))"
          using phase_column by simp
      qed
    qed
  qed
  have disjoint:
      "comma_semantic_b1_crt_occurrence_disjoint
        (comma_semantic_b1_crt_occurrence_columns occurrence)"
  proof -
    let ?columns = "comma_semantic_b1_crt_occurrence_columns occurrence"
    show ?thesis
      unfolding comma_semantic_b1_crt_occurrence_disjoint_def
        comma_semantic_b1_crt_occurrence_indexed_columns_def
    proof (intro ballI impI)+
      fix left right
      assume left: "left \<in> set (zip [0..<length ?columns] ?columns)"
        and right: "right \<in> set (zip [0..<length ?columns] ?columns)"
        and different: "fst left \<noteq> fst right"
      have left_facts:
          "fst left < length ?columns \<and> snd left = ?columns!fst left"
        using left by (auto simp: in_set_conv_nth nth_zip)
      have right_facts:
          "fst right < length ?columns \<and> snd right = ?columns!fst right"
        using right by (auto simp: in_set_conv_nth nth_zip)
      have cells_disjoint:
          "(map comma_crt_set ?columns)!fst left \<inter>
            (map comma_crt_set ?columns)!fst right = {}"
        using cells_partition left_facts right_facts different
        by (auto simp: comma_semantic_b1_crt_cells_partition_def nth_map)
      show "comma_crt_set (snd left) \<inter> comma_crt_set (snd right) = {}"
        using cells_disjoint left_facts right_facts by simp
    qed
  qed
  show ?thesis
    using binding_facts admitted_occurrence supported covered disjoint
    by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
qed

lemma comma_semantic_b1_crt_template_geometry_certified_from_facts:
  assumes template_bound: "template_cid<length templates"
    and ids_bound: "template_cid<length template_column_ids"
    and resolved:
      "comma_semantic_b1_crt_column_ids_resolve columns
        (template_column_ids!template_cid) (templates!template_cid)"
    and partition_certified:
      "comma_semantic_b1_crt_columns_partition_certified
        (templates!template_cid)"
  shows "comma_semantic_b1_crt_template_geometry_certified columns templates
    template_column_ids template_cid"
  using template_bound ids_bound resolved partition_certified
  by (simp add: comma_semantic_b1_crt_template_geometry_certified_def)

definition comma_semantic_b1_crt_constructed_occurrence_bound ::
    "comma_crt_column list \<Rightarrow> comma_crt_column list list \<Rightarrow>
      nat list list \<Rightarrow> nat list list \<Rightarrow>
      comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_descriptor list \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list list \<Rightarrow>
      comma_source_continuation_action list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor list \<Rightarrow>
      comma_semantic_b1_crt_piece_ref list list list \<Rightarrow>
      nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids sources occurrence_at
      occurrence_descriptors lift_refs slot_actions lift_descriptors piece_refs index \<longleftrightarrow>
    (if index<length sources \<and> index<length occurrence_descriptors \<and>
        index<length lift_refs \<and> index<length piece_refs
     then (case occurrence_at index of
       None \<Rightarrow> False
     | Some parent \<Rightarrow>
       (let source=sources!index;
            refs=lift_refs!index;
            actions=slot_actions;
            pieces=piece_refs!index;
            period=comma_decisive_sector_period
              (comma_source_continuation_base source);
            beta=comma_semantic_b1_crt_occurrence_beta parent;
            origins=comma_semantic_b1_crt_constructed_source_origins columns
              lift_column_ids sources occurrence_at refs source
        in source=comma_source_continuation_base source \<and>
          comma_round_admitted source \<and>
          length refs=period \<and>
          map comma_semantic_b1_crt_lift_ref_slot refs=[0..<period] \<and>
          length occurrence_descriptors=length sources \<and>
          length pieces=length beta \<and>
          (case occurrence_descriptors!index of
             (template_cid,(rebase,descriptor_beta)) \<Rightarrow>
            template_cid<length templates \<and>
            rebase=comma_semantic_b1_crt_occurrence_rebase parent \<and>
            descriptor_beta=beta \<and>
            comma_semantic_b1_crt_occurrence_columns parent=templates!template_cid) \<and>
          comma_semantic_b1_crt_occurrence_binding_check parent \<and>
          beta\<noteq>[] \<and> distinct beta \<and>
          comma_semantic_b1_crt_source_slot_action_row_certified source period actions \<and>
          list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
            occurrence_descriptors templates source parent refs lift_descriptors actions)
            [0..<period] \<and>
          list_all (\<lambda>slot.
            comma_semantic_b1_crt_constructed_goto_slot_certificate columns
              templates template_column_ids lift_column_ids
              occurrence_descriptors lift_descriptors index refs slot)
            [0..<period] \<and>
          sort (map comma_semantic_b1_crt_constructed_piece_origin
            (concat pieces)) = origins \<and>
          list_all (\<lambda>row.
            comma_semantic_b1_crt_group_construction_bound columns
              (comma_semantic_b1_crt_occurrence_rebase parent) row
              (template_column_ids !
                (fst (occurrence_descriptors!index)) ! row)
              (pieces!row) \<and>
            list_all (comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions columns
              lift_column_ids sources occurrence_at refs
              source actions parent row) (pieces!row)) [0..<length beta]))
     else False)"

lemma comma_semantic_b1_crt_constructed_occurrence_bound_index_guards:
  assumes bound:
    "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids sources occurrence_at
      occurrence_descriptors lift_refs slot_actions lift_descriptors piece_refs index"
  shows "index<length sources \<and> index<length occurrence_descriptors \<and>
    index<length lift_refs \<and> index<length piece_refs"
proof -
  let ?guard = "index<length sources \<and> index<length occurrence_descriptors \<and>
    index<length lift_refs \<and> index<length piece_refs"
  show ?thesis
  proof (cases ?guard)
    case True
    then show ?thesis by blast
  next
    case False
    have contradiction: False
      using bound False
      by (simp only: comma_semantic_b1_crt_constructed_occurrence_bound_def
          if_False)
    then show ?thesis by simp
  qed
qed

lemma comma_semantic_b1_crt_constructed_occurrence_bound_parent_present:
  assumes bound:
    "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids sources occurrence_at
      occurrence_descriptors lift_refs slot_actions lift_descriptors piece_refs index"
  shows "occurrence_at index\<noteq>None"
proof -
  have index_guard:
    "index<length sources \<and> index<length occurrence_descriptors \<and>
     index<length lift_refs \<and> index<length piece_refs"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_index_guards
      [OF bound])
  show ?thesis
  proof (cases "occurrence_at index")
    case None
    with bound index_guard show ?thesis
      by (auto simp: comma_semantic_b1_crt_constructed_occurrence_bound_def)
  next
    case (Some parent)
    then show ?thesis by simp
  qed
qed

lemma comma_semantic_b1_crt_constructed_occurrence_bound_origins_exact:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and lift_refs :: "comma_semantic_b1_crt_lift_ref list list"
    and slot_actions :: "comma_source_continuation_action list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and piece_refs :: "comma_semantic_b1_crt_piece_ref list list list"
    and index :: nat
  assumes bound:
    "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids sources occurrence_at
      occurrence_descriptors lift_refs slot_actions lift_descriptors piece_refs index"
  shows "sort (map comma_semantic_b1_crt_constructed_piece_origin
      (concat (piece_refs!index))) =
    comma_semantic_b1_crt_constructed_source_origins columns lift_column_ids
      sources occurrence_at (lift_refs!index) (sources!index)"
proof -
  have index_guard:
    "index<length sources \<and> index<length occurrence_descriptors \<and>
     index<length lift_refs \<and> index<length piece_refs"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_index_guards
      [OF bound])
  have parent_present:
    "occurrence_at index\<noteq>None"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_parent_present
      [OF bound])
  obtain parent where parent_at: "occurrence_at index=Some parent"
    using parent_present by (cases "occurrence_at index") auto
  show ?thesis using bound index_guard parent_at
    by (auto simp: comma_semantic_b1_crt_constructed_occurrence_bound_def
        Let_def)
qed

lemma comma_semantic_b1_crt_constructed_occurrence_bound_rejects_origin_mismatch:
  assumes bound:
    "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids sources occurrence_at
      occurrence_descriptors lift_refs slot_actions lift_descriptors piece_refs index"
    and source_origins:
      "comma_semantic_b1_crt_constructed_source_origins columns lift_column_ids
        sources occurrence_at (lift_refs!index) (sources!index) = expected"
    and mismatch:
      "sort (map comma_semantic_b1_crt_constructed_piece_origin
        (concat (piece_refs!index))) \<noteq> expected"
  shows False
  using comma_semantic_b1_crt_constructed_occurrence_bound_origins_exact[OF bound]
    source_origins mismatch by blast

lemma comma_semantic_b1_crt_constructed_occurrence_bound_beta_distinct:
  assumes bound:
    "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids sources occurrence_at
      occurrence_descriptors lift_refs slot_actions lift_descriptors piece_refs index"
    and parent_at: "occurrence_at index=Some parent"
  shows "distinct (comma_semantic_b1_crt_occurrence_beta parent)"
proof -
  have index_guard:
    "index<length sources \<and> index<length occurrence_descriptors \<and>
     index<length lift_refs \<and> index<length piece_refs"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_index_guards
      [OF bound])
  show ?thesis using bound parent_at index_guard
    by (simp only: comma_semantic_b1_crt_constructed_occurrence_bound_def
        Let_def index_guard if_True parent_at option.case; blast)
qed
ML \<open>Thm.consolidate @{thms comma_semantic_b1_crt_constructed_occurrence_bound_index_guards comma_semantic_b1_crt_constructed_occurrence_bound_parent_present}; Comma_Proof_Profile.report "Constructed occurrence: basic bound guards checked"\<close>
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_occurrence_bound_beta_distinct}]; Comma_Proof_Profile.report "Constructed occurrence: beta bound guard checked"\<close>

lemma comma_semantic_b1_crt_constructed_occurrence_bound_template_cid:
  assumes bound:
    "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids sources occurrence_at
      occurrence_descriptors lift_refs actions lift_descriptors piece_refs index"
  shows "fst (occurrence_descriptors!index)<length templates"
proof -
  have index_guard:
    "index<length sources \<and> index<length occurrence_descriptors \<and>
     index<length lift_refs \<and> index<length piece_refs"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_index_guards
      [OF bound])
  have parent_present:
    "occurrence_at index\<noteq>None"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_parent_present
      [OF bound])
  obtain parent where parent_at: "occurrence_at index=Some parent"
    using parent_present by (cases "occurrence_at index") auto
  obtain template_cid rebase descriptor_beta where descriptor_at:
    "occurrence_descriptors!index=(template_cid,(rebase,descriptor_beta))"
    by (cases "occurrence_descriptors!index";
        cases "snd (occurrence_descriptors!index)") auto
  have cid: "template_cid<length templates"
    using bound index_guard parent_at descriptor_at
    by (simp only: comma_semantic_b1_crt_constructed_occurrence_bound_def
        Let_def index_guard if_True parent_at option.case descriptor_at
        prod.case; blast)
  show ?thesis using cid descriptor_at by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_occurrence_bound_template_cid}]; Comma_Proof_Profile.report "Constructed occurrence: template CID bound checked"\<close>

lemma comma_semantic_b1_crt_constructed_occurrence_bound_goto_lift_cid:
  assumes bound:
    "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids sources occurrence_at
      occurrence_descriptors lift_refs actions lift_descriptors piece_refs index"
    and slot: "slot<length (lift_refs!index)"
    and reference:
      "(lift_refs!index)!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
  shows "lift_cid<length lift_descriptors"
proof -
  have index_guard:
    "index<length sources \<and> index<length occurrence_descriptors \<and>
     index<length lift_refs \<and> index<length piece_refs"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_index_guards
      [OF bound])
  have parent_present:
    "occurrence_at index\<noteq>None"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_parent_present
      [OF bound])
  obtain parent where parent_at: "occurrence_at index=Some parent"
    using parent_present by (cases "occurrence_at index") auto
  have guard_true:
    "(index<length sources \<and> index<length occurrence_descriptors \<and>
      index<length lift_refs \<and> index<length piece_refs)=True"
    by (rule eqTrueI[OF index_guard])
  let ?source="sources!index"
  let ?refs="lift_refs!index"
  let ?period="comma_decisive_sector_period
    (comma_source_continuation_base ?source)"
  have selected_slot_facts:
    "length ?refs=?period \<and>
     list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions sources
       occurrence_at occurrence_descriptors templates ?source parent ?refs
       lift_descriptors actions) [0..<?period]"
  proof -
    note normalized_bound = bound[unfolded
      comma_semantic_b1_crt_constructed_occurrence_bound_def
      guard_true if_True parent_at option.case Let_def]
    show ?thesis using normalized_bound by blast
  qed
  have slot_period: "slot<?period"
    using slot selected_slot_facts by simp
  have selected_slot_valid:
    "comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
       occurrence_descriptors templates ?source parent ?refs lift_descriptors
       actions slot"
    using selected_slot_facts slot_period by (auto simp: list_all_iff)
  show ?thesis
    using selected_slot_valid reference slot slot_period
    by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
        split: if_splits comma_source_continuation_action.splits)
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_occurrence_bound_goto_lift_cid}]; Comma_Proof_Profile.report "Constructed occurrence: Goto lift CID bound checked"\<close>

lemma comma_semantic_b1_crt_constructed_occurrences_catalog_geometry_facts:
  fixes columns templates template_column_ids lift_column_ids sources
    occurrence_at occurrence_descriptors lift_refs slot_actions_table
    lift_descriptors piece_refs
  assumes bounds:
      "list_all (\<lambda>index. comma_semantic_b1_crt_constructed_occurrence_bound
        columns templates template_column_ids lift_column_ids sources
        occurrence_at occurrence_descriptors lift_refs (slot_actions_table!index)
        lift_descriptors piece_refs index) [0..<length sources]"
    and template_catalog:
      "list_all (\<lambda>cid. comma_semantic_b1_crt_template_geometry_certified
        columns templates template_column_ids cid) [0..<length templates]"
    and lift_catalog:
      "list_all (\<lambda>cid. comma_semantic_b1_crt_lift_geometry_certified
        columns templates template_column_ids lift_column_ids lift_descriptors cid)
        [0..<length lift_descriptors]"
  shows parent_template_geometries:
      "\<And>index. index<length sources \<Longrightarrow>
        comma_semantic_b1_crt_template_geometry_certified columns templates
          template_column_ids (fst (occurrence_descriptors!index))"
    and used_lift_geometries:
      "\<And>index slot child_index lift_cid. index<length sources \<Longrightarrow>
        slot<length (lift_refs!index) \<Longrightarrow>
        (lift_refs!index)!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid
        \<Longrightarrow> comma_semantic_b1_crt_lift_geometry_certified columns
          templates template_column_ids lift_column_ids lift_descriptors lift_cid"
proof -
  show "\<And>index. index<length sources \<Longrightarrow>
      comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids (fst (occurrence_descriptors!index))"
  proof -
    fix index assume index: "index<length sources"
    have bound: "comma_semantic_b1_crt_constructed_occurrence_bound columns
        templates template_column_ids lift_column_ids sources occurrence_at
        occurrence_descriptors lift_refs (slot_actions_table!index)
        lift_descriptors piece_refs index"
      by (rule comma_semantic_b1_crt_list_all_upt_index[OF bounds index])
    have cid: "fst (occurrence_descriptors!index)<length templates"
      by (rule comma_semantic_b1_crt_constructed_occurrence_bound_template_cid
        [OF bound])
    show "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids (fst (occurrence_descriptors!index))"
      using template_catalog cid by (auto simp: list_all_iff)
  qed
  show "\<And>index slot child_index lift_cid. index<length sources \<Longrightarrow>
      slot<length (lift_refs!index) \<Longrightarrow>
      (lift_refs!index)!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid
      \<Longrightarrow> comma_semantic_b1_crt_lift_geometry_certified columns
        templates template_column_ids lift_column_ids lift_descriptors lift_cid"
  proof -
    fix index slot child_index lift_cid
    assume index: "index<length sources" and slot: "slot<length (lift_refs!index)"
      and ref: "(lift_refs!index)!slot=
        Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    have bound: "comma_semantic_b1_crt_constructed_occurrence_bound columns
        templates template_column_ids lift_column_ids sources occurrence_at
        occurrence_descriptors lift_refs (slot_actions_table!index)
        lift_descriptors piece_refs index"
      by (rule comma_semantic_b1_crt_list_all_upt_index[OF bounds index])
    have cid: "lift_cid<length lift_descriptors"
      by (rule comma_semantic_b1_crt_constructed_occurrence_bound_goto_lift_cid
        [OF bound slot ref])
    show "comma_semantic_b1_crt_lift_geometry_certified columns templates
        template_column_ids lift_column_ids lift_descriptors lift_cid"
      using lift_catalog cid by (auto simp: list_all_iff)
  qed
qed

lemmas comma_semantic_b1_crt_occurrence_bounds_oracle_audit_bundle =
  comma_semantic_b1_crt_template_geometry_certified_partition
  comma_semantic_b1_crt_occurrence_wellformed_from_template_geometry
  comma_semantic_b1_crt_template_geometry_certified_from_facts
  comma_semantic_b1_crt_constructed_occurrence_bound_index_guards
  comma_semantic_b1_crt_constructed_occurrence_bound_parent_present
  comma_semantic_b1_crt_constructed_occurrence_bound_origins_exact
  comma_semantic_b1_crt_constructed_occurrence_bound_rejects_origin_mismatch
  comma_semantic_b1_crt_constructed_occurrence_bound_beta_distinct
  comma_semantic_b1_crt_constructed_occurrence_bound_template_cid
  comma_semantic_b1_crt_constructed_occurrence_bound_goto_lift_cid
  comma_semantic_b1_crt_constructed_occurrences_catalog_geometry_facts
ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms
    comma_semantic_b1_crt_occurrence_bounds_oracle_audit_bundle})
    then () else error "Constructed occurrence bounds local oracle audit failed"
  Thm.consolidate @{thms comma_semantic_b1_crt_occurrence_bounds_oracle_audit_bundle};
  Comma_Proof_Profile.report "Constructed occurrence bounds: local oracle audit checked"
\<close>

end
