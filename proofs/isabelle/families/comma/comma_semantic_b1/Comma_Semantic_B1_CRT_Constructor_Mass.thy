theory Comma_Semantic_B1_CRT_Constructor_Mass
  imports Comma_Semantic_B1_CRT_Constructed_Occurrence
    Comma_Semantic_B1_CRT_Cardinality
begin

text \<open>
Lift binding is occurrence-local authority: it certifies the descriptor and
the exact global column-ID row for its lifted columns, without requiring the
referenced child template's partition proof.  Child-first construction can
then obtain that geometry from the already-established child occurrence.
\<close>

definition comma_semantic_b1_crt_lift_binding_certified ::
    "comma_crt_column list \<Rightarrow> comma_crt_column list list \<Rightarrow>
      nat list list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_lift_binding_certified columns templates
      lift_column_ids lift_descriptors lift_cid \<longleftrightarrow>
    (if lift_cid<length lift_column_ids \<and>
        lift_cid<length lift_descriptors then
       (let descriptor=lift_descriptors!lift_cid
        in comma_semantic_b1_crt_lift_descriptor_valid templates descriptor \<and>
          (case comma_semantic_b1_crt_lift_columns_option templates descriptor of
             None \<Rightarrow> False
           | Some lifted \<Rightarrow>
               comma_semantic_b1_crt_column_ids_resolve columns
                 (lift_column_ids!lift_cid) lifted))
     else False)"

definition comma_semantic_b1_crt_template_mass_certified ::
    "comma_crt_column list \<Rightarrow> comma_crt_column list list \<Rightarrow>
      nat list list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_template_mass_certified columns templates
      template_column_ids template_cid \<longleftrightarrow>
    template_cid<length templates \<and>
    template_cid<length template_column_ids \<and>
    comma_semantic_b1_crt_column_ids_resolve columns
      (template_column_ids!template_cid) (templates!template_cid) \<and>
    sum_list (map comma_semantic_b1_crt_column_mass
      (templates!template_cid))=924"

lemma comma_semantic_b1_crt_template_mass_certified_intro:
  assumes template_bound: "template_cid<length templates"
    and ids_bound: "template_cid<length template_column_ids"
    and row_resolution:
      "comma_semantic_b1_crt_column_ids_resolve columns
        (template_column_ids!template_cid) (templates!template_cid)"
    and row_mass:
      "sum_list (map comma_semantic_b1_crt_column_mass
        (templates!template_cid))=924"
  shows "comma_semantic_b1_crt_template_mass_certified columns templates
    template_column_ids template_cid"
  unfolding comma_semantic_b1_crt_template_mass_certified_def
  using template_bound ids_bound row_resolution row_mass by blast

lemma comma_semantic_b1_crt_list_all_remdups:
  "list_all P (remdups xs) = list_all P xs"
  by (simp only: list_all_iff set_remdups)

lemma comma_semantic_b1_crt_template_mass_certified_cardinality:
  assumes table_admitted: "list_all (comma_crt_admitted 0) columns"
    and mass:
      "comma_semantic_b1_crt_template_mass_certified columns templates
        template_column_ids template_cid"
  shows "template_cid<length templates \<and>
    template_cid<length template_column_ids \<and>
    comma_semantic_b1_crt_column_ids_resolve columns
      (template_column_ids!template_cid) (templates!template_cid) \<and>
    sum_list (map card (map comma_crt_set (templates!template_cid)))=924"
proof -
  have cid_bound: "template_cid<length templates"
    and row_bound: "template_cid<length template_column_ids"
    and resolved:
      "comma_semantic_b1_crt_column_ids_resolve columns
        (template_column_ids!template_cid) (templates!template_cid)"
    and mass_sum:
      "sum_list (map comma_semantic_b1_crt_column_mass
        (templates!template_cid))=924"
    using mass
    by (auto simp: comma_semantic_b1_crt_template_mass_certified_def)
  have row_admitted:
      "list_all (comma_crt_admitted 0) (templates!template_cid)"
  proof -
    have mapped_admitted:
        "list_all (comma_crt_admitted 0)
          (map (\<lambda>cid. columns!cid) (template_column_ids!template_cid))"
      by (rule comma_semantic_b1_crt_column_ids_resolve_preserves_list_all
        [OF table_admitted resolved])
    have row_map:
        "map (\<lambda>cid. columns!cid) (template_column_ids!template_cid)=
          templates!template_cid"
      by (rule comma_semantic_b1_crt_column_ids_resolve_map[OF resolved])
    show ?thesis using mapped_admitted by (simp add: row_map)
  qed
  have card_mass:
      "sum_list (map card (map comma_crt_set (templates!template_cid)))=
        sum_list (map comma_semantic_b1_crt_column_mass
          (templates!template_cid))"
    by (rule comma_semantic_b1_crt_column_list_card_mass[OF row_admitted])
  show ?thesis using cid_bound row_bound resolved mass_sum card_mass by simp
qed

ML \<open>
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_template_mass_certified_intro
      comma_semantic_b1_crt_list_all_remdups
      comma_semantic_b1_crt_template_mass_certified_cardinality};
  val _ = Comma_Proof_Profile.report
    "Semantic B1 constructor mass stage=template-cardinality-complete";
\<close>

lemma comma_semantic_b1_crt_used_template_masses_cover_sources:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
  assumes descriptor_extent: "length occurrence_descriptors=length sources"
    and used_template_masses:
      "list_all (comma_semantic_b1_crt_template_mass_certified
        columns templates template_column_ids)
        (remdups (map fst occurrence_descriptors))"
  shows "\<And>index. index<length sources \<Longrightarrow>
    comma_semantic_b1_crt_template_mass_certified columns templates
      template_column_ids (fst (occurrence_descriptors!index))"
proof -
  fix index assume index: "index<length sources"
  have descriptor_bound: "index<length occurrence_descriptors"
    using index descriptor_extent by simp
  have selected_used:
      "fst (occurrence_descriptors!index) \<in>
        set (remdups (map fst occurrence_descriptors))"
  proof -
    have descriptor_nth_mem:
        "occurrence_descriptors!index \<in> set occurrence_descriptors"
      by (rule nth_mem[OF descriptor_bound])
    have selected_mem_image:
        "fst (occurrence_descriptors!index) \<in>
          fst ` set occurrence_descriptors"
      by (rule imageI[OF descriptor_nth_mem])
    have selected_mem:
        "fst (occurrence_descriptors!index) \<in>
          set (map fst occurrence_descriptors)"
      using selected_mem_image by simp
    show ?thesis using selected_mem by simp
  qed
  show "comma_semantic_b1_crt_template_mass_certified columns templates
      template_column_ids (fst (occurrence_descriptors!index))"
    using used_template_masses selected_used by (auto simp: list_all_iff)
qed

lemma comma_semantic_b1_crt_template_geometry_from_resolved_wellformed_occurrence:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids :: "nat list list"
    and template_cid :: nat
    and child :: comma_semantic_b1_crt_occurrence
  assumes template_bound: "template_cid<length templates"
    and ids_bound: "template_cid<length template_column_ids"
    and child_columns:
      "comma_semantic_b1_crt_occurrence_columns child=templates!template_cid"
    and row_resolution:
      "comma_semantic_b1_crt_column_ids_resolve columns
        (template_column_ids!template_cid) (templates!template_cid)"
    and child_wellformed: "comma_semantic_b1_crt_occurrence_wellformed child"
  shows "comma_semantic_b1_crt_template_geometry_certified columns templates
    template_column_ids template_cid"
proof -
  have child_admitted:
      "list_all (comma_crt_admitted 0)
        (comma_semantic_b1_crt_occurrence_columns child)"
    using child_wellformed
    by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have child_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set
          (comma_semantic_b1_crt_occurrence_columns child))"
    by (rule comma_semantic_b1_crt_occurrence_columns_partition
      [OF child_wellformed])
  have template_admitted:
      "list_all (comma_crt_admitted 0) (templates!template_cid)"
    using child_admitted child_columns by simp
  have template_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set (templates!template_cid))"
    using child_partition child_columns by simp
  have partition_certified:
      "comma_semantic_b1_crt_columns_partition_certified
        (templates!template_cid)"
    by (rule comma_semantic_b1_crt_columns_partition_certified_complete
      [OF template_admitted template_partition])
  show ?thesis
    by (rule comma_semantic_b1_crt_template_geometry_certified_from_facts
      [OF template_bound ids_bound row_resolution partition_certified])
qed

lemma comma_semantic_b1_crt_lift_geometry_from_binding_and_template_geometry:
  assumes binding:
      "comma_semantic_b1_crt_lift_binding_certified columns templates
        lift_column_ids lift_descriptors lift_cid"
    and template_geometry:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids
          (comma_semantic_b1_crt_lift_descriptor_template_cid
            (lift_descriptors!lift_cid))"
  shows "comma_semantic_b1_crt_lift_geometry_certified columns templates
    template_column_ids lift_column_ids lift_descriptors lift_cid"
  using binding template_geometry
  by (auto simp: comma_semantic_b1_crt_lift_binding_certified_def
      comma_semantic_b1_crt_lift_geometry_certified_def Let_def
      split: if_splits option.splits)

lemma comma_semantic_b1_crt_used_lift_geometry_from_child:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and lift_cid template_cid :: nat
    and child :: comma_semantic_b1_crt_occurrence
  assumes binding:
      "comma_semantic_b1_crt_lift_binding_certified columns templates
        lift_column_ids lift_descriptors lift_cid"
    and descriptor_child:
      "comma_semantic_b1_crt_lift_descriptor_template_cid
        (lift_descriptors!lift_cid)=template_cid"
    and template_bound: "template_cid<length templates"
    and ids_bound: "template_cid<length template_column_ids"
    and child_columns:
      "comma_semantic_b1_crt_occurrence_columns child=templates!template_cid"
    and row_resolution:
      "comma_semantic_b1_crt_column_ids_resolve columns
        (template_column_ids!template_cid) (templates!template_cid)"
    and child_wellformed: "comma_semantic_b1_crt_occurrence_wellformed child"
  shows "comma_semantic_b1_crt_lift_geometry_certified columns templates
    template_column_ids lift_column_ids lift_descriptors lift_cid"
proof -
  have child_template_geometry:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids template_cid"
    by (rule comma_semantic_b1_crt_template_geometry_from_resolved_wellformed_occurrence
      [OF template_bound ids_bound child_columns row_resolution child_wellformed])
  have descriptor_template_geometry:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids
          (comma_semantic_b1_crt_lift_descriptor_template_cid
            (lift_descriptors!lift_cid))"
    using child_template_geometry descriptor_child by simp
  show ?thesis
    by (rule comma_semantic_b1_crt_lift_geometry_from_binding_and_template_geometry
      [OF binding descriptor_template_geometry])
qed

lemma comma_semantic_b1_crt_used_lift_geometry_from_selected_child:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and actions :: "comma_source_continuation_action list"
    and source :: comma_finite_position
    and parent child :: comma_semantic_b1_crt_occurrence
    and slot child_index lift_cid :: nat
  assumes reference:
      "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    and action:
      "actions!slot=Comma_Continuation_Goto action_child shift"
    and selected_valid:
      "comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
        occurrence_descriptors templates source parent refs lift_descriptors
        actions slot"
    and child_at: "occurrence_at child_index=Some child"
    and child_wellformed: "comma_semantic_b1_crt_occurrence_wellformed child"
    and child_template_row:
      "fst (occurrence_descriptors!child_index)<length templates \<and>
       fst (occurrence_descriptors!child_index)<length template_column_ids \<and>
       comma_semantic_b1_crt_column_ids_resolve columns
         (template_column_ids!fst (occurrence_descriptors!child_index))
         (templates!fst (occurrence_descriptors!child_index))"
    and lift_binding:
      "comma_semantic_b1_crt_lift_binding_certified columns templates
        lift_column_ids lift_descriptors lift_cid"
  shows "comma_semantic_b1_crt_lift_geometry_certified columns templates
    template_column_ids lift_column_ids lift_descriptors lift_cid"
proof -
  have descriptor_facts:
      "lift_cid<length lift_descriptors \<and>
       comma_semantic_b1_crt_lift_descriptor_template_cid
         (lift_descriptors!lift_cid)<length templates \<and>
       fst (occurrence_descriptors!child_index)=
         comma_semantic_b1_crt_lift_descriptor_template_cid
           (lift_descriptors!lift_cid) \<and>
       comma_semantic_b1_crt_occurrence_columns child=
         templates!comma_semantic_b1_crt_lift_descriptor_template_cid
           (lift_descriptors!lift_cid)"
    using selected_valid reference action child_at
    by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
        split: if_splits option.splits prod.splits
          comma_source_continuation_action.splits)
  have template_cid_bound:
      "comma_semantic_b1_crt_lift_descriptor_template_cid
        (lift_descriptors!lift_cid)<length templates"
    using descriptor_facts by blast
  let ?template_cid =
    "comma_semantic_b1_crt_lift_descriptor_template_cid
      (lift_descriptors!lift_cid)"
  have child_template_cid_eq:
      "fst (occurrence_descriptors!child_index)=?template_cid"
    using descriptor_facts by blast
  have child_template_ids_bound:
      "fst (occurrence_descriptors!child_index)<length template_column_ids"
    by (rule conjunct1[OF conjunct2[OF child_template_row]])
  have template_ids_bound: "?template_cid<length template_column_ids"
    using child_template_ids_bound child_template_cid_eq by simp
  have child_template_row_resolution:
      "comma_semantic_b1_crt_column_ids_resolve columns
        (template_column_ids!fst (occurrence_descriptors!child_index))
        (templates!fst (occurrence_descriptors!child_index))"
    by (rule conjunct2[OF conjunct2[OF child_template_row]])
  have template_row_resolution:
      "comma_semantic_b1_crt_column_ids_resolve columns
        (template_column_ids! ?template_cid) (templates! ?template_cid)"
    using child_template_row_resolution child_template_cid_eq by simp
  have child_columns:
      "comma_semantic_b1_crt_occurrence_columns child=templates! ?template_cid"
    using descriptor_facts by blast
  have child_template_geometry:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids ?template_cid"
    by (rule comma_semantic_b1_crt_template_geometry_from_resolved_wellformed_occurrence
      [OF template_cid_bound template_ids_bound child_columns
        template_row_resolution child_wellformed])
  have descriptor_template_geometry:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids
          (comma_semantic_b1_crt_lift_descriptor_template_cid
            (lift_descriptors!lift_cid))"
    using child_template_geometry by simp
  show ?thesis
    by (rule comma_semantic_b1_crt_lift_geometry_from_binding_and_template_geometry
      [OF lift_binding descriptor_template_geometry])
qed

lemma comma_semantic_b1_crt_constructed_occurrences_wellformed_and_used_lifts_from_mass:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and lift_refs :: "comma_semantic_b1_crt_lift_ref list list"
    and slot_actions_table :: "comma_source_continuation_action list list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and piece_refs :: "comma_semantic_b1_crt_piece_ref list list list"
  assumes table_admitted: "list_all (comma_crt_admitted 0) columns"
    and bounds:
      "list_all (\<lambda>index. comma_semantic_b1_crt_constructed_occurrence_bound
        columns templates template_column_ids lift_column_ids sources
        occurrence_at occurrence_descriptors lift_refs (slot_actions_table!index)
        lift_descriptors piece_refs index) [0..<length sources]"
    and source_template_rows:
      "\<And>index. index<length sources \<Longrightarrow>
        fst (occurrence_descriptors!index)<length templates \<and>
        fst (occurrence_descriptors!index)<length template_column_ids \<and>
        comma_semantic_b1_crt_column_ids_resolve columns
          (template_column_ids!fst (occurrence_descriptors!index))
          (templates!fst (occurrence_descriptors!index))"
    and parent_masses:
      "\<And>index. index<length sources \<Longrightarrow>
        sum_list (map card (map comma_crt_set
          (templates!fst (occurrence_descriptors!index))))=924"
    and used_lift_bindings:
      "\<And>index slot child_index lift_cid. index<length sources \<Longrightarrow>
        slot<length (lift_refs!index) \<Longrightarrow>
        (lift_refs!index)!slot=
          Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
        comma_semantic_b1_crt_lift_binding_certified columns templates
          lift_column_ids lift_descriptors lift_cid"
  shows "(\<forall>index<length sources. \<forall>parent.
      occurrence_at index=Some parent \<longrightarrow>
      comma_semantic_b1_crt_occurrence_wellformed parent) \<and>
    (\<forall>index<length sources. \<forall>slot child_index lift_cid.
      slot<length (lift_refs!index) \<longrightarrow>
      (lift_refs!index)!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<longrightarrow>
      comma_semantic_b1_crt_lift_geometry_certified columns templates
        template_column_ids lift_column_ids lift_descriptors lift_cid)"
proof -
  let ?wellformed = "\<lambda>index. \<forall>parent.
    occurrence_at index=Some parent \<longrightarrow>
    comma_semantic_b1_crt_occurrence_wellformed parent"
  let ?used_lifts = "\<lambda>index. \<forall>slot child_index lift_cid.
    slot<length (lift_refs!index) \<longrightarrow>
    (lift_refs!index)!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<longrightarrow>
    comma_semantic_b1_crt_lift_geometry_certified columns templates
      template_column_ids lift_column_ids lift_descriptors lift_cid"
  let ?certified = "\<lambda>index. ?wellformed index \<and> ?used_lifts index"
  have step:
      "\<And>index. index<length sources \<Longrightarrow>
        (\<And>child_index. child_index<index \<Longrightarrow> ?certified child_index) \<Longrightarrow>
        ?certified index"
  proof -
    fix index
    assume index: "index<length sources"
      and earlier: "\<And>child_index. child_index<index \<Longrightarrow> ?certified child_index"
    have bound:
        "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
          template_column_ids lift_column_ids sources occurrence_at
          occurrence_descriptors lift_refs (slot_actions_table!index)
          lift_descriptors piece_refs index"
      by (rule comma_semantic_b1_crt_list_all_upt_index[OF bounds index])
    have occurrence_present: "occurrence_at index\<noteq>None"
      by (rule comma_semantic_b1_crt_constructed_occurrence_bound_parent_present
        [OF bound])
    show "?certified index"
    proof (cases "occurrence_at index")
      case None
      with occurrence_present show ?thesis by blast
    next
      case (Some parent)
      have parent_at: "occurrence_at index=Some parent" using Some .
      have earlier_wellformed:
          "\<And>child_index child. child_index<index \<Longrightarrow>
            occurrence_at child_index=Some child \<Longrightarrow>
            comma_semantic_b1_crt_occurrence_wellformed child"
      proof -
        fix child_index child
        assume before: "child_index<index"
          and child_at: "occurrence_at child_index=Some child"
        have child_certified: "?certified child_index"
          by (rule earlier[OF before])
        show "comma_semantic_b1_crt_occurrence_wellformed child"
          using child_certified child_at by blast
      qed
      have parent_template_resolution:
          "fst (occurrence_descriptors!index)<length templates \<and>
           fst (occurrence_descriptors!index)<length template_column_ids \<and>
           comma_semantic_b1_crt_column_ids_resolve columns
             (template_column_ids!fst (occurrence_descriptors!index))
             (templates!fst (occurrence_descriptors!index))"
        using source_template_rows[OF index] by blast
      have parent_mass:
          "sum_list (map card (map comma_crt_set
            (templates!fst (occurrence_descriptors!index))))=924"
        by (rule parent_masses[OF index])
      have used_geometries:
          "\<And>slot child_index lift_cid. slot<length (lift_refs!index) \<Longrightarrow>
            (lift_refs!index)!slot=
              Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
            comma_semantic_b1_crt_lift_geometry_certified columns templates
              template_column_ids lift_column_ids lift_descriptors lift_cid"
      proof -
        fix slot child_index lift_cid
        assume slot_bound: "slot<length (lift_refs!index)"
          and reference:
            "(lift_refs!index)!slot=
              Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
        have child_bound:
            "child_index<index \<and> child_index<length occurrence_descriptors"
        proof -
          have certificate:
              "comma_semantic_b1_crt_constructed_goto_slot_certificate columns
                templates template_column_ids lift_column_ids occurrence_descriptors
                lift_descriptors index (lift_refs!index) slot"
          proof -
            have source: "sources!index=comma_source_continuation_base (sources!index)"
              and refs_length:
                "length (lift_refs!index)=comma_decisive_sector_period
                  (comma_source_continuation_base (sources!index))"
              and slot_certificates:
                "list_all (\<lambda>slot. comma_semantic_b1_crt_constructed_goto_slot_certificate
                    columns templates template_column_ids lift_column_ids
                    occurrence_descriptors lift_descriptors index
                    (lift_refs!index) slot)
                  [0..<comma_decisive_sector_period
                    (comma_source_continuation_base (sources!index))]"
              using bound index parent_at
              by (auto simp: comma_semantic_b1_crt_constructed_occurrence_bound_def
                  Let_def split: if_splits option.splits prod.splits)
            have slot_period:
                "slot<comma_decisive_sector_period
                  (comma_source_continuation_base (sources!index))"
              using slot_bound refs_length by simp
            show ?thesis
              by (rule comma_semantic_b1_crt_list_all_upt_index
                [OF slot_certificates slot_period])
          qed
          show ?thesis
            by (rule comma_semantic_b1_crt_goto_slot_certificate_child_bounds
              [OF certificate reference])
        qed
        have child_in_sources: "child_index<length sources"
          using child_bound index by arith
        have child_template_row:
            "fst (occurrence_descriptors!child_index)<length templates \<and>
             fst (occurrence_descriptors!child_index)<length template_column_ids \<and>
             comma_semantic_b1_crt_column_ids_resolve columns
               (template_column_ids!fst (occurrence_descriptors!child_index))
               (templates!fst (occurrence_descriptors!child_index))"
          by (rule source_template_rows[OF child_in_sources])
        have child_exists: "\<exists>child. occurrence_at child_index=Some child"
        proof -
          have slot_valid:
              "comma_semantic_b1_crt_lift_slot_valid_from_actions sources
                occurrence_at occurrence_descriptors templates (sources!index)
                parent (lift_refs!index) lift_descriptors
                (slot_actions_table!index) slot"
          proof -
            have valid_slots:
                "list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions
                  sources occurrence_at occurrence_descriptors templates
                  (sources!index) parent (lift_refs!index)
                  lift_descriptors (slot_actions_table!index))
                  [0..<comma_decisive_sector_period
                    (comma_source_continuation_base (sources!index))]"
              using bound index parent_at
              by (auto simp: comma_semantic_b1_crt_constructed_occurrence_bound_def
                  Let_def split: if_splits option.splits prod.splits)
            have refs_length:
                "length (lift_refs!index)=comma_decisive_sector_period
                  (comma_source_continuation_base (sources!index))"
              using bound index parent_at
              by (auto simp: comma_semantic_b1_crt_constructed_occurrence_bound_def
                  Let_def split: if_splits option.splits prod.splits)
            have slot_period: "slot<comma_decisive_sector_period
                (comma_source_continuation_base (sources!index))"
              using slot_bound refs_length by simp
            show ?thesis
              by (rule comma_semantic_b1_crt_list_all_upt_index
                [OF valid_slots slot_period])
          qed
          show ?thesis
            using slot_valid reference
            by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
                split: if_splits option.splits prod.splits
                  comma_source_continuation_action.splits)
        qed
        then obtain child where child_at:
            "occurrence_at child_index=Some child" by blast
        have child_wellformed:
            "comma_semantic_b1_crt_occurrence_wellformed child"
        proof -
          have child_precedes: "child_index<index"
            using child_bound by blast
          show ?thesis by (rule earlier_wellformed[OF child_precedes child_at])
        qed
        have valid_slots:
            "list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions
              sources occurrence_at occurrence_descriptors templates
              (sources!index) parent (lift_refs!index) lift_descriptors
              (slot_actions_table!index))
              [0..<comma_decisive_sector_period
                (comma_source_continuation_base (sources!index))]"
          using bound index parent_at
          by (auto simp: comma_semantic_b1_crt_constructed_occurrence_bound_def
              Let_def split: if_splits option.splits prod.splits)
        have refs_length:
            "length (lift_refs!index)=comma_decisive_sector_period
              (comma_source_continuation_base (sources!index))"
          using bound index parent_at
          by (auto simp: comma_semantic_b1_crt_constructed_occurrence_bound_def
              Let_def split: if_splits option.splits prod.splits)
        have slot_period: "slot<comma_decisive_sector_period
            (comma_source_continuation_base (sources!index))"
          using slot_bound refs_length by simp
        have selected_valid:
            "comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
              occurrence_descriptors templates (sources!index) parent
              (lift_refs!index) lift_descriptors (slot_actions_table!index) slot"
          by (rule comma_semantic_b1_crt_list_all_upt_index
            [OF valid_slots slot_period])
        have row:
            "comma_semantic_b1_crt_source_slot_action_row_certified
              (sources!index)
              (comma_decisive_sector_period
                (comma_source_continuation_base (sources!index)))
              (slot_actions_table!index)"
          using bound index parent_at
          by (auto simp: comma_semantic_b1_crt_constructed_occurrence_bound_def
              Let_def split: if_splits option.splits prod.splits)
        have action_eq:
            "(slot_actions_table!index)!slot=
              comma_semantic_b1_source_slot_action (sources!index) slot"
          by (rule comma_semantic_b1_crt_source_slot_action_row_certified_nth
            [OF row slot_period])
        have index_guard:
            "index<length sources \<and> index<length occurrence_descriptors \<and>
             index<length lift_refs \<and> index<length piece_refs"
          by (rule comma_semantic_b1_crt_constructed_occurrence_bound_index_guards
            [OF bound])
        note expanded_bound = bound[unfolded
          comma_semantic_b1_crt_constructed_occurrence_bound_def
          if_P[OF index_guard] parent_at option.simps Let_def]
        have normalized_source:
            "sources!index=comma_source_continuation_base (sources!index)"
          by (rule expanded_bound[THEN conjunct1])
        have selected_valid_plain:
            "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
              occurrence_descriptors templates (sources!index) parent
              (lift_refs!index) lift_descriptors slot"
          by (rule comma_semantic_b1_crt_lift_slot_valid_from_actions_implies_valid
            [OF row slot_period selected_valid])
        have source_goto:
            "\<exists>action_child shift child_occurrence.
              comma_semantic_b1_source_slot_action (sources!index) slot=
                Comma_Continuation_Goto action_child shift \<and>
              sources!child_index=comma_source_continuation_base action_child \<and>
              occurrence_at child_index=Some child_occurrence"
          by (rule comma_semantic_b1_crt_lift_slot_valid_goto_action
            [OF normalized_source slot_bound slot_period reference selected_valid_plain])
        then obtain action_child shift where source_action:
            "comma_semantic_b1_source_slot_action (sources!index) slot=
              Comma_Continuation_Goto action_child shift"
          by blast
        have action:
            "(slot_actions_table!index)!slot=
              Comma_Continuation_Goto action_child shift"
          using action_eq source_action by simp
        have binding:
            "comma_semantic_b1_crt_lift_binding_certified columns templates
              lift_column_ids lift_descriptors lift_cid"
          by (rule used_lift_bindings[OF index slot_bound reference])
        show "comma_semantic_b1_crt_lift_geometry_certified columns templates
            template_column_ids lift_column_ids lift_descriptors lift_cid"
          by (rule comma_semantic_b1_crt_used_lift_geometry_from_selected_child
            [OF reference action selected_valid child_at child_wellformed
              child_template_row binding])
      qed
      have parent_wellformed:
          "comma_semantic_b1_crt_occurrence_wellformed parent"
        apply (rule comma_semantic_b1_crt_constructed_occurrence_from_partition_or_mass
          [OF table_admitted bound _ parent_at parent_template_resolution])
          apply (rule earlier_wellformed; assumption)
         apply (rule disjI2[OF parent_mass])
        apply (rule used_geometries; assumption)
        done
      show ?thesis
      proof
        show "?wellformed index"
        proof (intro allI impI)
          fix selected
          assume selected_at: "occurrence_at index=Some selected"
          have selected_eq: "selected=parent" using selected_at parent_at by simp
          show "comma_semantic_b1_crt_occurrence_wellformed selected"
            using parent_wellformed selected_eq by simp
        qed
        show "?used_lifts index"
          using used_geometries by blast
      qed
    qed
  qed
  have all: "\<forall>index<length sources. ?certified index"
    by (rule comma_semantic_b1_crt_source_order_induction[OF step])
  show ?thesis using all by blast
qed

ML \<open>
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_constructed_occurrences_wellformed_and_used_lifts_from_mass};
  val _ = Comma_Proof_Profile.report
    "Semantic B1 constructor mass stage=occurrence-wellformed-complete";
\<close>

lemma comma_semantic_b1_crt_constructed_occurrences_catalog_geometry_from_mass:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and lift_refs :: "comma_semantic_b1_crt_lift_ref list list"
    and slot_actions_table :: "comma_source_continuation_action list list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and piece_refs :: "comma_semantic_b1_crt_piece_ref list list list"
  assumes table_admitted: "list_all (comma_crt_admitted 0) columns"
    and bounds:
      "list_all (\<lambda>index. comma_semantic_b1_crt_constructed_occurrence_bound
        columns templates template_column_ids lift_column_ids sources
        occurrence_at occurrence_descriptors lift_refs (slot_actions_table!index)
        lift_descriptors piece_refs index) [0..<length sources]"
    and template_masses:
      "\<And>index. index<length sources \<Longrightarrow>
        comma_semantic_b1_crt_template_mass_certified columns templates
          template_column_ids (fst (occurrence_descriptors!index))"
    and used_lift_bindings:
      "\<And>index slot child_index lift_cid. index<length sources \<Longrightarrow>
        slot<length (lift_refs!index) \<Longrightarrow>
        (lift_refs!index)!slot=
          Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
        comma_semantic_b1_crt_lift_binding_certified columns templates
          lift_column_ids lift_descriptors lift_cid"
  shows all_occurrences_wellformed:
      "\<forall>index<length sources. \<forall>parent.
        occurrence_at index=Some parent \<longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed parent"
    and parent_template_geometries:
      "\<forall>index<length sources.
        comma_semantic_b1_crt_template_geometry_certified columns templates
          template_column_ids (fst (occurrence_descriptors!index))"
    and used_lift_geometries:
      "\<forall>index<length sources. \<forall>slot child_index lift_cid.
        slot<length (lift_refs!index) \<longrightarrow>
        (lift_refs!index)!slot=
          Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<longrightarrow>
        comma_semantic_b1_crt_lift_geometry_certified columns templates
          template_column_ids lift_column_ids lift_descriptors lift_cid"
proof -
  have source_template_mass_facts:
      "\<And>index. index<length sources \<Longrightarrow>
        fst (occurrence_descriptors!index)<length templates \<and>
        fst (occurrence_descriptors!index)<length template_column_ids \<and>
        comma_semantic_b1_crt_column_ids_resolve columns
          (template_column_ids!fst (occurrence_descriptors!index))
          (templates!fst (occurrence_descriptors!index)) \<and>
        sum_list (map card (map comma_crt_set
          (templates!fst (occurrence_descriptors!index))))=924"
  proof -
    fix index assume index: "index<length sources"
    have facts:
        "fst (occurrence_descriptors!index)<length templates \<and>
         fst (occurrence_descriptors!index)<length template_column_ids \<and>
         comma_semantic_b1_crt_column_ids_resolve columns
           (template_column_ids!fst (occurrence_descriptors!index))
           (templates!fst (occurrence_descriptors!index)) \<and>
         sum_list (map card (map comma_crt_set
           (templates!fst (occurrence_descriptors!index))))=924"
      by (rule comma_semantic_b1_crt_template_mass_certified_cardinality
        [OF table_admitted template_masses[OF index]])
    show "fst (occurrence_descriptors!index)<length templates \<and>
        fst (occurrence_descriptors!index)<length template_column_ids \<and>
        comma_semantic_b1_crt_column_ids_resolve columns
          (template_column_ids!fst (occurrence_descriptors!index))
          (templates!fst (occurrence_descriptors!index)) \<and>
        sum_list (map card (map comma_crt_set
          (templates!fst (occurrence_descriptors!index))))=924"
      by (rule facts)
  qed
  have source_template_rows:
      "\<And>index. index<length sources \<Longrightarrow>
        fst (occurrence_descriptors!index)<length templates \<and>
        fst (occurrence_descriptors!index)<length template_column_ids \<and>
        comma_semantic_b1_crt_column_ids_resolve columns
          (template_column_ids!fst (occurrence_descriptors!index))
          (templates!fst (occurrence_descriptors!index))"
  proof -
    fix index assume index: "index<length sources"
    have facts: "fst (occurrence_descriptors!index)<length templates \<and>
        fst (occurrence_descriptors!index)<length template_column_ids \<and>
        comma_semantic_b1_crt_column_ids_resolve columns
          (template_column_ids!fst (occurrence_descriptors!index))
          (templates!fst (occurrence_descriptors!index)) \<and>
        sum_list (map card (map comma_crt_set
          (templates!fst (occurrence_descriptors!index))))=924"
      by (rule source_template_mass_facts[OF index])
    show "fst (occurrence_descriptors!index)<length templates \<and>
        fst (occurrence_descriptors!index)<length template_column_ids \<and>
        comma_semantic_b1_crt_column_ids_resolve columns
          (template_column_ids!fst (occurrence_descriptors!index))
          (templates!fst (occurrence_descriptors!index))"
      using facts by blast
  qed
  have parent_masses:
      "\<And>index. index<length sources \<Longrightarrow>
        sum_list (map card (map comma_crt_set
          (templates!fst (occurrence_descriptors!index))))=924"
  proof -
    fix index assume index: "index<length sources"
    have facts: "fst (occurrence_descriptors!index)<length templates \<and>
        fst (occurrence_descriptors!index)<length template_column_ids \<and>
        comma_semantic_b1_crt_column_ids_resolve columns
          (template_column_ids!fst (occurrence_descriptors!index))
          (templates!fst (occurrence_descriptors!index)) \<and>
        sum_list (map card (map comma_crt_set
          (templates!fst (occurrence_descriptors!index))))=924"
      by (rule source_template_mass_facts[OF index])
    show "sum_list (map card (map comma_crt_set
        (templates!fst (occurrence_descriptors!index))))=924"
      using facts by blast
  qed
  have induction_result:
      "(\<forall>index<length sources. \<forall>parent.
          occurrence_at index=Some parent \<longrightarrow>
          comma_semantic_b1_crt_occurrence_wellformed parent) \<and>
       (\<forall>index<length sources. \<forall>slot child_index lift_cid.
          slot<length (lift_refs!index) \<longrightarrow>
          (lift_refs!index)!slot=
            Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<longrightarrow>
          comma_semantic_b1_crt_lift_geometry_certified columns templates
            template_column_ids lift_column_ids lift_descriptors lift_cid)"
    by (rule comma_semantic_b1_crt_constructed_occurrences_wellformed_and_used_lifts_from_mass
      [OF table_admitted bounds source_template_rows parent_masses used_lift_bindings])
  have all_wellformed:
      "\<forall>index<length sources. \<forall>parent.
        occurrence_at index=Some parent \<longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed parent"
    by (rule conjunct1[OF induction_result])
  show "\<forall>index<length sources. \<forall>parent.
      occurrence_at index=Some parent \<longrightarrow>
      comma_semantic_b1_crt_occurrence_wellformed parent"
    by (rule all_wellformed)
  ML_prf \<open>Comma_Proof_Profile.report
    "Semantic B1 constructor mass stage=catalog-parent-geometry-entered"\<close>
  show "\<forall>index<length sources.
      comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids (fst (occurrence_descriptors!index))"
  proof (intro allI impI)
    fix index assume index: "index<length sources"
    have bound:
        "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
          template_column_ids lift_column_ids sources occurrence_at
          occurrence_descriptors lift_refs (slot_actions_table!index)
          lift_descriptors piece_refs index"
      by (rule comma_semantic_b1_crt_list_all_upt_index[OF bounds index])
    have cid_bound: "fst (occurrence_descriptors!index)<length templates"
      by (rule comma_semantic_b1_crt_constructed_occurrence_bound_template_cid
        [OF bound])
    have parent_present: "occurrence_at index\<noteq>None"
      by (rule comma_semantic_b1_crt_constructed_occurrence_bound_parent_present
        [OF bound])
    obtain parent where parent_at: "occurrence_at index=Some parent"
      using parent_present by (cases "occurrence_at index") auto
    have index_guard:
        "index<length sources \<and> index<length occurrence_descriptors \<and>
         index<length lift_refs \<and> index<length piece_refs"
      by (rule comma_semantic_b1_crt_constructed_occurrence_bound_index_guards
        [OF bound])
    note expanded_bound = bound[unfolded
      comma_semantic_b1_crt_constructed_occurrence_bound_def
      if_P[OF index_guard] parent_at option.simps Let_def]
    obtain template_cid rebase descriptor_beta where descriptor_at:
        "occurrence_descriptors!index=(template_cid,(rebase,descriptor_beta))"
      by (cases "occurrence_descriptors!index";
          cases "snd (occurrence_descriptors!index)") auto
    have parent_columns_at_cid:
        "comma_semantic_b1_crt_occurrence_columns parent=templates!template_cid"
      using expanded_bound descriptor_at
      by (simp only: descriptor_at prod.case; blast)
    have parent_columns:
        "comma_semantic_b1_crt_occurrence_columns parent=
          templates!fst (occurrence_descriptors!index)"
      using parent_columns_at_cid descriptor_at by simp
    have parent_wellformed:
        "comma_semantic_b1_crt_occurrence_wellformed parent"
      using all_wellformed index parent_at by blast
    have source_rows:
        "fst (occurrence_descriptors!index)<length templates \<and>
         fst (occurrence_descriptors!index)<length template_column_ids \<and>
        comma_semantic_b1_crt_column_ids_resolve columns
          (template_column_ids!fst (occurrence_descriptors!index))
          (templates!fst (occurrence_descriptors!index))"
      by (rule source_template_rows[OF index])
    have row_bound: "fst (occurrence_descriptors!index)<length template_column_ids"
      by (rule conjunct1[OF conjunct2[OF source_rows]])
    have row_resolution:
        "comma_semantic_b1_crt_column_ids_resolve columns
          (template_column_ids!fst (occurrence_descriptors!index))
          (templates!fst (occurrence_descriptors!index))"
      by (rule conjunct2[OF conjunct2[OF source_rows]])
    show "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids (fst (occurrence_descriptors!index))"
      by (rule comma_semantic_b1_crt_template_geometry_from_resolved_wellformed_occurrence
        [OF cid_bound row_bound parent_columns row_resolution parent_wellformed])
  qed
  ML_prf \<open>Comma_Proof_Profile.report
    "Semantic B1 constructor mass stage=catalog-parent-geometry-complete"\<close>
  show "\<forall>index<length sources. \<forall>slot child_index lift_cid.
      slot<length (lift_refs!index) \<longrightarrow>
      (lift_refs!index)!slot=
        Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<longrightarrow>
      comma_semantic_b1_crt_lift_geometry_certified columns templates
        template_column_ids lift_column_ids lift_descriptors lift_cid"
    by (rule conjunct2[OF induction_result])
qed

ML \<open>
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_constructed_occurrences_catalog_geometry_from_mass};
  val _ = Comma_Proof_Profile.report
    "Semantic B1 constructor mass stage=catalog-geometry-complete";
\<close>

ML \<open>
  val bundle = @{thms
    comma_semantic_b1_crt_list_all_remdups
    comma_semantic_b1_crt_template_mass_certified_cardinality
    comma_semantic_b1_crt_used_template_masses_cover_sources
    comma_semantic_b1_crt_template_geometry_from_resolved_wellformed_occurrence
    comma_semantic_b1_crt_lift_geometry_from_binding_and_template_geometry
    comma_semantic_b1_crt_used_lift_geometry_from_child
    comma_semantic_b1_crt_used_lift_geometry_from_selected_child
    comma_semantic_b1_crt_constructed_occurrences_wellformed_and_used_lifts_from_mass
    comma_semantic_b1_crt_constructed_occurrences_catalog_geometry_from_mass};
  val _ = if null (Thm_Deps.all_oracles bundle) then ()
    else error "Constructed occurrence mass bridge has oracle dependencies";
  val _ = Comma_Proof_Profile.report
    "Semantic B1 constructor mass stage=oracle-audit-complete";
  val _ = Thm.consolidate bundle;
  val _ = Comma_Proof_Profile.report
    "Semantic B1 constructor mass stage=bundle-consolidated";
\<close>

end
