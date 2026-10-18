theory Comma_Semantic_B1_CRT_Compact_Refinement
  imports Comma_Semantic_B1.Comma_Semantic_B1_CRT_Constructed_Refinement
    Comma_Semantic_B1.Comma_Semantic_B1_CRT_Local_Cover_Candidate
begin
text \<open>Concrete B1 soundness is driven by one occurrence-local coverage
witness per source, with template geometry shared by normalized template CID.
No per-output construction-piece table is part of the certificate.\<close>

lemma comma_semantic_b1_crt_used_template_geometries_cover_sources:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
  assumes descriptor_extent: "length occurrence_descriptors = length sources"
    and used_geometries:
      "list_all (comma_semantic_b1_crt_template_geometry_certified
        columns templates template_column_ids)
        (remdups (map fst occurrence_descriptors))"
  shows "\<And>index. index < length sources \<Longrightarrow>
    comma_semantic_b1_crt_template_geometry_certified columns templates
      template_column_ids (fst (occurrence_descriptors!index))"
proof -
  fix index assume index: "index < length sources"
  have descriptor_bound: "index < length occurrence_descriptors"
    using index descriptor_extent by simp
  have selected:
      "fst (occurrence_descriptors!index) \<in>
        set (remdups (map fst occurrence_descriptors))"
  proof -
    have descriptor_mem: "occurrence_descriptors!index \<in>
        set occurrence_descriptors"
      by (rule nth_mem[OF descriptor_bound])
    have selected_mem: "fst (occurrence_descriptors!index) \<in>
        set (map fst occurrence_descriptors)"
      using descriptor_mem by auto
    show ?thesis using selected_mem by simp
  qed
  show "comma_semantic_b1_crt_template_geometry_certified columns templates
      template_column_ids (fst (occurrence_descriptors!index))"
    using used_geometries selected by (auto simp: list_all_iff)
qed

definition comma_semantic_b1_crt_used_lift_cids ::
    "comma_semantic_b1_crt_lift_ref list list \<Rightarrow> nat list" where
  "comma_semantic_b1_crt_used_lift_cids refs =
    remdups (concat (map (\<lambda>reference.
      case reference of
        Comma_B1_Lift_Terminal_Ref _ _ \<Rightarrow> []
      | Comma_B1_Lift_Goto_Ref _ _ lift_cid \<Rightarrow> [lift_cid])
      (concat refs)))"

lemma comma_semantic_b1_crt_used_lift_cids_contains_reference:
  assumes source: "index < length refs"
    and slot: "slot < length (refs!index)"
    and reference:
      "(refs!index)!slot = Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
  shows "lift_cid \<in> set (comma_semantic_b1_crt_used_lift_cids refs)"
proof -
  have source_mem: "refs!index \<in> set refs"
    by (rule nth_mem[OF source])
  have slot_mem: "(refs!index)!slot \<in> set (refs!index)"
    by (rule nth_mem[OF slot])
  have ref_mem: "Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<in>
      set (concat refs)"
    using source_mem slot_mem reference by auto
  show ?thesis
    using ref_mem
    by (auto simp: comma_semantic_b1_crt_used_lift_cids_def)
qed

definition comma_semantic_b1_crt_compact_occurrence_check ::
    "comma_crt_column list list \<Rightarrow> comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_descriptor list \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
      occurrence_descriptors lift_refs lift_descriptors index \<longleftrightarrow>
    (if index < length sources \<and> index < length occurrence_descriptors \<and>
        index < length lift_refs then
       (case occurrence_at index of
          None \<Rightarrow> False
        | Some parent \<Rightarrow>
          (let source = sources!index; refs = lift_refs!index in
           source = comma_source_continuation_base source \<and>
           comma_round_admitted source \<and>
           (case occurrence_descriptors!index of
              (template_cid, (rebase, beta)) \<Rightarrow>
                template_cid < length templates \<and>
                rebase = comma_semantic_b1_crt_occurrence_rebase parent \<and>
                beta = comma_semantic_b1_crt_occurrence_beta parent \<and>
                comma_semantic_b1_crt_occurrence_columns parent =
                  templates!template_cid) \<and>
           comma_semantic_b1_crt_occurrence_binding_check parent \<and>
           list_all comma_crt_supported
             (comma_semantic_b1_crt_occurrence_columns parent) \<and>
           comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
             occurrence_descriptors templates source parent refs lift_descriptors \<and>
           list_all (\<lambda>slot.
             case refs!slot of
               Comma_B1_Lift_Terminal_Ref ref_slot _ \<Rightarrow> ref_slot = slot
             | Comma_B1_Lift_Goto_Ref ref_slot child_index _ \<Rightarrow>
                 ref_slot = slot \<and> child_index < index)
             [0..<length refs]))
     else False)"

lemma comma_semantic_b1_crt_compact_occurrence_check_exposes:
  assumes checked:
      "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
        occurrence_descriptors lift_refs lift_descriptors index"
    and occurrence: "occurrence_at index = Some parent"
  shows "sources!index = comma_source_continuation_base (sources!index) \<and>
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
  using checked occurrence
  by (auto simp: comma_semantic_b1_crt_compact_occurrence_check_def
      Let_def split: if_splits option.splits prod.splits)

lemma comma_semantic_b1_crt_compact_occurrence_check_total:
  assumes checked:
      "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
        occurrence_descriptors lift_refs lift_descriptors index"
    and index: "index < length sources"
  shows "\<exists>parent. occurrence_at index = Some parent"
  using checked index
  by (cases "occurrence_at index")
    (auto simp: comma_semantic_b1_crt_compact_occurrence_check_def
      split: if_splits option.splits prod.splits)

lemma comma_semantic_b1_crt_compact_occurrence_check_wellformed:
  assumes checked:
      "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
        occurrence_descriptors lift_refs lift_descriptors index"
    and occurrence: "occurrence_at index = Some parent"
    and template_geometry:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids (fst (occurrence_descriptors!index))"
  shows "comma_semantic_b1_crt_occurrence_wellformed parent"
proof -
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
      [OF checked occurrence])
  have selected_template:
      "comma_semantic_b1_crt_occurrence_columns parent =
        templates ! fst (occurrence_descriptors!index)"
    using exposed by blast
  have binding: "comma_semantic_b1_crt_occurrence_binding_check parent"
    using exposed by blast
  have supported:
      "list_all comma_crt_supported
        (comma_semantic_b1_crt_occurrence_columns parent)"
    using exposed by blast
  show ?thesis
    by (rule comma_semantic_b1_crt_occurrence_wellformed_from_template_geometry
      [OF binding template_geometry selected_template supported])
qed

lemma comma_semantic_b1_crt_compact_occurrences_candidate_matches:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and lift_refs :: "comma_semantic_b1_crt_lift_ref list list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and children :: "comma_finite_position \<Rightarrow>
      comma_semantic_b1_crt_occurrence option"
  assumes descriptor_extent:
      "length occurrence_descriptors = length sources"
    and compact:
      "list_all (\<lambda>index.
        comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
          occurrence_descriptors lift_refs lift_descriptors index)
        [0..<length sources]"
    and template_geometries:
      "list_all (comma_semantic_b1_crt_template_geometry_certified
        columns templates template_column_ids)
        (remdups (map fst occurrence_descriptors))"
    and children_resolve:
      "\<And>index. index < length sources \<Longrightarrow>
        children (sources!index) = occurrence_at index"
  shows "\<forall>index<length sources. \<forall>parent.
    occurrence_at index = Some parent \<longrightarrow>
    comma_semantic_b1_crt_occurrence_candidate_matches children
      (sources!index) parent"
proof -
  have check_at:
      "\<And>index. index < length sources \<Longrightarrow>
        comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
          occurrence_descriptors lift_refs lift_descriptors index"
  proof -
    fix index
    assume index: "index < length sources"
    have member: "index \<in> set [0..<length sources]" using index by simp
    show "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
        occurrence_descriptors lift_refs lift_descriptors index"
      using compact member by (auto simp: list_all_iff)
  qed
  have geometry_at:
      "\<And>index. index < length sources \<Longrightarrow>
        comma_semantic_b1_crt_template_geometry_certified columns templates
          template_column_ids (fst (occurrence_descriptors!index))"
    by (rule comma_semantic_b1_crt_used_template_geometries_cover_sources
      [OF descriptor_extent template_geometries])
  have each_parent:
      "\<And>index parent. index < length sources \<Longrightarrow>
        occurrence_at index = Some parent \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_candidate_matches children
          (sources!index) parent"
  proof -
    fix index parent
    assume index: "index < length sources"
      and parent_at: "occurrence_at index = Some parent"
      have checked_parent:
          "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
            occurrence_descriptors lift_refs lift_descriptors index"
        by (rule check_at[OF index])
      have witness:
          "comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
            occurrence_descriptors templates (sources!index) parent
            (lift_refs!index) lift_descriptors"
        using comma_semantic_b1_crt_compact_occurrence_check_exposes
          [OF checked_parent parent_at] by blast
      have parent_wellformed:
          "comma_semantic_b1_crt_occurrence_wellformed parent"
        by (rule comma_semantic_b1_crt_compact_occurrence_check_wellformed
          [OF checked_parent parent_at geometry_at[OF index]])
      have referenced_children_wellformed:
          "\<And>slot child_index lift_cid child. slot < length (lift_refs!index) \<Longrightarrow>
            (lift_refs!index)!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
            occurrence_at child_index=Some child \<Longrightarrow>
            comma_semantic_b1_crt_occurrence_wellformed child"
      proof -
        fix slot child_index lift_cid child
        assume slot: "slot < length (lift_refs!index)"
          and ref: "(lift_refs!index)!slot=
            Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
          and child_at: "occurrence_at child_index=Some child"
        have child_bound: "child_index < length sources"
          by (rule comma_semantic_b1_crt_lift_local_cover_child_index_bound
            [OF witness slot ref])
        have child_check:
            "comma_semantic_b1_crt_compact_occurrence_check templates sources occurrence_at
              occurrence_descriptors lift_refs lift_descriptors child_index"
          by (rule check_at[OF child_bound])
        show "comma_semantic_b1_crt_occurrence_wellformed child"
          by (rule comma_semantic_b1_crt_compact_occurrence_check_wellformed
            [OF child_check child_at geometry_at[OF child_bound]])
      qed
    show "comma_semantic_b1_crt_occurrence_candidate_matches children
        (sources!index) parent"
      by (rule comma_semantic_b1_crt_lift_local_cover_candidate_matches
        [OF witness parent_wellformed referenced_children_wellformed children_resolve])
  qed
  show ?thesis using each_parent by blast
qed

ML \<open>
  Thm.consolidate @{thms comma_semantic_b1_crt_compact_occurrences_candidate_matches};
  val _ = if null (Thm_Deps.all_oracles @{thms
      comma_semantic_b1_crt_compact_occurrences_candidate_matches})
    then () else error "Comma compact occurrence refinement used an oracle"
\<close>
end
