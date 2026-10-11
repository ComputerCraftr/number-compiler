theory Comma_Semantic_B1_CRT_Constructed_Occurrence
  imports "HOL-Library.Product_Lexorder"
    Comma_Semantic_B1_CRT_Occurrence_Bounds
begin
ML \<open>Comma_Proof_Profile.report "Constructed occurrence stage=entered"\<close>
text \<open>The certificate binds every sorted source origin once to its exact slot action, child output, and parent destination; it neither enumerates phases nor assumes parent geometry.\<close>
lemma comma_semantic_b1_crt_constructed_live_source_partition:
  assumes partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map (\<lambda>entry. comma_crt_set (fst entry)) entries)"
    and admitted:
      "list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry)) entries"
  shows "comma_semantic_b1_crt_cells_partition {..<924}
    (map (\<lambda>entry. comma_crt_set (fst entry))
      (filter (\<lambda>entry. comma_crt_supported (fst entry)) entries))"
proof -
  have filtered:
    "map (\<lambda>entry. comma_crt_set (fst entry))
        (filter (\<lambda>entry. comma_crt_supported (fst entry)) entries) =
      filter (\<lambda>cell. cell\<noteq>{})
        (map (\<lambda>entry. comma_crt_set (fst entry)) entries)"
    using admitted
  proof (induction entries)
    case Nil
    then show ?case by simp
  next
    case (Cons entry entries)
    have head_admitted: "comma_crt_admitted 0 (fst entry)"
      and tail_admitted:
        "list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry)) entries"
      using Cons.prems by simp_all
    have tail:
      "map (\<lambda>entry. comma_crt_set (fst entry))
          (filter (\<lambda>entry. comma_crt_supported (fst entry)) entries) =
        filter (\<lambda>cell. cell\<noteq>{})
          (map (\<lambda>entry. comma_crt_set (fst entry)) entries)"
      by (rule Cons.IH[OF tail_admitted])
    show ?case
      using tail comma_crt_supported_nonempty[OF head_admitted]
      by simp
  qed
  show ?thesis
    using comma_semantic_b1_crt_filter_empty_cells_partition[OF partition]
      filtered by simp
qed
lemma comma_semantic_b1_crt_constructed_piece_entry:
  fixes columns :: "comma_crt_column list"
    and lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and source :: comma_finite_position
    and parent :: comma_semantic_b1_crt_occurrence
    and row :: nat
    and piece :: comma_semantic_b1_crt_piece_ref
  assumes matches:
      "comma_semantic_b1_crt_constructed_piece_matches columns
        lift_column_ids sources occurrence_at refs source parent row piece"
    and supported:
      "comma_crt_supported (columns!comma_semantic_b1_crt_piece_cid piece)"
  shows "\<exists>entry\<in>set (comma_semantic_b1_crt_constructed_source_live_entries
      columns lift_column_ids occurrence_at refs source).
      fst entry=comma_semantic_b1_crt_constructed_piece_origin piece \<and>
      comma_crt_set (fst (snd entry))=comma_crt_set
        (columns!comma_semantic_b1_crt_piece_cid piece) \<and>
      snd (snd entry)=comma_semantic_b1_crt_occurrence_beta parent!row"
proof (cases piece)
  case (Comma_B1_Piece_Terminal piece_period slot cid parent_column)
  let ?period="comma_decisive_sector_period
    (comma_source_continuation_base source)"
  have slot_bound: "slot<?period" and ref_bound: "slot<length refs"
    and ref_eq: "refs!slot=Comma_B1_Lift_Terminal_Ref slot row"
    and terminal:
      "\<exists>result. comma_semantic_b1_terminal_action_result
        (comma_semantic_b1_source_slot_action source slot)=Some result \<and>
        comma_semantic_b1_crt_occurrence_beta parent!row=result"
    and column_eq:
      "columns!cid=comma_crt_source_scope_column (?period,slot)"
    using matches Comma_B1_Piece_Terminal
    by (auto simp: comma_semantic_b1_crt_constructed_piece_matches_def
      Let_def split: option.splits)
  from terminal obtain result where action_result:
    "comma_semantic_b1_terminal_action_result
      (comma_semantic_b1_source_slot_action source slot)=Some result"
    and beta_eq: "comma_semantic_b1_crt_occurrence_beta parent!row=result"
    by blast
  let ?column="comma_crt_source_scope_column (?period,slot)"
  let ?entry="((slot,0),(?column,result))"
  have terminal_supported: "comma_crt_supported ?column"
    using supported column_eq Comma_B1_Piece_Terminal
    by (simp add: comma_semantic_b1_crt_piece_cid.simps)
  have slot_entry:
    "?entry \<in> set (comma_semantic_b1_crt_constructed_slot_live_entries
      columns lift_column_ids occurrence_at refs source slot)"
    using slot_bound ref_bound ref_eq action_result terminal_supported
    by (simp add: comma_semantic_b1_crt_constructed_slot_live_entries_def
      Let_def)
  have slot_list_member:
    "slot \<in> set [0..< ?period]"
    using slot_bound by simp
  have mapped_slot:
    "comma_semantic_b1_crt_constructed_slot_live_entries
       columns lift_column_ids occurrence_at refs source slot \<in>
      set (map (comma_semantic_b1_crt_constructed_slot_live_entries
        columns lift_column_ids occurrence_at refs source) [0..< ?period])"
    using slot_list_member by (auto simp: set_map)
  have source_entry:
    "?entry \<in> set (comma_semantic_b1_crt_constructed_source_live_entries
      columns lift_column_ids occurrence_at refs source)"
    using slot_entry mapped_slot
    by (auto simp: comma_semantic_b1_crt_constructed_source_live_entries_def
      set_concat)
  show ?thesis
    using source_entry beta_eq column_eq Comma_B1_Piece_Terminal
    by (intro bexI[where x="?entry"])
      (auto simp: comma_semantic_b1_crt_constructed_piece_origin_def
        comma_semantic_b1_crt_constructed_source_live_entries_def
        comma_semantic_b1_crt_piece_cid.simps)
next
  case (Comma_B1_Piece_Goto piece_period slot child_index child_column
      lift_cid cid parent_column)
  let ?period="comma_decisive_sector_period
    (comma_source_continuation_base source)"
  have goto_facts:
    "\<exists>child_source shift child_occurrence.
       slot<?period \<and> slot<length refs \<and>
       refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<and>
       lift_cid<length lift_column_ids \<and>
       comma_semantic_b1_source_slot_action source slot=
         Comma_Continuation_Goto child_source shift \<and>
       occurrence_at child_index=Some child_occurrence \<and>
       child_column<length
         (comma_semantic_b1_crt_occurrence_beta child_occurrence) \<and>
       length (lift_column_ids!lift_cid)=
         length (comma_semantic_b1_crt_occurrence_beta child_occurrence) \<and>
       comma_semantic_b1_crt_occurrence_beta parent!row=
         comma_semantic_b1_crt_occurrence_beta child_occurrence!child_column \<and>
       cid=lift_column_ids!lift_cid!child_column"
    using matches Comma_B1_Piece_Goto
    by (auto simp: comma_semantic_b1_crt_constructed_piece_matches_def
      Let_def split: option.splits comma_source_continuation_action.splits)
  from goto_facts obtain child_source shift child_occurrence where slot_bound:
    "slot<?period"
    and ref_bound: "slot<length refs"
    and ref_eq: "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    and lift_bound: "lift_cid<length lift_column_ids"
    and action_eq:
      "comma_semantic_b1_source_slot_action source slot=
        Comma_Continuation_Goto child_source shift"
    and child_at: "occurrence_at child_index=Some child_occurrence"
    and child_column_bound:
      "child_column<length
        (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
    and width_eq:
      "length (lift_column_ids!lift_cid)=
        length (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
    and beta_eq:
      "comma_semantic_b1_crt_occurrence_beta parent!row=
        comma_semantic_b1_crt_occurrence_beta child_occurrence!child_column"
    and cid_eq: "cid=lift_column_ids!lift_cid!child_column"
    by blast
  let ?child_beta="comma_semantic_b1_crt_occurrence_beta child_occurrence"
  let ?column="columns!(lift_column_ids!lift_cid!child_column)"
  let ?entry="((slot,Suc child_column),(?column,?child_beta!child_column))"
  have child_supported: "comma_crt_supported ?column"
    using supported cid_eq Comma_B1_Piece_Goto
    by (simp add: comma_semantic_b1_crt_piece_cid.simps)
  have child_slot:
    "child_column \<in> set (filter (\<lambda>j. comma_crt_supported
        (columns!(lift_column_ids!lift_cid!j))) [0..<length ?child_beta])"
    using child_column_bound child_supported by (simp add: set_filter)
  have slot_entry:
    "?entry \<in> set (comma_semantic_b1_crt_constructed_slot_live_entries
      columns lift_column_ids occurrence_at refs source slot)"
    using slot_bound ref_bound ref_eq lift_bound action_eq child_at width_eq
      child_slot
    by (simp add: comma_semantic_b1_crt_constructed_slot_live_entries_def
      Let_def)
  have slot_list_member:
    "slot \<in> set [0..< ?period]"
    using slot_bound by simp
  have mapped_slot:
    "comma_semantic_b1_crt_constructed_slot_live_entries
       columns lift_column_ids occurrence_at refs source slot \<in>
      set (map (comma_semantic_b1_crt_constructed_slot_live_entries
        columns lift_column_ids occurrence_at refs source) [0..< ?period])"
    using slot_list_member by (auto simp: set_map)
  have source_entry:
    "?entry \<in> set (comma_semantic_b1_crt_constructed_source_live_entries
      columns lift_column_ids occurrence_at refs source)"
    using slot_entry mapped_slot
    by (auto simp: comma_semantic_b1_crt_constructed_source_live_entries_def
      set_concat)
  show ?thesis
    using source_entry beta_eq cid_eq Comma_B1_Piece_Goto
    by (intro bexI[where x="?entry"])
      (auto simp: comma_semantic_b1_crt_constructed_piece_origin_def
        comma_semantic_b1_crt_piece_cid.simps)
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_piece_entry}]; Comma_Proof_Profile.report "Constructed occurrence: piece binding checked"\<close>
lemma comma_semantic_b1_crt_constructed_source_origins_distinct:
  "distinct (comma_semantic_b1_crt_constructed_source_origins columns lift_column_ids sources occurrence_at refs source)"
proof -
  let ?period="comma_decisive_sector_period
    (comma_source_continuation_base source)"
  let ?slots="[0..<?period]"
  let ?rows="\<lambda>slot. comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids sources occurrence_at refs source slot"
  have slots_distinct: "distinct ?slots" by simp
  have rows_distinct: "\<And>slot. slot \<in> set ?slots \<Longrightarrow>
      distinct (?rows slot)"
    unfolding comma_semantic_b1_crt_constructed_slot_origins_def Let_def
    by (simp only: comma_semantic_b1_crt_tagged_map_distinct;
      auto simp: distinct_map inj_on_def
      split: comma_semantic_b1_crt_lift_ref.splits
        comma_source_continuation_action.splits option.splits)
  have rows_tagged: "\<And>slot. slot \<in> set ?slots \<Longrightarrow>
      list_all (\<lambda>entry. fst entry=slot) (?rows slot)"
    by (auto intro: comma_semantic_b1_crt_constructed_slot_origins_tagged)
  have tagged: "\<And>slot entry. slot \<in> set ?slots \<Longrightarrow>
      entry \<in> set (?rows slot) \<Longrightarrow> fst entry=slot"
    using rows_tagged by (auto simp: list_all_iff)
  have "distinct (concat (map ?rows ?slots))"
    by (rule comma_semantic_b1_crt_distinct_concat_tagged_rows
      [OF slots_distinct rows_distinct tagged])
  then show ?thesis
    by (simp add: comma_semantic_b1_crt_constructed_source_origins_def)
qed
lemma comma_semantic_b1_crt_constructed_occurrence_wellformed:
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
    and index :: nat
    and parent :: comma_semantic_b1_crt_occurrence
  assumes table_admitted: "list_all (comma_crt_admitted 0) columns"
    and bound: "comma_semantic_b1_crt_constructed_occurrence_bound columns templates template_column_ids lift_column_ids sources occurrence_at occurrence_descriptors lift_refs (slot_actions_table!index) lift_descriptors piece_refs index"
    and earlier: "\<And>child_index child. child_index<index \<Longrightarrow> occurrence_at child_index=Some child \<Longrightarrow> comma_semantic_b1_crt_occurrence_wellformed child"
    and parent_at: "occurrence_at index=Some parent"
    and parent_template_geometry:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids (fst (occurrence_descriptors!index))"
    and used_lift_geometries:
      "\<And>slot child_index lift_cid. slot<length (lift_refs!index) \<Longrightarrow>
        (lift_refs!index)!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
        comma_semantic_b1_crt_lift_geometry_certified columns templates
          template_column_ids lift_column_ids lift_descriptors lift_cid"
  shows "comma_semantic_b1_crt_occurrence_wellformed parent"
proof -
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: parent induction entered"\<close>
  let ?source="sources!index"
  let ?refs="lift_refs!index"
  let ?actions="slot_actions_table!index"
  let ?rows="piece_refs!index"
  let ?beta="comma_semantic_b1_crt_occurrence_beta parent"
  let ?period="comma_decisive_sector_period (comma_source_continuation_base ?source)"
  let ?live="comma_semantic_b1_crt_constructed_source_live_entries columns lift_column_ids occurrence_at ?refs ?source"
  let ?entries="map (\<lambda>entry. (fst entry, (comma_crt_set (fst (snd entry)),snd (snd entry)))) ?live"
  let ?labels="map (\<lambda>entry. snd (snd entry)) ?entries"
  let ?cells="map (\<lambda>entry. fst (snd entry)) ?entries"
  let ?origins="comma_semantic_b1_crt_constructed_source_origins columns lift_column_ids sources occurrence_at ?refs ?source"
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: entering parent-bound extraction"\<close>
  obtain template_cid descriptor_rebase descriptor_beta where descriptor_at:
    "occurrence_descriptors!index=(template_cid,(descriptor_rebase,descriptor_beta))"
    by (cases "occurrence_descriptors!index";
        cases "snd (occurrence_descriptors!index)") auto
  have index_guard:
    "index<length sources \<and> index<length occurrence_descriptors \<and>
     index<length lift_refs \<and> index<length piece_refs"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_index_guards
      [OF bound])
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: index guard submitted"\<close>
  have normalized: "?source=comma_source_continuation_base ?source"
    using bound index_guard parent_at
    by (auto simp: comma_semantic_b1_crt_constructed_occurrence_bound_def
        Let_def)
  have source_is_base: "comma_source_continuation_base ?source=?source"
    by (rule sym[OF normalized])
  have bound_body:
    "?source=comma_source_continuation_base ?source \<and>
     comma_round_admitted ?source \<and>
     length ?refs=?period \<and>
     map comma_semantic_b1_crt_lift_ref_slot ?refs=[0..<?period] \<and>
     length occurrence_descriptors=length sources \<and>
     length ?rows=length ?beta \<and>
     template_cid<length templates \<and>
     descriptor_rebase=comma_semantic_b1_crt_occurrence_rebase parent \<and>
     descriptor_beta=?beta \<and>
     comma_semantic_b1_crt_occurrence_columns parent=templates!template_cid \<and>
     comma_semantic_b1_crt_occurrence_binding_check parent \<and>
     ?beta\<noteq>[] \<and> distinct ?beta \<and>
     comma_semantic_b1_crt_source_slot_action_row_certified ?source ?period ?actions \<and>
     list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
       occurrence_descriptors templates ?source parent ?refs lift_descriptors ?actions)
       [0..<?period] \<and>
     list_all (\<lambda>slot.
       comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
         template_column_ids lift_column_ids occurrence_descriptors
         lift_descriptors index ?refs slot) [0..<?period] \<and>
     sort (map comma_semantic_b1_crt_constructed_piece_origin (concat ?rows))=?origins \<and>
     list_all (\<lambda>row.
       comma_semantic_b1_crt_group_construction_bound columns
         (comma_semantic_b1_crt_occurrence_rebase parent) row
         (template_column_ids!template_cid!row) (?rows!row) \<and>
       list_all (comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions columns
         lift_column_ids sources occurrence_at ?refs ?source ?actions parent row)
         (?rows!row)) [0..<length ?beta]"
    using bound index_guard parent_at descriptor_at source_is_base
    by (simp add: comma_semantic_b1_crt_constructed_occurrence_bound_def
        Let_def)
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: bound body submitted"\<close>
  have index_bound: "index<length sources"
    using index_guard by blast
  have source_admitted: "comma_round_admitted ?source"
    and refs_length: "length ?refs=?period"
    and refs_slots: "map comma_semantic_b1_crt_lift_ref_slot ?refs=[0..<?period]"
    and rows_width: "length ?rows=length ?beta"
    and parent_columns:
      "comma_semantic_b1_crt_occurrence_columns parent=templates!template_cid"
    and parent_binding: "comma_semantic_b1_crt_occurrence_binding_check parent"
    and action_row_certified:
      "comma_semantic_b1_crt_source_slot_action_row_certified ?source ?period ?actions"
    and slots_valid_from_actions:
      "list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions sources
        occurrence_at occurrence_descriptors templates ?source parent ?refs
        lift_descriptors ?actions) [0..<?period]"
    and slot_certificates: "list_all (\<lambda>slot.
      comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
        template_column_ids lift_column_ids occurrence_descriptors lift_descriptors
        index ?refs slot) [0..<?period]"
    and piece_origin_sort:
      "sort (map comma_semantic_b1_crt_constructed_piece_origin
        (concat ?rows))=?origins"
    and rows_bindings_from_actions: "list_all (\<lambda>row.
      comma_semantic_b1_crt_group_construction_bound columns
        (comma_semantic_b1_crt_occurrence_rebase parent) row
        (template_column_ids!template_cid!row) (?rows!row) \<and>
      list_all (comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions columns
        lift_column_ids sources occurrence_at ?refs ?source ?actions parent row)
        (?rows!row)) [0..<length ?beta]"
    using bound_body
    by (auto simp: source_is_base)
  have parent_geometry_certified:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids template_cid"
    using parent_template_geometry descriptor_at by simp
  have slots_valid:
      "list_all (comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
        occurrence_descriptors templates ?source parent ?refs lift_descriptors)
        [0..<?period]"
  proof (unfold list_all_iff, intro ballI)
    fix slot assume member: "slot\<in>set [0..<?period]"
    have slot: "slot<?period" using member by simp
    have fact:
        "comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
          occurrence_descriptors templates ?source parent ?refs lift_descriptors
          ?actions slot"
      using slots_valid_from_actions member by (auto simp: list_all_iff)
    show "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
        occurrence_descriptors templates ?source parent ?refs lift_descriptors slot"
      by (rule comma_semantic_b1_crt_lift_slot_valid_from_actions_implies_valid
        [OF action_row_certified slot fact])
  qed
  have rows_certificate_template: "list_all (\<lambda>row.
      comma_semantic_b1_crt_group_construction_bound columns
        (comma_semantic_b1_crt_occurrence_rebase parent) row
        (template_column_ids!template_cid!row) (?rows!row) \<and>
      list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
        lift_column_ids sources occurrence_at ?refs ?source parent row)
        (?rows!row)) [0..<length ?beta]"
  proof (rule iffD2[OF list_all_iff], intro ballI)
    fix row assume member: "row\<in>set [0..<length ?beta]"
    have row_fact:
        "comma_semantic_b1_crt_group_construction_bound columns
            (comma_semantic_b1_crt_occurrence_rebase parent) row
            (template_column_ids!template_cid!row) (?rows!row) \<and>
         list_all (comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions
            columns lift_column_ids sources occurrence_at ?refs ?source ?actions
            parent row) (?rows!row)"
      using rows_bindings_from_actions member by (auto simp: list_all_iff)
    have bindings:
        "list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
          lift_column_ids sources occurrence_at ?refs ?source parent row)
          (?rows!row)"
      using row_fact
      by (auto simp: list_all_iff
        dest: comma_semantic_b1_crt_constructed_piece_binding_from_actions_old)
    show "comma_semantic_b1_crt_group_construction_bound columns
          (comma_semantic_b1_crt_occurrence_rebase parent) row
          (template_column_ids!template_cid!row) (?rows!row) \<and>
       list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
          lift_column_ids sources occurrence_at ?refs ?source parent row)
          (?rows!row)"
      using row_fact bindings by blast
  qed
  have rows_certificate: "list_all (\<lambda>row.
      comma_semantic_b1_crt_group_construction_bound columns
        (comma_semantic_b1_crt_occurrence_rebase parent) row
        (template_column_ids!fst (occurrence_descriptors!index)!row) (?rows!row) \<and>
      list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
        lift_column_ids sources occurrence_at ?refs ?source parent row)
        (?rows!row)) [0..<length ?beta]"
    using rows_certificate_template descriptor_at by simp
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: parent-bound extraction submitted"\<close>
  have parent_geometry_facts:
    "template_cid<length templates \<and>
     template_cid<length template_column_ids \<and>
     comma_semantic_b1_crt_column_ids_resolve columns
       (template_column_ids!template_cid) (templates!template_cid)"
    by (rule comma_semantic_b1_crt_template_geometry_certified_resolves
      [OF parent_geometry_certified])
  have parent_resolution:
    "comma_semantic_b1_crt_column_ids_resolve columns
      (template_column_ids!template_cid)
      (comma_semantic_b1_crt_occurrence_columns parent)"
    using parent_geometry_facts parent_columns
    by (simp only: parent_columns; blast)
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: parent resolution submitted"\<close>
  have origins_distinct: "distinct ?origins" by (rule comma_semantic_b1_crt_constructed_source_origins_distinct)
  have rows_binding_at:
    "\<And>row. row<length ?beta \<Longrightarrow>
      comma_semantic_b1_crt_group_construction_bound columns
        (comma_semantic_b1_crt_occurrence_rebase parent) row
        (template_column_ids!fst (occurrence_descriptors!index)!row) (?rows!row) \<and>
      list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
        lift_column_ids sources occurrence_at ?refs ?source parent row)
        (?rows!row)"
    by (rule comma_semantic_b1_crt_list_all_upt_index[OF rows_certificate])
  have rows_at:
    "\<And>row. row<length ?beta \<Longrightarrow>
      comma_semantic_b1_crt_group_construction_bound columns
        (comma_semantic_b1_crt_occurrence_rebase parent) row
        (template_column_ids!fst (occurrence_descriptors!index)!row) (?rows!row) \<and>
      list_all (comma_semantic_b1_crt_constructed_piece_matches columns
        lift_column_ids sources occurrence_at ?refs ?source parent row)
        (?rows!row)"
  proof -
    fix row assume row_bound: "row<length ?beta"
    have group:
      "comma_semantic_b1_crt_group_construction_bound columns
        (comma_semantic_b1_crt_occurrence_rebase parent) row
        (template_column_ids!fst (occurrence_descriptors!index)!row) (?rows!row)"
      and bindings:
      "list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
        lift_column_ids sources occurrence_at ?refs ?source parent row)
        (?rows!row)"
      using rows_binding_at[OF row_bound] by blast+
    have selected_certificates:
      "\<And>slot. slot<?period \<Longrightarrow>
        comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
          occurrence_descriptors templates ?source parent ?refs lift_descriptors slot \<and>
        comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
          template_column_ids lift_column_ids occurrence_descriptors
          lift_descriptors index ?refs slot"
    proof -
      fix slot assume slot_bound: "slot<?period"
      have valid:
        "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
          occurrence_descriptors templates ?source parent ?refs lift_descriptors slot"
        by (rule comma_semantic_b1_crt_list_all_upt_index
          [OF slots_valid slot_bound])
      have certificate:
        "comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
          template_column_ids lift_column_ids occurrence_descriptors lift_descriptors
          index ?refs slot"
        by (rule comma_semantic_b1_crt_list_all_upt_index
          [OF slot_certificates slot_bound])
      show "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
          occurrence_descriptors templates ?source parent ?refs lift_descriptors slot \<and>
        comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
          template_column_ids lift_column_ids occurrence_descriptors
          lift_descriptors index ?refs slot"
        using valid certificate by simp
    qed
    have matches:
      "list_all (comma_semantic_b1_crt_constructed_piece_matches columns
        lift_column_ids sources occurrence_at ?refs ?source parent row) (?rows!row)"
      by (rule comma_semantic_b1_crt_constructed_piece_matches_list_from_certificates
        [OF normalized selected_certificates earlier used_lift_geometries bindings])
    show "comma_semantic_b1_crt_group_construction_bound columns
        (comma_semantic_b1_crt_occurrence_rebase parent) row
        (template_column_ids!fst (occurrence_descriptors!index)!row) (?rows!row) \<and>
      list_all (comma_semantic_b1_crt_constructed_piece_matches columns
        lift_column_ids sources occurrence_at ?refs ?source parent row) (?rows!row)"
      using group matches by simp
  qed
  have beta_distinct: "distinct ?beta"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_beta_distinct
      [OF bound parent_at])
  have refs_length_source: "length ?refs=comma_decisive_sector_period ?source" using refs_length normalized by simp
  have action_row_certified_source:
      "comma_semantic_b1_crt_source_slot_action_row_certified ?source
        (comma_decisive_sector_period ?source) ?actions"
    using action_row_certified source_is_base by simp
  have refs_slots_length: "map comma_semantic_b1_crt_lift_ref_slot ?refs=[0..<length ?refs]" using refs_slots refs_length by simp
  have slots_valid_from_actions_length:
      "list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions sources
        occurrence_at occurrence_descriptors templates ?source parent ?refs
        lift_descriptors ?actions) [0..<length ?refs]"
    using slots_valid_from_actions refs_length by simp
  have slot_certificates_length:
    "list_all (\<lambda>slot.
      comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
        template_column_ids lift_column_ids occurrence_descriptors lift_descriptors
        index ?refs slot) [0..<length ?refs]"
    using slot_certificates refs_length by simp
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: parent-bound extraction proof passed"\<close>
  have source_partition:
    "comma_semantic_b1_crt_cells_partition {..<924} (map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids occurrence_at ?refs ?source)) \<and> list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry)) (comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids occurrence_at ?refs ?source) \<and> map snd ?live=comma_semantic_b1_crt_constructed_live_source_cells columns lift_column_ids occurrence_at ?refs ?source"
  proof (rule comma_semantic_b1_crt_constructed_bound_source_partition
      [OF normalized source_admitted table_admitted refs_length_source refs_slots_length
        action_row_certified_source slots_valid_from_actions_length
        slot_certificates_length])
    fix child occurrence
    assume child_before: "child<index"
      and child_at: "occurrence_at child=Some occurrence"
    show "comma_semantic_b1_crt_occurrence_wellformed occurrence"
      by (rule earlier[OF child_before child_at])
  next
    fix slot child_index lift_cid
    assume slot: "slot<length ?refs"
      and ref: "?refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    show "comma_semantic_b1_crt_lift_geometry_certified columns templates
        template_column_ids lift_column_ids lift_descriptors lift_cid"
      by (rule used_lift_geometries[OF slot ref])
  qed
  from source_partition have source_cells_partition: "comma_semantic_b1_crt_cells_partition {..<924} (map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids occurrence_at ?refs ?source))" and source_entries_admitted: "list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry)) (comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids occurrence_at ?refs ?source)" and source_live_equal: "map snd ?live=comma_semantic_b1_crt_constructed_live_source_cells columns lift_column_ids occurrence_at ?refs ?source" by blast+
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: source partition helper passed"\<close>
  have live_partition: "comma_semantic_b1_crt_cells_partition {..<924} (map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_live_source_cells columns lift_column_ids occurrence_at ?refs ?source))" unfolding comma_semantic_b1_crt_constructed_live_source_cells_def by (rule comma_semantic_b1_crt_constructed_live_source_partition[where entries="comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids occurrence_at ?refs ?source", OF source_cells_partition source_entries_admitted])
  have mapped_cells: "map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_live_source_cells columns lift_column_ids occurrence_at ?refs ?source) = map (\<lambda>entry. fst (snd entry)) ?entries" using arg_cong[where f="map (\<lambda>entry. comma_crt_set (fst entry))", OF source_live_equal] by (simp add: comma_semantic_b1_crt_constructed_live_source_cells_def map_map o_def)
  have cells_partition: "comma_semantic_b1_crt_cells_partition {..<924} (map (\<lambda>entry. fst (snd entry)) ?entries)"
    using live_partition mapped_cells by simp
  have period: "?period\<in>comma_semantic_b1_crt_source_periods" by (rule comma_semantic_b1_generated_source_period_six[OF source_admitted])
  have each_slot_origins:
    "\<And>slot. slot<?period \<Longrightarrow> map fst (comma_semantic_b1_crt_constructed_slot_live_entries columns lift_column_ids occurrence_at ?refs ?source slot) = comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids sources occurrence_at ?refs ?source slot"
  proof -
    fix slot assume slot: "slot<?period"
    have child_index_bound:
      "\<And>child_index lift_cid. ?refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow> child_index<length sources"
    proof -
      fix child_index lift_cid
      assume ref_eq: "?refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
      have slot_cert:
        "comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
          template_column_ids lift_column_ids occurrence_descriptors lift_descriptors
          index ?refs slot"
        by (rule comma_semantic_b1_crt_list_all_upt_index
          [OF slot_certificates slot])
      have child_bounds:
        "child_index<index \<and>
         child_index<length occurrence_descriptors"
        by (rule comma_semantic_b1_crt_goto_slot_certificate_child_bounds
          [OF slot_cert ref_eq])
      have child_lt: "child_index<index"
        and child_descriptor_bound: "child_index<length occurrence_descriptors"
        using child_bounds by blast+
      show "child_index<length sources"
        by (rule less_trans[OF child_lt index_bound])
    qed
    show "map fst (comma_semantic_b1_crt_constructed_slot_live_entries columns lift_column_ids occurrence_at ?refs ?source slot) = comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids sources occurrence_at ?refs ?source slot"
      by (rule comma_semantic_b1_crt_constructed_slot_live_entry_origins
        [OF period slot _ child_index_bound]) (use normalized in simp)
  qed
  have live_origins: "map fst ?live=?origins"
    by (rule comma_semantic_b1_crt_constructed_source_live_entry_origins
      [where period="?period"]) (use each_slot_origins in simp_all)
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: source origins helper passed"\<close>
  have pieces_origins:
    "set (map comma_semantic_b1_crt_constructed_piece_origin (concat ?rows))=set ?origins"
  proof -
    have "set (sort (map comma_semantic_b1_crt_constructed_piece_origin (concat ?rows)))=set ?origins"
      by (rule arg_cong[where f=set, OF piece_origin_sort])
    then show ?thesis by (simp add: set_sort)
  qed
  have origins_exact:
    "set (map comma_semantic_b1_crt_constructed_piece_origin (concat ?rows))= set (map fst ?entries)"
    using pieces_origins live_origins by (simp add: map_map o_def)
  have entries_origin_distinct: "distinct (map fst ?entries)"
    using origins_distinct live_origins by (simp add: map_map o_def)
  have entries_injective: "inj_on fst (set ?entries)"
    using entries_origin_distinct by (auto simp: distinct_map inj_on_def)
  have row_binding:
    "\<And>row piece. row<length ?beta \<Longrightarrow> piece\<in>set (?rows!row) \<Longrightarrow> \<exists>entry\<in>set ?entries. comma_semantic_b1_crt_constructed_piece_origin piece=fst entry \<and> comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)= fst (snd entry) \<and> snd (snd entry)=?beta!row"
  proof -
    fix row piece
    assume row: "row<length ?beta" and piece: "piece\<in>set (?rows!row)"
    have group: "comma_semantic_b1_crt_group_construction_bound columns (comma_semantic_b1_crt_occurrence_rebase parent) row (template_column_ids!fst (occurrence_descriptors!index)!row) (?rows!row)"
      and matches: "list_all (comma_semantic_b1_crt_constructed_piece_matches columns lift_column_ids sources occurrence_at ?refs ?source parent row) (?rows!row)"
      using rows_at[OF row] by blast+
    have matched: "comma_semantic_b1_crt_constructed_piece_matches columns lift_column_ids sources occurrence_at ?refs ?source parent row piece"
      using matches piece by (auto simp: list_all_iff)
    have supported: "comma_crt_supported (columns!comma_semantic_b1_crt_piece_cid piece)"
      using group piece by (auto simp: comma_semantic_b1_crt_group_construction_bound_def
        list_all_iff split: if_splits)
    obtain entry where entry: "entry\<in>set ?live"
      and origin: "fst entry=comma_semantic_b1_crt_constructed_piece_origin piece"
      and support: "comma_crt_set (fst (snd entry))=comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)"
      and result: "snd (snd entry)=?beta!row"
      using comma_semantic_b1_crt_constructed_piece_entry[OF matched supported]
      by blast
    have mapped_member: "(fst entry,(comma_crt_set (fst (snd entry)),snd (snd entry)))\<in>set ?entries" unfolding set_map by (rule imageI[OF entry])
    show "\<exists>entry\<in>set ?entries. comma_semantic_b1_crt_constructed_piece_origin piece=fst entry \<and> comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)= fst (snd entry) \<and> snd (snd entry)=?beta!row"
    proof (rule bexI[where x="(fst entry,(comma_crt_set (fst (snd entry)),snd (snd entry)))"])
      show "comma_semantic_b1_crt_constructed_piece_origin piece=fst (fst entry,(comma_crt_set (fst (snd entry)),snd (snd entry))) \<and> comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)=fst (snd (fst entry,(comma_crt_set (fst (snd entry)),snd (snd entry)))) \<and> snd (snd (fst entry,(comma_crt_set (fst (snd entry)),snd (snd entry))))=?beta!row" using origin support result by simp
      show "(fst entry,(comma_crt_set (fst (snd entry)),snd (snd entry)))\<in>set ?entries" by (rule mapped_member)
    qed
  qed
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: row binding helper passed"\<close>
  have labels_set: "set ?labels=set ?beta"
  proof (rule set_eqI)
    fix result
    show "result\<in>set ?labels \<longleftrightarrow> result\<in>set ?beta"
    proof
      assume member: "result\<in>set ?labels"
      have member_image: "result\<in>(\<lambda>entry. snd (snd entry)) ` set ?entries" using member by (simp only: set_map)
      then obtain entry where entry: "entry\<in>set ?entries" and result: "result=snd (snd entry)" by (rule imageE)
      have fst_mapped_member: "fst entry\<in>set (map fst ?entries)"
        by (rule comma_semantic_b1_crt_map_set_member[OF entry])
      have piece_origin_set_member: "fst entry\<in>set (map comma_semantic_b1_crt_constructed_piece_origin (concat ?rows))"
        using origins_exact fst_mapped_member by blast
      have piece_origin_image: "fst entry\<in>comma_semantic_b1_crt_constructed_piece_origin ` set (concat ?rows)"
        using piece_origin_set_member by (simp only: set_map)
      obtain piece where piece: "piece\<in>set (concat ?rows)"
        and origin_rev: "fst entry=comma_semantic_b1_crt_constructed_piece_origin piece"
        using piece_origin_image by (rule imageE)
      have origin: "comma_semantic_b1_crt_constructed_piece_origin piece=fst entry"
        by (rule sym[OF origin_rev])
      obtain row where row: "row<length ?rows" and piece_row: "piece\<in>set (?rows!row)"
        using comma_semantic_b1_crt_concat_member_row[OF piece] by blast
      have row_bound: "row<length ?beta" using row rows_width by simp
      have other_exists: "\<exists>other\<in>set ?entries. comma_semantic_b1_crt_constructed_piece_origin piece=fst other \<and> comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)=fst (snd other) \<and> snd (snd other)=?beta!row"
        by (rule row_binding[OF row_bound piece_row])
      obtain other where other: "other\<in>set ?entries"
        and other_origin: "comma_semantic_b1_crt_constructed_piece_origin piece=fst other"
        and other_support: "comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)= fst (snd other)"
        and other_result: "snd (snd other)=?beta!row"
        using other_exists by blast
      ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: label source match found"\<close>
      have same_fst: "fst other=fst entry" by (rule trans[OF sym[OF other_origin] origin])
      have same: "other=entry" by (rule inj_onD[OF entries_injective same_fst other entry])
      show "result\<in>set ?beta" using result other_result same nth_mem[OF row_bound] by simp
      ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: label forward direction passed"\<close>
    next
      assume member: "result\<in>set ?beta"
      then obtain row where row: "row<length ?beta" and result: "?beta!row=result"
        by (auto simp: in_set_conv_nth)
      have group: "comma_semantic_b1_crt_group_construction_bound columns (comma_semantic_b1_crt_occurrence_rebase parent) row (template_column_ids!fst (occurrence_descriptors!index)!row) (?rows!row)"
        using rows_at[OF row] by blast
      have nonempty: "?rows!row\<noteq>[]"
        using group by (auto simp: comma_semantic_b1_crt_group_construction_bound_def
          split: if_splits)
      obtain piece where piece: "piece\<in>set (?rows!row)" using nonempty by (cases "?rows!row") auto
      have entry_exists: "\<exists>entry\<in>set ?entries. comma_semantic_b1_crt_constructed_piece_origin piece=fst entry \<and> comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)=fst (snd entry) \<and> snd (snd entry)=?beta!row"
        by (rule row_binding[OF row piece])
      obtain entry where entry: "entry\<in>set ?entries"
        and origin: "comma_semantic_b1_crt_constructed_piece_origin piece=fst entry"
        and support: "comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)= fst (snd entry)"
        and entry_result: "snd (snd entry)=?beta!row"
        using entry_exists by blast
      have label_member: "snd (snd entry)\<in>set ?labels" by (rule comma_semantic_b1_crt_map_set_member[OF entry])
      show "result\<in>set ?labels" using label_member entry_result result by simp
      ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: label reverse direction passed"\<close>
    qed
  qed
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: label equivalence checked"\<close>
  have group_unions:
    "\<And>row. row<length ?beta \<Longrightarrow> (\<Union>piece\<in>set (?rows!row). comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)) = comma_semantic_b1_crt_group_support ?labels ?cells (?beta!row)"
  proof -
    fix row assume row: "row<length ?beta"
    show "(\<Union>piece\<in>set (?rows!row). comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)) = comma_semantic_b1_crt_group_support ?labels ?cells (?beta!row)"
      by (rule comma_semantic_b1_crt_group_row_union_from_origins
        [OF rows_width row beta_distinct entries_injective origins_exact row_binding])
  qed
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: grouped support helper passed"\<close>
  have parent_resolved_template:
    "map (\<lambda>cid. columns!cid) (template_column_ids!template_cid) =
      comma_semantic_b1_crt_occurrence_columns parent"
    by (rule comma_semantic_b1_crt_column_ids_resolve_map[OF parent_resolution])
  have parent_resolved:
    "map (\<lambda>cid. columns!cid) (template_column_ids!fst (occurrence_descriptors!index)) =
      comma_semantic_b1_crt_occurrence_columns parent"
    using parent_resolved_template descriptor_at by simp
  have parent_admitted: "list_all (comma_crt_admitted 0) (comma_semantic_b1_crt_occurrence_columns parent)"
    using comma_semantic_b1_crt_column_ids_resolve_preserves_list_all
      [OF table_admitted parent_resolution] parent_resolved_template by simp
  have parent_template_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set (templates!template_cid))"
    by (rule comma_semantic_b1_crt_template_geometry_certified_partition
      [OF parent_geometry_certified])
  have parent_cells_partition:
      "comma_semantic_b1_crt_cells_partition {..<924}
        (map comma_crt_set (comma_semantic_b1_crt_occurrence_columns parent))"
    using parent_template_partition parent_columns by simp
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: parent partition checked"\<close>
  have source_width: "length ?labels=length ?cells" by simp
  have parent_width:
      "length ?beta=length (map comma_crt_set
        (comma_semantic_b1_crt_occurrence_columns parent))"
    using parent_binding
    by (simp add: comma_semantic_b1_crt_occurrence_binding_check_def)
  have parent_rebase_bound:
      "comma_semantic_b1_crt_occurrence_rebase parent<924"
    using parent_binding
    by (simp add: comma_semantic_b1_crt_occurrence_binding_check_def)
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: parent width/rebase checked"\<close>
  have local_coverage:
      "\<forall>row<length ?beta.
        comma_semantic_b1_crt_group_support ?labels ?cells (?beta!row) \<subseteq>
          comma_semantic_b1_crt_rebase_set
            (comma_semantic_b1_crt_occurrence_rebase parent)
            (map comma_crt_set
              (comma_semantic_b1_crt_occurrence_columns parent)!row)"
  proof (intro allI impI)
    fix row
    assume row: "row<length ?beta"
    have group:
        "comma_semantic_b1_crt_group_construction_bound columns
          (comma_semantic_b1_crt_occurrence_rebase parent) row
          (template_column_ids!fst (occurrence_descriptors!index)!row)
          (?rows!row)"
      using rows_at[OF row] by blast
    have source_union:
        "(\<Union>piece\<in>set (?rows!row).
          comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)) =
         comma_semantic_b1_crt_group_support ?labels ?cells (?beta!row)"
      by (rule group_unions[OF row])
    have union_covered:
        "(\<Union>piece\<in>set (?rows!row).
          comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)) \<subseteq>
         comma_semantic_b1_crt_rebase_set
           (comma_semantic_b1_crt_occurrence_rebase parent)
           (comma_crt_set
             (columns!(template_column_ids!fst (occurrence_descriptors!index)!row)))"
      by (rule comma_semantic_b1_crt_group_construction_bound_sound
        [OF table_admitted group])
    have row_columns:
        "row<length (comma_semantic_b1_crt_occurrence_columns parent)"
      using row parent_width by simp
    have selected_column:
        "comma_semantic_b1_crt_occurrence_columns parent!row =
          columns!(template_column_ids!fst (occurrence_descriptors!index)!row)"
      by (rule comma_semantic_b1_crt_map_nth
        [where f="\<lambda>cid. columns!cid"
          and xs="template_column_ids!fst (occurrence_descriptors!index)"
          and ys="comma_semantic_b1_crt_occurrence_columns parent" and i=row,
          OF parent_resolved row_columns])
    have mapped_selected_column:
        "(map comma_crt_set
          (comma_semantic_b1_crt_occurrence_columns parent))!row =
         comma_crt_set
          (columns!(template_column_ids!fst (occurrence_descriptors!index)!row))"
      using selected_column row_columns by (simp add: nth_map)
    show "comma_semantic_b1_crt_group_support ?labels ?cells (?beta!row) \<subseteq>
        comma_semantic_b1_crt_rebase_set
          (comma_semantic_b1_crt_occurrence_rebase parent)
          (map comma_crt_set
            (comma_semantic_b1_crt_occurrence_columns parent)!row)"
      using union_covered by (simp only: source_union mapped_selected_column)
  qed
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: local coverage checked"\<close>
  have grouped_rebased:
    "map comma_crt_set (comma_semantic_b1_crt_occurrence_columns parent) = map (comma_semantic_b1_crt_rebase_set ((924-comma_semantic_b1_crt_occurrence_rebase parent) mod 924)) (comma_semantic_b1_crt_group_supports ?labels ?cells ?beta)"
    by (rule sym[OF comma_semantic_b1_crt_group_partition_rebase_local_eq
      [OF source_width cells_partition labels_set beta_distinct
        parent_cells_partition parent_width parent_rebase_bound local_coverage]])
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: parent geometry helper passed"\<close>
  have support_nonempty:
    "list_all (\<lambda>row. comma_semantic_b1_crt_group_support ?labels ?cells (?beta!row)\<noteq>{}) [0..<length ?beta]"
  proof (unfold list_all_iff, intro ballI)
    fix row assume row: "row\<in>set [0..<length ?beta]"
    have row_bound: "row<length ?beta" using row by simp
    have group: "comma_semantic_b1_crt_group_construction_bound columns (comma_semantic_b1_crt_occurrence_rebase parent) row (template_column_ids!fst (occurrence_descriptors!index)!row) (?rows!row)"
      using rows_at[OF row_bound] by blast
    have nonempty: "?rows!row\<noteq>[]"
      using group by (auto simp: comma_semantic_b1_crt_group_construction_bound_def
        split: if_splits)
    obtain piece where piece: "piece\<in>set (?rows!row)" using nonempty by (cases "?rows!row") auto
    have supported: "comma_crt_supported (columns!comma_semantic_b1_crt_piece_cid piece)"
      using group piece by (auto simp: comma_semantic_b1_crt_group_construction_bound_def
        list_all_iff split: if_splits)
    have cid_bound: "comma_semantic_b1_crt_piece_cid piece<length columns"
      using group piece by (auto simp: comma_semantic_b1_crt_group_construction_bound_def list_all_iff split: if_splits)
    have admitted: "comma_crt_admitted 0 (columns!comma_semantic_b1_crt_piece_cid piece)"
      using table_admitted cid_bound by (auto simp: list_all_iff nth_mem)
    have piece_nonempty: "comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)\<noteq>{}"
      using comma_crt_supported_nonempty[OF admitted] supported by blast
    have union_nonempty: "(\<Union>piece\<in>set (?rows!row). comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece))\<noteq>{}"
      using piece piece_nonempty by blast
    show "comma_semantic_b1_crt_group_support ?labels ?cells (?beta!row)\<noteq>{}"
      using group_unions[OF row_bound] union_nonempty by simp
  qed
  ML_prf \<open>Comma_Proof_Profile.report "Constructed occurrence: support nonemptiness helper passed"\<close>
  have shift_bound: "(924-comma_semantic_b1_crt_occurrence_rebase parent) mod 924<924" by simp
  show ?thesis
    by (rule comma_semantic_b1_crt_grouped_rebase_wellformed
      [OF parent_binding parent_admitted source_width cells_partition labels_set
        beta_distinct grouped_rebased shift_bound support_nonempty])
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_occurrence_wellformed}]; Comma_Proof_Profile.report "Constructed occurrence: parent theorem checked"\<close>
lemma comma_semantic_b1_crt_constructed_occurrences_wellformed:
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
    and bounds: "list_all (\<lambda>index. comma_semantic_b1_crt_constructed_occurrence_bound columns templates template_column_ids lift_column_ids sources occurrence_at occurrence_descriptors lift_refs (slot_actions_table!index) lift_descriptors piece_refs index) [0..<length sources]"
    and parent_template_geometries:
      "\<And>index. index<length sources \<Longrightarrow>
        comma_semantic_b1_crt_template_geometry_certified columns templates
          template_column_ids (fst (occurrence_descriptors!index))"
    and used_lift_geometries:
      "\<And>index slot child_index lift_cid. index<length sources \<Longrightarrow>
        slot<length (lift_refs!index) \<Longrightarrow>
        (lift_refs!index)!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
        comma_semantic_b1_crt_lift_geometry_certified columns templates
          template_column_ids lift_column_ids lift_descriptors lift_cid"
  shows "\<forall>index<length sources. \<forall>parent. occurrence_at index=Some parent \<longrightarrow> comma_semantic_b1_crt_occurrence_wellformed parent"
proof -
  let ?certified="\<lambda>index. \<forall>parent. occurrence_at index=Some parent \<longrightarrow> comma_semantic_b1_crt_occurrence_wellformed parent"
  have step: "\<And>index. index<length sources \<Longrightarrow> (\<And>child_index. child_index<index \<Longrightarrow> ?certified child_index) \<Longrightarrow> ?certified index"
  proof -
    fix index assume index: "index<length sources"
      and earlier: "\<And>child_index. child_index<index \<Longrightarrow> ?certified child_index"
    have bound: "comma_semantic_b1_crt_constructed_occurrence_bound columns templates template_column_ids lift_column_ids sources occurrence_at occurrence_descriptors lift_refs (slot_actions_table!index) lift_descriptors piece_refs index"
      using comma_semantic_b1_crt_list_all_upt_index[OF bounds index] .
    have occurrence_present: "occurrence_at index\<noteq>None"
      by (rule comma_semantic_b1_crt_constructed_occurrence_bound_parent_present
        [OF bound])
    show "?certified index"
    proof (cases "occurrence_at index")
      case None
      with occurrence_present show ?thesis by simp
    next
      case (Some parent)
      have earlier_wf: "\<And>child_index child. child_index<index \<Longrightarrow> occurrence_at child_index=Some child \<Longrightarrow> comma_semantic_b1_crt_occurrence_wellformed child"
        using earlier by blast
      have parent_wellformed:
        "comma_semantic_b1_crt_occurrence_wellformed parent"
      proof (rule comma_semantic_b1_crt_constructed_occurrence_wellformed
          [OF table_admitted bound earlier_wf Some])
        show "comma_semantic_b1_crt_template_geometry_certified columns templates
            template_column_ids (fst (occurrence_descriptors!index))"
          by (rule parent_template_geometries[OF index])
        fix slot child_index lift_cid
        assume slot: "slot<length (lift_refs!index)"
          and ref: "(lift_refs!index)!slot=
            Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
        show "comma_semantic_b1_crt_lift_geometry_certified columns templates
            template_column_ids lift_column_ids lift_descriptors lift_cid"
          by (rule used_lift_geometries[OF index slot ref])
      qed
      show ?thesis
      proof (intro allI impI)
        fix selected assume selected_at: "occurrence_at index=Some selected"
        have selected_eq: "selected=parent"
          using selected_at Some by simp
        show "comma_semantic_b1_crt_occurrence_wellformed selected"
          using parent_wellformed selected_eq by simp
      qed
    qed
  qed
  have all: "\<forall>index<length sources. ?certified index"
    by (rule comma_semantic_b1_crt_source_order_induction[OF step])
  show ?thesis using all by blast
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_occurrences_wellformed}]; Comma_Proof_Profile.report "Constructed occurrence: source-order theorem checked"\<close>
lemmas comma_semantic_b1_crt_constructed_occurrence_oracle_audit_bundle =
  comma_semantic_b1_crt_constructed_live_source_partition
  comma_semantic_b1_crt_constructed_piece_entry
  comma_semantic_b1_crt_constructed_occurrence_wellformed
  comma_semantic_b1_crt_constructed_occurrences_wellformed
  comma_semantic_b1_crt_constructed_source_origins_distinct
ML \<open>
  Thm.consolidate @{thms comma_semantic_b1_crt_constructed_occurrence_oracle_audit_bundle};
  Comma_Proof_Profile.report
    "Constructed occurrence stage=final claims consolidated"
\<close>
end
