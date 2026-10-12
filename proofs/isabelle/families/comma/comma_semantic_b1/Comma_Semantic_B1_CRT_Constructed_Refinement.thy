theory Comma_Semantic_B1_CRT_Constructed_Refinement
  imports Comma_Semantic_B1_CRT_Constructed_Occurrence
begin
ML \<open>
structure Comma_Constructed_Refinement_Profile =
struct
  val started = Time.now ()
  fun report stage =
    Comma_Proof_Profile.report
      (stage ^ " elapsed_ms=" ^
        LargeInt.toString (Time.toMilliseconds (Time.- (Time.now (), started))))
end
\<close>
lemma comma_semantic_b1_crt_constructed_live_entry_covered:
  fixes columns :: "comma_crt_column list"
    and lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and source :: comma_finite_position
    and parent :: comma_semantic_b1_crt_occurrence
    and rows :: "comma_semantic_b1_crt_piece_ref list list"
    and parent_ids :: "nat list"
    and entry :: "(nat \<times> nat) \<times>
      (comma_crt_column \<times> comma_semantic_b1_result)"
  assumes table: "list_all (comma_crt_admitted 0) columns"
    and parent_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed parent"
    and parent_beta_distinct:
      "distinct (comma_semantic_b1_crt_occurrence_beta parent)"
    and parent_rebase:
      "comma_semantic_b1_crt_occurrence_rebase parent=rebase"
    and parent_resolution:
      "comma_semantic_b1_crt_column_ids_resolve columns parent_ids
        (comma_semantic_b1_crt_occurrence_columns parent)"
    and rows_width:
      "length rows=length (comma_semantic_b1_crt_occurrence_beta parent)"
    and rows_certificate:
      "list_all (\<lambda>row.
        comma_semantic_b1_crt_group_construction_bound columns rebase row
          (parent_ids!row) (rows!row) \<and>
        list_all (comma_semantic_b1_crt_constructed_piece_matches columns
          lift_column_ids sources occurrence_at refs source parent row)
          (rows!row)) [0..<length (comma_semantic_b1_crt_occurrence_beta parent)]"
    and piece_origins:
      "set (map comma_semantic_b1_crt_constructed_piece_origin (concat rows))=
        set (comma_semantic_b1_crt_constructed_source_origins columns
          lift_column_ids sources occurrence_at refs source)"
    and live_origins:
      "map fst (comma_semantic_b1_crt_constructed_source_live_entries
        columns lift_column_ids occurrence_at refs source)=
        comma_semantic_b1_crt_constructed_source_origins columns
          lift_column_ids sources occurrence_at refs source"
    and entry:
      "entry\<in>set (comma_semantic_b1_crt_constructed_source_live_entries
        columns lift_column_ids occurrence_at refs source)"
    and entry_admitted: "comma_crt_admitted 0 (fst (snd entry))"
  shows "comma_semantic_b1_crt_local_piece_covered parent
    (fst (snd entry)) (snd (snd entry))"
proof -
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "live-entry entered"\<close>
  have origin_live: "fst entry\<in>set (map fst
      (comma_semantic_b1_crt_constructed_source_live_entries
        columns lift_column_ids occurrence_at refs source))"
    by (rule comma_semantic_b1_crt_map_set_member[OF entry])
  have origin: "fst entry\<in>
      set (comma_semantic_b1_crt_constructed_source_origins columns
        lift_column_ids sources occurrence_at refs source)"
    using origin_live live_origins by simp
  have piece_origin_member:
      "fst entry\<in>comma_semantic_b1_crt_constructed_piece_origin `
        set (concat rows)"
    using origin piece_origins by (simp only: set_map)
  then obtain piece where piece:
      "piece\<in>set (concat rows)"
    and piece_origin: "fst entry=
      comma_semantic_b1_crt_constructed_piece_origin piece"
    by (rule imageE)
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "live-entry origin witness"\<close>
  obtain row where row: "row<length rows"
    and piece_row: "piece\<in>set (rows!row)"
    using comma_semantic_b1_crt_concat_member_row[OF piece] by blast
  have row_bound:
      "row<length (comma_semantic_b1_crt_occurrence_beta parent)"
    using row rows_width by simp
  have row_facts:
      "comma_semantic_b1_crt_group_construction_bound columns rebase row
          (parent_ids!row) (rows!row) \<and>
       list_all (comma_semantic_b1_crt_constructed_piece_matches columns
          lift_column_ids sources occurrence_at refs source parent row)
          (rows!row)"
    by (rule comma_semantic_b1_crt_list_all_upt_index
      [OF rows_certificate row_bound])
  have group:
      "comma_semantic_b1_crt_group_construction_bound columns rebase row
        (parent_ids!row) (rows!row)"
    and matches:
      "list_all (comma_semantic_b1_crt_constructed_piece_matches columns
        lift_column_ids sources occurrence_at refs source parent row)
        (rows!row)"
    by (use row_facts in blast)+
  have matched:
      "comma_semantic_b1_crt_constructed_piece_matches columns lift_column_ids
        sources occurrence_at refs source parent row piece"
    using matches piece_row by (auto simp: list_all_iff)
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "live-entry row match"\<close>
  have piece_facts:
      "comma_semantic_b1_crt_piece_cid piece<length columns \<and>
       comma_crt_supported (columns!comma_semantic_b1_crt_piece_cid piece)"
    using group piece_row by (auto simp:
      comma_semantic_b1_crt_group_construction_bound_def list_all_iff
      split: if_splits)
  have piece_supported:
      "comma_crt_supported (columns!comma_semantic_b1_crt_piece_cid piece)"
    using piece_facts by blast
  have piece_cid_bound:
      "comma_semantic_b1_crt_piece_cid piece<length columns"
    using piece_facts by blast
  have piece_admitted:
      "comma_crt_admitted 0 (columns!comma_semantic_b1_crt_piece_cid piece)"
    using table piece_cid_bound by (auto simp: list_all_iff nth_mem)
  obtain other where other:
      "other\<in>set (comma_semantic_b1_crt_constructed_source_live_entries
        columns lift_column_ids occurrence_at refs source)"
    and other_origin:
      "fst other=comma_semantic_b1_crt_constructed_piece_origin piece"
    and other_set:
      "comma_crt_set (fst (snd other))=
        comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)"
    and other_result:
      "snd (snd other)=comma_semantic_b1_crt_occurrence_beta parent!row"
    using comma_semantic_b1_crt_constructed_piece_entry[OF matched piece_supported]
    by blast
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "live-entry source binding"\<close>
  have origins_distinct:
      "distinct (comma_semantic_b1_crt_constructed_source_origins columns
        lift_column_ids sources occurrence_at refs source)"
    by (rule comma_semantic_b1_crt_constructed_source_origins_distinct)
  have entries_origin_distinct:
      "distinct (map fst
        (comma_semantic_b1_crt_constructed_source_live_entries
          columns lift_column_ids occurrence_at refs source))"
    using origins_distinct live_origins by simp
  have entries_injective:
      "inj_on fst (set
        (comma_semantic_b1_crt_constructed_source_live_entries
          columns lift_column_ids occurrence_at refs source))"
    using entries_origin_distinct by (auto simp: distinct_map inj_on_def)
  have same_origin: "fst other=fst entry"
    using other_origin piece_origin by simp
  have same_entry: "other=entry"
    by (rule inj_onD[OF entries_injective same_origin other entry])
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "live-entry unique source origin"\<close>
  have parent_binding:
      "comma_semantic_b1_crt_occurrence_binding_check parent"
    using parent_wellformed by (simp add:
      comma_semantic_b1_crt_occurrence_wellformed_def
      comma_semantic_b1_crt_occurrence_binding_check_def)
  have beta_distinct:
      "distinct (comma_semantic_b1_crt_occurrence_beta parent)"
    using parent_beta_distinct by simp
  have parent_resolved:
      "map (\<lambda>cid. columns!cid) parent_ids=
        comma_semantic_b1_crt_occurrence_columns parent"
    by (rule comma_semantic_b1_crt_column_ids_resolve_map[OF parent_resolution])
  have parent_width:
      "length (comma_semantic_b1_crt_occurrence_columns parent)=
        length (comma_semantic_b1_crt_occurrence_beta parent)"
    using parent_binding by (simp add:
      comma_semantic_b1_crt_occurrence_binding_check_def)
  have row_column:
      "comma_semantic_b1_crt_occurrence_columns parent!row=columns!(parent_ids!row)"
    by (rule comma_semantic_b1_crt_map_nth[OF parent_resolved])
      (use row_bound parent_width in simp)
  have piece_covered:
      "comma_semantic_b1_crt_local_piece_covered parent
        (columns!comma_semantic_b1_crt_piece_cid piece)
        (comma_semantic_b1_crt_occurrence_beta parent!row)"
    by (rule comma_semantic_b1_crt_group_piece_local_covered
      [OF table parent_binding beta_distinct parent_rebase row_bound
        row_column group piece_row])
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "live-entry group coverage"\<close>
  have candidate_eq:
      "comma_crt_set (fst (snd entry))=
        comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)"
    using same_entry other_set by simp
  have covered_at_row:
      "comma_semantic_b1_crt_local_piece_covered parent
        (fst (snd entry)) (comma_semantic_b1_crt_occurrence_beta parent!row)"
    using comma_semantic_b1_crt_local_piece_covered_set_cong
      [OF parent_wellformed entry_admitted piece_admitted candidate_eq]
      piece_covered by simp
  show ?thesis using covered_at_row same_entry other_result by simp
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_live_entry_covered}];
  Comma_Constructed_Refinement_Profile.report "Constructed refinement stage=live-entry coverage checked"
\<close>
lemma comma_semantic_b1_crt_constructed_bound_lift_local_cover:
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
    and index :: nat and parent :: comma_semantic_b1_crt_occurrence
  assumes table: "list_all (comma_crt_admitted 0) columns"
    and bound:
      "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
        template_column_ids lift_column_ids sources occurrence_at
        occurrence_descriptors lift_refs (slot_actions_table!index) lift_descriptors piece_refs index"
    and earlier:
      "\<And>child child_occurrence. child<index \<Longrightarrow>
        occurrence_at child=Some child_occurrence \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
    and parent_at: "occurrence_at index=Some parent"
    and parent_template_geometry:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids (fst (occurrence_descriptors!index))"
    and used_lift_geometries:
      "\<And>slot child_index lift_cid. slot<length (lift_refs!index) \<Longrightarrow>
        (lift_refs!index)!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
        comma_semantic_b1_crt_lift_geometry_certified columns templates
          template_column_ids lift_column_ids lift_descriptors lift_cid"
  shows "comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
    occurrence_descriptors templates (sources!index) parent (lift_refs!index)
    lift_descriptors"
proof -
  let ?source="sources!index"
  let ?refs="lift_refs!index"
  let ?actions="slot_actions_table!index"
  let ?rows="piece_refs!index"
  let ?beta="comma_semantic_b1_crt_occurrence_beta parent"
  let ?period="comma_decisive_sector_period
    (comma_source_continuation_base ?source)"
  let ?live="comma_semantic_b1_crt_constructed_source_live_entries columns
    lift_column_ids occurrence_at ?refs ?source"
  let ?origins="comma_semantic_b1_crt_constructed_source_origins columns
    lift_column_ids sources occurrence_at ?refs ?source"
  obtain template_cid descriptor_tail where descriptor_pair:
      "occurrence_descriptors!index=(template_cid,descriptor_tail)"
    by (cases "occurrence_descriptors!index") auto
  obtain descriptor_rebase descriptor_beta where descriptor_tail:
      "descriptor_tail=(descriptor_rebase,descriptor_beta)"
    by (cases descriptor_tail) auto
  have descriptor_at:
      "occurrence_descriptors!index=(template_cid,
        (descriptor_rebase,descriptor_beta))"
    using descriptor_pair descriptor_tail by simp
  have index_guard: "index<length sources \<and> index<length occurrence_descriptors \<and>
      index<length lift_refs \<and> index<length piece_refs"
    by (rule comma_semantic_b1_crt_constructed_occurrence_bound_index_guards[OF bound])
  have index_bound: "index<length sources" using index_guard by blast
  let ?bound_body = "?source=comma_source_continuation_base ?source \<and>
       comma_round_admitted ?source \<and>
       length ?refs=?period \<and>
       map comma_semantic_b1_crt_lift_ref_slot ?refs=[0..<?period] \<and>
       length occurrence_descriptors=length sources \<and>
       length ?rows=length ?beta \<and>
       (template_cid<length templates \<and>
        descriptor_rebase=comma_semantic_b1_crt_occurrence_rebase parent \<and>
        descriptor_beta=?beta \<and>
        comma_semantic_b1_crt_occurrence_columns parent=templates!template_cid) \<and>
       comma_semantic_b1_crt_occurrence_binding_check parent \<and>
       ?beta\<noteq>[] \<and> distinct ?beta \<and>
       comma_semantic_b1_crt_source_slot_action_row_certified ?source ?period ?actions \<and>
       list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions
         sources occurrence_at occurrence_descriptors templates ?source parent
         ?refs lift_descriptors ?actions) [0..<?period] \<and>
       list_all (\<lambda>slot.
         comma_semantic_b1_crt_constructed_goto_slot_certificate columns
           templates template_column_ids lift_column_ids occurrence_descriptors
           lift_descriptors index ?refs slot) [0..<?period] \<and>
       sort (map comma_semantic_b1_crt_constructed_piece_origin (concat ?rows))=?origins \<and>
       list_all (\<lambda>row.
         comma_semantic_b1_crt_group_construction_bound columns
           (comma_semantic_b1_crt_occurrence_rebase parent) row
           (template_column_ids!template_cid!row) (?rows!row) \<and>
         list_all (comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions
           columns lift_column_ids sources occurrence_at ?refs ?source ?actions
           parent row) (?rows!row)) [0..<length ?beta]"
  note expanded_bound = bound[unfolded
    comma_semantic_b1_crt_constructed_occurrence_bound_def
    if_P[OF index_guard] parent_at option.simps Let_def]
  have bound_body: "?bound_body"
    by (rule expanded_bound[unfolded descriptor_at prod.case fst_conv])
  note bound_tail1 = conjunct2[OF bound_body]
  note bound_tail2 = conjunct2[OF bound_tail1]
  note bound_tail3 = conjunct2[OF bound_tail2]
  note bound_tail4 = conjunct2[OF bound_tail3]
  note bound_tail5 = conjunct2[OF bound_tail4]
  note bound_tail6 = conjunct2[OF bound_tail5]
  note bound_tail7 = conjunct2[OF bound_tail6]
  note bound_tail8 = conjunct2[OF bound_tail7]
  note bound_tail9 = conjunct2[OF bound_tail8]
  note bound_tail10 = conjunct2[OF bound_tail9]
  note bound_tail11 = conjunct2[OF bound_tail10]
  note bound_tail12 = conjunct2[OF bound_tail11]
  note bound_tail13 = conjunct2[OF bound_tail12]
  note bound_tail14 = conjunct2[OF bound_tail13]
  have normalized: "?source=comma_source_continuation_base ?source" by (rule conjunct1[OF bound_body])
  have source_admitted: "comma_round_admitted ?source"
    by (rule conjunct1[OF bound_tail1])
  have refs_length: "length ?refs=?period"
    by (rule conjunct1[OF bound_tail2])
  have refs_slots:
      "map comma_semantic_b1_crt_lift_ref_slot ?refs=[0..<?period]"
    by (rule conjunct1[OF bound_tail3])
  have descriptors_width: "length occurrence_descriptors=length sources"
    by (rule conjunct1[OF bound_tail4])
  have rows_width: "length ?rows=length ?beta"
    by (rule conjunct1[OF bound_tail5])
  have descriptor_facts:
      "template_cid<length templates \<and>
       descriptor_rebase=comma_semantic_b1_crt_occurrence_rebase parent \<and>
       descriptor_beta=?beta \<and>
       comma_semantic_b1_crt_occurrence_columns parent=templates!template_cid"
    by (rule conjunct1[OF bound_tail6])
  have parent_columns:
      "comma_semantic_b1_crt_occurrence_columns parent=templates!template_cid"
    by (rule conjunct2[OF conjunct2[OF conjunct2[OF descriptor_facts]]])
  have parent_binding:
      "comma_semantic_b1_crt_occurrence_binding_check parent"
    by (rule conjunct1[OF bound_tail7])
  have beta_facts: "?beta\<noteq>[] \<and> distinct ?beta"
    using conjunct1[OF bound_tail8] conjunct1[OF bound_tail9] by blast
  have action_row_certified:
      "comma_semantic_b1_crt_source_slot_action_row_certified ?source ?period ?actions"
    by (rule conjunct1[OF bound_tail10])
  have slots_valid_from_actions:
      "list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
        occurrence_descriptors templates ?source parent ?refs lift_descriptors ?actions)
        [0..<?period]"
    by (rule conjunct1[OF bound_tail11])
  have slot_certificates:
      "list_all (\<lambda>slot.
        comma_semantic_b1_crt_constructed_goto_slot_certificate columns
          templates template_column_ids lift_column_ids occurrence_descriptors
          lift_descriptors index ?refs slot) [0..<?period]"
    by (rule conjunct1[OF bound_tail12])
  have piece_origin_sort:
      "sort (map comma_semantic_b1_crt_constructed_piece_origin
        (concat ?rows))=?origins"
    by (rule conjunct1[OF bound_tail13])
  have rows_bindings:
      "list_all (\<lambda>row.
        comma_semantic_b1_crt_group_construction_bound columns
          (comma_semantic_b1_crt_occurrence_rebase parent) row
          (template_column_ids!template_cid!row) (?rows!row) \<and>
        list_all (comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions columns
          lift_column_ids sources occurrence_at ?refs ?source ?actions parent row)
          (?rows!row)) [0..<length ?beta]"
    by (rule bound_tail14)
  have parent_geometry_certified:
      "comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids template_cid"
    using parent_template_geometry descriptor_at by simp
  have parent_resolution:
    "comma_semantic_b1_crt_column_ids_resolve columns
        (template_column_ids!template_cid)
        (comma_semantic_b1_crt_occurrence_columns parent)"
    using comma_semantic_b1_crt_template_geometry_certified_resolves
      [OF parent_geometry_certified] parent_columns
    by (simp only: parent_columns; blast)
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "parent bound extraction"\<close>
  have parent_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed parent"
  proof (rule comma_semantic_b1_crt_constructed_occurrence_wellformed
      [OF table bound earlier parent_at parent_template_geometry])
    fix slot child_index lift_cid
    assume slot: "slot<length ?refs"
      and ref: "?refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    show "comma_semantic_b1_crt_lift_geometry_certified columns templates
        template_column_ids lift_column_ids lift_descriptors lift_cid"
      by (rule used_lift_geometries[OF slot ref])
  qed
  have beta_distinct: "distinct ?beta" using beta_facts by blast
  have parent_resolved:
      "map (\<lambda>cid. columns!cid) (template_column_ids!template_cid)=
        comma_semantic_b1_crt_occurrence_columns parent"
    by (rule comma_semantic_b1_crt_column_ids_resolve_map[OF parent_resolution])
  have origins_distinct: "distinct ?origins"
    by (rule comma_semantic_b1_crt_constructed_source_origins_distinct)
  have piece_origins:
      "set (map comma_semantic_b1_crt_constructed_piece_origin (concat ?rows))=
        set ?origins"
  proof -
    have "set (sort (map comma_semantic_b1_crt_constructed_piece_origin
        (concat ?rows)))=set ?origins"
      by (rule arg_cong[where f=set, OF piece_origin_sort])
    then show ?thesis by (simp add: set_sort)
  qed
  have period: "?period\<in>comma_semantic_b1_crt_source_periods"
    by (rule comma_semantic_b1_generated_source_period_six[OF source_admitted])
  have selected_certificates:
      "\<And>slot. slot<?period \<Longrightarrow>
        comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
          occurrence_descriptors templates ?source parent ?refs lift_descriptors slot \<and>
        comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
          template_column_ids lift_column_ids occurrence_descriptors
          lift_descriptors index ?refs slot"
  proof -
    fix slot assume slot_bound: "slot<?period"
    have slot_member: "slot\<in>set [0..<?period]"
      using slot_bound by simp
    have slot_valid_from_actions:
        "comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
          occurrence_descriptors templates ?source parent ?refs lift_descriptors
          ?actions slot"
      using slots_valid_from_actions slot_member by (simp add: list_all_iff)
    have slot_valid:
        "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
          occurrence_descriptors templates ?source parent ?refs lift_descriptors slot"
      by (rule comma_semantic_b1_crt_lift_slot_valid_from_actions_implies_valid
        [OF action_row_certified slot_bound slot_valid_from_actions])
    have slot_certificate:
        "comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
          template_column_ids lift_column_ids occurrence_descriptors
          lift_descriptors index ?refs slot"
      using slot_certificates slot_member by (simp add: list_all_iff)
    show "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at occurrence_descriptors
        templates ?source parent ?refs lift_descriptors slot \<and>
      comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
        template_column_ids lift_column_ids occurrence_descriptors lift_descriptors index ?refs slot"
      using slot_valid slot_certificate by blast
  qed
  have rows_binding_at:
      "\<And>row. row<length ?beta \<Longrightarrow>
        comma_semantic_b1_crt_group_construction_bound columns
          (comma_semantic_b1_crt_occurrence_rebase parent) row
          (template_column_ids!template_cid!row) (?rows!row) \<and>
        list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
          lift_column_ids sources occurrence_at ?refs ?source parent row)
          (?rows!row)"
  proof -
    fix row assume row_bound: "row<length ?beta"
    have row_data:
        "comma_semantic_b1_crt_group_construction_bound columns
            (comma_semantic_b1_crt_occurrence_rebase parent) row
            (template_column_ids!template_cid!row) (?rows!row) \<and>
         list_all (comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions
            columns lift_column_ids sources occurrence_at ?refs ?source ?actions
            parent row) (?rows!row)"
      by (rule comma_semantic_b1_crt_list_all_upt_index[OF rows_bindings row_bound])
    have old_bindings:
        "list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
          lift_column_ids sources occurrence_at ?refs ?source parent row)
          (?rows!row)"
      using row_data
      by (auto simp: list_all_iff
        dest: comma_semantic_b1_crt_constructed_piece_binding_from_actions_old)
    show "comma_semantic_b1_crt_group_construction_bound columns
        (comma_semantic_b1_crt_occurrence_rebase parent) row
        (template_column_ids!template_cid!row) (?rows!row) \<and>
      list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
        lift_column_ids sources occurrence_at ?refs ?source parent row) (?rows!row)"
      using row_data old_bindings by blast
  qed
  have rows_certificate:
      "list_all (\<lambda>row.
        comma_semantic_b1_crt_group_construction_bound columns
          (comma_semantic_b1_crt_occurrence_rebase parent) row
          (template_column_ids!template_cid!row) (?rows!row) \<and>
        list_all (comma_semantic_b1_crt_constructed_piece_matches columns
          lift_column_ids sources occurrence_at ?refs ?source parent row)
          (?rows!row)) [0..<length ?beta]"
  proof (rule iffD2[OF list_all_iff], intro ballI)
    fix row assume row_member: "row\<in>set [0..<length ?beta]"
    have row_bound: "row<length ?beta" using row_member by simp
    have row_bindings:
        "comma_semantic_b1_crt_group_construction_bound columns
            (comma_semantic_b1_crt_occurrence_rebase parent) row
            (template_column_ids!template_cid!row) (?rows!row) \<and>
         list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
            lift_column_ids sources occurrence_at ?refs ?source parent row)
            (?rows!row)"
      by (rule rows_binding_at[OF row_bound])
    have piece_matches:
        "list_all (comma_semantic_b1_crt_constructed_piece_matches columns
          lift_column_ids sources occurrence_at ?refs ?source parent row)
          (?rows!row)"
      by (rule comma_semantic_b1_crt_constructed_piece_matches_list_from_certificates
        [OF normalized selected_certificates earlier used_lift_geometries
          conjunct2[OF row_bindings]])
    show "comma_semantic_b1_crt_group_construction_bound columns
        (comma_semantic_b1_crt_occurrence_rebase parent) row
        (template_column_ids!template_cid!row) (?rows!row) \<and>
      list_all (comma_semantic_b1_crt_constructed_piece_matches columns
        lift_column_ids sources occurrence_at ?refs ?source parent row)
        (?rows!row)"
      using row_bindings piece_matches by blast
  qed
  have each_slot_origins:
      "\<And>slot. slot<?period \<Longrightarrow>
        map fst (comma_semantic_b1_crt_constructed_slot_live_entries
          columns lift_column_ids occurrence_at ?refs ?source slot)=
        comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids
          sources occurrence_at ?refs ?source slot"
  proof -
    fix slot assume slot: "slot<?period"
    have slot_mem: "slot\<in>set [0..<?period]" using slot by simp
    have child_index_bound:
        "\<And>child lift_cid. ?refs!slot=
          Comma_B1_Lift_Goto_Ref slot child lift_cid \<Longrightarrow>
          child<length sources"
    proof -
      fix child lift_cid
      assume ref_eq: "?refs!slot=Comma_B1_Lift_Goto_Ref slot child lift_cid"
      have slot_certificate:
          "comma_semantic_b1_crt_constructed_goto_slot_certificate columns
            templates template_column_ids lift_column_ids occurrence_descriptors
            lift_descriptors index ?refs slot"
        by (rule comma_semantic_b1_crt_list_all_upt_index
          [OF slot_certificates slot])
      have child_bounds:
          "child<index \<and> child<length occurrence_descriptors"
        by (rule comma_semantic_b1_crt_goto_slot_certificate_child_bounds
          [OF slot_certificate ref_eq])
      show "child<length sources"
        using child_bounds index_bound by (meson less_trans)
    qed
    show "map fst (comma_semantic_b1_crt_constructed_slot_live_entries
        columns lift_column_ids occurrence_at ?refs ?source slot)=
      comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids
        sources occurrence_at ?refs ?source slot"
      by (rule comma_semantic_b1_crt_constructed_slot_live_entry_origins
        [OF period slot _ child_index_bound]) (use normalized in simp)
  qed
  have live_origins:
      "map fst ?live=?origins"
    by (rule comma_semantic_b1_crt_constructed_source_live_entry_origins
      [where period="?period"]) (use each_slot_origins normalized in simp_all)
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "parent origin alignment"\<close>
  have rows_at:
      "\<And>row. row<length ?beta \<Longrightarrow>
        comma_semantic_b1_crt_group_construction_bound columns
          (comma_semantic_b1_crt_occurrence_rebase parent) row
          (template_column_ids!template_cid!row) (?rows!row) \<and>
        list_all (comma_semantic_b1_crt_constructed_piece_matches columns
          lift_column_ids sources occurrence_at ?refs ?source parent row)
          (?rows!row)"
    by (rule comma_semantic_b1_crt_list_all_upt_index[OF rows_certificate])
  have local_slots:
      "list_all (comma_semantic_b1_crt_lift_local_slot_valid sources
        occurrence_at occurrence_descriptors templates ?source parent ?refs
        lift_descriptors) [0..<?period]"
  proof (unfold list_all_iff, intro ballI)
    fix slot assume slot_member: "slot\<in>set [0..<?period]"
    have slot_bound: "slot<?period" using slot_member by simp
    have ref_bound: "slot<length ?refs" using refs_length slot_bound by simp
    have slots_at:
        "(map comma_semantic_b1_crt_lift_ref_slot ?refs)!slot=
          [0..<?period]!slot"
      by (rule arg_cong[OF refs_slots, where f="\<lambda>refs. refs!slot"])
    have ref_slot:
        "comma_semantic_b1_crt_lift_ref_slot (?refs!slot)=slot"
      using slots_at ref_bound slot_bound by (simp add: nth_map nth_upt)
    have base_valid:
        "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
          occurrence_descriptors templates ?source parent ?refs lift_descriptors slot"
      by (rule conjunct1[OF selected_certificates[OF slot_bound]])
    have base_valid_from_actions:
        "comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
          occurrence_descriptors templates ?source parent ?refs lift_descriptors
          ?actions slot"
      using slots_valid_from_actions slot_member by (simp add: list_all_iff)
    have action_eq:
        "?actions!slot=comma_semantic_b1_source_slot_action ?source slot"
      by (rule comma_semantic_b1_crt_source_slot_action_row_certified_nth
        [OF action_row_certified slot_bound])
    have action_bound: "slot<length ?actions" using action_row_certified slot_bound
      by (auto simp: comma_semantic_b1_crt_source_slot_action_row_certified_def)
    show "comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
        occurrence_descriptors templates ?source parent ?refs lift_descriptors slot"
    proof (cases "?refs!slot")
      case (Comma_B1_Lift_Terminal_Ref ref_slot parent_column)
      have ref_eq: "?refs!slot=Comma_B1_Lift_Terminal_Ref slot parent_column"
        using Comma_B1_Lift_Terminal_Ref ref_slot by simp
      obtain result where terminal_from_actions:
          "comma_semantic_b1_terminal_action_result (?actions!slot)=Some result"
        and beta_result: "?beta!parent_column=result"
        and parent_column_bound:
          "parent_column<length
            (comma_semantic_b1_crt_occurrence_columns parent)"
        using base_valid_from_actions ref_eq ref_bound slot_bound normalized action_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
          split: if_splits option.splits)
      have terminal:
          "comma_semantic_b1_terminal_action_result
            (comma_semantic_b1_source_slot_action ?source slot)=Some result"
        using terminal_from_actions action_eq by simp
      have beta_bound: "parent_column<length ?beta"
        using parent_binding parent_column_bound
        by (auto simp: comma_semantic_b1_crt_occurrence_binding_check_def)
      have scope_admitted:
          "comma_crt_admitted 0
            (comma_crt_source_scope_column (?period,slot))"
        by (rule comma_semantic_b1_crt_lift_scope_admitted[OF period slot_bound])
      have slot_phase_bound: "slot<924"
        using period slot_bound by (auto simp:
          comma_semantic_b1_crt_source_periods_def)
      have scope_active:
          "comma_crt_eval slot (comma_crt_source_scope_column (?period,slot))"
        using comma_semantic_b1_crt_lift_scope_eval
          [OF period slot_bound slot_phase_bound] slot_bound by simp
      have scope_supported:
          "comma_crt_supported (comma_crt_source_scope_column (?period,slot))"
        by (rule comma_crt_eval_supported[OF scope_admitted scope_active])
      let ?entry="((slot,0),
        (comma_crt_source_scope_column (?period,slot),result))"
      have slot_entry:
          "?entry\<in>set (comma_semantic_b1_crt_constructed_slot_live_entries
            columns lift_column_ids occurrence_at ?refs ?source slot)"
        using slot_bound ref_bound ref_eq terminal scope_supported
        by (simp add: comma_semantic_b1_crt_constructed_slot_live_entries_def
          Let_def)
      have slot_member: "slot\<in>set [0..<?period]" using slot_bound by simp
      have entry_live: "?entry\<in>set ?live"
        using slot_entry slot_member by (auto simp:
          comma_semantic_b1_crt_constructed_source_live_entries_def set_concat)
      have entry_admitted:
          "comma_crt_admitted 0 (fst (snd ?entry))"
        using scope_admitted by simp
      note entry_coverage_fact =
        comma_semantic_b1_crt_constructed_live_entry_covered
          [where rebase="comma_semantic_b1_crt_occurrence_rebase parent"
            and rows="?rows" and parent_ids="template_column_ids!template_cid"
            and source="?source" and refs="?refs" and entry="?entry",
           OF table parent_wellformed beta_distinct refl parent_resolution
            rows_width rows_certificate piece_origins live_origins entry_live
            entry_admitted]
      have covered:
          "comma_semantic_b1_crt_local_piece_covered parent
            (comma_crt_source_scope_column (?period,slot)) result"
        using entry_coverage_fact by (simp only: fst_conv snd_conv)
      ML_prf \<open>Comma_Constructed_Refinement_Profile.report "parent terminal slot coverage"\<close>
      show ?thesis using base_valid ref_bound ref_eq terminal beta_result covered
        by (simp add: comma_semantic_b1_crt_lift_local_slot_valid_def
          Let_def)
    next
      case (Comma_B1_Lift_Goto_Ref ref_slot child lift_cid)
      have ref_eq: "?refs!slot=Comma_B1_Lift_Goto_Ref slot child lift_cid"
        using Comma_B1_Lift_Goto_Ref ref_slot by simp
      obtain child_source shift where action_from_actions:
          "?actions!slot=Comma_Continuation_Goto child_source shift"
        using base_valid_from_actions ref_eq ref_bound slot_bound normalized action_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
          split: if_splits comma_source_continuation_action.splits)
      have action:
          "comma_semantic_b1_source_slot_action ?source slot=
            Comma_Continuation_Goto child_source shift"
        using action_from_actions action_eq by simp
      obtain child_occurrence where child_at:
          "occurrence_at child=Some child_occurrence"
        using base_valid_from_actions ref_eq action_from_actions ref_bound slot_bound normalized action_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
          split: if_splits option.splits prod.splits)
      have slot_certificate:
          "comma_semantic_b1_crt_constructed_goto_slot_certificate columns
            templates template_column_ids lift_column_ids occurrence_descriptors
            lift_descriptors index ?refs slot"
        by (rule conjunct2[OF selected_certificates[OF slot_bound]])
      have child_bounds:
          "child<index \<and> child<length occurrence_descriptors"
        by (rule comma_semantic_b1_crt_goto_slot_certificate_child_bounds
          [OF slot_certificate ref_eq])
      have child_lt: "child<index"
        and child_descriptor_bound: "child<length occurrence_descriptors"
        using child_bounds by blast+
      have child_wellformed:
          "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
        using earlier child_lt child_at by blast
      have lift_geometry:
          "comma_semantic_b1_crt_lift_geometry_certified columns templates
            template_column_ids lift_column_ids lift_descriptors lift_cid"
        by (rule used_lift_geometries[OF ref_bound ref_eq])
      have lift_cid_bounds:
          "lift_cid<length lift_column_ids \<and>
           lift_cid<length lift_descriptors"
        using comma_semantic_b1_crt_lift_geometry_certified_exposes
          [OF lift_geometry] by blast
      note lift_bound = conjunct1[OF lift_cid_bounds]
      note descriptor_bound = conjunct2[OF lift_cid_bounds]
      have lift_details:
          "comma_semantic_b1_crt_lift_descriptor_valid
              templates (lift_descriptors!lift_cid) \<and>
           comma_semantic_b1_crt_occurrence_columns child_occurrence=
             templates!comma_semantic_b1_crt_lift_descriptor_template_cid
               (lift_descriptors!lift_cid)"
        using base_valid_from_actions ref_eq action_from_actions child_at
          ref_bound slot_bound normalized action_bound
        child_descriptor_bound lift_bound descriptor_bound
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
          split: if_splits option.splits prod.splits)
      note lift_valid = conjunct1[OF lift_details]
      note child_columns = conjunct2[OF lift_details]
      define lifted where
        "lifted=comma_semantic_b1_crt_lift_columns templates
          (lift_descriptors!lift_cid)"
      have resolved:
          "comma_semantic_b1_crt_column_ids_resolve columns
            (lift_column_ids!lift_cid) lifted"
        unfolding lifted_def
        by (rule comma_semantic_b1_crt_lift_geometry_certified_resolves[OF lift_geometry])
      have row_resolved:
          "map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid)=lifted"
        by (rule comma_semantic_b1_crt_column_ids_resolve_map[OF resolved])
      have row_admitted:
          "list_all (comma_crt_admitted 0)
            (map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid))"
        by (rule comma_semantic_b1_crt_column_ids_resolve_preserves_list_all
          [OF table resolved])
      have child_width:
          "length (comma_semantic_b1_crt_occurrence_columns child_occurrence)=
            length (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
        using child_wellformed by (simp add:
          comma_semantic_b1_crt_occurrence_wellformed_def)
      have lifted_width:
          "length lifted=length
            (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
        by (simp only: lifted_def comma_semantic_b1_crt_lift_columns_def
          comma_semantic_b1_crt_lift_columns_option_def
          lift_valid if_True option.simps length_map
          child_columns[symmetric] child_width)
      have row_width:
          "length (lift_column_ids!lift_cid)=
            length (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
        using row_resolved lifted_width by (metis length_map)
      have live_column:
          "\<And>child_column. child_column<length
              (comma_semantic_b1_crt_occurrence_beta child_occurrence) \<Longrightarrow>
            lifted!child_column=
              columns!(lift_column_ids!lift_cid!child_column)"
        by (rule comma_semantic_b1_crt_map_nth[OF row_resolved])
          (simp only: lifted_width)
      have covered_rows:
          "list_all (\<lambda>entry. comma_semantic_b1_crt_local_piece_covered
              parent (fst entry) (snd entry)) (zip lifted
                (comma_semantic_b1_crt_occurrence_beta child_occurrence))"
      proof -
        have indexed_zip:
            "zip lifted (comma_semantic_b1_crt_occurrence_beta child_occurrence)=
             map (\<lambda>child_column. (lifted!child_column,
                    comma_semantic_b1_crt_occurrence_beta child_occurrence!
                      child_column))
               [0..<length (comma_semantic_b1_crt_occurrence_beta child_occurrence)]"
          using comma_semantic_b1_crt_zip_indexed[OF lifted_width]
          by (simp only: lifted_width)
        have all_columns:
            "list_all (\<lambda>child_column.
              comma_semantic_b1_crt_local_piece_covered parent
                (lifted!child_column)
                (comma_semantic_b1_crt_occurrence_beta child_occurrence!
                  child_column))
              [0..<length (comma_semantic_b1_crt_occurrence_beta child_occurrence)]"
        proof (unfold list_all_iff, intro ballI)
          fix child_column
          assume child_column_mem:
              "child_column\<in>set
                [0..<length (comma_semantic_b1_crt_occurrence_beta child_occurrence)]"
          have child_column_bound:
              "child_column<length
                (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
            using child_column_mem by simp
          have candidate_admitted:
              "comma_crt_admitted 0 (lifted!child_column)"
          proof -
            have cid_admitted:
                "comma_crt_admitted 0
                  (columns!(lift_column_ids!lift_cid!child_column))"
              using row_admitted child_column_bound row_width
              by (auto simp: list_all_iff nth_map nth_mem)
            show ?thesis using live_column[OF child_column_bound] cid_admitted
              by simp
          qed
          show "comma_semantic_b1_crt_local_piece_covered parent
              (lifted!child_column)
              (comma_semantic_b1_crt_occurrence_beta child_occurrence!
                child_column)"
          proof (cases "comma_crt_supported (lifted!child_column)")
            case False
            then show ?thesis
              by (rule comma_semantic_b1_crt_local_piece_covered_if_unsupported
                [OF parent_wellformed candidate_admitted])
          next
            case True
            let ?entry="((slot,Suc child_column),
              (lifted!child_column,
                comma_semantic_b1_crt_occurrence_beta child_occurrence!
                  child_column))"
            have entry_slot:
                "?entry\<in>set
                  (comma_semantic_b1_crt_constructed_slot_live_entries
                    columns lift_column_ids occurrence_at ?refs ?source slot)"
              using slot_bound ref_bound ref_eq action child_at lift_bound
                row_width child_column_bound True
                live_column[OF child_column_bound]
              by (simp add:
                comma_semantic_b1_crt_constructed_slot_live_entries_def
                Let_def set_filter)
            have slot_member: "slot\<in>set [0..<?period]"
              using slot_bound by simp
            have entry_live: "?entry\<in>set ?live"
              using entry_slot slot_member by (auto simp:
                comma_semantic_b1_crt_constructed_source_live_entries_def
                set_concat)
            have entry_admitted:
                "comma_crt_admitted 0 (fst (snd ?entry))"
              using candidate_admitted by simp
            note entry_coverage_fact =
              comma_semantic_b1_crt_constructed_live_entry_covered
                [where rebase="comma_semantic_b1_crt_occurrence_rebase parent"
                  and rows="?rows"
                  and parent_ids="template_column_ids!template_cid"
                  and source="?source" and refs="?refs" and entry="?entry",
                 OF table parent_wellformed beta_distinct refl parent_resolution
                  rows_width rows_certificate piece_origins live_origins entry_live
                  entry_admitted]
            have covered:
                "comma_semantic_b1_crt_local_piece_covered parent
                  (lifted!child_column)
                  (comma_semantic_b1_crt_occurrence_beta child_occurrence!
                    child_column)"
              using entry_coverage_fact by (simp only: fst_conv snd_conv)
            show ?thesis using covered by simp
          qed
        qed
        show ?thesis using indexed_zip all_columns by (simp add: list_all_iff)
      qed
      ML_prf \<open>Comma_Constructed_Refinement_Profile.report "parent Goto child rows coverage"\<close>
      have option_lifted:
          "comma_semantic_b1_crt_lift_columns_option templates
            (lift_descriptors!lift_cid)=Some lifted"
        using lift_valid lifted_def by (simp add:
          comma_semantic_b1_crt_lift_columns_option_def
          comma_semantic_b1_crt_lift_columns_def)
      have local_valid:
          "comma_semantic_b1_crt_lift_local_slot_valid sources occurrence_at
            occurrence_descriptors templates ?source parent ?refs
            lift_descriptors slot"
        using base_valid ref_bound ref_eq action child_at lift_bound descriptor_bound
          option_lifted lifted_def lifted_width covered_rows
        by (simp add: comma_semantic_b1_crt_lift_local_slot_valid_def
          Let_def split: option.splits)
      ML_prf \<open>Comma_Constructed_Refinement_Profile.report "parent Goto local slot closure"\<close>
      show ?thesis using local_valid by simp
    qed
  qed
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "parent all slots covered"\<close>
  have source_base: "?source=comma_source_continuation_base ?source"
    by (rule normalized)
  have source_admitted: "comma_round_admitted ?source"
    by (rule source_admitted)
  have parent_distinct: "distinct
      (comma_semantic_b1_crt_occurrence_beta parent)"
    using beta_distinct by simp
  have parent_binding_fact:
      "comma_semantic_b1_crt_occurrence_binding_check parent"
    by (rule parent_binding)
  show ?thesis
    using source_base source_admitted parent_binding_fact parent_distinct
      descriptors_width refs_length refs_slots local_slots
    by (simp add: comma_semantic_b1_crt_lift_local_cover_witness_def)
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_bound_lift_local_cover}];
  Comma_Constructed_Refinement_Profile.report "Constructed refinement stage=parent local-cover checked"
\<close>
lemma comma_semantic_b1_crt_constructed_occurrences_candidate_matches:
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
    and children :: "comma_finite_position \<Rightarrow>
      comma_semantic_b1_crt_occurrence option"
  assumes table: "list_all (comma_crt_admitted 0) columns"
    and bounds:
      "list_all (\<lambda>index.
        comma_semantic_b1_crt_constructed_occurrence_bound columns templates
          template_column_ids lift_column_ids sources occurrence_at
          occurrence_descriptors lift_refs (slot_actions_table!index)
          lift_descriptors piece_refs index)
        [0..<length sources]"
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
    and children_resolve:
      "\<And>index. index<length sources \<Longrightarrow>
        children (sources!index)=occurrence_at index"
  shows "\<forall>index<length sources. \<forall>parent.
    occurrence_at index=Some parent \<longrightarrow>
    comma_semantic_b1_crt_occurrence_candidate_matches children
      (sources!index) parent"
proof -
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "all-source theorem entered"\<close>
  have all_wellformed:
      "\<forall>index<length sources. \<forall>parent.
        occurrence_at index=Some parent \<longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed parent"
    by (rule comma_semantic_b1_crt_constructed_occurrences_wellformed
      [OF table bounds parent_template_geometries used_lift_geometries])
  ML_prf \<open>Comma_Constructed_Refinement_Profile.report "all-source induction available"\<close>
  have each_wellformed:
      "\<And>index parent. index<length sources \<Longrightarrow>
        occurrence_at index=Some parent \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed parent"
    using all_wellformed by blast
  show ?thesis
  proof (rule allI, rule impI)
    fix index
    assume index: "index<length sources"
    show "\<forall>parent. occurrence_at index=Some parent \<longrightarrow>
        comma_semantic_b1_crt_occurrence_candidate_matches children
          (sources!index) parent"
    proof (rule allI, rule impI)
      fix parent
      assume parent_at: "occurrence_at index=Some parent"
      have bound:
          "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
            template_column_ids lift_column_ids sources occurrence_at
            occurrence_descriptors lift_refs (slot_actions_table!index)
            lift_descriptors piece_refs index"
        by (rule comma_semantic_b1_crt_list_all_upt_index[OF bounds index])
      have earlier:
          "\<And>child child_occurrence. child<index \<Longrightarrow>
            occurrence_at child=Some child_occurrence \<Longrightarrow>
            comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
      proof -
        fix child child_occurrence
        assume child_before: "child<index"
          and child_at: "occurrence_at child=Some child_occurrence"
        have child_bound: "child<length sources"
          by (rule less_trans[OF child_before index])
        show "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
          by (rule each_wellformed[OF child_bound child_at])
      qed
      have witness:
          "comma_semantic_b1_crt_lift_local_cover_witness sources occurrence_at
            occurrence_descriptors templates (sources!index) parent
            (lift_refs!index) lift_descriptors"
      proof (rule comma_semantic_b1_crt_constructed_bound_lift_local_cover
          [OF table bound earlier parent_at])
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
      have parent_wellformed:
          "comma_semantic_b1_crt_occurrence_wellformed parent"
        by (rule each_wellformed[OF index parent_at])
      show "comma_semantic_b1_crt_occurrence_candidate_matches children
          (sources!index) parent"
        by (rule comma_semantic_b1_crt_lift_local_cover_candidate_matches
          [OF witness parent_wellformed each_wellformed children_resolve])
    qed
  qed
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_occurrences_candidate_matches}];
  Comma_Constructed_Refinement_Profile.report "Constructed refinement stage=all-source candidate exactness checked"
\<close>
lemmas comma_semantic_b1_crt_constructed_refinement_oracle_audit_bundle =
  comma_semantic_b1_crt_constructed_live_entry_covered
  comma_semantic_b1_crt_constructed_bound_lift_local_cover
  comma_semantic_b1_crt_constructed_occurrences_candidate_matches
ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms
    comma_semantic_b1_crt_partition_oracle_audit_bundle
    comma_semantic_b1_crt_construction_binding_oracle_audit_bundle
    comma_semantic_b1_crt_occurrence_bounds_oracle_audit_bundle
    comma_semantic_b1_crt_constructed_occurrence_oracle_audit_bundle
    comma_semantic_b1_crt_constructed_refinement_oracle_audit_bundle})
    then () else error "Comma constructed refinement local oracle audit failed"
  val _ = Comma_Constructed_Refinement_Profile.report
    "unified generic oracle audit checked"
\<close>
end
