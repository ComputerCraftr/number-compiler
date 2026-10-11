theory Comma_Semantic_B1_CRT_Slot_Certificates
  imports "HOL-Library.Product_Lexorder"
    Comma_Semantic_B1_CRT_Partition_Composition
begin

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=entered"\<close>

text \<open>
Canonical template and lift certificates separate reusable geometry from
occurrence-specific result binding.  A Goto piece uses these certificates and
the selected slot-valid fact; its remaining check is only the binding-index
and CID correspondence.
\<close>

definition comma_semantic_b1_crt_template_geometry_certified ::
    "comma_crt_column list \<Rightarrow> comma_crt_column list list \<Rightarrow>
      nat list list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_template_geometry_certified columns templates
      template_column_ids template_cid \<longleftrightarrow>
    template_cid<length templates \<and>
    template_cid<length template_column_ids \<and>
    comma_semantic_b1_crt_column_ids_resolve columns
      (template_column_ids!template_cid) (templates!template_cid) \<and>
    comma_semantic_b1_crt_columns_partition_certified (templates!template_cid)"

definition comma_semantic_b1_crt_lift_geometry_certified ::
    "comma_crt_column list \<Rightarrow> comma_crt_column list list \<Rightarrow>
      nat list list \<Rightarrow> nat list list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_lift_geometry_certified columns templates
      template_column_ids lift_column_ids lift_descriptors lift_cid \<longleftrightarrow>
    (if lift_cid<length lift_column_ids \<and>
        lift_cid<length lift_descriptors then
       (let descriptor=lift_descriptors!lift_cid;
            template_cid=comma_semantic_b1_crt_lift_descriptor_template_cid descriptor
        in comma_semantic_b1_crt_lift_descriptor_valid templates descriptor \<and>
          comma_semantic_b1_crt_template_geometry_certified columns templates
            template_column_ids template_cid \<and>
          (case comma_semantic_b1_crt_lift_columns_option templates descriptor of
             None \<Rightarrow> False
           | Some lifted \<Rightarrow>
               comma_semantic_b1_crt_column_ids_resolve columns
                 (lift_column_ids!lift_cid) lifted))
     else False)"

lemma comma_semantic_b1_crt_template_geometry_certified_resolves:
  assumes certified:
    "comma_semantic_b1_crt_template_geometry_certified columns templates
      template_column_ids template_cid"
  shows "template_cid<length templates \<and>
      template_cid<length template_column_ids \<and>
      comma_semantic_b1_crt_column_ids_resolve columns
      (template_column_ids!template_cid) (templates!template_cid)"
  using certified
  by (auto simp: comma_semantic_b1_crt_template_geometry_certified_def)

lemma comma_semantic_b1_crt_lift_geometry_certified_exposes:
  assumes certified:
    "comma_semantic_b1_crt_lift_geometry_certified columns templates
      template_column_ids lift_column_ids lift_descriptors lift_cid"
  shows "lift_cid<length lift_column_ids \<and>
      lift_cid<length lift_descriptors \<and>
      comma_semantic_b1_crt_lift_descriptor_valid templates
        (lift_descriptors!lift_cid) \<and>
      comma_semantic_b1_crt_template_geometry_certified columns templates
        template_column_ids
        (comma_semantic_b1_crt_lift_descriptor_template_cid
          (lift_descriptors!lift_cid)) \<and>
      (\<exists>lifted. comma_semantic_b1_crt_lift_columns_option templates
          (lift_descriptors!lift_cid)=Some lifted \<and>
        comma_semantic_b1_crt_column_ids_resolve columns
          (lift_column_ids!lift_cid) lifted)"
  using certified
  by (auto simp: comma_semantic_b1_crt_lift_geometry_certified_def Let_def
      split: if_splits option.splits)

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=lift-geometry-resolve entered"\<close>

lemma comma_semantic_b1_crt_lift_geometry_certified_resolves:
  assumes certified:
    "comma_semantic_b1_crt_lift_geometry_certified columns templates
      template_column_ids lift_column_ids lift_descriptors lift_cid"
  shows "comma_semantic_b1_crt_column_ids_resolve columns
      (lift_column_ids!lift_cid)
      (comma_semantic_b1_crt_lift_columns templates (lift_descriptors!lift_cid))"
  using certified
  by (auto simp: comma_semantic_b1_crt_lift_geometry_certified_def
      comma_semantic_b1_crt_lift_columns_def Let_def
      split: if_splits option.splits)

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=lift-geometry-resolve submitted"\<close>

definition comma_semantic_b1_crt_constructed_goto_slot_certificate ::
    "comma_crt_column list \<Rightarrow> comma_crt_column list list \<Rightarrow>
      nat list list \<Rightarrow> nat list list \<Rightarrow>
      comma_semantic_b1_crt_descriptor list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor list \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
      template_column_ids lift_column_ids occurrence_descriptors lift_descriptors
      index refs slot \<longleftrightarrow>
    (if slot<length refs then
       (case refs!slot of
          Comma_B1_Lift_Terminal_Ref _ _ \<Rightarrow> True
        | Comma_B1_Lift_Goto_Ref ref_slot child_index lift_cid \<Rightarrow>
            child_index<index \<and>
            child_index<length occurrence_descriptors \<and>
            ref_slot=slot \<and>
            (case occurrence_descriptors!child_index of
               (child_template,(child_rebase,child_beta)) \<Rightarrow>
                 distinct child_beta))
     else False)"

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=goto-certificate-resolve entered"\<close>

lemma comma_semantic_b1_crt_goto_slot_certificate_child_bounds:
  assumes certificate:
    "comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
      template_column_ids lift_column_ids occurrence_descriptors lift_descriptors
      index refs slot"
    and reference:
      "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
  shows "child_index<index \<and> child_index<length occurrence_descriptors"
  using certificate reference
  by (auto simp: comma_semantic_b1_crt_constructed_goto_slot_certificate_def
      split: if_splits prod.splits)

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=goto-certificate-resolve submitted"\<close>

definition comma_semantic_b1_crt_constructed_piece_matches ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_finite_position \<Rightarrow>
      comma_semantic_b1_crt_occurrence \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_crt_piece_ref \<Rightarrow> bool" where
  "comma_semantic_b1_crt_constructed_piece_matches columns lift_column_ids
      sources occurrence_at refs source parent destination piece \<longleftrightarrow>
    (let period=comma_decisive_sector_period
          (comma_source_continuation_base source);
         beta=comma_semantic_b1_crt_occurrence_beta parent
     in destination<length beta \<and>
       (case piece of
          Comma_B1_Piece_Terminal piece_period slot cid parent_column \<Rightarrow>
            slot<period \<and> slot<length refs \<and> piece_period=period \<and>
            parent_column=destination \<and>
            refs!slot=Comma_B1_Lift_Terminal_Ref slot destination \<and>
            (case comma_semantic_b1_terminal_action_result
                (comma_semantic_b1_source_slot_action source slot) of
               Some result \<Rightarrow> beta!destination=result \<and>
                 cid<length columns \<and>
                 columns!cid=comma_crt_source_scope_column (period,slot)
             | None \<Rightarrow> False)
        | Comma_B1_Piece_Goto piece_period slot child_index child_column
            lift_cid cid parent_column \<Rightarrow>
            slot<period \<and> slot<length refs \<and> piece_period=period \<and>
            parent_column=destination \<and>
            child_index<length sources \<and>
            lift_cid<length lift_column_ids \<and>
            refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<and>
            (case comma_semantic_b1_source_slot_action source slot of
               Comma_Continuation_Goto child _ \<Rightarrow>
                 sources!child_index=comma_source_continuation_base child \<and>
                 (case occurrence_at child_index of
                    Some child_occurrence \<Rightarrow>
                      child_column<length
                        (comma_semantic_b1_crt_occurrence_columns child_occurrence) \<and>
                      child_column<length
                        (comma_semantic_b1_crt_occurrence_beta child_occurrence) \<and>
                      length (lift_column_ids!lift_cid)=
                        length (comma_semantic_b1_crt_occurrence_beta child_occurrence) \<and>
                      beta!destination=
                        (comma_semantic_b1_crt_occurrence_beta child_occurrence)!child_column \<and>
                      cid<length columns \<and>
                      cid=lift_column_ids!lift_cid!child_column
                  | None \<Rightarrow> False)
             | _ \<Rightarrow> False)))"

definition comma_semantic_b1_crt_constructed_piece_binding_matches ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow> comma_finite_position \<Rightarrow>
      comma_semantic_b1_crt_occurrence \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_crt_piece_ref \<Rightarrow> bool" where
  "comma_semantic_b1_crt_constructed_piece_binding_matches columns lift_column_ids
      sources occurrence_at refs source parent destination piece \<longleftrightarrow>
    (let period=comma_decisive_sector_period
          (comma_source_continuation_base source);
         beta=comma_semantic_b1_crt_occurrence_beta parent
     in case piece of
       Comma_B1_Piece_Terminal piece_period slot cid parent_column \<Rightarrow>
         piece_period=period \<and> slot<period \<and> slot<length refs \<and>
         parent_column=destination \<and> refs!slot=
           Comma_B1_Lift_Terminal_Ref slot destination \<and>
         destination<length beta \<and> cid<length columns \<and>
         columns!cid=comma_crt_source_scope_column (period,slot)
     | Comma_B1_Piece_Goto piece_period slot child_index child_column lift_cid
          cid parent_column \<Rightarrow>
         piece_period=period \<and> slot<period \<and> slot<length refs \<and>
         parent_column=destination \<and> child_index<length sources \<and>
         lift_cid<length lift_column_ids \<and>
         refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<and>
         (case occurrence_at child_index of
            None \<Rightarrow> False
          | Some child_occurrence \<Rightarrow>
              destination<length beta \<and>
              child_column<length
                (comma_semantic_b1_crt_occurrence_beta child_occurrence) \<and>
              child_column<length (lift_column_ids!lift_cid) \<and>
              cid<length columns \<and>
              beta!destination=
                (comma_semantic_b1_crt_occurrence_beta child_occurrence)!child_column \<and>
              cid=lift_column_ids!lift_cid!child_column))"

definition comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow> comma_finite_position \<Rightarrow>
      comma_source_continuation_action list \<Rightarrow>
      comma_semantic_b1_crt_occurrence \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_crt_piece_ref \<Rightarrow> bool" where
  "comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions
      columns lift_column_ids sources occurrence_at refs source actions parent
      destination piece \<longleftrightarrow>
    comma_semantic_b1_crt_constructed_piece_binding_matches columns
      lift_column_ids sources occurrence_at refs source parent destination piece \<and>
    (case piece of
       Comma_B1_Piece_Terminal period slot cid parent_column \<Rightarrow>
         slot<length actions \<and>
         (case comma_semantic_b1_terminal_action_result (actions!slot) of
            Some result \<Rightarrow>
              comma_semantic_b1_crt_occurrence_beta parent!destination=result
          | None \<Rightarrow> False)
     | Comma_B1_Piece_Goto period slot child_index child_column lift_cid cid
          parent_column \<Rightarrow>
         slot<length actions \<and>
         (case actions!slot of
            Comma_Continuation_Goto child shift \<Rightarrow>
              sources!child_index=comma_source_continuation_base child
          | _ \<Rightarrow> False))"

lemma comma_semantic_b1_crt_constructed_piece_binding_from_actions_old:
  assumes binding:
    "comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions
      columns lift_column_ids sources occurrence_at refs source actions parent
      destination piece"
  shows "comma_semantic_b1_crt_constructed_piece_binding_matches columns
      lift_column_ids sources occurrence_at refs source parent destination piece"
  using binding
  by (simp add: comma_semantic_b1_crt_constructed_piece_binding_matches_from_actions_def)

lemma comma_semantic_b1_crt_lift_slot_valid_goto_action:
  fixes sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and templates :: "comma_crt_column list list"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and source :: comma_finite_position
    and parent :: comma_semantic_b1_crt_occurrence
  assumes normalized: "source=comma_source_continuation_base source"
    and slot_bound: "slot<length refs"
    and source_slot: "slot<comma_decisive_sector_period
      (comma_source_continuation_base source)"
    and reference:
      "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    and valid: "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
      occurrence_descriptors templates source parent refs descriptors slot"
  shows "\<exists>child shift child_occurrence.
    comma_semantic_b1_source_slot_action source slot=
      Comma_Continuation_Goto child shift \<and>
    sources!child_index=comma_source_continuation_base child \<and>
    occurrence_at child_index=Some child_occurrence"
  using normalized slot_bound source_slot reference valid
  by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
      split: if_splits option.splits prod.splits
        comma_source_continuation_action.splits)

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=single-goto-match entered"\<close>

lemma comma_semantic_b1_crt_constructed_goto_piece_matches_from_certificates:
  fixes columns :: "comma_crt_column list"
    and template_column_ids :: "nat list list"
    and lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and templates :: "comma_crt_column list list"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and source :: comma_finite_position
    and parent child_occurrence :: comma_semantic_b1_crt_occurrence
    and index :: nat
  assumes normalized: "source=comma_source_continuation_base source"
    and slot_valid: "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
      occurrence_descriptors templates source parent refs lift_descriptors slot"
    and slot_certificate:
      "comma_semantic_b1_crt_constructed_goto_slot_certificate columns
        templates template_column_ids lift_column_ids occurrence_descriptors
        lift_descriptors index refs slot"
    and lift_geometry_certificate:
      "comma_semantic_b1_crt_lift_geometry_certified columns templates
        template_column_ids lift_column_ids lift_descriptors lift_cid"
    and child_at: "occurrence_at child_index=Some child_occurrence"
    and child_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
    and binding:
      "comma_semantic_b1_crt_constructed_piece_binding_matches columns
        lift_column_ids sources occurrence_at refs source parent destination
        (Comma_B1_Piece_Goto period slot child_index child_column lift_cid cid destination)"
  shows "comma_semantic_b1_crt_constructed_piece_matches columns lift_column_ids
    sources occurrence_at refs source parent destination
    (Comma_B1_Piece_Goto period slot child_index child_column lift_cid cid destination)"
proof -
  have source_slot:
    "slot<comma_decisive_sector_period (comma_source_continuation_base source)"
    and slot_refs: "slot<length refs"
    and period_eq: "period=comma_decisive_sector_period
      (comma_source_continuation_base source)"
    and destination_bound:
      "destination<length (comma_semantic_b1_crt_occurrence_beta parent)"
    and child_index_bound: "child_index<length sources"
    and lift_cid_bound: "lift_cid<length lift_column_ids"
    and child_column_bound:
      "child_column<length
        (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
    and child_lift_bound: "child_column<length (lift_column_ids!lift_cid)"
    and cid_bound: "cid<length columns"
    and beta_eq:
      "comma_semantic_b1_crt_occurrence_beta parent!destination=
        comma_semantic_b1_crt_occurrence_beta child_occurrence!child_column"
    and cid_eq: "cid=lift_column_ids!lift_cid!child_column"
    using binding child_at
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        Let_def split: option.splits)
  have reference:
    "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    using binding
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        Let_def)
  have lift_certificate:
    "comma_semantic_b1_crt_lift_geometry_certified columns templates
      template_column_ids lift_column_ids lift_descriptors lift_cid"
    using lift_geometry_certificate .
  obtain action_child shift selected_child where action_facts:
    "comma_semantic_b1_source_slot_action source slot=
       Comma_Continuation_Goto action_child shift"
    "sources!child_index=comma_source_continuation_base action_child"
    "occurrence_at child_index=Some selected_child"
    using comma_semantic_b1_crt_lift_slot_valid_goto_action
      [OF normalized slot_refs source_slot reference slot_valid]
    by blast
  have selected_child_eq: "selected_child=child_occurrence"
    using action_facts(3) child_at by simp
  have lift_width:
    "length (lift_column_ids!lift_cid)=
      length (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
  proof -
    obtain descriptor_lifted where option_lifted:
      "comma_semantic_b1_crt_lift_columns_option templates
          (lift_descriptors!lift_cid)=Some descriptor_lifted"
      and lift_resolved:
        "comma_semantic_b1_crt_column_ids_resolve columns
          (lift_column_ids!lift_cid) descriptor_lifted"
      and descriptor_valid:
        "comma_semantic_b1_crt_lift_descriptor_valid templates
          (lift_descriptors!lift_cid)"
      using comma_semantic_b1_crt_lift_geometry_certified_exposes
        [OF lift_certificate]
      by blast
    have resolved_width: "length (lift_column_ids!lift_cid)=length descriptor_lifted"
      using lift_resolved by (simp add: comma_semantic_b1_crt_column_ids_resolve_def)
    have child_template:
      "comma_semantic_b1_crt_occurrence_columns child_occurrence=
        templates!comma_semantic_b1_crt_lift_descriptor_template_cid
          (lift_descriptors!lift_cid)"
      using slot_valid reference action_facts(1) child_at normalized slot_refs source_slot
      by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
          split: if_splits option.splits prod.splits
            comma_source_continuation_action.splits)
    have lifted_width: "length descriptor_lifted=
      length (comma_semantic_b1_crt_occurrence_columns child_occurrence)"
      using option_lifted descriptor_valid child_template
      by (auto simp: comma_semantic_b1_crt_lift_columns_option_def
          comma_semantic_b1_crt_lift_descriptor_valid_def split: if_splits)
    have child_width: "length (comma_semantic_b1_crt_occurrence_columns child_occurrence)=
      length (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
      using child_wellformed by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
    show ?thesis using resolved_width lifted_width child_width by simp
  qed
  have child_columns_bound:
    "child_column<length
      (comma_semantic_b1_crt_occurrence_columns child_occurrence)"
    using child_column_bound child_wellformed
    by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def)
  show ?thesis
    using period_eq source_slot slot_refs destination_bound child_index_bound
      lift_cid_bound child_columns_bound child_column_bound lift_width cid_bound
      beta_eq cid_eq action_facts(1) action_facts(2) selected_child_eq child_at
      reference
    by (simp add: comma_semantic_b1_crt_constructed_piece_matches_def Let_def)
qed

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=single-goto-match submitted"\<close>

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=single-piece-match entered"\<close>

lemma comma_semantic_b1_crt_constructed_piece_matches_from_certificates:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and source :: comma_finite_position
    and parent :: comma_semantic_b1_crt_occurrence
  assumes normalized: "source=comma_source_continuation_base source"
    and slot_valid: "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
      occurrence_descriptors templates source parent refs lift_descriptors
      (fst (comma_semantic_b1_crt_constructed_piece_origin piece))"
    and slot_certificate:
      "comma_semantic_b1_crt_constructed_goto_slot_certificate columns
        templates template_column_ids lift_column_ids occurrence_descriptors
        lift_descriptors index refs
        (fst (comma_semantic_b1_crt_constructed_piece_origin piece))"
    and earlier_wellformed:
      "\<And>child_index child_occurrence. child_index<index \<Longrightarrow>
        occurrence_at child_index=Some child_occurrence \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
    and used_lift_geometries:
      "\<And>slot child_index lift_cid. slot<length refs \<Longrightarrow>
        refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
        comma_semantic_b1_crt_lift_geometry_certified columns templates
          template_column_ids lift_column_ids lift_descriptors lift_cid"
    and binding:
      "comma_semantic_b1_crt_constructed_piece_binding_matches columns
        lift_column_ids sources occurrence_at refs source parent destination piece"
  shows "comma_semantic_b1_crt_constructed_piece_matches columns lift_column_ids
    sources occurrence_at refs source parent destination piece"
proof (cases piece)
  case (Comma_B1_Piece_Terminal period slot cid parent_column)
  have terminal_binding:
    "comma_semantic_b1_crt_constructed_piece_binding_matches columns
      lift_column_ids sources occurrence_at refs source parent destination
      (Comma_B1_Piece_Terminal period slot cid parent_column)"
    using binding Comma_B1_Piece_Terminal by simp
  have slot_valid_case:
    "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
      occurrence_descriptors templates source parent refs lift_descriptors slot"
    using slot_valid Comma_B1_Piece_Terminal
    by (simp add: comma_semantic_b1_crt_constructed_piece_origin_def)
  have parent_column_eq: "parent_column=destination"
    using terminal_binding
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        Let_def)
  have reference:
    "refs!slot=Comma_B1_Lift_Terminal_Ref slot parent_column"
    using terminal_binding parent_column_eq
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        Let_def)
  have slot_bound: "slot<length refs"
    and source_slot: "slot<comma_decisive_sector_period
      (comma_source_continuation_base source)"
    using terminal_binding
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        Let_def)
  have terminal_result:
    "\<exists>result. comma_semantic_b1_terminal_action_result
      (comma_semantic_b1_source_slot_action source slot)=Some result \<and>
      comma_semantic_b1_crt_occurrence_beta parent!destination=result"
    using slot_valid_case reference parent_column_eq normalized slot_bound source_slot
    by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def Let_def
        split: option.splits)
  show ?thesis
    using terminal_binding parent_column_eq terminal_result
      Comma_B1_Piece_Terminal
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        comma_semantic_b1_crt_constructed_piece_matches_def Let_def
        split: option.splits)
next
  case (Comma_B1_Piece_Goto period slot child_index child_column lift_cid cid
      parent_column)
  have parent_column_eq: "parent_column=destination"
    using binding Comma_B1_Piece_Goto
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        Let_def)
  have goto_binding:
    "comma_semantic_b1_crt_constructed_piece_binding_matches columns
      lift_column_ids sources occurrence_at refs source parent destination
      (Comma_B1_Piece_Goto period slot child_index child_column lift_cid cid
        destination)"
    using binding Comma_B1_Piece_Goto parent_column_eq by simp
  have reference:
    "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    using goto_binding Comma_B1_Piece_Goto
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        Let_def)
  have slot_refs: "slot<length refs"
    using goto_binding
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        Let_def)
  have slot_valid_case:
    "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
      occurrence_descriptors templates source parent refs lift_descriptors slot"
    using slot_valid Comma_B1_Piece_Goto
    by (simp add: comma_semantic_b1_crt_constructed_piece_origin_def)
  have slot_certificate_case:
    "comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
      template_column_ids lift_column_ids occurrence_descriptors lift_descriptors
      index refs slot"
    using slot_certificate Comma_B1_Piece_Goto
    by (simp add: comma_semantic_b1_crt_constructed_piece_origin_def)
  have child_bounds:
    "child_index<index \<and> child_index<length occurrence_descriptors"
    by (rule comma_semantic_b1_crt_goto_slot_certificate_child_bounds
      [OF slot_certificate_case reference])
  have index_bound: "child_index<index"
    and descriptor_bound: "child_index<length occurrence_descriptors"
    using child_bounds by blast+
  obtain child_occurrence where child_at:
    "occurrence_at child_index=Some child_occurrence"
    using binding Comma_B1_Piece_Goto
    by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
        Let_def split: option.splits)
  have child_wellformed:
    "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
    by (rule earlier_wellformed[OF index_bound child_at])
  have goto_matches:
    "comma_semantic_b1_crt_constructed_piece_matches columns lift_column_ids
      sources occurrence_at refs source parent destination
      (Comma_B1_Piece_Goto period slot child_index child_column lift_cid cid
        destination)"
    by (rule comma_semantic_b1_crt_constructed_goto_piece_matches_from_certificates
      [OF normalized slot_valid_case slot_certificate_case
        used_lift_geometries[OF slot_refs reference] child_at child_wellformed
        goto_binding])
  show ?thesis using goto_matches parent_column_eq Comma_B1_Piece_Goto by simp
qed

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=single-piece-match submitted"\<close>

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=piece-list-match entered"\<close>

lemma comma_semantic_b1_crt_constructed_piece_matches_list_from_certificates:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and source :: comma_finite_position
    and parent :: comma_semantic_b1_crt_occurrence
  assumes normalized: "source=comma_source_continuation_base source"
    and selected_certificates:
      "\<And>slot. slot<comma_decisive_sector_period
          (comma_source_continuation_base source) \<Longrightarrow>
        comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
          occurrence_descriptors templates source parent refs lift_descriptors slot \<and>
        comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
          template_column_ids lift_column_ids occurrence_descriptors
          lift_descriptors index refs slot"
    and earlier_wellformed:
      "\<And>child_index child_occurrence. child_index<index \<Longrightarrow>
        occurrence_at child_index=Some child_occurrence \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
    and used_lift_geometries:
      "\<And>slot child_index lift_cid. slot<length refs \<Longrightarrow>
        refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
        comma_semantic_b1_crt_lift_geometry_certified columns templates
          template_column_ids lift_column_ids lift_descriptors lift_cid"
    and bindings:
      "list_all (comma_semantic_b1_crt_constructed_piece_binding_matches columns
        lift_column_ids sources occurrence_at refs source parent destination) pieces"
  shows "list_all (comma_semantic_b1_crt_constructed_piece_matches columns
    lift_column_ids sources occurrence_at refs source parent destination) pieces"
proof (unfold list_all_iff, intro ballI)
  fix piece assume piece_mem: "piece\<in>set pieces"
  have binding:
    "comma_semantic_b1_crt_constructed_piece_binding_matches columns
      lift_column_ids sources occurrence_at refs source parent destination piece"
    using bindings piece_mem by (auto simp: list_all_iff)
  show "comma_semantic_b1_crt_constructed_piece_matches columns
      lift_column_ids sources occurrence_at refs source parent destination piece"
  proof (cases piece)
    case (Comma_B1_Piece_Terminal period slot cid parent_column)
    have slot_bound: "slot<comma_decisive_sector_period
        (comma_source_continuation_base source)"
      using binding Comma_B1_Piece_Terminal
      by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
          Let_def)
    have selected_valid:
      "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
        occurrence_descriptors templates source parent refs lift_descriptors
        (fst (comma_semantic_b1_crt_constructed_piece_origin piece))"
      and selected_certificate:
      "comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
        template_column_ids lift_column_ids occurrence_descriptors
        lift_descriptors index refs
        (fst (comma_semantic_b1_crt_constructed_piece_origin piece))"
      using selected_certificates[OF slot_bound] Comma_B1_Piece_Terminal
      by (simp_all add: comma_semantic_b1_crt_constructed_piece_origin_def)
    show ?thesis
      using comma_semantic_b1_crt_constructed_piece_matches_from_certificates
        [OF normalized selected_valid selected_certificate earlier_wellformed
          used_lift_geometries binding]
        Comma_B1_Piece_Terminal by simp
  next
    case (Comma_B1_Piece_Goto period slot child_index child_column lift_cid cid
        parent_column)
    have slot_bound: "slot<comma_decisive_sector_period
        (comma_source_continuation_base source)"
      using binding Comma_B1_Piece_Goto
      by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
          Let_def)
    have selected_valid:
      "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
        occurrence_descriptors templates source parent refs lift_descriptors
        (fst (comma_semantic_b1_crt_constructed_piece_origin piece))"
      and selected_certificate:
      "comma_semantic_b1_crt_constructed_goto_slot_certificate columns templates
        template_column_ids lift_column_ids occurrence_descriptors
        lift_descriptors index refs
        (fst (comma_semantic_b1_crt_constructed_piece_origin piece))"
      using selected_certificates[OF slot_bound] Comma_B1_Piece_Goto
      by (simp_all add: comma_semantic_b1_crt_constructed_piece_origin_def)
    show ?thesis
      using comma_semantic_b1_crt_constructed_piece_matches_from_certificates
        [OF normalized selected_valid selected_certificate earlier_wellformed
          used_lift_geometries binding]
        Comma_B1_Piece_Goto by simp
  qed
qed

ML \<open>Comma_Proof_Profile.report "Slot certificates stage=piece-list-match submitted"\<close>

lemma comma_semantic_b1_crt_constructed_bound_source_partition:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and template_column_ids :: "nat list list"
    and index :: nat
    and parent :: comma_semantic_b1_crt_occurrence
    and source :: comma_finite_position
  assumes normalized: "source=comma_source_continuation_base source"
    and source_admitted: "comma_round_admitted source"
    and table_admitted: "list_all (comma_crt_admitted 0) columns"
    and refs_length:
      "length refs=comma_decisive_sector_period source"
    and refs_slots:
      "map comma_semantic_b1_crt_lift_ref_slot refs=[0..<length refs]"
    and actions_certified:
      "comma_semantic_b1_crt_source_slot_action_row_certified source
        (comma_decisive_sector_period source) actions"
    and slots_valid:
      "list_all (comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
        occurrence_descriptors templates source parent refs lift_descriptors actions)
        [0..<length refs]"
    and slot_certificates:
      "list_all (\<lambda>slot.
         comma_semantic_b1_crt_constructed_goto_slot_certificate columns
           templates template_column_ids lift_column_ids occurrence_descriptors
           lift_descriptors index refs slot) [0..<length refs]"
    and children_wellformed:
      "\<And>child_index child_occurrence.
        child_index<index \<Longrightarrow>
        occurrence_at child_index=Some child_occurrence \<Longrightarrow>
        comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
    and used_lift_geometries:
      "\<And>slot child_index lift_cid.
        slot<length refs \<Longrightarrow>
        refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid \<Longrightarrow>
        comma_semantic_b1_crt_lift_geometry_certified columns templates
          template_column_ids lift_column_ids lift_descriptors lift_cid"
  shows "comma_semantic_b1_crt_cells_partition {..<924}
    (map (\<lambda>entry. comma_crt_set (fst entry))
      (comma_semantic_b1_crt_constructed_source_cells columns
        lift_column_ids occurrence_at refs source)) \<and>
    list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry))
      (comma_semantic_b1_crt_constructed_source_cells columns
        lift_column_ids occurrence_at refs source) \<and>
    map snd (comma_semantic_b1_crt_constructed_source_live_entries
      columns lift_column_ids occurrence_at refs source) =
    comma_semantic_b1_crt_constructed_live_source_cells columns lift_column_ids
      occurrence_at refs source"
proof -
  let ?period="comma_decisive_sector_period source"
  have period: "?period\<in>comma_semantic_b1_crt_source_periods"
    using comma_semantic_b1_generated_source_period_six[OF source_admitted] normalized[symmetric] by simp
  have period_positive: "0<?period"
    using period by (auto simp: comma_semantic_b1_crt_source_periods_def)
  have period_base: "?period=comma_decisive_sector_period (comma_source_continuation_base source)" using normalized by simp
  have each_slot:
    "\<And>slot. slot<?period \<Longrightarrow>
      comma_semantic_b1_crt_cells_partition
        (comma_semantic_b1_crt_slot_cylinder ?period slot)
        (map (\<lambda>entry. comma_crt_set (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns
            lift_column_ids occurrence_at refs source slot)) \<and>
      list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry))
        (comma_semantic_b1_crt_constructed_slot_cells columns
          lift_column_ids occurrence_at refs source slot) \<and>
      map snd (comma_semantic_b1_crt_constructed_slot_live_entries columns
        lift_column_ids occurrence_at refs source slot) =
      filter (\<lambda>entry. comma_crt_supported (fst entry))
        (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
          occurrence_at refs source slot)"
  proof -
    fix slot
    assume slot: "slot<?period"
    have ref_bound: "slot<length refs" using slot refs_length by simp
    have refs_slot: "comma_semantic_b1_crt_lift_ref_slot (refs!slot)=slot"
      using arg_cong[where f="\<lambda>xs. xs!slot", OF refs_slots] ref_bound
      by (simp add: nth_map nth_upt)
    have slot_valid_from_actions:
      "comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
        occurrence_descriptors templates source parent refs lift_descriptors actions slot"
      using slots_valid slot ref_bound by (auto simp: list_all_iff)
    have slot_valid:
      "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
        occurrence_descriptors templates source parent refs lift_descriptors slot"
      by (rule comma_semantic_b1_crt_lift_slot_valid_from_actions_implies_valid
        [OF actions_certified slot slot_valid_from_actions])
    show "comma_semantic_b1_crt_cells_partition
        (comma_semantic_b1_crt_slot_cylinder ?period slot)
        (map (\<lambda>entry. comma_crt_set (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns
            lift_column_ids occurrence_at refs source slot)) \<and>
        list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns
            lift_column_ids occurrence_at refs source slot) \<and>
        map snd (comma_semantic_b1_crt_constructed_slot_live_entries columns
          lift_column_ids occurrence_at refs source slot) =
        filter (\<lambda>entry. comma_crt_supported (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
            occurrence_at refs source slot)"
    proof (cases "refs!slot")
      case (Comma_B1_Lift_Terminal_Ref ref_slot parent_column)
      have ref_eq: "refs!slot=Comma_B1_Lift_Terminal_Ref slot parent_column"
        using Comma_B1_Lift_Terminal_Ref refs_slot by simp
      have action_eq:
        "actions!slot=comma_semantic_b1_source_slot_action source slot"
        by (rule comma_semantic_b1_crt_source_slot_action_row_certified_nth
          [OF actions_certified slot])
      have terminal_from_actions:
        "\<exists>result. comma_semantic_b1_terminal_action_result
          (actions!slot)=Some result"
        using slot_valid_from_actions ref_eq ref_bound slot
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
          split: if_splits option.splits)
      then obtain result where terminal_from_actions:
        "comma_semantic_b1_terminal_action_result (actions!slot)=Some result"
        by blast
      have terminal:
        "comma_semantic_b1_terminal_action_result
          (comma_semantic_b1_source_slot_action source slot)=Some result"
        using terminal_from_actions action_eq by simp
      have scope_admitted:
        "comma_crt_admitted 0 (comma_crt_source_scope_column (?period,slot))"
        by (rule comma_semantic_b1_crt_lift_scope_admitted[OF period slot])
      have partition:
        "comma_semantic_b1_crt_cells_partition
          (comma_semantic_b1_crt_slot_cylinder ?period slot)
          (map (\<lambda>entry. comma_crt_set (fst entry))
            (comma_semantic_b1_crt_constructed_slot_cells columns
              lift_column_ids occurrence_at refs source slot))"
        by (rule comma_semantic_b1_crt_constructed_terminal_slot_partition
          [OF period slot ref_bound period_base ref_eq terminal refl])
      have admitted:
        "list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns
            lift_column_ids occurrence_at refs source slot)"
        using period slot ref_bound ref_eq terminal scope_admitted normalized
        by (simp add: comma_semantic_b1_crt_constructed_slot_cells_def Let_def)
      have cells_alignment:
        "map snd (comma_semantic_b1_crt_constructed_slot_live_entries columns
          lift_column_ids occurrence_at refs source slot) =
         filter (\<lambda>entry. comma_crt_supported (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
            occurrence_at refs source slot)"
        by (rule comma_semantic_b1_crt_constructed_terminal_live_entry_cells
          [OF period slot ref_bound period_base ref_eq refl terminal])
      show ?thesis using partition admitted cells_alignment by simp
    next
      case (Comma_B1_Lift_Goto_Ref ref_slot child_index lift_cid)
      have ref_eq: "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
        using Comma_B1_Lift_Goto_Ref refs_slot by simp
      have action_eq:
        "actions!slot=comma_semantic_b1_source_slot_action source slot"
        by (rule comma_semantic_b1_crt_source_slot_action_row_certified_nth
          [OF actions_certified slot])
      obtain child shift where action_from_actions:
        "actions!slot=Comma_Continuation_Goto child shift"
        using slot_valid_from_actions ref_eq ref_bound slot
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
          split: if_splits option.splits prod.splits
            comma_source_continuation_action.splits)
      have action:
        "comma_semantic_b1_source_slot_action source slot=
          Comma_Continuation_Goto child shift"
        using action_from_actions action_eq by simp
      obtain child_occurrence where child_at:
        "occurrence_at child_index=Some child_occurrence"
        using slot_valid_from_actions ref_eq action_from_actions ref_bound slot
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
          split: if_splits option.splits prod.splits)
      have slot_certificate:
        "comma_semantic_b1_crt_constructed_goto_slot_certificate columns
          templates template_column_ids lift_column_ids occurrence_descriptors
          lift_descriptors index refs slot"
        by (rule comma_semantic_b1_crt_list_all_upt_index
          [OF slot_certificates ref_bound])
      have child_bounds:
        "child_index<index \<and>
         child_index<length occurrence_descriptors"
        by (rule comma_semantic_b1_crt_goto_slot_certificate_child_bounds
          [OF slot_certificate ref_eq])
      have child_lt: "child_index<index"
        and child_descriptor_bound: "child_index<length occurrence_descriptors"
        using child_bounds by blast+
      have child_wf:
        "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
        by (rule children_wellformed[OF child_lt child_at])
      have details:
        "lift_cid<length lift_descriptors \<and>
         comma_semantic_b1_crt_lift_descriptor_period (lift_descriptors!lift_cid)=?period \<and>
         comma_semantic_b1_crt_lift_descriptor_slot (lift_descriptors!lift_cid)=slot \<and>
         comma_semantic_b1_crt_lift_descriptor_template_cid
           (lift_descriptors!lift_cid)<length templates \<and>
         comma_semantic_b1_crt_occurrence_columns child_occurrence=
           templates!comma_semantic_b1_crt_lift_descriptor_template_cid
             (lift_descriptors!lift_cid) \<and>
         comma_semantic_b1_crt_lift_descriptor_net_shift
           (lift_descriptors!lift_cid)=
             (shift+comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924 \<and>
         comma_semantic_b1_crt_lift_descriptor_valid templates
           (lift_descriptors!lift_cid)"
        using slot_valid ref_eq action child_at ref_bound slot normalized
        by (auto simp: comma_semantic_b1_crt_lift_slot_valid_def
          split: option.splits prod.splits)
      have lift_valid: "comma_semantic_b1_crt_lift_descriptor_valid templates (lift_descriptors!lift_cid)"
        and lift_period: "comma_semantic_b1_crt_lift_descriptor_period (lift_descriptors!lift_cid)=?period"
        and lift_slot: "comma_semantic_b1_crt_lift_descriptor_slot (lift_descriptors!lift_cid)=slot"
        and child_columns: "comma_semantic_b1_crt_occurrence_columns child_occurrence=templates!comma_semantic_b1_crt_lift_descriptor_template_cid (lift_descriptors!lift_cid)"
        and lift_net: "comma_semantic_b1_crt_lift_descriptor_net_shift (lift_descriptors!lift_cid)=(shift+comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924"
        using details by blast+
      have lift_geometry:
        "comma_semantic_b1_crt_lift_geometry_certified columns templates
          template_column_ids lift_column_ids lift_descriptors lift_cid"
        using used_lift_geometries[OF ref_bound ref_eq] .
      have resolved:
        "comma_semantic_b1_crt_column_ids_resolve columns
          (lift_column_ids!lift_cid)
          (comma_semantic_b1_crt_lift_columns templates
            (lift_descriptors!lift_cid))"
        by (rule comma_semantic_b1_crt_lift_geometry_certified_resolves
          [OF lift_geometry])
      have lifted:
        "comma_semantic_b1_crt_lift_columns templates
            (lift_descriptors!lift_cid) =
          map (\<lambda>column. comma_crt_apply_shifted Comma_CRT_And
            (comma_semantic_b1_crt_lift_descriptor_net_shift
              (lift_descriptors!lift_cid))
            (comma_crt_source_scope_column (?period,slot)) column)
            (comma_semantic_b1_crt_occurrence_columns child_occurrence)"
        using lift_valid lift_period lift_slot child_columns lift_net period slot normalized
        by (simp add: comma_semantic_b1_crt_lift_columns_def
          comma_semantic_b1_crt_lift_columns_option_def
          comma_semantic_b1_crt_lift_descriptor_valid_def)
      have row_resolves:
        "map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid) =
          comma_semantic_b1_crt_lift_columns templates
            (lift_descriptors!lift_cid)"
        by (rule comma_semantic_b1_crt_column_ids_resolve_map[OF resolved])
      have row_admitted:
        "list_all (comma_crt_admitted 0)
          (map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid))"
        by (rule comma_semantic_b1_crt_column_ids_resolve_preserves_list_all
          [OF table_admitted resolved])
      have lift_row:
        "map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid) =
          map (\<lambda>column. comma_crt_apply_shifted Comma_CRT_And
            ((shift+comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924)
            (comma_crt_source_scope_column (?period,slot)) column)
            (comma_semantic_b1_crt_occurrence_columns child_occurrence)"
        using row_resolves lifted lift_net by simp
      have net: "(shift+comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924 = (shift+comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924" by simp
      have lift_bounds:
        "lift_cid<length lift_column_ids \<and>
         lift_cid<length lift_descriptors"
        using comma_semantic_b1_crt_lift_geometry_certified_exposes
          [OF lift_geometry] by blast
      have lift_bound: "lift_cid<length lift_column_ids"
        using lift_bounds by blast
      have lift_width:
        "length (lift_column_ids!lift_cid)=
          length (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
      proof -
        have lengths:
          "length (lift_column_ids!lift_cid)=length (comma_semantic_b1_crt_occurrence_columns child_occurrence)"
          using arg_cong[where f=length, OF lift_row] by simp
        show ?thesis using lengths child_wf
          by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
      qed
      have cells:
        "comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
           occurrence_at refs source slot =
         zip (map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid))
           (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
        using slot ref_bound ref_eq action child_at lift_bound lift_width normalized
        by (simp add: comma_semantic_b1_crt_constructed_slot_cells_def Let_def)
      have cells_admitted:
        "list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
            occurrence_at refs source slot)"
        using row_admitted cells
        by (auto simp: list_all_iff in_set_zip)
      have partition:
        "comma_semantic_b1_crt_cells_partition
          (comma_semantic_b1_crt_slot_cylinder ?period slot)
          (map (\<lambda>entry. comma_crt_set (fst entry))
            (comma_semantic_b1_crt_constructed_slot_cells columns
              lift_column_ids occurrence_at refs source slot))"
        by (rule comma_semantic_b1_crt_constructed_goto_slot_partition
          [where columns=columns and lift_column_ids=lift_column_ids and occurrence_at=occurrence_at and refs=refs and source=source and period="?period" and slot=slot and child_index=child_index and child=child and shift=shift and child_occurrence=child_occurrence and lift_cid=lift_cid and net="(shift+comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924"
            , OF period slot ref_bound period_base ref_eq action child_at child_wf lift_bound lift_row net])
      have cells_alignment:
        "map snd (comma_semantic_b1_crt_constructed_slot_live_entries columns
          lift_column_ids occurrence_at refs source slot) =
         filter (\<lambda>entry. comma_crt_supported (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
            occurrence_at refs source slot)"
        by (rule comma_semantic_b1_crt_constructed_goto_live_entry_cells
          [where columns=columns and lift_column_ids=lift_column_ids and occurrence_at=occurrence_at and refs=refs and source=source and period="?period" and slot=slot and child_index=child_index and child=child and shift=shift and child_occurrence=child_occurrence and lift_cid=lift_cid
            , OF period slot ref_bound period_base ref_eq action child_at lift_bound lift_width])
      show ?thesis using partition cells_admitted cells_alignment by simp
    qed
  qed
  have partition:
    "comma_semantic_b1_crt_cells_partition {..<924}
      (concat (map (\<lambda>slot. map (\<lambda>entry. comma_crt_set (fst entry))
        (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
          occurrence_at refs source slot)) [0..<?period]))"
    by (rule comma_semantic_b1_crt_constructed_source_cells_partition
      [OF period period_positive]) (use each_slot in auto)
  have admitted:
    "list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry))
      (concat (map (comma_semantic_b1_crt_constructed_slot_cells columns
        lift_column_ids occurrence_at refs source) [0..<?period]))"
    using each_slot by (auto simp: list_all_iff)
  have live_alignment:
    "map snd (comma_semantic_b1_crt_constructed_source_live_entries
        columns lift_column_ids occurrence_at refs source) =
      comma_semantic_b1_crt_constructed_live_source_cells columns lift_column_ids
        occurrence_at refs source"
    by (rule comma_semantic_b1_crt_constructed_source_live_entry_cells[OF period_base])
      (use each_slot in auto)
  have source_cells_eq: "comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids occurrence_at refs source = concat (map (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids occurrence_at refs source) [0..<?period])" by (simp only: comma_semantic_b1_crt_constructed_source_cells_def period_base[symmetric])
  have partition_source: "comma_semantic_b1_crt_cells_partition {..<924} (map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids occurrence_at refs source))" using partition source_cells_eq by (simp only: source_cells_eq map_concat map_map o_def)
  have admitted_source: "list_all (\<lambda>entry. comma_crt_admitted 0 (fst entry)) (comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids occurrence_at refs source)" using admitted source_cells_eq by (simp only: source_cells_eq)
  show ?thesis using partition_source admitted_source live_alignment by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_bound_source_partition}]; Comma_Proof_Profile.report "Constructed occurrence: source partition checked"\<close>
ML \<open>
  val _ = Comma_Proof_Profile.report "Slot certificates stage=oracle-audit entered"
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_semantic_b1_crt_lift_geometry_certified_resolves comma_semantic_b1_crt_template_geometry_certified_resolves comma_semantic_b1_crt_lift_geometry_certified_exposes
      comma_semantic_b1_crt_goto_slot_certificate_child_bounds
      comma_semantic_b1_crt_lift_slot_valid_goto_action
      comma_semantic_b1_crt_constructed_goto_piece_matches_from_certificates
      comma_semantic_b1_crt_constructed_piece_matches_from_certificates
      comma_semantic_b1_crt_constructed_piece_matches_list_from_certificates
      comma_semantic_b1_crt_constructed_bound_source_partition})
    then () else error "Slot certificate refinement depends on an oracle"
  val _ = Comma_Proof_Profile.report "Slot certificates stage=oracle-audit checked"
\<close>

end
