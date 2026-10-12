theory Comma_Semantic_B1_CRT_Construction_Binding
  imports Comma_Semantic_B1_CRT_Multiset
    Comma_Semantic_B1_CRT_Column_DAG
begin

ML \<open>Comma_Proof_Profile.report "Construction binding stage=entered"\<close>

lemma comma_semantic_b1_crt_tagged_map_distinct:
  "distinct (map (\<lambda>column. (slot,column)) columns) = distinct columns"
  by (simp add: distinct_map inj_on_def)

text \<open>
Construction bindings are proof data, rather than a second geometry replay.
Each parent result row lists the exact slot pieces routed to it.  The
certificate gives a ColumnCID for each piece in row order.  The checker
verifies each piece is covered by its selected rebased parent column.  A
certified parent-template partition and the source partition then recover the
exact grouped geometry without rebuilding an OR fold over those columns.
\<close>

definition comma_semantic_b1_crt_column_ids_resolve ::
    "comma_crt_column list \<Rightarrow> nat list \<Rightarrow>
      comma_crt_column list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_column_ids_resolve columns ids values \<longleftrightarrow>
    length ids = length values \<and>
    (\<forall>i<length ids. ids!i<length columns \<and>
      columns!(ids!i)=values!i)"

text \<open>
The source catalogue has one explicit row of certified action values per
source.  Consumers use these row values after the source/slot equation has
been checked, so piece bindings do not unfold the endpoint action again.
\<close>
definition comma_semantic_b1_crt_slot_actions_table ::
    "comma_finite_position list \<Rightarrow>
      comma_source_continuation_action list list" where
  "comma_semantic_b1_crt_slot_actions_table sources =
    map (\<lambda>source. map (comma_semantic_b1_source_slot_action source)
      [0..<comma_decisive_sector_period
        (comma_source_continuation_base source)]) sources"

lemma comma_semantic_b1_crt_slot_actions_table_row:
  assumes index: "index<length sources"
  shows "comma_semantic_b1_crt_slot_actions_table sources!index =
    map (comma_semantic_b1_source_slot_action (sources!index))
      [0..<comma_decisive_sector_period
        (comma_source_continuation_base (sources!index))]"
  using index by (simp add: comma_semantic_b1_crt_slot_actions_table_def)

definition comma_semantic_b1_crt_source_slot_action_row_certified ::
    "comma_finite_position \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_source_slot_action_row_certified source period actions
    \<longleftrightarrow> length actions=period \<and>
      (\<forall>slot<period. actions!slot=
        comma_semantic_b1_source_slot_action source slot)"

lemma comma_semantic_b1_crt_source_slot_action_row_certified_nth:
  assumes certified:
      "comma_semantic_b1_crt_source_slot_action_row_certified source period actions"
    and slot: "slot<period"
  shows "actions!slot=comma_semantic_b1_source_slot_action source slot"
  using certified slot
  by (auto simp: comma_semantic_b1_crt_source_slot_action_row_certified_def)

lemma comma_semantic_b1_crt_source_action_row_length_le_28:
  assumes admitted: "comma_round_admitted source"
    and row: "comma_semantic_b1_crt_source_slot_action_row_certified source
      (comma_decisive_sector_period
        (comma_source_continuation_base source)) actions"
  shows "length actions \<le> 28"
proof -
  have period:
      "comma_decisive_sector_period
        (comma_source_continuation_base source) \<in>
          comma_semantic_b1_crt_source_periods"
    by (rule comma_semantic_b1_generated_source_period_six[OF admitted])
  have period_bound:
      "comma_decisive_sector_period
        (comma_source_continuation_base source) \<le> 28"
    using period by (auto simp: comma_semantic_b1_crt_source_periods_def)
  have row_length:
      "length actions=comma_decisive_sector_period
        (comma_source_continuation_base source)"
    using row
    by (simp add: comma_semantic_b1_crt_source_slot_action_row_certified_def)
  show ?thesis using row_length period_bound by simp
qed

definition comma_semantic_b1_crt_lift_slot_valid_from_actions ::
    "comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_descriptor list \<Rightarrow>
      comma_crt_column list list \<Rightarrow> comma_finite_position \<Rightarrow>
      comma_semantic_b1_crt_occurrence \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor list \<Rightarrow>
      comma_source_continuation_action list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_lift_slot_valid_from_actions sources occurrence_at
      occurrence_descriptors templates source parent refs descriptors actions slot
    \<longleftrightarrow>
      (if slot<length actions \<and> slot<comma_decisive_sector_period
          (comma_source_continuation_base source) \<and> slot<length refs then
       (case refs!slot of
          Comma_B1_Lift_Terminal_Ref ref_slot parent_column \<Rightarrow>
            ref_slot=slot \<and>
            parent_column<length (comma_semantic_b1_crt_occurrence_columns parent) \<and>
            (case comma_semantic_b1_terminal_action_result (actions!slot) of
               None \<Rightarrow> False
             | Some result \<Rightarrow>
                 comma_semantic_b1_crt_occurrence_beta parent!parent_column=result)
        | Comma_B1_Lift_Goto_Ref ref_slot child_index lift_cid \<Rightarrow>
            (case actions!slot of
               Comma_Continuation_Goto child shift \<Rightarrow>
                 ref_slot=slot \<and> child_index<length sources \<and>
                 child_index<length occurrence_descriptors \<and>
                 lift_cid<length descriptors \<and>
                 sources!child_index=comma_source_continuation_base child \<and>
                 (case (occurrence_at child_index,descriptors!lift_cid) of
                    (Some child_occurrence,descriptor) \<Rightarrow>
                      fst (occurrence_descriptors!child_index)=
                        comma_semantic_b1_crt_lift_descriptor_template_cid descriptor \<and>
                      comma_semantic_b1_crt_lift_descriptor_period descriptor=
                        comma_decisive_sector_period (comma_source_continuation_base source) \<and>
                      comma_semantic_b1_crt_lift_descriptor_slot descriptor=slot \<and>
                      comma_semantic_b1_crt_lift_descriptor_template_cid descriptor<length templates \<and>
                      comma_semantic_b1_crt_occurrence_columns child_occurrence=
                        templates!comma_semantic_b1_crt_lift_descriptor_template_cid descriptor \<and>
                      comma_semantic_b1_crt_lift_descriptor_net_shift descriptor=
                        (shift+comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924 \<and>
                      comma_semantic_b1_crt_lift_descriptor_valid templates descriptor
                  | _ \<Rightarrow> False)
             | _ \<Rightarrow> False))
      else False)"

lemma comma_semantic_b1_crt_lift_slot_valid_from_actions_implies_valid:
  assumes row:
      "comma_semantic_b1_crt_source_slot_action_row_certified source period actions"
    and slot: "slot<period"
    and valid: "comma_semantic_b1_crt_lift_slot_valid_from_actions sources
      occurrence_at occurrence_descriptors templates source parent refs
      descriptors actions slot"
  shows "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
    occurrence_descriptors templates source parent refs descriptors slot"
proof -
  have action:
    "actions!slot=comma_semantic_b1_source_slot_action source slot"
    by (rule comma_semantic_b1_crt_source_slot_action_row_certified_nth
      [OF row slot])
  show ?thesis using valid action slot
    by (auto simp: comma_semantic_b1_crt_lift_slot_valid_from_actions_def
        comma_semantic_b1_crt_lift_slot_valid_def
        split: if_splits option.splits prod.splits
          comma_semantic_b1_crt_lift_ref.splits
          comma_source_continuation_action.splits)
qed
lemma comma_semantic_b1_crt_column_ids_resolve_list_all2:
  "comma_semantic_b1_crt_column_ids_resolve columns ids values =
    list_all2 (\<lambda>cid value. cid<length columns \<and>
      columns!cid=value) ids values"
  by (simp add: comma_semantic_b1_crt_column_ids_resolve_def
    list_all2_conv_all_nth)
lemma comma_semantic_b1_crt_column_ids_resolve_map:
  assumes resolved:
    "comma_semantic_b1_crt_column_ids_resolve columns ids values"
  shows "map (\<lambda>cid. columns!cid) ids=values"
proof (rule nth_equalityI)
  show "length (map (\<lambda>cid. columns!cid) ids)=length values"
    using resolved by (simp add: comma_semantic_b1_crt_column_ids_resolve_def)
  fix i
  assume i: "i<length (map (\<lambda>cid. columns!cid) ids)"
  have i_ids: "i<length ids" using i by simp
  have id_bound: "ids!i<length columns"
    and column_eq: "columns!(ids!i)=values!i"
    using resolved i_ids
    by (auto simp: comma_semantic_b1_crt_column_ids_resolve_def)
  show "map (\<lambda>cid. columns!cid) ids ! i = values!i"
    using i_ids id_bound column_eq by (simp add: nth_map)
qed

lemma comma_semantic_b1_crt_column_ids_resolve_from_map:
  assumes bounded: "list_all (\<lambda>cid. cid<length columns) ids"
    and mapped: "map (\<lambda>cid. columns!cid) ids=values"
  shows "comma_semantic_b1_crt_column_ids_resolve columns ids values"
  using bounded unfolding mapped[symmetric]
  by (simp add: comma_semantic_b1_crt_column_ids_resolve_def
      list_all_length)

lemma comma_semantic_b1_crt_column_ids_resolve_columns_for_from_map:
  assumes table: "columns=comma_semantic_b1_crt_columns_for dag extent"
    and bounded: "list_all (\<lambda>cid. cid<extent) ids"
    and mapped: "map (comma_semantic_b1_crt_column_at dag) ids=values"
  shows "comma_semantic_b1_crt_column_ids_resolve columns ids values"
proof -
  have bounds: "list_all (\<lambda>cid. cid<length columns) ids"
    using bounded table
    by (simp only: comma_semantic_b1_crt_columns_for_length)
  have columns_map:
      "map (\<lambda>cid. columns!cid) ids=
        map (comma_semantic_b1_crt_column_at dag) ids"
  proof (rule map_cong[OF refl])
    fix cid
    assume "cid\<in>set ids"
    then have "cid<extent" using bounded by (simp add: list_all_iff)
    then show "columns!cid=comma_semantic_b1_crt_column_at dag cid"
      using table by (simp add: comma_semantic_b1_crt_columns_for_nth)
  qed
  show ?thesis
    by (rule comma_semantic_b1_crt_column_ids_resolve_from_map
      [OF bounds trans[OF columns_map mapped]])
qed

lemma comma_semantic_b1_crt_column_ids_resolve_columns_for:
  assumes table:
      "columns = comma_semantic_b1_crt_columns_for dag extent"
    and resolved:
      "comma_semantic_b1_crt_column_ids_resolve columns ids values"
  shows "values = map (comma_semantic_b1_crt_column_at dag) ids"
proof -
  have columns_length: "length columns=extent"
    using table by (simp add: comma_semantic_b1_crt_columns_for_length)
  have ids_bounded: "\<forall>cid\<in>set ids. cid<extent"
  proof (intro ballI)
    fix cid
    assume cid_in: "cid\<in>set ids"
    then obtain i where i_bound: "i<length ids" and cid_eq: "ids!i=cid"
      by (auto simp: in_set_conv_nth)
    have id_bound: "ids!i<length columns"
      using resolved i_bound
      by (auto simp: comma_semantic_b1_crt_column_ids_resolve_def)
    show "cid<extent"
      using id_bound columns_length cid_eq by simp
  qed
  have resolved_map:
      "map (\<lambda>cid. columns!cid) ids=values"
    by (rule comma_semantic_b1_crt_column_ids_resolve_map[OF resolved])
  have table_map:
      "map (\<lambda>cid. columns!cid) ids=
        map (comma_semantic_b1_crt_column_at dag) ids"
  proof (rule map_cong[OF refl])
    fix cid
    assume cid_in: "cid\<in>set ids"
    have cid_bound: "cid<extent"
      using ids_bounded cid_in by blast
    show "columns!cid=comma_semantic_b1_crt_column_at dag cid"
      using table cid_bound
      by (simp add: comma_semantic_b1_crt_columns_for_nth)
  qed
  show ?thesis using resolved_map table_map by metis
qed

lemma comma_semantic_b1_crt_column_ids_resolve_preserves_list_all:
  fixes columns :: "comma_crt_column list" and ids :: "nat list"
    and selected_columns :: "comma_crt_column list"
    and P :: "comma_crt_column \<Rightarrow> bool"
  assumes table: "list_all P columns"
    and resolved: "comma_semantic_b1_crt_column_ids_resolve columns ids selected_columns"
  shows "list_all P (map (\<lambda>cid. columns!cid) ids)"
proof -
  have all_columns: "\<forall>column\<in>set columns. P column"
    using table by (simp add: list_all_iff)
  have all_values: "\<forall>column\<in>set (map (\<lambda>cid. columns!cid) ids). P column"
  proof (intro ballI)
    fix column
    assume column: "column\<in>set (map (\<lambda>cid. columns!cid) ids)"
    then obtain cid where cid: "cid\<in>set ids" and column_eq: "column=columns!cid" by auto
    obtain i where i: "i<length ids" and cid_eq: "cid=ids!i"
      using cid by (auto simp: in_set_conv_nth)
    have cid_bound: "ids!i<length columns"
      using resolved i by (auto simp: comma_semantic_b1_crt_column_ids_resolve_def)
    have value_member: "columns!(ids!i)\<in>set columns" by (rule nth_mem[OF cid_bound])
    have value_ok: "P (columns!(ids!i))" by (rule bspec[OF all_columns value_member])
    show "P column" using value_ok column_eq cid_eq by simp
  qed
  show ?thesis using all_values by (simp add: list_all_iff)
qed
datatype comma_semantic_b1_crt_piece_ref =
    Comma_B1_Piece_Terminal nat nat nat nat
  | Comma_B1_Piece_Goto nat nat nat nat nat nat nat

fun comma_semantic_b1_crt_piece_period ::
    "comma_semantic_b1_crt_piece_ref \<Rightarrow> nat" where
  "comma_semantic_b1_crt_piece_period (Comma_B1_Piece_Terminal period slot cid parent) = period"
| "comma_semantic_b1_crt_piece_period
      (Comma_B1_Piece_Goto period slot child child_column lift cid parent) = period"

fun comma_semantic_b1_crt_piece_slot ::
    "comma_semantic_b1_crt_piece_ref \<Rightarrow> nat" where
  "comma_semantic_b1_crt_piece_slot (Comma_B1_Piece_Terminal period slot cid parent) = slot"
| "comma_semantic_b1_crt_piece_slot
      (Comma_B1_Piece_Goto period slot child child_column lift cid parent) = slot"

fun comma_semantic_b1_crt_piece_cid ::
    "comma_semantic_b1_crt_piece_ref \<Rightarrow> nat" where
  "comma_semantic_b1_crt_piece_cid (Comma_B1_Piece_Terminal period slot cid parent) = cid"
| "comma_semantic_b1_crt_piece_cid
      (Comma_B1_Piece_Goto period slot child child_column lift cid parent) = cid"

fun comma_semantic_b1_crt_piece_parent_column ::
    "comma_semantic_b1_crt_piece_ref \<Rightarrow> nat" where
  "comma_semantic_b1_crt_piece_parent_column
      (Comma_B1_Piece_Terminal period slot cid parent) = parent"
| "comma_semantic_b1_crt_piece_parent_column
      (Comma_B1_Piece_Goto period slot child child_column lift cid parent) = parent"

definition comma_semantic_b1_crt_group_construction_bound ::
    "comma_crt_column list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_crt_piece_ref list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_group_construction_bound columns rebase parent_index
      parent_cid pieces \<longleftrightarrow>
    (if parent_cid<length columns \<and> pieces\<noteq>[] \<and>
        list_all (\<lambda>piece.
          comma_semantic_b1_crt_piece_cid piece<length columns \<and>
          comma_semantic_b1_crt_piece_parent_column piece=parent_index \<and>
          comma_crt_supported
            (columns!comma_semantic_b1_crt_piece_cid piece) \<and>
          \<not> comma_crt_supported (comma_crt_apply Comma_CRT_And
            (columns!comma_semantic_b1_crt_piece_cid piece)
            (comma_crt_negate
              (comma_crt_shift rebase (columns!parent_cid))))) pieces
     then True
     else False)"

lemma comma_semantic_b1_crt_overlapping_parent_columns_rejected:
  "comma_semantic_b1_crt_group_construction_bound
      [Comma_CRT_Bool True,Comma_CRT_Bool True] 0 0 0
        [Comma_B1_Piece_Terminal 1 0 0 0] \<and>
   comma_semantic_b1_crt_group_construction_bound
      [Comma_CRT_Bool True,Comma_CRT_Bool True] 0 1 1
        [Comma_B1_Piece_Terminal 1 0 0 1] \<and>
   comma_crt_set (Comma_CRT_Bool True) \<subseteq>
      comma_semantic_b1_crt_rebase_set 0 (comma_crt_set (Comma_CRT_Bool True)) \<and>
   \<not> comma_semantic_b1_crt_columns_partition_certified
      [Comma_CRT_Bool True,Comma_CRT_Bool True]"
proof (intro conjI)
  show "comma_semantic_b1_crt_group_construction_bound
      [Comma_CRT_Bool True,Comma_CRT_Bool True] 0 0 0
        [Comma_B1_Piece_Terminal 1 0 0 0]" by code_simp
  show "comma_semantic_b1_crt_group_construction_bound
      [Comma_CRT_Bool True,Comma_CRT_Bool True] 0 1 1
        [Comma_B1_Piece_Terminal 1 0 0 1]" by code_simp
  show "comma_crt_set (Comma_CRT_Bool True) \<subseteq>
      comma_semantic_b1_crt_rebase_set 0 (comma_crt_set (Comma_CRT_Bool True))"
    by (auto simp: comma_crt_set_def comma_semantic_b1_crt_rebase_set_def)
  show "\<not> comma_semantic_b1_crt_columns_partition_certified
      [Comma_CRT_Bool True,Comma_CRT_Bool True]" by code_simp
qed

lemma comma_semantic_b1_crt_group_construction_bound_sound:
  assumes table_admitted: "list_all (comma_crt_admitted 0) columns"
    and bound:
      "comma_semantic_b1_crt_group_construction_bound columns rebase parent_index
        parent_cid pieces"
  shows "(\<Union>piece\<in>set pieces.
      comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)) \<subseteq>
    comma_semantic_b1_crt_rebase_set rebase
      (comma_crt_set (columns!parent_cid))"
proof -
  have parent_bound: "parent_cid<length columns"
    and pieces_nonempty: "pieces\<noteq>[]"
    and pieces_valid: "list_all (\<lambda>piece.
      comma_semantic_b1_crt_piece_cid piece<length columns \<and>
      comma_semantic_b1_crt_piece_parent_column piece=parent_index \<and>
      comma_crt_supported
        (columns!comma_semantic_b1_crt_piece_cid piece) \<and>
      \<not> comma_crt_supported (comma_crt_apply Comma_CRT_And
        (columns!comma_semantic_b1_crt_piece_cid piece)
        (comma_crt_negate (comma_crt_shift rebase (columns!parent_cid))))
      ) pieces"
    using bound by (auto simp: comma_semantic_b1_crt_group_construction_bound_def
      split: if_splits)
  have parent_admitted: "comma_crt_admitted 0 (columns!parent_cid)"
    using table_admitted parent_bound
    by (auto simp: list_all_iff nth_mem)
  have shifted_admitted:
      "comma_crt_admitted 0 (comma_crt_shift rebase (columns!parent_cid))"
    by (rule comma_crt_shift_admitted[OF parent_admitted])
  have shifted_set:
      "comma_crt_set (comma_crt_shift rebase (columns!parent_cid)) =
        comma_semantic_b1_crt_rebase_set rebase
          (comma_crt_set (columns!parent_cid))"
    using comma_crt_shift_column_exact[OF parent_admitted]
    by (simp add: comma_semantic_b1_crt_rebase_set_def)
  have each_covered:
      "\<forall>piece\<in>set pieces.
        comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece) \<subseteq>
          comma_crt_set (comma_crt_shift rebase (columns!parent_cid))"
  proof (intro ballI)
    fix piece
    assume piece: "piece\<in>set pieces"
    have facts:
        "comma_semantic_b1_crt_piece_cid piece<length columns \<and>
         comma_semantic_b1_crt_piece_parent_column piece=parent_index \<and>
         comma_crt_supported (columns!comma_semantic_b1_crt_piece_cid piece) \<and>
         \<not> comma_crt_supported (comma_crt_apply Comma_CRT_And
           (columns!comma_semantic_b1_crt_piece_cid piece)
           (comma_crt_negate (comma_crt_shift rebase (columns!parent_cid))))"
      using pieces_valid piece by (auto simp: list_all_iff)
    have piece_admitted:
        "comma_crt_admitted 0 (columns!comma_semantic_b1_crt_piece_cid piece)"
      using table_admitted facts by (auto simp: list_all_iff nth_mem)
    show "comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece) \<subseteq>
        comma_crt_set (comma_crt_shift rebase (columns!parent_cid))"
      by (rule comma_semantic_b1_crt_unsupported_and_subset
        [OF piece_admitted shifted_admitted]) (use facts in blast)
  qed
  show ?thesis
    using each_covered shifted_set by blast
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_group_construction_bound_sound}];
  Comma_Proof_Profile.report "Construction binding stage=per-piece coverage checked"
\<close>

lemma comma_semantic_b1_crt_rebase_inverse_set:
  assumes shift: "shift<924" and cells: "cells\<subseteq>{..<924}"
  shows "comma_semantic_b1_crt_rebase_set shift
      (comma_semantic_b1_crt_rebase_set ((924-shift) mod 924) cells)=cells"
proof (rule set_eqI)
  fix phase
  have cancel: "((phase+shift) mod 924 + (924-shift) mod 924) mod 924=phase mod 924"
    using comma_semantic_b1_cancel_shift[of phase shift] shift
    by (simp add: comma_semantic_b1_inverse_shift_def)
  show "phase\<in>comma_semantic_b1_crt_rebase_set shift
      (comma_semantic_b1_crt_rebase_set ((924-shift) mod 924) cells) \<longleftrightarrow>
      phase\<in>cells"
  proof
    assume member: "phase\<in>comma_semantic_b1_crt_rebase_set shift
        (comma_semantic_b1_crt_rebase_set ((924-shift) mod 924) cells)"
    then have phase_bound: "phase<924"
      and inner: "(phase+shift) mod 924\<in>
        comma_semantic_b1_crt_rebase_set ((924-shift) mod 924) cells"
      by (auto simp: comma_semantic_b1_crt_rebase_set_def)
    have result: "((phase+shift) mod 924 + (924-shift) mod 924) mod 924\<in>cells"
      using inner by (auto simp: comma_semantic_b1_crt_rebase_set_def)
    show "phase\<in>cells" using result cancel phase_bound by simp
  next
    assume member: "phase\<in>cells"
    have phase_bound: "phase<924" using cells member by blast
    have shifted_bound: "(phase+shift) mod 924<924" by simp
    have inner: "(phase+shift) mod 924\<in>
        comma_semantic_b1_crt_rebase_set ((924-shift) mod 924) cells"
      using phase_bound shifted_bound member cancel
      by (auto simp: comma_semantic_b1_crt_rebase_set_def)
    show "phase\<in>comma_semantic_b1_crt_rebase_set shift
        (comma_semantic_b1_crt_rebase_set ((924-shift) mod 924) cells)"
      using phase_bound inner by (auto simp: comma_semantic_b1_crt_rebase_set_def)
  qed
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_rebase_inverse_set}];
  Comma_Proof_Profile.report "Construction binding stage=inverse-rebase checked"
\<close>

lemma comma_semantic_b1_crt_group_piece_parent_covered:
  assumes table: "list_all (comma_crt_admitted 0) columns"
    and rebase: "rebase<924"
    and parent_admitted: "comma_crt_admitted 0 (columns!parent_cid)"
    and parent_column:
      "comma_semantic_b1_crt_occurrence_columns parent!row=columns!parent_cid"
    and bound:
      "comma_semantic_b1_crt_group_construction_bound columns rebase row
        parent_cid pieces"
    and piece: "piece\<in>set pieces"
  shows "comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece) \<subseteq>
    comma_crt_set (comma_crt_shift rebase
      (comma_semantic_b1_crt_occurrence_columns parent!row))"
proof -
  have piece_coverage:
      "(\<Union>item\<in>set pieces.
        comma_crt_set (columns!comma_semantic_b1_crt_piece_cid item)) \<subseteq>
       comma_semantic_b1_crt_rebase_set rebase
         (comma_crt_set (columns!parent_cid))"
    by (rule comma_semantic_b1_crt_group_construction_bound_sound[OF table bound])
  have shifted:
      "comma_crt_set (comma_crt_shift rebase (columns!parent_cid))=
        comma_semantic_b1_crt_rebase_set rebase
          (comma_crt_set (columns!parent_cid))"
    using comma_crt_shift_column_exact[OF parent_admitted, of rebase]
    by (simp only: comma_semantic_b1_crt_rebase_set_def)
  have piece_in_union:
      "comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece) \<subseteq>
        (\<Union>item\<in>set pieces.
          comma_crt_set (columns!comma_semantic_b1_crt_piece_cid item))"
    using piece by blast
  have covered:
      "comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece) \<subseteq>
        comma_semantic_b1_crt_rebase_set rebase (comma_crt_set (columns!parent_cid))"
    by (rule subset_trans[OF piece_in_union piece_coverage])
  show ?thesis using covered by (simp only: parent_column shifted)
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_group_piece_parent_covered}];
  Comma_Proof_Profile.report "Construction binding stage=piece-parent coverage checked"
\<close>

lemma comma_semantic_b1_crt_piece_difference_empty:
  assumes piece_admitted: "comma_crt_admitted 0 piece"
    and parent_admitted: "comma_crt_admitted 0 parent"
    and subset: "comma_crt_set piece\<subseteq>comma_crt_set parent"
  shows "comma_crt_set (comma_crt_apply Comma_CRT_And piece
      (comma_crt_negate parent))={}"
proof -
  have negated_admitted: "comma_crt_admitted 0 (comma_crt_negate parent)"
    by (rule comma_crt_negate_admitted[OF parent_admitted])
  show ?thesis using comma_crt_apply_and_set[OF piece_admitted negated_admitted]
      comma_crt_negate_set[OF parent_admitted] subset by auto
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_piece_difference_empty}];
  Comma_Proof_Profile.report "Construction binding stage=piece-difference checked"
\<close>

lemma comma_semantic_b1_crt_find_result_index_nth:
  assumes distinct: "distinct beta" and index: "index<length beta"
  shows "comma_semantic_b1_crt_find_result_index beta (beta!index)=Some index"
  using distinct index
proof (induction beta arbitrary: index)
  case Nil
  then show ?case by simp
next
  case (Cons head tail)
  show ?case
  proof (cases index)
    case 0
    then show ?thesis by simp
  next
    case (Suc index')
    have tail_distinct: "distinct tail" using Cons.prems(1) by simp
    have index_bound: "index'<length tail" using Cons.prems(2) Suc by simp
    have head_not: "head\<noteq>tail!index'"
    proof
      assume equal: "head=tail!index'"
      have "tail!index'\<in>set tail" by (rule nth_mem[OF index_bound])
      with equal Cons.prems(1) show False by simp
    qed
    have tail_result:
      "comma_semantic_b1_crt_find_result_index tail (tail!index')=Some index'"
      by (rule Cons.IH[OF tail_distinct index_bound])
    show ?thesis using Suc head_not tail_result by simp
  qed
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_find_result_index_nth}];
  Comma_Proof_Profile.report "Construction binding stage=result-index checked"
\<close>

lemma comma_semantic_b1_crt_group_piece_local_covered:
  fixes columns :: "comma_crt_column list"
    and pieces :: "comma_semantic_b1_crt_piece_ref list"
    and parent :: comma_semantic_b1_crt_occurrence
  assumes table: "list_all (comma_crt_admitted 0) columns"
    and parent_binding:
      "comma_semantic_b1_crt_occurrence_binding_check parent"
    and beta_distinct:
      "distinct (comma_semantic_b1_crt_occurrence_beta parent)"
    and rebase:
      "comma_semantic_b1_crt_occurrence_rebase parent=rebase"
    and row: "row<length (comma_semantic_b1_crt_occurrence_beta parent)"
    and parent_column:
      "comma_semantic_b1_crt_occurrence_columns parent!row=columns!parent_cid"
    and bound:
      "comma_semantic_b1_crt_group_construction_bound columns rebase row
        parent_cid pieces"
    and piece: "piece\<in>set pieces"
  shows "comma_semantic_b1_crt_local_piece_covered parent
      (columns!comma_semantic_b1_crt_piece_cid piece)
      (comma_semantic_b1_crt_occurrence_beta parent!row)"
proof -
  have parent_cid_bound: "parent_cid<length columns"
    and piece_bound: "comma_semantic_b1_crt_piece_cid piece<length columns"
    using bound piece
    by (auto simp: comma_semantic_b1_crt_group_construction_bound_def
      list_all_iff split: if_splits)
  have parent_width:
      "length (comma_semantic_b1_crt_occurrence_columns parent)=
        length (comma_semantic_b1_crt_occurrence_beta parent)"
    using parent_binding
    by (auto simp: comma_semantic_b1_crt_occurrence_binding_check_def)
  have selected_index:
      "comma_semantic_b1_crt_find_result_index
        (comma_semantic_b1_crt_occurrence_beta parent)
        (comma_semantic_b1_crt_occurrence_beta parent!row)=Some row"
    by (rule comma_semantic_b1_crt_find_result_index_nth
      [OF beta_distinct row])
  have selected_parent:
      "comma_semantic_b1_crt_local_parent_column parent
        (comma_semantic_b1_crt_occurrence_beta parent!row)=
       Some (comma_crt_shift rebase
        (comma_semantic_b1_crt_occurrence_columns parent!row))"
    using selected_index parent_width row rebase
    by (simp add: comma_semantic_b1_crt_local_parent_column_def Let_def)
  have piece_admitted:
      "comma_crt_admitted 0 (columns!comma_semantic_b1_crt_piece_cid piece)"
    using table piece_bound by (auto simp: list_all_iff nth_mem)
  have parent_admitted: "comma_crt_admitted 0 (columns!parent_cid)"
    using table parent_cid_bound by (auto simp: list_all_iff nth_mem)
  have shifted_admitted:
      "comma_crt_admitted 0
        (comma_crt_shift rebase (comma_semantic_b1_crt_occurrence_columns parent!row))"
    using parent_admitted parent_column
    by (simp add: comma_crt_shift_admitted)
  have rebase_bound: "rebase<924"
    using parent_binding rebase
    by (simp add: comma_semantic_b1_crt_occurrence_binding_check_def)
  have piece_subset:
      "comma_crt_set (columns!comma_semantic_b1_crt_piece_cid piece)\<subseteq>
        comma_crt_set (comma_crt_shift rebase
          (comma_semantic_b1_crt_occurrence_columns parent!row))"
    by (rule comma_semantic_b1_crt_group_piece_parent_covered
      [OF table rebase_bound parent_admitted parent_column bound piece])
  have negated_admitted:
      "comma_crt_admitted 0 (comma_crt_negate
        (comma_crt_shift rebase
          (comma_semantic_b1_crt_occurrence_columns parent!row)))"
    by (rule comma_crt_negate_admitted[OF shifted_admitted])
  have difference_admitted:
      "comma_crt_admitted 0 (comma_crt_apply Comma_CRT_And
        (columns!comma_semantic_b1_crt_piece_cid piece)
        (comma_crt_negate (comma_crt_shift rebase
          (comma_semantic_b1_crt_occurrence_columns parent!row))))"
    by (rule comma_crt_apply_admitted[OF piece_admitted negated_admitted])
  have difference_set:
      "comma_crt_set (comma_crt_apply Comma_CRT_And
        (columns!comma_semantic_b1_crt_piece_cid piece)
        (comma_crt_negate (comma_crt_shift rebase
          (comma_semantic_b1_crt_occurrence_columns parent!row))))={}"
    by (rule comma_semantic_b1_crt_piece_difference_empty
      [OF piece_admitted shifted_admitted piece_subset])
  have difference_unsupported:
      "\<not> comma_crt_supported (comma_crt_apply Comma_CRT_And
        (columns!comma_semantic_b1_crt_piece_cid piece)
        (comma_crt_negate (comma_crt_shift rebase
          (comma_semantic_b1_crt_occurrence_columns parent!row))))"
  proof
    assume supported: "comma_crt_supported (comma_crt_apply Comma_CRT_And
      (columns!comma_semantic_b1_crt_piece_cid piece)
      (comma_crt_negate (comma_crt_shift rebase
        (comma_semantic_b1_crt_occurrence_columns parent!row))))"
    have difference_iff:
        "comma_crt_set (comma_crt_apply Comma_CRT_And
        (columns!comma_semantic_b1_crt_piece_cid piece)
        (comma_crt_negate (comma_crt_shift rebase
          (comma_semantic_b1_crt_occurrence_columns parent!row))))\<noteq>{} \<longleftrightarrow>
         comma_crt_supported (comma_crt_apply Comma_CRT_And
           (columns!comma_semantic_b1_crt_piece_cid piece)
           (comma_crt_negate (comma_crt_shift rebase
             (comma_semantic_b1_crt_occurrence_columns parent!row))))"
      by (rule comma_crt_supported_nonempty[OF difference_admitted])
    have nonempty:
        "comma_crt_set (comma_crt_apply Comma_CRT_And
          (columns!comma_semantic_b1_crt_piece_cid piece)
          (comma_crt_negate (comma_crt_shift rebase
            (comma_semantic_b1_crt_occurrence_columns parent!row))))\<noteq>{}"
      using difference_iff supported by simp
    show False using difference_set nonempty by simp
  qed
  show ?thesis
    using selected_parent piece_admitted shifted_admitted difference_unsupported
    by (simp add: comma_semantic_b1_crt_local_piece_covered_def)
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_group_piece_local_covered}];
  Comma_Proof_Profile.report "Construction binding stage=piece-coverage checked"
\<close>

lemma comma_semantic_b1_crt_local_parent_column_admitted:
  assumes parent: "comma_semantic_b1_crt_occurrence_wellformed parent"
    and selected:
      "comma_semantic_b1_crt_local_parent_column parent result=Some parent_column"
  shows "comma_crt_admitted 0 parent_column"
proof -
  obtain index where index:
      "index<length (comma_semantic_b1_crt_occurrence_columns parent)"
    and parent_column_eq:
      "parent_column=comma_crt_shift
        (comma_semantic_b1_crt_occurrence_rebase parent)
        (comma_semantic_b1_crt_occurrence_columns parent!index)"
    by (rule comma_semantic_b1_crt_local_parent_column_some[OF selected])
  have columns_admitted:
      "list_all (comma_crt_admitted 0)
        (comma_semantic_b1_crt_occurrence_columns parent)"
    using parent by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def)
  have selected_column_member:
      "comma_semantic_b1_crt_occurrence_columns parent!index\<in>
        set (comma_semantic_b1_crt_occurrence_columns parent)"
    by (rule nth_mem[OF index])
  have selected_column_admitted:
      "comma_crt_admitted 0
        (comma_semantic_b1_crt_occurrence_columns parent!index)"
    using columns_admitted selected_column_member by (simp add: list_all_iff)
  have shifted_admitted:
      "comma_crt_admitted 0 (comma_crt_shift
        (comma_semantic_b1_crt_occurrence_rebase parent)
        (comma_semantic_b1_crt_occurrence_columns parent!index))"
    by (rule comma_crt_shift_admitted[OF selected_column_admitted])
  show ?thesis using parent_column_eq shifted_admitted by simp
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_local_parent_column_admitted}];
  Comma_Proof_Profile.report "Constructed refinement stage=parent-column admission checked"
\<close>

lemma comma_semantic_b1_crt_local_piece_covered_set_cong:
  assumes parent: "comma_semantic_b1_crt_occurrence_wellformed parent"
    and left: "comma_crt_admitted 0 left"
    and right: "comma_crt_admitted 0 right"
    and same: "comma_crt_set left=comma_crt_set right"
  shows "comma_semantic_b1_crt_local_piece_covered parent left result =
    comma_semantic_b1_crt_local_piece_covered parent right result"
proof (cases "comma_semantic_b1_crt_local_parent_column parent result")
  case None
  have support_eq: "comma_crt_supported left=comma_crt_supported right"
    using comma_crt_supported_nonempty[OF left]
      comma_crt_supported_nonempty[OF right] same by blast
  show ?thesis by (simp add: comma_semantic_b1_crt_local_piece_covered_def
    None left right support_eq)
next
  case (Some parent_column)
  have parent_selected:
      "comma_semantic_b1_crt_local_parent_column parent result=
        Some parent_column"
    by (rule Some)
  have parent_column_admitted:
      "comma_crt_admitted 0 parent_column"
    by (rule comma_semantic_b1_crt_local_parent_column_admitted
      [OF parent parent_selected])
  have negated_admitted:
      "comma_crt_admitted 0 (comma_crt_negate parent_column)"
    by (rule comma_crt_negate_admitted[OF parent_column_admitted])
  have left_difference_admitted:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And left
          (comma_crt_negate parent_column))"
    by (rule comma_crt_apply_admitted[OF left negated_admitted])
  have right_difference_admitted:
      "comma_crt_admitted 0
        (comma_crt_apply Comma_CRT_And right
          (comma_crt_negate parent_column))"
    by (rule comma_crt_apply_admitted[OF right negated_admitted])
  have difference_eq:
      "comma_crt_set (comma_crt_apply Comma_CRT_And left
          (comma_crt_negate parent_column)) =
       comma_crt_set (comma_crt_apply Comma_CRT_And right
          (comma_crt_negate parent_column))"
    using same comma_crt_apply_and_set[OF left negated_admitted]
      comma_crt_apply_and_set[OF right negated_admitted] by simp
  have support_eq:
      "comma_crt_supported
          (comma_crt_apply Comma_CRT_And left (comma_crt_negate parent_column)) =
       comma_crt_supported
          (comma_crt_apply Comma_CRT_And right (comma_crt_negate parent_column))"
    using comma_crt_supported_nonempty[OF left_difference_admitted]
      comma_crt_supported_nonempty[OF right_difference_admitted] difference_eq
    by blast
  show ?thesis by (simp add: comma_semantic_b1_crt_local_piece_covered_def
    Some left right parent_column_admitted support_eq)
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_local_piece_covered_set_cong}];
  Comma_Proof_Profile.report "Constructed refinement stage=piece-set-congruence checked"
\<close>

lemma comma_semantic_b1_crt_local_piece_covered_if_unsupported:
  assumes parent: "comma_semantic_b1_crt_occurrence_wellformed parent"
    and admitted: "comma_crt_admitted 0 candidate"
    and unsupported: "\<not> comma_crt_supported candidate"
  shows "comma_semantic_b1_crt_local_piece_covered parent candidate result"
proof -
  have candidate_empty: "comma_crt_set candidate={}"
    using comma_crt_supported_nonempty[OF admitted] unsupported by blast
  show ?thesis
  proof (cases "comma_semantic_b1_crt_local_parent_column parent result")
    case None
    then show ?thesis by (simp add:
      comma_semantic_b1_crt_local_piece_covered_def None admitted unsupported)
  next
    case (Some parent_column)
    have parent_selected:
        "comma_semantic_b1_crt_local_parent_column parent result=
          Some parent_column"
      by (rule Some)
    have parent_column_admitted:
        "comma_crt_admitted 0 parent_column"
      by (rule comma_semantic_b1_crt_local_parent_column_admitted
        [OF parent parent_selected])
    have negated_admitted:
        "comma_crt_admitted 0 (comma_crt_negate parent_column)"
      by (rule comma_crt_negate_admitted[OF parent_column_admitted])
    have difference_admitted:
        "comma_crt_admitted 0 (comma_crt_apply Comma_CRT_And
          candidate (comma_crt_negate parent_column))"
      by (rule comma_crt_apply_admitted[OF admitted negated_admitted])
    have candidate_subset: "comma_crt_set candidate\<subseteq>comma_crt_set parent_column"
      using candidate_empty by simp
    have difference_empty:
        "comma_crt_set (comma_crt_apply Comma_CRT_And
          candidate (comma_crt_negate parent_column))={}"
      by (rule comma_semantic_b1_crt_piece_difference_empty
        [OF admitted parent_column_admitted candidate_subset])
    have difference_unsupported:
        "\<not> comma_crt_supported (comma_crt_apply Comma_CRT_And
          candidate (comma_crt_negate parent_column))"
      using comma_crt_supported_nonempty[OF difference_admitted] difference_empty
      by blast
    show ?thesis by (simp add: comma_semantic_b1_crt_local_piece_covered_def
      Some admitted parent_column_admitted difference_unsupported)
  qed
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_local_piece_covered_if_unsupported}];
  Comma_Proof_Profile.report "Constructed refinement stage=empty-piece coverage checked"
\<close>


text \<open>
The following source-order induction is the joint geometry/exactness carrier
used by the concrete publisher.  A step may use only facts for earlier source
indices, so child exactness and the first construction certificate are
established together; aliases reuse the already established template fact.
\<close>

lemma comma_semantic_b1_crt_source_order_induction:
  fixes certified :: "nat \<Rightarrow> bool"
  assumes step:
    "\<And>i. i<length sources \<Longrightarrow>
      (\<And>j. j<i \<Longrightarrow> certified j) \<Longrightarrow> certified i"
  shows "\<forall>i<length sources. certified i"
proof (rule allI)
  fix i
  show "i<length sources \<longrightarrow> certified i"
  proof (induction i rule: less_induct)
    case (less i)
    show ?case
    proof
      assume i_bound: "i<length sources"
      show "certified i"
      proof (rule step[OF i_bound])
        fix j
        assume j_bound: "j<i"
        have j_in_range: "j<length sources"
          by (rule less_trans[OF j_bound i_bound])
        show "certified j"
          using less.IH[OF j_bound] j_in_range by blast
      qed
    qed
  qed
qed
ML \<open>
  Thm.consolidate [@{thm comma_semantic_b1_crt_source_order_induction}];
  Comma_Proof_Profile.report "Construction binding stage=source-order checked"
\<close>



lemmas comma_semantic_b1_crt_construction_binding_oracle_audit_bundle =
  comma_semantic_b1_crt_overlapping_parent_columns_rejected
  comma_semantic_b1_crt_rebase_inverse_set
  comma_semantic_b1_crt_group_piece_parent_covered
  comma_semantic_b1_crt_piece_difference_empty
  comma_semantic_b1_crt_group_construction_bound_sound
  comma_semantic_b1_crt_find_result_index_nth
  comma_semantic_b1_crt_group_piece_local_covered
  comma_semantic_b1_crt_column_ids_resolve_map
  comma_semantic_b1_crt_column_ids_resolve_from_map
  comma_semantic_b1_crt_column_ids_resolve_columns_for_from_map
  comma_semantic_b1_crt_column_ids_resolve_columns_for
  comma_semantic_b1_crt_column_ids_resolve_list_all2
  comma_semantic_b1_crt_column_ids_resolve_preserves_list_all
  comma_semantic_b1_crt_tagged_map_distinct
  comma_semantic_b1_crt_source_order_induction
  comma_semantic_b1_crt_local_parent_column_admitted
  comma_semantic_b1_crt_local_piece_covered_set_cong
  comma_semantic_b1_crt_local_piece_covered_if_unsupported

end
