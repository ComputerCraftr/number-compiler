theory Comma_Semantic_B1_CRT_Partition_Composition
  imports Comma_Semantic_B1_CRT_Structural_Partition
    Comma_Semantic_B1_CRT_Construction_Binding
begin
ML \<open>Comma_Proof_Profile.report "Partition composition: entered"\<close>
text \<open>Small list-composition lemmas for structural source-slot partitions.\<close>
lemma comma_semantic_b1_crt_lift_column_set_matches:
  fixes period slot net :: nat and child_column :: comma_crt_column
  assumes source_period: "period\<in>comma_semantic_b1_crt_source_periods"
    and slot_bound: "slot<period"
    and child_admitted: "comma_crt_admitted 0 child_column"
  shows "comma_crt_set
      (comma_crt_apply_shifted Comma_CRT_And net
        (comma_crt_source_scope_column (period,slot)) child_column) =
    comma_semantic_b1_crt_slot_cylinder period slot \<inter>
      {phase. phase<924 \<and>
        (phase+net) mod 924\<in>comma_crt_set child_column}"
proof -
  have eval:
      "comma_crt_eval phase
          (comma_crt_apply_shifted Comma_CRT_And net
            (comma_crt_source_scope_column (period,slot)) child_column) =
        (phase mod period=slot \<and>
          comma_crt_eval (phase+net) child_column)"
    if "phase<924" for phase
    by (rule comma_semantic_b1_crt_lift_column_eval
      [OF source_period slot_bound child_admitted that])
  have periodic:
      "comma_crt_eval ((phase+net) mod 924) child_column =
        comma_crt_eval (phase+net) child_column" for phase
    by (rule comma_crt_eval_periodic[OF child_admitted])
  show ?thesis
  proof (rule set_eqI)
    fix phase
    show "phase\<in>comma_crt_set
          (comma_crt_apply_shifted Comma_CRT_And net
            (comma_crt_source_scope_column (period,slot)) child_column) \<longleftrightarrow>
        phase\<in>comma_semantic_b1_crt_slot_cylinder period slot \<inter>
          {phase. phase<924 \<and>
            (phase+net) mod 924\<in>comma_crt_set child_column}"
    proof (cases "phase<924")
      case True
      show ?thesis
        using eval[OF True] periodic
        by (auto simp: comma_crt_set_def
          comma_semantic_b1_crt_slot_cylinder_def)
    next
      case False
      then show ?thesis
        by (auto simp: comma_crt_set_def
          comma_semantic_b1_crt_slot_cylinder_def)
    qed
  qed
qed
lemma comma_semantic_b1_crt_lift_column_row_sets_match:
  fixes period slot net :: nat and child_columns :: "comma_crt_column list"
  assumes source_period: "period\<in>comma_semantic_b1_crt_source_periods"
    and slot_bound: "slot<period"
    and children_admitted: "list_all (comma_crt_admitted 0) child_columns"
  shows "map (\<lambda>child_column. comma_crt_set
      (comma_crt_apply_shifted Comma_CRT_And net
        (comma_crt_source_scope_column (period,slot)) child_column)) child_columns =
    comma_semantic_b1_crt_lift_cells period slot net
      (map comma_crt_set child_columns)"
  using children_admitted
proof (induction child_columns)
  case Nil
  then show ?case by (simp add: comma_semantic_b1_crt_lift_cells_def)
next
  case (Cons child_column child_columns)
  have child_admitted: "comma_crt_admitted 0 child_column"
    and tail_admitted: "list_all (comma_crt_admitted 0) child_columns"
    using Cons.prems by simp_all
  have head:
      "comma_crt_set
          (comma_crt_apply_shifted Comma_CRT_And net
            (comma_crt_source_scope_column (period,slot)) child_column) =
        comma_semantic_b1_crt_slot_cylinder period slot \<inter>
          {phase. phase<924 \<and>
            (phase+net) mod 924\<in>comma_crt_set child_column}"
    by (rule comma_semantic_b1_crt_lift_column_set_matches
      [OF source_period slot_bound child_admitted])
  have tail:
      "map (\<lambda>child_column. comma_crt_set
          (comma_crt_apply_shifted Comma_CRT_And net
            (comma_crt_source_scope_column (period,slot)) child_column)) child_columns =
        comma_semantic_b1_crt_lift_cells period slot net
          (map comma_crt_set child_columns)"
    by (rule Cons.IH[OF tail_admitted])
  show ?case using head tail
    by (simp add: comma_semantic_b1_crt_lift_cells_def)
qed
lemma comma_semantic_b1_crt_slot_cylinders_cover_clock:
  assumes period: "0<period"
  shows "(\<Union>slot\<in>set [0..<period].
      comma_semantic_b1_crt_slot_cylinder period slot) = {..<924}"
proof (rule set_eqI)
  fix phase :: nat
  show "phase \<in> (\<Union>slot\<in>set [0..<period].
      comma_semantic_b1_crt_slot_cylinder period slot) \<longleftrightarrow>
      phase \<in> {..<924}"
  proof
    assume member:
      "phase \<in> (\<Union>slot\<in>set [0..<period].
        comma_semantic_b1_crt_slot_cylinder period slot)"
    then show "phase \<in> {..<924}"
      by (auto simp: comma_semantic_b1_crt_slot_cylinder_def)
  next
    assume phase_bound: "phase \<in> {..<924}"
    have residue: "phase mod period<period"
      using mod_less_divisor[OF period, of phase] .
    have slot_member: "phase mod period \<in> set [0..<period]"
      using residue by simp
    have cylinder:
      "phase \<in> comma_semantic_b1_crt_slot_cylinder period
        (phase mod period)"
      using phase_bound by (simp add: comma_semantic_b1_crt_slot_cylinder_def)
    show "phase \<in> (\<Union>slot\<in>set [0..<period].
        comma_semantic_b1_crt_slot_cylinder period slot)"
      using slot_member cylinder by blast
  qed
qed
lemma comma_semantic_b1_crt_nonempty_filter_distinct:
  assumes pairwise:
      "\<forall>i<length cells. \<forall>j<length cells.
        i\<noteq>j \<longrightarrow> cells!i\<inter>cells!j={}"
  shows "distinct (filter (\<lambda>cell. cell\<noteq>{}) cells)"
  using pairwise
proof (induction cells)
  case Nil
  then show ?case by simp
next
  case (Cons cell cells)
  have tail_pairwise:
      "\<forall>i<length cells. \<forall>j<length cells.
        i\<noteq>j \<longrightarrow> cells!i\<inter>cells!j={}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i_bound: "i<length cells" and j_bound: "j<length cells"
      and different: "i\<noteq>j"
    have i_bound': "Suc i<length (cell#cells)" using i_bound by simp
    have j_bound': "Suc j<length (cell#cells)" using j_bound by simp
    have different': "Suc i\<noteq>Suc j" using different by simp
    have source_disjoint:
        "(cell#cells)!(Suc i)\<inter>(cell#cells)!(Suc j)={}"
      by (rule Cons.prems[rule_format, OF i_bound' j_bound' different'])
    show "cells!i\<inter>cells!j={}" using source_disjoint by simp
  qed
  have tail_distinct: "distinct (filter (\<lambda>item. item\<noteq>{}) cells)"
    by (rule Cons.IH[OF tail_pairwise])
  show ?case
  proof (cases "cell={}")
    case True
    then show ?thesis using tail_distinct by simp
  next
    case False
    have cell_notin_tail: "cell\<notin>set (filter (\<lambda>item. item\<noteq>{}) cells)"
    proof
      assume member: "cell\<in>set (filter (\<lambda>item. item\<noteq>{}) cells)"
      then have member_tail: "cell\<in>set cells" by simp
      obtain j where j_bound: "j<length cells" and cell_at: "cells!j=cell"
        using member_tail by (auto simp: in_set_conv_nth)
      have zero_bound: "0<length (cell#cells)" by simp
      have other_bound: "Suc j<length (cell#cells)" using j_bound by simp
      have indices_differ: "0\<noteq>Suc j" by simp
      have same_disjoint:
          "(cell#cells)!0\<inter>(cell#cells)!(Suc j)={}"
        by (rule Cons.prems[rule_format, OF zero_bound other_bound indices_differ])
      have "cell={}" using same_disjoint cell_at by simp
      with False show False by contradiction
    qed
    show ?thesis using tail_distinct cell_notin_tail by auto
  qed
qed
lemma comma_semantic_b1_crt_filter_empty_cells_partition:
  assumes partition:
      "comma_semantic_b1_crt_cells_partition universe cells"
  shows "comma_semantic_b1_crt_cells_partition universe
    (filter (\<lambda>cell. cell\<noteq>{}) cells)"
proof -
  have bounded:
      "\<forall>i<length cells. cells!i\<subseteq>universe"
    and covered:
      "\<forall>phase\<in>universe. \<exists>i<length cells. phase\<in>cells!i"
    and pairwise:
      "\<forall>i<length cells. \<forall>j<length cells.
        i\<noteq>j \<longrightarrow> cells!i\<inter>cells!j={}"
    using partition by (auto simp: comma_semantic_b1_crt_cells_partition_def)
  let ?filtered = "filter (\<lambda>cell. cell\<noteq>{}) cells"
  have filtered_distinct:
      "distinct ?filtered"
    by (rule comma_semantic_b1_crt_nonempty_filter_distinct[OF pairwise])
  have filtered_bounded:
      "\<forall>i<length ?filtered. ?filtered!i\<subseteq>universe"
  proof (intro allI impI)
    fix i
    assume i_bound: "i<length ?filtered"
    have member: "?filtered!i\<in>set ?filtered"
      by (rule nth_mem[OF i_bound])
    then have original_member: "?filtered!i\<in>set cells" by auto
    obtain j where j_bound: "j<length cells" and original_eq: "cells!j=?filtered!i"
      using original_member by (auto simp: in_set_conv_nth)
    show "?filtered!i\<subseteq>universe"
      using bounded j_bound original_eq by blast
  qed
  have filtered_covered:
      "\<forall>phase\<in>universe. \<exists>i<length ?filtered. phase\<in>?filtered!i"
  proof (intro ballI)
    fix phase
    assume phase: "phase\<in>universe"
    obtain j where j_bound: "j<length cells" and member: "phase\<in>cells!j"
      using covered phase by blast
    have nonempty: "cells!j\<noteq>{}" using member by auto
    have filtered_member: "cells!j\<in>set ?filtered"
      using nth_mem[OF j_bound] nonempty by simp
    have filtered_index:
        "\<exists>i<length ?filtered. ?filtered!i=cells!j"
      using filtered_member by (metis in_set_conv_nth)
    obtain i where i_bound: "i<length ?filtered" and filtered_eq: "?filtered!i=cells!j"
      using filtered_index by blast
    show "\<exists>i<length ?filtered. phase\<in>?filtered!i"
      using i_bound filtered_eq member by auto
  qed
  have filtered_pairwise:
      "\<forall>i<length ?filtered. \<forall>j<length ?filtered.
        i\<noteq>j \<longrightarrow> ?filtered!i\<inter>?filtered!j={}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i_bound: "i<length ?filtered" and j_bound: "j<length ?filtered"
      and different: "i\<noteq>j"
    have index_equivalence: "?filtered!i=?filtered!j \<longleftrightarrow> i=j"
      by (rule nth_eq_iff_index_eq[OF filtered_distinct i_bound j_bound])
    have values_differ: "?filtered!i\<noteq>?filtered!j"
      using index_equivalence different by blast
    have left_member: "?filtered!i\<in>set cells"
      using nth_mem[OF i_bound] by auto
    have right_member: "?filtered!j\<in>set cells"
      using nth_mem[OF j_bound] by auto
    obtain left_index where left_index_bound: "left_index<length cells"
      and left_eq: "cells!left_index=?filtered!i"
      using left_member by (auto simp: in_set_conv_nth)
    obtain right_index where right_index_bound: "right_index<length cells"
      and right_eq: "cells!right_index=?filtered!j"
      using right_member by (auto simp: in_set_conv_nth)
    have indices_differ: "left_index\<noteq>right_index"
      using values_differ left_eq right_eq by auto
    have source_disjoint: "cells!left_index\<inter>cells!right_index={}"
      by (rule pairwise[rule_format, OF left_index_bound right_index_bound indices_differ])
    show "?filtered!i\<inter>?filtered!j={}"
      using source_disjoint left_eq right_eq by simp
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using filtered_bounded filtered_covered filtered_pairwise by blast
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_lift_column_set_matches}, @{thm comma_semantic_b1_crt_lift_column_row_sets_match}, @{thm comma_semantic_b1_crt_slot_cylinders_cover_clock}, @{thm comma_semantic_b1_crt_nonempty_filter_distinct}, @{thm comma_semantic_b1_crt_filter_empty_cells_partition}]; Comma_Proof_Profile.report "Partition composition: basic list algebra checked"\<close>
definition comma_semantic_b1_crt_constructed_slot_origins ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_finite_position \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) list" where
  "comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids
      sources occurrence_at refs source slot =
    (let period=comma_decisive_sector_period
          (comma_source_continuation_base source)
     in map (\<lambda>column. (slot,column))
       (if slot<period \<and> slot<length refs then
       (case (refs!slot, comma_semantic_b1_source_slot_action source slot) of
          (Comma_B1_Lift_Terminal_Ref ref_slot _, action) \<Rightarrow>
            (case comma_semantic_b1_terminal_action_result action of
               Some _ \<Rightarrow> if ref_slot=slot then [0] else []
             | None \<Rightarrow> [])
        | (Comma_B1_Lift_Goto_Ref ref_slot child_index lift_cid,
            Comma_Continuation_Goto _ _) \<Rightarrow>
            (if ref_slot=slot \<and> child_index<length sources \<and>
                lift_cid<length lift_column_ids
             then (case occurrence_at child_index of
               Some child_occurrence \<Rightarrow>
                 (let child_beta=comma_semantic_b1_crt_occurrence_beta
                       child_occurrence
                  in if lift_cid<length lift_column_ids \<and>
                      length (lift_column_ids!lift_cid)=length child_beta then
                       map Suc (filter (\<lambda>child_column.
                           comma_crt_supported
                             (columns!(lift_column_ids!lift_cid!child_column)))
                           [0..<length child_beta])
                     else [])
             | None \<Rightarrow> [])
             else [])
        | _ \<Rightarrow> [])
     else []))"
lemma comma_semantic_b1_crt_tagged_map:
  "list_all (\<lambda>entry. fst entry=slot)
    (map (\<lambda>column. (slot,column)) columns)"
  by (induction columns) simp_all
lemma comma_semantic_b1_crt_constructed_slot_origins_tagged:
  shows "list_all (\<lambda>entry. fst entry=slot)
    (comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids
      sources occurrence_at refs source slot)"
  unfolding comma_semantic_b1_crt_constructed_slot_origins_def Let_def
  by (rule comma_semantic_b1_crt_tagged_map)
definition comma_semantic_b1_crt_constructed_source_origins ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_finite_position \<Rightarrow> (nat \<times> nat) list" where
  "comma_semantic_b1_crt_constructed_source_origins columns lift_column_ids
      sources occurrence_at refs source = concat (map
        (comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids
          sources occurrence_at refs source)
        [0..<comma_decisive_sector_period
          (comma_source_continuation_base source)])"
definition comma_semantic_b1_crt_constructed_piece_origin ::
    "comma_semantic_b1_crt_piece_ref \<Rightarrow> nat \<times> nat" where
  "comma_semantic_b1_crt_constructed_piece_origin piece =
    (case piece of
       Comma_B1_Piece_Terminal period slot cid parent \<Rightarrow>
         (slot,0)
     | Comma_B1_Piece_Goto period slot child child_column lift cid parent \<Rightarrow>
         (slot,Suc child_column))"
text \<open>The source-cell expansion is proof-side only, formed once per source occurrence to connect compact origins to the structural partition argument; it is not part of the published certificate.\<close>
definition comma_semantic_b1_crt_constructed_slot_cells ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_finite_position \<Rightarrow> nat \<Rightarrow>
      (comma_crt_column \<times> comma_semantic_b1_result) list" where
  "comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
      occurrence_at refs source slot =
    (let period=comma_decisive_sector_period
          (comma_source_continuation_base source)
     in if slot<period \<and> slot<length refs then
       (case (refs!slot, comma_semantic_b1_source_slot_action source slot) of
          (Comma_B1_Lift_Terminal_Ref ref_slot _, action) \<Rightarrow>
            (case comma_semantic_b1_terminal_action_result action of
               Some result \<Rightarrow>
                 if ref_slot=slot then
                   [(comma_crt_source_scope_column (period,slot),result)]
                 else []
             | None \<Rightarrow> [])
        | (Comma_B1_Lift_Goto_Ref ref_slot child_index lift_cid,
            Comma_Continuation_Goto _ _) \<Rightarrow>
            (if ref_slot=slot \<and> lift_cid<length lift_column_ids
             then (case occurrence_at child_index of
               Some child_occurrence \<Rightarrow>
                 (let child_beta=comma_semantic_b1_crt_occurrence_beta
                       child_occurrence
                  in if length (lift_column_ids!lift_cid)=length child_beta then
                       zip (map (\<lambda>cid. columns!cid)
                            (lift_column_ids!lift_cid)) child_beta
                     else [])
             | None \<Rightarrow> [])
             else [])
        | _ \<Rightarrow> [])
     else [])"
definition comma_semantic_b1_crt_constructed_source_cells ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_finite_position \<Rightarrow>
      (comma_crt_column \<times> comma_semantic_b1_result) list" where
  "comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids
      occurrence_at refs source = concat (map
        (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
          occurrence_at refs source)
        [0..<comma_decisive_sector_period
          (comma_source_continuation_base source)])"
definition comma_semantic_b1_crt_constructed_live_source_cells ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_finite_position \<Rightarrow>
      (comma_crt_column \<times> comma_semantic_b1_result) list" where
  "comma_semantic_b1_crt_constructed_live_source_cells columns lift_column_ids
      occurrence_at refs source = filter
        (\<lambda>entry. comma_crt_supported (fst entry))
        (comma_semantic_b1_crt_constructed_source_cells columns lift_column_ids
          occurrence_at refs source)"
text \<open>Origin-tagged live cells connect compact origins to the generic partition theorems without adding phase or set enumeration to the published certificate, which stores only compact origins and destination bindings.\<close>
definition comma_semantic_b1_crt_constructed_slot_live_entries ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_finite_position \<Rightarrow> nat \<Rightarrow>
      ((nat \<times> nat) \<times>
        (comma_crt_column \<times> comma_semantic_b1_result)) list" where
  "comma_semantic_b1_crt_constructed_slot_live_entries columns lift_column_ids
      occurrence_at refs source slot =
    (let period=comma_decisive_sector_period
          (comma_source_continuation_base source)
     in if slot<period \<and> slot<length refs then
       (case (refs!slot, comma_semantic_b1_source_slot_action source slot) of
          (Comma_B1_Lift_Terminal_Ref ref_slot _, action) \<Rightarrow>
            (case comma_semantic_b1_terminal_action_result action of
               Some result \<Rightarrow>
                 (let column=comma_crt_source_scope_column (period,slot)
                  in if ref_slot=slot \<and> comma_crt_supported column then
                       [((slot,0),(column,result))]
                     else [])
             | None \<Rightarrow> [])
        | (Comma_B1_Lift_Goto_Ref ref_slot child_index lift_cid,
            Comma_Continuation_Goto _ _) \<Rightarrow>
            (if ref_slot=slot \<and> lift_cid<length lift_column_ids
             then (case occurrence_at child_index of
               Some child_occurrence \<Rightarrow>
                 (let child_beta=comma_semantic_b1_crt_occurrence_beta
                       child_occurrence
                  in if length (lift_column_ids!lift_cid)=length child_beta then
                       map (\<lambda>child_column.
                           ((slot,Suc child_column),
                            (columns!(lift_column_ids!lift_cid!child_column),
                              child_beta!child_column)))
                         (filter (\<lambda>child_column.
                           comma_crt_supported
                             (columns!(lift_column_ids!lift_cid!child_column)))
                           [0..<length child_beta])
                     else [])
             | None \<Rightarrow> [])
             else [])
        | _ \<Rightarrow> [])
     else [])"
definition comma_semantic_b1_crt_constructed_source_live_entries ::
    "comma_crt_column list \<Rightarrow> nat list list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_finite_position \<Rightarrow>
      ((nat \<times> nat) \<times>
        (comma_crt_column \<times> comma_semantic_b1_result)) list" where
  "comma_semantic_b1_crt_constructed_source_live_entries columns lift_column_ids
      occurrence_at refs source = concat (map
        (comma_semantic_b1_crt_constructed_slot_live_entries columns lift_column_ids
          occurrence_at refs source)
        [0..<comma_decisive_sector_period
          (comma_source_continuation_base source)])"
lemma comma_semantic_b1_crt_constructed_slot_live_entry_origins:
  assumes period: "period\<in>comma_semantic_b1_crt_source_periods"
    and slot: "slot<period"
    and period_eq:
      "period=comma_decisive_sector_period
        (comma_source_continuation_base source)"
    and child_index_bound:
      "\<And>child_index lift_cid.
        refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid
        \<Longrightarrow> child_index<length sources"
  shows "map fst (comma_semantic_b1_crt_constructed_slot_live_entries
      columns lift_column_ids occurrence_at refs source slot) =
    comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids
      sources occurrence_at refs source slot"
proof -
  have scope_admitted:
      "comma_semantic_b1_crt_scope_admitted (period,slot)"
    using period slot
    by (auto simp: comma_semantic_b1_crt_scope_admitted_def
      comma_semantic_b1_scope_admitted_def
      comma_semantic_b1_crt_source_periods_def)
  have scope_column_admitted:
      "comma_crt_admitted 0 (comma_crt_source_scope_column (period,slot))"
    by (rule comma_semantic_b1_crt_lift_scope_admitted[OF period slot])
  have phase_bound: "slot<924"
    using period slot by (auto simp: comma_semantic_b1_crt_source_periods_def)
  have scope_active:
      "comma_crt_eval slot (comma_crt_source_scope_column (period,slot))"
    using comma_semantic_b1_crt_lift_scope_eval[OF period slot phase_bound]
      slot by simp
  have scope_supported:
      "comma_crt_supported (comma_crt_source_scope_column (period,slot))"
    by (rule comma_crt_eval_supported[OF scope_column_admitted scope_active])
  show ?thesis
    using period slot period_eq scope_supported child_index_bound
    by (cases "refs!slot";
        cases "comma_semantic_b1_source_slot_action source slot")
      (auto simp: comma_semantic_b1_crt_constructed_slot_live_entries_def
        comma_semantic_b1_crt_constructed_slot_origins_def Let_def
        split: option.splits)
qed
lemma comma_semantic_b1_crt_constructed_source_live_entry_origins:
  assumes period_eq:
      "period=comma_decisive_sector_period
        (comma_source_continuation_base source)"
    and each_slot:
      "\<And>slot. slot<period \<Longrightarrow>
        map fst (comma_semantic_b1_crt_constructed_slot_live_entries
          columns lift_column_ids occurrence_at refs source slot) =
        comma_semantic_b1_crt_constructed_slot_origins columns lift_column_ids
          sources occurrence_at refs source slot"
  shows "map fst (comma_semantic_b1_crt_constructed_source_live_entries
      columns lift_column_ids occurrence_at refs source) =
    comma_semantic_b1_crt_constructed_source_origins columns lift_column_ids
      sources occurrence_at refs source"
proof -
  have slot_map: "map (\<lambda>slot. map fst
        (comma_semantic_b1_crt_constructed_slot_live_entries columns
          lift_column_ids occurrence_at refs source slot)) [0..<period] =
      map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_origins
        columns lift_column_ids sources occurrence_at refs source slot) [0..<period]"
    by (rule map_cong) (auto simp: each_slot)
  have inner_map:
    "map (map fst) (map (\<lambda>slot.
        comma_semantic_b1_crt_constructed_slot_live_entries columns
          lift_column_ids occurrence_at refs source slot) [0..<period]) =
      map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_origins
        columns lift_column_ids sources occurrence_at refs source slot) [0..<period]"
  proof -
    have mapped:
      "map (map fst) (map (\<lambda>slot.
          comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot) [0..<period]) =
        map (\<lambda>slot. map fst
          (comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot)) [0..<period]"
      by (simp only: map_map o_def)
    show ?thesis by (rule trans[OF mapped slot_map])
  qed
  have flattened:
    "map fst (concat (map (\<lambda>slot.
        comma_semantic_b1_crt_constructed_slot_live_entries columns
          lift_column_ids occurrence_at refs source slot) [0..<period])) =
      concat (map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_origins
        columns lift_column_ids sources occurrence_at refs source slot) [0..<period])"
    by (simp only: map_concat; rule arg_cong[OF inner_map])
  show ?thesis using flattened period_eq by (simp add:
    comma_semantic_b1_crt_constructed_source_live_entries_def
    comma_semantic_b1_crt_constructed_source_origins_def)
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_slot_live_entry_origins}, @{thm comma_semantic_b1_crt_constructed_source_live_entry_origins}]; Comma_Proof_Profile.report "Partition composition: origin mappings checked"\<close>
lemma comma_semantic_b1_crt_constructed_goto_live_entry_cells:
  assumes period: "period\<in>comma_semantic_b1_crt_source_periods"
    and slot: "slot<period"
    and ref_bound: "slot<length refs"
    and period_eq:
      "period=comma_decisive_sector_period
        (comma_source_continuation_base source)"
    and reference:
      "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    and action:
      "comma_semantic_b1_source_slot_action source slot=
        Comma_Continuation_Goto child shift"
    and child_at: "occurrence_at child_index=Some child_occurrence"
    and lift_bound: "lift_cid<length lift_column_ids"
    and lift_width:
      "length (lift_column_ids!lift_cid)=
        length (comma_semantic_b1_crt_occurrence_beta child_occurrence)"
  shows "map snd (comma_semantic_b1_crt_constructed_slot_live_entries
      columns lift_column_ids occurrence_at refs source slot) =
    filter (\<lambda>entry. comma_crt_supported (fst entry))
      (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
        occurrence_at refs source slot)"
proof -
  let ?beta="comma_semantic_b1_crt_occurrence_beta child_occurrence"
  let ?row="map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid)"
  let ?value="\<lambda>i. (?row!i,?beta!i)"
  let ?keep="\<lambda>entry. comma_crt_supported (fst entry)"
  let ?select="\<lambda>i. comma_crt_supported (?row!i)"
  have cells:
    "comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
        occurrence_at refs source slot = zip ?row ?beta"
    using period slot ref_bound period_eq reference action child_at lift_bound lift_width
    by (simp add: comma_semantic_b1_crt_constructed_slot_cells_def Let_def)
  have indexed_zip:
    "zip ?row ?beta = map ?value [0..<length ?beta]"
  proof -
    have row_width: "length ?row=length ?beta"
      using lift_width by simp
    have indexed:
      "zip ?row ?beta =
        map (\<lambda>i. (?row!i,?beta!i)) [0..<length ?row]"
      by (rule comma_semantic_b1_crt_zip_indexed[OF row_width])
    show ?thesis using indexed row_width by simp
  qed
  have selected:
    "filter ?keep (map ?value [0..<length ?beta]) =
      map ?value (filter ?select [0..<length ?beta])"
    by (rule comma_semantic_b1_crt_filter_map_equiv) simp
  have row_nth: "\<And>i. i<length ?beta \<Longrightarrow>
      ?row!i=columns!(lift_column_ids!lift_cid!i)"
    using lift_width by (simp add: nth_map)
  have selected_indices:
    "filter ?select [0..<length ?beta] =
      filter (\<lambda>i. comma_crt_supported
        (columns!(lift_column_ids!lift_cid!i))) [0..<length ?beta]"
  proof (rule filter_cong)
    show "[0..<length ?beta]=[0..<length ?beta]" by simp
  next
    fix i
    assume i: "i\<in>set [0..<length ?beta]"
    then have i_bound: "i<length ?beta" by simp
    show "?select i \<longleftrightarrow>
        comma_crt_supported (columns!(lift_column_ids!lift_cid!i))"
      using row_nth[OF i_bound] by simp
  qed
  have indexed_entries:
    "map (\<lambda>i. ((slot,Suc i),?value i))
        (filter ?select [0..<length ?beta]) =
      map (\<lambda>i. ((slot,Suc i),
          (columns!(lift_column_ids!lift_cid!i),?beta!i)))
        (filter (\<lambda>i. comma_crt_supported
          (columns!(lift_column_ids!lift_cid!i))) [0..<length ?beta])"
  proof -
    have selected_lists:
      "filter ?select [0..<length ?beta] =
        filter (\<lambda>i. comma_crt_supported
          (columns!(lift_column_ids!lift_cid!i))) [0..<length ?beta]"
      by (rule selected_indices)
    show ?thesis
      by (rule map_cong[OF selected_lists]) (auto simp: row_nth)
  qed
  have entries:
    "comma_semantic_b1_crt_constructed_slot_live_entries columns lift_column_ids
        occurrence_at refs source slot =
      map (\<lambda>i. ((slot,Suc i),?value i))
        (filter ?select [0..<length ?beta])"
    using period slot ref_bound period_eq reference action child_at lift_bound lift_width
    using indexed_entries
    by (simp add: comma_semantic_b1_crt_constructed_slot_live_entries_def Let_def)
  show ?thesis using cells indexed_zip selected entries by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_goto_live_entry_cells}]; Comma_Proof_Profile.report "Partition composition: Goto live cells checked"\<close>
lemma comma_semantic_b1_crt_constructed_terminal_live_entry_cells:
  assumes period: "period\<in>comma_semantic_b1_crt_source_periods"
    and slot: "slot<period"
    and ref_bound: "slot<length refs"
    and period_eq:
      "period=comma_decisive_sector_period
        (comma_source_continuation_base source)"
    and reference:
      "refs!slot=Comma_B1_Lift_Terminal_Ref slot parent_column"
    and action:
      "comma_semantic_b1_source_slot_action source slot=action"
    and terminal:
      "comma_semantic_b1_terminal_action_result action=Some result"
  shows "map snd (comma_semantic_b1_crt_constructed_slot_live_entries
      columns lift_column_ids occurrence_at refs source slot) =
    filter (\<lambda>entry. comma_crt_supported (fst entry))
      (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
        occurrence_at refs source slot)"
proof -
  have scope_admitted:
      "comma_crt_admitted 0 (comma_crt_source_scope_column (period,slot))"
    by (rule comma_semantic_b1_crt_lift_scope_admitted[OF period slot])
  have phase_bound: "slot<924"
    using period slot by (auto simp: comma_semantic_b1_crt_source_periods_def)
  have scope_active:
      "comma_crt_eval slot (comma_crt_source_scope_column (period,slot))"
    using comma_semantic_b1_crt_lift_scope_eval[OF period slot phase_bound]
      slot by simp
  have scope_supported:
      "comma_crt_supported (comma_crt_source_scope_column (period,slot))"
    by (rule comma_crt_eval_supported[OF scope_admitted scope_active])
  show ?thesis
    using period slot ref_bound period_eq reference action terminal scope_supported
    by (simp add: comma_semantic_b1_crt_constructed_slot_live_entries_def
      comma_semantic_b1_crt_constructed_slot_cells_def Let_def)
qed
lemma comma_semantic_b1_crt_constructed_source_live_entry_cells:
  assumes period_eq:
      "period=comma_decisive_sector_period
        (comma_source_continuation_base source)"
    and each_slot:
      "\<And>slot. slot<period \<Longrightarrow>
        map snd (comma_semantic_b1_crt_constructed_slot_live_entries
          columns lift_column_ids occurrence_at refs source slot) =
        filter (\<lambda>entry. comma_crt_supported (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
            occurrence_at refs source slot)"
  shows "map snd (comma_semantic_b1_crt_constructed_source_live_entries
      columns lift_column_ids occurrence_at refs source) =
    comma_semantic_b1_crt_constructed_live_source_cells columns lift_column_ids
      occurrence_at refs source"
proof -
  have slot_map: "map (\<lambda>slot. map snd
        (comma_semantic_b1_crt_constructed_slot_live_entries columns
          lift_column_ids occurrence_at refs source slot)) [0..<period] =
      map (\<lambda>slot. filter (\<lambda>entry. comma_crt_supported (fst entry))
        (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
          occurrence_at refs source slot)) [0..<period]"
    by (rule map_cong) (auto simp: each_slot)
  have inner_map: "map (map snd) (map (\<lambda>slot.
        comma_semantic_b1_crt_constructed_slot_live_entries columns
          lift_column_ids occurrence_at refs source slot) [0..<period]) =
      map (filter (\<lambda>entry. comma_crt_supported (fst entry)))
        (map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_cells
          columns lift_column_ids occurrence_at refs source slot) [0..<period])"
  proof -
    have mapped:
      "map (map snd) (map (\<lambda>slot.
          comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot) [0..<period]) =
        map (\<lambda>slot. map snd
          (comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot)) [0..<period]"
      by (simp only: map_map o_def)
    have selected: "map (\<lambda>slot. map snd
          (comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot)) [0..<period] =
        map (\<lambda>slot. filter (\<lambda>entry. comma_crt_supported (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
            occurrence_at refs source slot)) [0..<period]"
      by (rule slot_map)
    have rearranged:
      "map (\<lambda>slot. filter (\<lambda>entry. comma_crt_supported (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
            occurrence_at refs source slot)) [0..<period] =
        map (filter (\<lambda>entry. comma_crt_supported (fst entry)))
          (map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_cells
            columns lift_column_ids occurrence_at refs source slot) [0..<period])"
      by (simp only: map_map o_def)
    have mapped_selected:
      "map (map snd) (map (\<lambda>slot.
          comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot) [0..<period]) =
        map (\<lambda>slot. filter (\<lambda>entry. comma_crt_supported (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
            occurrence_at refs source slot)) [0..<period]"
      by (rule trans[OF mapped selected])
    show ?thesis
      by (rule trans[OF mapped_selected rearranged])
  qed
  have flattened: "map snd (concat (map (\<lambda>slot.
        comma_semantic_b1_crt_constructed_slot_live_entries columns
          lift_column_ids occurrence_at refs source slot) [0..<period])) =
      filter (\<lambda>entry. comma_crt_supported (fst entry))
        (concat (map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_cells
          columns lift_column_ids occurrence_at refs source slot) [0..<period]))"
  proof -
    have flatten_map:
      "map snd (concat (map (\<lambda>slot.
          comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot) [0..<period])) =
        concat (map (map snd) (map (\<lambda>slot.
          comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot) [0..<period]))"
      by (simp only: map_concat)
    have flattened_map:
      "concat (map (map snd) (map (\<lambda>slot.
          comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot) [0..<period])) =
        concat (map (filter (\<lambda>entry. comma_crt_supported (fst entry)))
          (map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_cells
            columns lift_column_ids occurrence_at refs source slot) [0..<period]))"
      by (rule arg_cong[OF inner_map])
    have filtered_concat:
      "concat (map (filter (\<lambda>entry. comma_crt_supported (fst entry)))
          (map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_cells
            columns lift_column_ids occurrence_at refs source slot) [0..<period])) =
        filter (\<lambda>entry. comma_crt_supported (fst entry))
          (concat (map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_cells
            columns lift_column_ids occurrence_at refs source slot) [0..<period]))"
      by (simp only: filter_concat[symmetric])
    have flattened_filtered:
      "map snd (concat (map (\<lambda>slot.
          comma_semantic_b1_crt_constructed_slot_live_entries columns
            lift_column_ids occurrence_at refs source slot) [0..<period])) =
        concat (map (filter (\<lambda>entry. comma_crt_supported (fst entry)))
          (map (\<lambda>slot. comma_semantic_b1_crt_constructed_slot_cells
            columns lift_column_ids occurrence_at refs source slot) [0..<period]))"
      by (rule trans[OF flatten_map flattened_map])
    show ?thesis
      by (rule trans[OF flattened_filtered filtered_concat])
  qed
  show ?thesis using flattened period_eq by (simp add:
    comma_semantic_b1_crt_constructed_source_live_entries_def
    comma_semantic_b1_crt_constructed_live_source_cells_def
    comma_semantic_b1_crt_constructed_source_cells_def)
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_terminal_live_entry_cells}, @{thm comma_semantic_b1_crt_constructed_source_live_entry_cells}]; Comma_Proof_Profile.report "Partition composition: terminal and source live cells checked"\<close>
lemma comma_semantic_b1_crt_occurrence_columns_partition:
  assumes wellformed: "comma_semantic_b1_crt_occurrence_wellformed occurrence"
  shows "comma_semantic_b1_crt_cells_partition {..<924} (map comma_crt_set (comma_semantic_b1_crt_occurrence_columns occurrence))"
proof -
  let ?columns="comma_semantic_b1_crt_occurrence_columns occurrence"
  have covered: "comma_semantic_b1_crt_occurrence_covered ?columns"
    and disjoint: "comma_semantic_b1_crt_occurrence_disjoint ?columns"
    using wellformed by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def)
  have bounded: "\<forall>i<length (map comma_crt_set ?columns). (map comma_crt_set ?columns)!i\<subseteq>{..<924}"
    by (auto simp: comma_crt_set_def)
  have covered_cells:
    "\<forall>phase\<in>{..<924}. \<exists>i<length (map comma_crt_set ?columns). phase\<in>(map comma_crt_set ?columns)!i"
  proof (intro ballI)
    fix phase :: nat
    assume phase: "phase\<in>{..<924}"
    obtain entry where entry: "entry\<in>set (zip [0..<length ?columns] ?columns)"
      and phase_entry: "phase\<in>comma_crt_set (snd entry)"
      using covered phase
      by (auto simp: comma_semantic_b1_crt_occurrence_covered_def
        comma_semantic_b1_crt_occurrence_indexed_columns_def)
    obtain i where i: "i<length ?columns" and entry_eq: "entry=(i,?columns!i)"
      using entry by (auto simp: in_set_conv_nth nth_zip)
    show "\<exists>i<length (map comma_crt_set ?columns). phase\<in>(map comma_crt_set ?columns)!i"
      using i phase_entry entry_eq by (auto simp: nth_map)
  qed
  have pairwise:
    "\<forall>i<length (map comma_crt_set ?columns). \<forall>j<length (map comma_crt_set ?columns). i\<noteq>j \<longrightarrow> (map comma_crt_set ?columns)!i \<inter> (map comma_crt_set ?columns)!j={}"
  proof (intro allI impI allI impI impI)
    fix i j
    assume i: "i<length (map comma_crt_set ?columns)"
      and j: "j<length (map comma_crt_set ?columns)"
      and different: "i\<noteq>j"
    have left: "(i,?columns!i)\<in>set (zip [0..<length ?columns] ?columns)"
      using i by (auto simp: in_set_conv_nth nth_zip)
    have right: "(j,?columns!j)\<in>set (zip [0..<length ?columns] ?columns)"
      using j by (auto simp: in_set_conv_nth nth_zip)
    have indexed_disjoint:
      "\<And>left right.
        left\<in>set (zip [0..<length ?columns] ?columns) \<Longrightarrow>
        right\<in>set (zip [0..<length ?columns] ?columns) \<Longrightarrow>
        fst left\<noteq>fst right \<Longrightarrow>
        comma_crt_set (snd left) \<inter> comma_crt_set (snd right)={}"
      using disjoint
      by (auto simp: comma_semantic_b1_crt_occurrence_disjoint_def
        comma_semantic_b1_crt_occurrence_indexed_columns_def)
    have cells_disjoint:
      "comma_crt_set (?columns!i) \<inter> comma_crt_set (?columns!j)={}"
      using indexed_disjoint[OF left right] different by simp
    show "(map comma_crt_set ?columns)!i \<inter> (map comma_crt_set ?columns)!j={}"
      using cells_disjoint i j by simp
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_cells_partition_def
    using bounded covered_cells pairwise by blast
qed
lemma comma_semantic_b1_crt_lifted_columns_partition:
  assumes period: "period\<in>comma_semantic_b1_crt_source_periods"
    and slot: "slot<period"
    and child_admitted:
      "list_all (comma_crt_admitted 0) child_columns"
    and child_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} (map comma_crt_set child_columns)"
  shows "comma_semantic_b1_crt_cells_partition (comma_semantic_b1_crt_slot_cylinder period slot) (map (\<lambda>column. comma_crt_set (comma_crt_apply_shifted Comma_CRT_And net (comma_crt_source_scope_column (period,slot)) column)) child_columns)"
proof -
  have row_sets:
    "map (\<lambda>column. comma_crt_set (comma_crt_apply_shifted Comma_CRT_And net (comma_crt_source_scope_column (period,slot)) column)) child_columns = comma_semantic_b1_crt_lift_cells period slot net (map comma_crt_set child_columns)"
    by (rule comma_semantic_b1_crt_lift_column_row_sets_match
      [OF period slot child_admitted])
  have lifted:
    "comma_semantic_b1_crt_cells_partition (comma_semantic_b1_crt_slot_cylinder period slot) (comma_semantic_b1_crt_lift_cells period slot net (map comma_crt_set child_columns))"
  proof -
    have period_positive: "0<period"
      using period by (auto simp: comma_semantic_b1_crt_source_periods_def)
    show ?thesis
      by (rule comma_semantic_b1_crt_lift_cells_partition
        [OF child_partition period_positive slot])
  qed
  show ?thesis using lifted row_sets by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_occurrence_columns_partition}, @{thm comma_semantic_b1_crt_lifted_columns_partition}]; Comma_Proof_Profile.report "Partition composition: occurrence and lifted partitions checked"\<close>
lemma comma_semantic_b1_crt_constructed_terminal_slot_partition:
  assumes period: "period\<in>comma_semantic_b1_crt_source_periods"
    and slot: "slot<period"
    and ref_bound: "slot<length refs"
    and period_eq:
      "period=comma_decisive_sector_period (comma_source_continuation_base source)"
    and reference:
      "refs!slot=Comma_B1_Lift_Terminal_Ref slot parent_column"
    and terminal:
      "comma_semantic_b1_terminal_action_result action=Some result"
    and action:
      "comma_semantic_b1_source_slot_action source slot=action"
  shows "comma_semantic_b1_crt_cells_partition (comma_semantic_b1_crt_slot_cylinder period slot) (map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids occurrence_at refs source slot))"
proof -
  have cells:
    "comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids occurrence_at refs source slot = [(comma_crt_source_scope_column (period,slot),result)]"
    using period slot ref_bound period_eq reference terminal action
    by (simp add: comma_semantic_b1_crt_constructed_slot_cells_def Let_def)
  have scope_period: "fst (period,slot)\<in>comma_semantic_b1_crt_source_periods"
    using period by simp
  have scope_admitted:
    "comma_semantic_b1_crt_scope_admitted (period,slot)"
    using period slot
    by (auto simp: comma_semantic_b1_crt_scope_admitted_def
      comma_semantic_b1_scope_admitted_def
      comma_semantic_b1_crt_source_periods_def)
  have scope_set:
    "comma_crt_set (comma_crt_source_scope_column (period,slot)) = comma_semantic_b1_crt_slot_cylinder period slot"
    using comma_crt_source_scope_column_set[OF scope_admitted scope_period]
    by (simp add: comma_semantic_b1_crt_slot_cylinder_def
      comma_semantic_b1_crt_scope_holds_def)
  show ?thesis using cells scope_set
    by (simp add: comma_semantic_b1_crt_cells_partition_def)
qed
lemma comma_semantic_b1_crt_constructed_goto_slot_partition:
  assumes period: "period\<in>comma_semantic_b1_crt_source_periods"
    and slot: "slot<period"
    and ref_bound: "slot<length refs"
    and period_eq:
      "period=comma_decisive_sector_period (comma_source_continuation_base source)"
    and reference:
      "refs!slot=Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    and action:
      "comma_semantic_b1_source_slot_action source slot= Comma_Continuation_Goto child shift"
    and child_at: "occurrence_at child_index=Some child_occurrence"
    and child_wellformed:
      "comma_semantic_b1_crt_occurrence_wellformed child_occurrence"
    and lift_bound: "lift_cid<length lift_column_ids"
    and lift_row:
      "map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid) = map (\<lambda>column. comma_crt_apply_shifted Comma_CRT_And net (comma_crt_source_scope_column (period,slot)) column) (comma_semantic_b1_crt_occurrence_columns child_occurrence)"
    and net:
      "net=(shift+comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924"
  shows "comma_semantic_b1_crt_cells_partition (comma_semantic_b1_crt_slot_cylinder period slot) (map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids occurrence_at refs source slot))"
proof -
  let ?child_columns="comma_semantic_b1_crt_occurrence_columns child_occurrence"
  let ?child_beta="comma_semantic_b1_crt_occurrence_beta child_occurrence"
  let ?row="map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid)"
  have child_width: "length ?child_columns=length ?child_beta"
    and child_admitted: "list_all (comma_crt_admitted 0) ?child_columns"
    using child_wellformed
    by (auto simp: comma_semantic_b1_crt_occurrence_wellformed_def)
  have child_partition:
      "comma_semantic_b1_crt_cells_partition {..<924} (map comma_crt_set ?child_columns)"
    by (rule comma_semantic_b1_crt_occurrence_columns_partition[OF child_wellformed])
  have lift_width: "length (lift_column_ids!lift_cid)=length ?child_beta"
  proof -
    have lengths:
      "length (map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid)) = length (map (\<lambda>column. comma_crt_apply_shifted Comma_CRT_And net (comma_crt_source_scope_column (period,slot)) column) ?child_columns)"
      using lift_row by simp
    show ?thesis using lengths child_width by simp
  qed
  have cells:
    "comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids occurrence_at refs source slot = zip (map (\<lambda>cid. columns!cid) (lift_column_ids!lift_cid)) ?child_beta"
    using period slot ref_bound period_eq reference action child_at lift_bound lift_width
    by (simp add: comma_semantic_b1_crt_constructed_slot_cells_def Let_def)
  have row_sets:
    "map (\<lambda>column. comma_crt_set (comma_crt_apply_shifted Comma_CRT_And net (comma_crt_source_scope_column (period,slot)) column)) ?child_columns = comma_semantic_b1_crt_lift_cells period slot net (map comma_crt_set ?child_columns)"
    by (rule comma_semantic_b1_crt_lift_column_row_sets_match
      [OF period slot child_admitted])
  have constructed_sets:
    "map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids occurrence_at refs source slot) = comma_semantic_b1_crt_lift_cells period slot net (map comma_crt_set ?child_columns)"
  proof -
    have first_columns: "map fst (zip ?row ?child_beta)=?row"
      using lift_width by simp
    have entry_sets:
      "map (\<lambda>entry. comma_crt_set (fst entry))
          (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids
            occurrence_at refs source slot) = map comma_crt_set ?row"
      using cells arg_cong[where f="map comma_crt_set", OF first_columns]
      by (simp add: map_map o_def)
    show ?thesis using entry_sets lift_row row_sets by (simp add: o_def)
  qed
  have period_positive: "0<period"
    using period by (auto simp: comma_semantic_b1_crt_source_periods_def)
  have lifted_partition:
    "comma_semantic_b1_crt_cells_partition (comma_semantic_b1_crt_slot_cylinder period slot) (comma_semantic_b1_crt_lift_cells period slot net (map comma_crt_set ?child_columns))"
    by (rule comma_semantic_b1_crt_lift_cells_partition
      [OF child_partition period_positive slot])
  show ?thesis using lifted_partition constructed_sets by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_terminal_slot_partition}, @{thm comma_semantic_b1_crt_constructed_goto_slot_partition}]; Comma_Proof_Profile.report "Partition composition: slot partitions checked"\<close>
lemma comma_semantic_b1_crt_constructed_source_cells_partition:
  assumes period: "period\<in>comma_semantic_b1_crt_source_periods"
    and period_positive: "0<period"
    and each_slot:
      "\<And>slot. slot<period \<Longrightarrow> comma_semantic_b1_crt_cells_partition (comma_semantic_b1_crt_slot_cylinder period slot) (map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids occurrence_at refs source slot))"
  shows "comma_semantic_b1_crt_cells_partition {..<924} (concat (map (\<lambda>slot. map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids occurrence_at refs source slot)) [0..<period]))"
proof -
  let ?slots="[0..<period]"
  let ?universe="\<lambda>slot. comma_semantic_b1_crt_slot_cylinder period slot"
  let ?cells="\<lambda>slot. map (\<lambda>entry. comma_crt_set (fst entry)) (comma_semantic_b1_crt_constructed_slot_cells columns lift_column_ids occurrence_at refs source slot)"
  have slots_distinct: "distinct ?slots" by simp
  have parts: "list_all (\<lambda>slot. comma_semantic_b1_crt_cells_partition (?universe slot) (?cells slot)) ?slots"
    using each_slot by (auto simp: list_all_iff)
  have disjoint:
    "\<And>left right. left\<in>set ?slots \<Longrightarrow> right\<in>set ?slots \<Longrightarrow> left\<noteq>right \<Longrightarrow> ?universe left \<inter> ?universe right = {}"
    by (auto simp: comma_semantic_b1_crt_slot_cylinder_def)
  have partition:
    "comma_semantic_b1_crt_cells_partition (\<Union>slot\<in>set ?slots. ?universe slot) (concat (map ?cells ?slots))"
    by (rule comma_semantic_b1_crt_partition_concat_disjoint
      [OF slots_distinct parts disjoint])
  have universe:
    "(\<Union>slot\<in>set ?slots. ?universe slot)={..<924}"
    by (rule comma_semantic_b1_crt_slot_cylinders_cover_clock[OF period_positive])
  show ?thesis using partition universe by simp
qed
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_constructed_source_cells_partition}]; Comma_Proof_Profile.report "Partition composition: source partition checked"\<close>
ML \<open>Thm.consolidate [@{thm comma_semantic_b1_crt_tagged_map}, @{thm comma_semantic_b1_crt_constructed_slot_origins_tagged}]; Comma_Proof_Profile.report "Partition composition: tagged slot origins checked"\<close>
lemmas comma_semantic_b1_crt_partition_oracle_audit_bundle =
  comma_semantic_b1_crt_lift_column_set_matches
  comma_semantic_b1_crt_lift_column_row_sets_match
  comma_semantic_b1_crt_slot_cylinders_cover_clock
  comma_semantic_b1_crt_nonempty_filter_distinct
  comma_semantic_b1_crt_filter_empty_cells_partition
  comma_semantic_b1_crt_tagged_map
  comma_semantic_b1_crt_constructed_slot_origins_tagged
  comma_semantic_b1_crt_constructed_slot_live_entry_origins
  comma_semantic_b1_crt_constructed_source_live_entry_origins
  comma_semantic_b1_crt_constructed_goto_live_entry_cells
  comma_semantic_b1_crt_constructed_terminal_live_entry_cells
  comma_semantic_b1_crt_constructed_source_live_entry_cells
  comma_semantic_b1_crt_occurrence_columns_partition
  comma_semantic_b1_crt_lifted_columns_partition
  comma_semantic_b1_crt_constructed_terminal_slot_partition
  comma_semantic_b1_crt_constructed_goto_slot_partition
  comma_semantic_b1_crt_constructed_source_cells_partition
end
