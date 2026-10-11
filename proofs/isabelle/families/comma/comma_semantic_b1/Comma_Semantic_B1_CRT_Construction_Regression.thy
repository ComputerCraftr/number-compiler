theory Comma_Semantic_B1_CRT_Construction_Regression
  imports Comma_Semantic_B1_CRT_Constructed_Occurrence
begin

definition comma_semantic_b1_crt_fixture_quarter :: comma_crt_column where
  "comma_semantic_b1_crt_fixture_quarter =
    Comma_CRT_Node 0
      [Comma_CRT_Bool True, Comma_CRT_Bool False,
       Comma_CRT_Bool False, Comma_CRT_Bool False]"

definition comma_semantic_b1_crt_fixture_quarter_shifted :: comma_crt_column where
  "comma_semantic_b1_crt_fixture_quarter_shifted =
    Comma_CRT_Node 0
      [Comma_CRT_Bool False, Comma_CRT_Bool True,
       Comma_CRT_Bool False, Comma_CRT_Bool False]"

definition comma_semantic_b1_crt_fixture_even :: comma_crt_column where
  "comma_semantic_b1_crt_fixture_even =
    Comma_CRT_Node 0
      [Comma_CRT_Bool True, Comma_CRT_Bool False,
       Comma_CRT_Bool True, Comma_CRT_Bool False]"

definition comma_semantic_b1_crt_fixture_odd :: comma_crt_column where
  "comma_semantic_b1_crt_fixture_odd =
    Comma_CRT_Node 0
      [Comma_CRT_Bool False, Comma_CRT_Bool True,
       Comma_CRT_Bool False, Comma_CRT_Bool True]"

definition comma_semantic_b1_crt_fixture_swapped_parent ::
    comma_semantic_b1_crt_occurrence where
  "comma_semantic_b1_crt_fixture_swapped_parent =
    \<lparr>comma_semantic_b1_crt_occurrence_columns =
       [comma_semantic_b1_crt_fixture_even, comma_semantic_b1_crt_fixture_odd],
     comma_semantic_b1_crt_occurrence_rebase = 0,
     comma_semantic_b1_crt_occurrence_beta =
       [Comma_Semantic_B1_Stop 9, Comma_Semantic_B1_Stop 8]\<rparr>"

lemma comma_semantic_b1_crt_fixture_even_eval:
  "comma_crt_eval phase comma_semantic_b1_crt_fixture_even \<longleftrightarrow>
    phase mod 4 = 0 \<or> phase mod 4 = 2"
proof -
  have residue_cases:
    "phase mod 4 = 0 \<or> phase mod 4 = 1 \<or>
     phase mod 4 = 2 \<or> phase mod 4 = 3"
  proof -
    have "phase mod 4 < 4" by simp
    then show ?thesis by presburger
  qed
  show ?thesis
    using residue_cases
    by (auto simp: comma_semantic_b1_crt_fixture_even_def
        comma_crt_eval_node_selected comma_crt_period_def)
qed

lemma comma_semantic_b1_crt_fixture_odd_eval:
  "comma_crt_eval phase comma_semantic_b1_crt_fixture_odd \<longleftrightarrow>
    phase mod 4 = 1 \<or> phase mod 4 = 3"
proof -
  have residue_cases:
    "phase mod 4 = 0 \<or> phase mod 4 = 1 \<or>
     phase mod 4 = 2 \<or> phase mod 4 = 3"
  proof -
    have "phase mod 4 < 4" by simp
    then show ?thesis by presburger
  qed
  show ?thesis
    using residue_cases
    by (auto simp: comma_semantic_b1_crt_fixture_odd_def
        comma_crt_eval_node_selected comma_crt_period_def)
qed

lemma comma_semantic_b1_crt_fixture_swapped_parent_wellformed:
  "comma_semantic_b1_crt_occurrence_wellformed
    comma_semantic_b1_crt_fixture_swapped_parent"
proof -
  have admitted:
    "comma_crt_admitted 0 comma_semantic_b1_crt_fixture_even"
    "comma_crt_admitted 0 comma_semantic_b1_crt_fixture_odd"
    by (simp_all add: comma_semantic_b1_crt_fixture_even_def
      comma_semantic_b1_crt_fixture_odd_def comma_crt_period_def)
  have supported:
    "comma_crt_supported comma_semantic_b1_crt_fixture_even"
    "comma_crt_supported comma_semantic_b1_crt_fixture_odd"
    by (simp_all add: comma_semantic_b1_crt_fixture_even_def
      comma_semantic_b1_crt_fixture_odd_def)
  have both_eval:
    "\<not> (comma_crt_eval phase comma_semantic_b1_crt_fixture_even \<and>
      comma_crt_eval phase comma_semantic_b1_crt_fixture_odd)"
    for phase
    using comma_semantic_b1_crt_fixture_even_eval[of phase]
      comma_semantic_b1_crt_fixture_odd_eval[of phase]
    by auto
  have sets_disjoint:
    "comma_crt_set comma_semantic_b1_crt_fixture_even \<inter>
      comma_crt_set comma_semantic_b1_crt_fixture_odd = {}"
    using both_eval by (auto simp: comma_crt_set_def)
  have disjoint:
    "comma_semantic_b1_crt_occurrence_disjoint
      [comma_semantic_b1_crt_fixture_even, comma_semantic_b1_crt_fixture_odd]"
    using sets_disjoint
    by (auto simp: comma_semantic_b1_crt_occurrence_disjoint_def
        comma_semantic_b1_crt_occurrence_indexed_columns_def)
  have one_eval:
    "comma_crt_eval phase comma_semantic_b1_crt_fixture_even \<or>
     comma_crt_eval phase comma_semantic_b1_crt_fixture_odd"
    for phase
  proof -
    have residue_cases:
      "phase mod 4 = 0 \<or> phase mod 4 = 1 \<or>
       phase mod 4 = 2 \<or> phase mod 4 = 3"
    proof -
      have "phase mod 4 < 4" by simp
      then show ?thesis by presburger
    qed
    show ?thesis
    using comma_semantic_b1_crt_fixture_even_eval[of phase]
      comma_semantic_b1_crt_fixture_odd_eval[of phase]
      residue_cases by auto
  qed
  have covered:
    "comma_semantic_b1_crt_occurrence_covered
      [comma_semantic_b1_crt_fixture_even, comma_semantic_b1_crt_fixture_odd]"
    using one_eval
    by (auto simp: comma_semantic_b1_crt_occurrence_covered_def
        comma_semantic_b1_crt_occurrence_indexed_columns_def comma_crt_set_def)
  show ?thesis
    using admitted supported disjoint covered
    by (simp add: comma_semantic_b1_crt_occurrence_wellformed_def
        comma_semantic_b1_crt_fixture_swapped_parent_def)
qed

lemma comma_semantic_b1_crt_fixture_swapped_parent_partition:
  "comma_semantic_b1_crt_cells_partition {..<924}
    (map comma_crt_set
      (comma_semantic_b1_crt_occurrence_columns
        comma_semantic_b1_crt_fixture_swapped_parent))"
  by (rule comma_semantic_b1_crt_occurrence_columns_partition
      [OF comma_semantic_b1_crt_fixture_swapped_parent_wellformed])

lemma comma_semantic_b1_crt_fixture_swapped_parent_beta_distinct:
  "distinct (comma_semantic_b1_crt_occurrence_beta
    comma_semantic_b1_crt_fixture_swapped_parent)"
  by (simp add: comma_semantic_b1_crt_fixture_swapped_parent_def)

lemma comma_semantic_b1_crt_fixture_swapped_parent_phase_one_lookup:
  "comma_semantic_b1_crt_occurrence_lookup
    comma_semantic_b1_crt_fixture_swapped_parent 1 =
      Some (Comma_Semantic_B1_Stop 8)"
  by (simp add: comma_semantic_b1_crt_fixture_swapped_parent_def
      comma_semantic_b1_crt_occurrence_lookup_def
      comma_semantic_b1_crt_occurrence_find_index_def
      comma_semantic_b1_crt_occurrence_indexed_columns_def
      comma_semantic_b1_crt_fixture_even_eval
      comma_semantic_b1_crt_fixture_odd_eval)

lemma comma_semantic_b1_crt_fixture_rejects_swapped_parent_label:
  "\<not> comma_semantic_b1_crt_local_piece_covered
    comma_semantic_b1_crt_fixture_swapped_parent
    comma_semantic_b1_crt_fixture_odd (Comma_Semantic_B1_Stop 9)"
proof -
  let ?parent = "comma_semantic_b1_crt_fixture_swapped_parent"
  let ?even = "comma_semantic_b1_crt_fixture_even"
  let ?odd = "comma_semantic_b1_crt_fixture_odd"
  have even_admitted: "comma_crt_admitted 0 ?even"
    and odd_admitted: "comma_crt_admitted 0 ?odd"
    by (simp_all add: comma_semantic_b1_crt_fixture_even_def
      comma_semantic_b1_crt_fixture_odd_def comma_crt_period_def)
  have even_false: "\<not> comma_crt_eval 1 ?even"
    by (simp add: comma_semantic_b1_crt_fixture_even_eval)
  have odd_true: "comma_crt_eval 1 ?odd"
    by (simp add: comma_semantic_b1_crt_fixture_odd_eval)
  have selected:
    "comma_semantic_b1_crt_local_parent_column ?parent
      (Comma_Semantic_B1_Stop 9) = Some ?even"
    by (simp add: comma_semantic_b1_crt_fixture_swapped_parent_def
        comma_semantic_b1_crt_local_parent_column_def
        comma_semantic_b1_crt_find_result_index.simps)
  have negated_admitted:
    "comma_crt_admitted 0 (comma_crt_negate ?even)"
    by (rule comma_crt_negate_admitted[OF even_admitted])
  have negated_true:
    "comma_crt_eval 1 (comma_crt_negate ?even)"
    using comma_crt_negate_eval[OF even_admitted, of 1] even_false by simp
  have conjunction_admitted:
    "comma_crt_admitted 0
      (comma_crt_apply Comma_CRT_And ?odd (comma_crt_negate ?even))"
    by (rule comma_crt_apply_admitted[OF odd_admitted negated_admitted])
  have conjunction_true:
    "comma_crt_eval 1
      (comma_crt_apply Comma_CRT_And ?odd (comma_crt_negate ?even))"
  proof -
    have refinement:
      "comma_crt_eval 1
          (comma_crt_apply Comma_CRT_And ?odd (comma_crt_negate ?even)) =
        comma_crt_boolean_value Comma_CRT_And
          (comma_crt_eval 1 ?odd)
          (comma_crt_eval 1 (comma_crt_negate ?even))"
      by (rule comma_crt_apply_refines_boolean
        [OF odd_admitted negated_admitted,
         where operation=Comma_CRT_And and phase=1])
    show ?thesis
      using refinement odd_true negated_true
      by (simp add: comma_crt_boolean_value_def)
  qed
  have conjunction_supported:
    "comma_crt_supported
      (comma_crt_apply Comma_CRT_And ?odd (comma_crt_negate ?even))"
    by (rule comma_crt_eval_supported[OF conjunction_admitted conjunction_true])
  show ?thesis
    using selected even_admitted odd_admitted conjunction_supported
    by (simp add: comma_semantic_b1_crt_local_piece_covered_def)
qed

ML \<open>
  val _ = Thm.consolidate @{thms
    comma_semantic_b1_crt_fixture_even_eval
    comma_semantic_b1_crt_fixture_odd_eval
    comma_semantic_b1_crt_fixture_swapped_parent_wellformed
    comma_semantic_b1_crt_fixture_swapped_parent_partition
    comma_semantic_b1_crt_fixture_swapped_parent_beta_distinct
    comma_semantic_b1_crt_fixture_swapped_parent_phase_one_lookup
    comma_semantic_b1_crt_fixture_rejects_swapped_parent_label}
\<close>

lemma comma_semantic_b1_crt_group_fold_fixture_valid:
  "comma_semantic_b1_crt_group_construction_bound
    [Comma_CRT_Bool False, comma_semantic_b1_crt_fixture_quarter]
    0 0 1 [Comma_B1_Piece_Terminal 1 0 1 0]"
  by code_simp

lemma comma_semantic_b1_crt_group_fold_rejects_wrong_parent:
  "\<not> comma_semantic_b1_crt_group_construction_bound
    [Comma_CRT_Bool False, comma_semantic_b1_crt_fixture_quarter]
    0 0 0 [Comma_B1_Piece_Terminal 1 0 1 0]"
  by code_simp

lemma comma_semantic_b1_crt_group_fold_rejects_wrong_rebase:
  "\<not> comma_semantic_b1_crt_group_construction_bound
    [Comma_CRT_Bool False, comma_semantic_b1_crt_fixture_quarter,
     comma_semantic_b1_crt_fixture_quarter_shifted]
    1 0 1 [Comma_B1_Piece_Terminal 1 0 1 0]"
  by code_simp

lemma comma_semantic_b1_crt_group_fold_rejects_wrong_piece_destination:
  "\<not> comma_semantic_b1_crt_group_construction_bound
    [Comma_CRT_Bool False, comma_semantic_b1_crt_fixture_quarter]
    0 1 1 [Comma_B1_Piece_Terminal 1 0 1 0]"
  by code_simp

lemma comma_semantic_b1_crt_group_fold_rejects_foreign_cid:
  "\<not> comma_semantic_b1_crt_group_construction_bound
    [Comma_CRT_Bool False, comma_semantic_b1_crt_fixture_quarter]
    0 0 0 [Comma_B1_Piece_Terminal 1 0 2 0]"
  by code_simp

lemma comma_semantic_b1_crt_malformed_column_rejected_by_admission:
  "\<not> comma_crt_admitted 0 (Comma_CRT_Node 0 [])"
  by (simp add: comma_crt_period_def)

lemma comma_semantic_b1_crt_fixture_near_terminal_action:
  "comma_decisive_sector_period
      (comma_source_continuation_base (Comma_Near 9 0 19))=1"
  "comma_semantic_b1_terminal_action_result
      (comma_semantic_b1_source_slot_action (Comma_Near 9 0 19) 0) \<noteq> None"
  by code_simp+

lemma comma_semantic_b1_crt_fixture_near_terminal_slot_origins:
  fixes columns :: "comma_crt_column list"
    and lift_column_ids :: "nat list list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
  shows "comma_semantic_b1_crt_constructed_source_origins columns lift_column_ids
      [Comma_Near 9 0 19]
      occurrence_at [Comma_B1_Lift_Terminal_Ref 0 0] (Comma_Near 9 0 19) = [(0,0)]"
proof -
  have period:
    "comma_decisive_sector_period
      (comma_source_continuation_base (Comma_Near 9 0 19))=1"
    and terminal:
      "comma_semantic_b1_terminal_action_result
        (comma_semantic_b1_source_slot_action (Comma_Near 9 0 19) 0) \<noteq> None"
    using comma_semantic_b1_crt_fixture_near_terminal_action by simp_all
  obtain result where terminal_result:
    "comma_semantic_b1_terminal_action_result
      (comma_semantic_b1_source_slot_action (Comma_Near 9 0 19) 0)=Some result"
    using terminal by (cases
      "comma_semantic_b1_terminal_action_result
        (comma_semantic_b1_source_slot_action (Comma_Near 9 0 19) 0)") auto
  show ?thesis using period terminal_result
    by (simp add: comma_semantic_b1_crt_constructed_source_origins_def
      comma_semantic_b1_crt_constructed_slot_origins_def Let_def)
qed

lemma comma_semantic_b1_crt_constructed_occurrence_bound_rejects_piece_omission:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and slot_actions :: "comma_source_continuation_action list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
  shows "\<not> comma_semantic_b1_crt_constructed_occurrence_bound columns templates
    template_column_ids lift_column_ids [Comma_Near 9 0 19] occurrence_at occurrence_descriptors
    [[Comma_B1_Lift_Terminal_Ref 0 0]]
    slot_actions lift_descriptors
    [[]] 0"
proof (rule notI)
  assume bound:
    "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids [Comma_Near 9 0 19] occurrence_at occurrence_descriptors
      [[Comma_B1_Lift_Terminal_Ref 0 0]] slot_actions lift_descriptors [[]] 0"
  have source_origins:
    "comma_semantic_b1_crt_constructed_source_origins columns lift_column_ids
      [Comma_Near 9 0 19] occurrence_at [Comma_B1_Lift_Terminal_Ref 0 0]
      (Comma_Near 9 0 19) = [(0,0)]"
    by (rule comma_semantic_b1_crt_fixture_near_terminal_slot_origins)
  have mismatch:
    "sort (map comma_semantic_b1_crt_constructed_piece_origin
        (concat ([[]]!0))) \<noteq> [(0,0)]"
    by (simp add: comma_semantic_b1_crt_constructed_piece_origin_def)
  show False
    using comma_semantic_b1_crt_constructed_occurrence_bound_origins_exact[OF bound]
      source_origins mismatch by simp
qed

lemma comma_semantic_b1_crt_constructed_occurrence_bound_rejects_piece_multiplicity:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and slot_actions :: "comma_source_continuation_action list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
  shows "\<not> comma_semantic_b1_crt_constructed_occurrence_bound columns templates
    template_column_ids lift_column_ids [Comma_Near 9 0 19] occurrence_at occurrence_descriptors
    [[Comma_B1_Lift_Terminal_Ref 0 0]]
    slot_actions lift_descriptors
    [[[Comma_B1_Piece_Terminal 1 0 1 0,
      Comma_B1_Piece_Terminal 1 0 1 0]]] 0"
proof (rule notI)
  assume bound:
    "comma_semantic_b1_crt_constructed_occurrence_bound columns templates
      template_column_ids lift_column_ids [Comma_Near 9 0 19] occurrence_at occurrence_descriptors
      [[Comma_B1_Lift_Terminal_Ref 0 0]] slot_actions lift_descriptors
      [[[Comma_B1_Piece_Terminal 1 0 1 0,
        Comma_B1_Piece_Terminal 1 0 1 0]]] 0"
  have source_origins:
    "comma_semantic_b1_crt_constructed_source_origins columns lift_column_ids
      [Comma_Near 9 0 19] occurrence_at [Comma_B1_Lift_Terminal_Ref 0 0]
      (Comma_Near 9 0 19) = [(0,0)]"
    by (rule comma_semantic_b1_crt_fixture_near_terminal_slot_origins)
  have mismatch:
    "sort (map comma_semantic_b1_crt_constructed_piece_origin
        (concat ([[[Comma_B1_Piece_Terminal 1 0 1 0,
          Comma_B1_Piece_Terminal 1 0 1 0]]]!0))) \<noteq> [(0,0)]"
    by (simp add: comma_semantic_b1_crt_constructed_piece_origin_def)
  show False
    using comma_semantic_b1_crt_constructed_occurrence_bound_origins_exact[OF bound]
      source_origins mismatch by simp
qed

lemma comma_semantic_b1_crt_piece_matches_rejects_wrong_terminal_result:
  fixes lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and source :: comma_finite_position
    and parent :: comma_semantic_b1_crt_occurrence
  assumes terminal:
      "comma_semantic_b1_terminal_action_result
        (comma_semantic_b1_source_slot_action source slot) = Some expected"
    and period_exact:
      "period=comma_decisive_sector_period
        (comma_source_continuation_base source)"
    and slot_bound: "slot<period"
    and refs_bound: "slot<length refs"
    and ref_exact:
      "refs!slot=Comma_B1_Lift_Terminal_Ref slot destination"
    and destination_bound:
      "destination<length (comma_semantic_b1_crt_occurrence_beta parent)"
    and parent_column: "parent_column=destination"
    and wrong_beta:
      "comma_semantic_b1_crt_occurrence_beta parent ! destination \<noteq> expected"
  shows "\<not> comma_semantic_b1_crt_constructed_piece_matches
      [Comma_CRT_Bool False,
       comma_crt_source_scope_column (period,slot)]
      lift_column_ids sources occurrence_at refs source parent destination
      (Comma_B1_Piece_Terminal period slot 1 parent_column)"
  using terminal period_exact slot_bound refs_bound ref_exact
    destination_bound parent_column wrong_beta
  by (auto simp: comma_semantic_b1_crt_constructed_piece_matches_def Let_def
      split: option.splits)

lemma comma_semantic_b1_crt_piece_matches_rejects_wrong_goto_source:
  fixes source child wrong_source :: comma_finite_position
  assumes action:
      "comma_semantic_b1_source_slot_action source 0 =
        Comma_Continuation_Goto child shift"
    and one_slot: "comma_decisive_sector_period
      (comma_source_continuation_base source)=1"
    and wrong_source:
      "wrong_source \<noteq> comma_source_continuation_base child"
  shows "\<not> comma_semantic_b1_crt_constructed_piece_matches
      [Comma_CRT_Bool False, comma_semantic_b1_crt_fixture_quarter]
      [[1]] [wrong_source]
      (\<lambda>_. Some
        \<lparr>comma_semantic_b1_crt_occurrence_columns=
             [comma_semantic_b1_crt_fixture_quarter],
         comma_semantic_b1_crt_occurrence_rebase=0,
         comma_semantic_b1_crt_occurrence_beta=[Comma_Semantic_B1_Invalid]\<rparr>)
      [Comma_B1_Lift_Goto_Ref 0 0 0] source
      \<lparr>comma_semantic_b1_crt_occurrence_columns=
           [comma_semantic_b1_crt_fixture_quarter],
       comma_semantic_b1_crt_occurrence_rebase=0,
       comma_semantic_b1_crt_occurrence_beta=[Comma_Semantic_B1_Invalid]\<rparr>
      0 (Comma_B1_Piece_Goto 1 0 0 0 0 1 0)"
  using action one_slot wrong_source
  by (auto simp: comma_semantic_b1_crt_constructed_piece_matches_def Let_def
      comma_semantic_b1_crt_fixture_quarter_def
      split: option.splits)

lemma comma_semantic_b1_crt_goto_slot_certificate_rejects_foreign_ref:
  fixes columns :: "comma_crt_column list"
    and templates :: "comma_crt_column list list"
    and template_column_ids lift_column_ids :: "nat list list"
    and occurrence_descriptors :: "comma_semantic_b1_crt_descriptor list"
    and lift_descriptors :: "comma_semantic_b1_crt_lift_descriptor list"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
  assumes foreign_ref:
      "refs!slot=Comma_B1_Lift_Goto_Ref (Suc slot) child_index lift_cid"
  shows "\<not> comma_semantic_b1_crt_constructed_goto_slot_certificate
    columns templates template_column_ids lift_column_ids occurrence_descriptors
    lift_descriptors index refs slot"
  using foreign_ref
  by (auto simp: comma_semantic_b1_crt_constructed_goto_slot_certificate_def
      split: if_splits prod.splits)

lemma comma_semantic_b1_crt_piece_binding_rejects_changed_beta:
  fixes columns :: "comma_crt_column list"
    and lift_column_ids :: "nat list list"
    and sources :: "comma_finite_position list"
    and occurrence_at :: "nat \<Rightarrow> comma_semantic_b1_crt_occurrence option"
    and refs :: "comma_semantic_b1_crt_lift_ref list"
    and source :: comma_finite_position
    and parent child_occurrence :: comma_semantic_b1_crt_occurrence
  assumes child_at: "occurrence_at child_index=Some child_occurrence"
    and changed_beta:
      "comma_semantic_b1_crt_occurrence_beta parent!destination \<noteq>
       comma_semantic_b1_crt_occurrence_beta child_occurrence!child_column"
  shows "\<not> comma_semantic_b1_crt_constructed_piece_binding_matches
    columns lift_column_ids sources occurrence_at refs source parent destination
    (Comma_B1_Piece_Goto period slot child_index child_column lift_cid cid
      destination)"
  using child_at changed_beta
  by (auto simp: comma_semantic_b1_crt_constructed_piece_binding_matches_def
      Let_def split: option.splits)

ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_semantic_b1_crt_group_fold_fixture_valid
    comma_semantic_b1_crt_group_fold_rejects_wrong_parent
    comma_semantic_b1_crt_group_fold_rejects_wrong_rebase
    comma_semantic_b1_crt_group_fold_rejects_wrong_piece_destination
    comma_semantic_b1_crt_group_fold_rejects_foreign_cid
    comma_semantic_b1_crt_malformed_column_rejected_by_admission
    comma_semantic_b1_crt_constructed_occurrence_bound_rejects_piece_omission
    comma_semantic_b1_crt_constructed_occurrence_bound_rejects_piece_multiplicity
    comma_semantic_b1_crt_fixture_near_terminal_action
    comma_semantic_b1_crt_fixture_near_terminal_slot_origins
    comma_semantic_b1_crt_piece_matches_rejects_wrong_terminal_result
    comma_semantic_b1_crt_piece_matches_rejects_wrong_goto_source
    comma_semantic_b1_crt_goto_slot_certificate_rejects_foreign_ref
    comma_semantic_b1_crt_piece_binding_rejects_changed_beta
    comma_semantic_b1_crt_fixture_even_eval
    comma_semantic_b1_crt_fixture_odd_eval
    comma_semantic_b1_crt_fixture_swapped_parent_wellformed
    comma_semantic_b1_crt_fixture_swapped_parent_partition
    comma_semantic_b1_crt_fixture_swapped_parent_beta_distinct
    comma_semantic_b1_crt_fixture_swapped_parent_phase_one_lookup
    comma_semantic_b1_crt_fixture_rejects_swapped_parent_label
  }) then ()
  else error "Comma_Semantic_B1_CRT_Construction_Regression oracle audit failed"
\<close>

end
