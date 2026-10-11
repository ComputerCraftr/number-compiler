theory Comma_Semantic_B1_CRT_Lift_Bindings
  imports Comma_Semantic_B1_CRT_Split_Bindings
begin
ML \<open>Comma_Proof_Profile.report "Lift bindings stage=entered"\<close>

text \<open>
Compact source entries keep one reference for each source slot.  A Goto
reference points to a child occurrence and a shared lift descriptor; its
columns are derived from the template and the descriptor's exact shift.  The
paired split action keeps control geometry separate from exact Stop weights.
\<close>

datatype comma_semantic_b1_crt_lift_ref =
    Comma_B1_Lift_Terminal_Ref nat nat
  | Comma_B1_Lift_Goto_Ref nat nat nat

record comma_semantic_b1_crt_lift_descriptor =
  comma_semantic_b1_crt_lift_descriptor_period :: nat
  comma_semantic_b1_crt_lift_descriptor_slot :: nat
  comma_semantic_b1_crt_lift_descriptor_template_cid :: nat
  comma_semantic_b1_crt_lift_descriptor_net_shift :: nat

fun comma_semantic_b1_crt_lift_ref_slot ::
    "comma_semantic_b1_crt_lift_ref \<Rightarrow> nat" where
  "comma_semantic_b1_crt_lift_ref_slot (Comma_B1_Lift_Terminal_Ref slot parent) = slot"
| "comma_semantic_b1_crt_lift_ref_slot
      (Comma_B1_Lift_Goto_Ref slot child_index lift_cid) = slot"

fun comma_semantic_b1_crt_lift_ref_child_index ::
    "comma_semantic_b1_crt_lift_ref \<Rightarrow> nat option" where
  "comma_semantic_b1_crt_lift_ref_child_index
      (Comma_B1_Lift_Terminal_Ref slot parent) = None"
| "comma_semantic_b1_crt_lift_ref_child_index
      (Comma_B1_Lift_Goto_Ref slot child_index lift_cid) = Some child_index"

fun comma_semantic_b1_crt_lift_ref_cid ::
    "comma_semantic_b1_crt_lift_ref \<Rightarrow> nat option" where
  "comma_semantic_b1_crt_lift_ref_cid
      (Comma_B1_Lift_Terminal_Ref slot parent) = None"
| "comma_semantic_b1_crt_lift_ref_cid
      (Comma_B1_Lift_Goto_Ref slot child_index lift_cid) = Some lift_cid"

fun comma_semantic_b1_crt_lift_ref_parent ::
    "comma_semantic_b1_crt_lift_ref \<Rightarrow> nat option" where
  "comma_semantic_b1_crt_lift_ref_parent
      (Comma_B1_Lift_Terminal_Ref slot parent) = Some parent"
| "comma_semantic_b1_crt_lift_ref_parent
      (Comma_B1_Lift_Goto_Ref slot child_index lift_cid) = None"

definition comma_semantic_b1_crt_lift_descriptor_valid ::
    "comma_crt_column list list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor \<Rightarrow> bool" where
  "comma_semantic_b1_crt_lift_descriptor_valid templates descriptor \<longleftrightarrow>
    comma_semantic_b1_crt_lift_descriptor_period descriptor \<in>
      comma_semantic_b1_crt_source_periods \<and>
    comma_semantic_b1_crt_lift_descriptor_slot descriptor <
      comma_semantic_b1_crt_lift_descriptor_period descriptor \<and>
    comma_semantic_b1_crt_lift_descriptor_template_cid descriptor < length templates \<and>
    comma_semantic_b1_crt_lift_descriptor_net_shift descriptor < 924"

definition comma_semantic_b1_crt_lift_columns_option ::
    "comma_crt_column list list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor \<Rightarrow>
      comma_crt_column list option" where
  "comma_semantic_b1_crt_lift_columns_option templates descriptor =
    (if comma_semantic_b1_crt_lift_descriptor_valid templates descriptor then
       Some (map (\<lambda>column. comma_crt_apply_shifted Comma_CRT_And
          (comma_semantic_b1_crt_lift_descriptor_net_shift descriptor)
          (comma_crt_source_scope_column
            (comma_semantic_b1_crt_lift_descriptor_period descriptor,
             comma_semantic_b1_crt_lift_descriptor_slot descriptor)) column)
          (templates ! comma_semantic_b1_crt_lift_descriptor_template_cid descriptor))
     else None)"

definition comma_semantic_b1_crt_lift_columns ::
    "comma_crt_column list list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor \<Rightarrow>
      comma_crt_column list" where
  "comma_semantic_b1_crt_lift_columns templates descriptor =
    (case comma_semantic_b1_crt_lift_columns_option templates descriptor of
       None \<Rightarrow> [] | Some columns \<Rightarrow> columns)"

definition comma_semantic_b1_crt_lift_slot_valid ::
    "comma_finite_position list \<Rightarrow>
      (nat \<Rightarrow> comma_semantic_b1_crt_occurrence option) \<Rightarrow>
      comma_semantic_b1_crt_descriptor list \<Rightarrow>
      comma_crt_column list list \<Rightarrow>
      comma_finite_position \<Rightarrow>
      comma_semantic_b1_crt_occurrence \<Rightarrow>
      comma_semantic_b1_crt_lift_ref list \<Rightarrow>
      comma_semantic_b1_crt_lift_descriptor list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_lift_slot_valid sources occurrence_at occurrence_descriptors templates
      source parent refs descriptors slot \<longleftrightarrow>
    (if slot < length refs \<and>
        slot < comma_decisive_sector_period
          (comma_source_continuation_base source) then
       (case refs ! slot of
          Comma_B1_Lift_Terminal_Ref ref_slot parent_column \<Rightarrow>
            (let action = comma_semantic_b1_source_slot_action source slot in
            ref_slot = slot \<and>
            parent_column < length (comma_semantic_b1_crt_occurrence_columns parent) \<and>
            (case comma_semantic_b1_terminal_action_result action of
               None \<Rightarrow> False
             | Some result \<Rightarrow>
                 comma_semantic_b1_crt_occurrence_beta parent ! parent_column = result))
        | Comma_B1_Lift_Goto_Ref ref_slot child_index lift_cid \<Rightarrow>
            (case comma_semantic_b1_source_slot_action source slot of
             Comma_Continuation_Goto child shift \<Rightarrow>
            ref_slot = slot \<and>
            child_index < length sources \<and>
            child_index < length occurrence_descriptors \<and>
            lift_cid < length descriptors \<and>
            sources ! child_index = comma_source_continuation_base child \<and>
            (case (occurrence_at child_index, descriptors ! lift_cid) of
               (Some child_occurrence, descriptor) \<Rightarrow>
                 fst (occurrence_descriptors ! child_index) =
                   comma_semantic_b1_crt_lift_descriptor_template_cid descriptor \<and>
                 comma_semantic_b1_crt_lift_descriptor_period descriptor =
                   comma_decisive_sector_period
                     (comma_source_continuation_base source) \<and>
                 comma_semantic_b1_crt_lift_descriptor_slot descriptor = slot \<and>
                 comma_semantic_b1_crt_lift_descriptor_template_cid descriptor <
                   length templates \<and>
                 comma_semantic_b1_crt_occurrence_columns child_occurrence =
                   templates ! comma_semantic_b1_crt_lift_descriptor_template_cid descriptor \<and>
                 comma_semantic_b1_crt_lift_descriptor_net_shift descriptor =
                   (shift + comma_semantic_b1_crt_occurrence_rebase child_occurrence) mod 924 \<and>
                 comma_semantic_b1_crt_lift_descriptor_valid templates descriptor
             | _ \<Rightarrow> False)
             | _ \<Rightarrow> False))
     else False)"

ML \<open>
  val _ = Thm.consolidate @{thms
    comma_semantic_b1_crt_lift_descriptor_valid_def
    comma_semantic_b1_crt_lift_columns_option_def
    comma_semantic_b1_crt_lift_columns_def
    comma_semantic_b1_crt_lift_slot_valid_def}
  val _ = Comma_Proof_Profile.report
    "Lift bindings stage=compact-definitions"
\<close>

lemma comma_semantic_b1_crt_lift_rejects_malformed_descriptor:
  "\<not> comma_semantic_b1_crt_lift_descriptor_valid
       [[Comma_CRT_Bool True]]
       (comma_semantic_b1_crt_lift_descriptor.make 5 0 0 0) \<and>
   \<not> comma_semantic_b1_crt_lift_descriptor_valid
       [[Comma_CRT_Bool True]]
       (comma_semantic_b1_crt_lift_descriptor.make 3 3 0 0) \<and>
   \<not> comma_semantic_b1_crt_lift_descriptor_valid
       [[Comma_CRT_Bool True]]
       (comma_semantic_b1_crt_lift_descriptor.make 3 1 0 924)"
  by code_simp

ML \<open>
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_lift_rejects_malformed_descriptor}
\<close>

lemma comma_semantic_b1_crt_lift_slot_rejects_foreign_child:
  assumes slot_bound: "slot < length refs"
    and source_slot: "slot < comma_decisive_sector_period
      (comma_source_continuation_base source)"
    and reference: "refs ! slot = Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    and action: "comma_semantic_b1_source_slot_action source slot =
      Comma_Continuation_Goto child shift"
    and child_bound: "child_index < length sources"
    and foreign: "sources ! child_index \<noteq> comma_source_continuation_base child"
  shows "\<not> comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
    occurrence_descriptors templates source parent refs descriptors slot"
  using slot_bound source_slot reference action child_bound foreign
  by (simp add: comma_semantic_b1_crt_lift_slot_valid_def)

lemma comma_semantic_b1_crt_lift_slot_rejects_out_of_range_child:
  assumes slot_bound: "slot < length refs"
    and source_slot: "slot < comma_decisive_sector_period
      (comma_source_continuation_base source)"
    and reference: "refs ! slot = Comma_B1_Lift_Goto_Ref slot child_index lift_cid"
    and action: "comma_semantic_b1_source_slot_action source slot =
      Comma_Continuation_Goto child shift"
    and child_foreign: "length sources \<le> child_index"
  shows "\<not> comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
    occurrence_descriptors templates source parent refs descriptors slot"
  using slot_bound source_slot reference action child_foreign
  by (simp add: comma_semantic_b1_crt_lift_slot_valid_def)

lemma comma_semantic_b1_crt_lift_slot_rejects_terminal_goto:
  assumes slot_bound: "slot < length refs"
    and source_slot: "slot < comma_decisive_sector_period
      (comma_source_continuation_base source)"
    and reference: "refs ! slot = Comma_B1_Lift_Terminal_Ref slot parent_column"
    and action: "comma_semantic_b1_source_slot_action source slot =
      Comma_Continuation_Goto child shift"
  shows "\<not> comma_semantic_b1_crt_lift_slot_valid sources occurrence_at
    occurrence_descriptors templates source parent refs descriptors slot"
  using slot_bound source_slot reference action
  by (simp add: comma_semantic_b1_crt_lift_slot_valid_def
      comma_semantic_b1_terminal_action_result.simps)

ML \<open>
  val _ = Thm.consolidate @{thms
    comma_semantic_b1_crt_lift_slot_rejects_foreign_child
    comma_semantic_b1_crt_lift_slot_rejects_out_of_range_child
    comma_semantic_b1_crt_lift_slot_rejects_terminal_goto}
  val _ = Comma_Proof_Profile.report
    "Lift bindings stage=fail-closed-contracts"
\<close>

lemma comma_semantic_b1_crt_lift_column_eval:
  fixes period slot net phase :: nat and child_column :: comma_crt_column
  assumes source_period:
      "period \<in> comma_semantic_b1_crt_source_periods"
    and slot: "slot < period"
    and child_admitted: "comma_crt_admitted 0 child_column"
    and phase: "phase < 924"
  shows "comma_crt_eval phase
      (comma_crt_apply_shifted Comma_CRT_And net
        (comma_crt_source_scope_column (period, slot)) child_column) =
    (phase mod period = slot \<and> comma_crt_eval (phase + net) child_column)"
proof -
  have scope_admitted: "comma_semantic_b1_crt_scope_admitted (period, slot)"
    using source_period slot
    by (auto simp: comma_semantic_b1_crt_scope_admitted_def
        comma_semantic_b1_scope_admitted_def
        comma_semantic_b1_crt_source_periods_def)
  have period_fst: "fst (period, slot) \<in> comma_semantic_b1_crt_source_periods"
    using source_period by simp
  have scope_column_admitted: "comma_crt_admitted 0
      (comma_crt_source_scope_column (period, slot))"
    by (rule comma_crt_source_scope_column_admitted[OF scope_admitted period_fst])
  have scope_set: "comma_crt_set (comma_crt_source_scope_column (period, slot)) =
      {point. point < 924 \<and> point mod period = slot}"
    using comma_crt_source_scope_column_set[OF scope_admitted period_fst]
    by (simp add: comma_semantic_b1_crt_scope_holds_def)
  have scope_eval: "comma_crt_eval phase (comma_crt_source_scope_column (period, slot)) =
      (phase mod period = slot)"
    using scope_set phase by (auto simp: comma_crt_set_def)
  have shifted_eval:
    "comma_crt_eval phase
        (comma_crt_apply_shifted Comma_CRT_And net
          (comma_crt_source_scope_column (period, slot)) child_column) =
      comma_crt_boolean_value Comma_CRT_And
        (comma_crt_eval phase (comma_crt_source_scope_column (period, slot)))
        (comma_crt_eval (phase + net) child_column)"
    by (rule comma_crt_apply_shifted_refines_boolean
      [OF scope_column_admitted child_admitted])
  show ?thesis using shifted_eval scope_eval
    by (simp add: comma_crt_boolean_value_def)
qed

lemma comma_semantic_b1_crt_lift_scope_admitted:
  assumes source_period:
      "period \<in> comma_semantic_b1_crt_source_periods"
    and slot: "slot < period"
  shows "comma_crt_admitted 0 (comma_crt_source_scope_column (period, slot))"
proof -
  have scope: "comma_semantic_b1_crt_scope_admitted (period, slot)"
    using source_period slot
    by (auto simp: comma_semantic_b1_crt_scope_admitted_def
        comma_semantic_b1_scope_admitted_def
        comma_semantic_b1_crt_source_periods_def)
  have period_fst:
      "fst (period, slot) \<in> comma_semantic_b1_crt_source_periods"
    using source_period by simp
  show ?thesis
    by (rule comma_crt_source_scope_column_admitted[OF scope period_fst])
qed

lemma comma_semantic_b1_crt_lift_scope_eval:
  assumes source_period:
      "period \<in> comma_semantic_b1_crt_source_periods"
    and slot: "slot < period"
    and phase: "phase < 924"
  shows "comma_crt_eval phase (comma_crt_source_scope_column (period, slot)) =
    (phase mod period = slot)"
proof -
  have scope: "comma_semantic_b1_crt_scope_admitted (period, slot)"
    using source_period slot
    by (auto simp: comma_semantic_b1_crt_scope_admitted_def
        comma_semantic_b1_scope_admitted_def
        comma_semantic_b1_crt_source_periods_def)
  have period_fst:
      "fst (period, slot) \<in> comma_semantic_b1_crt_source_periods"
    using source_period by simp
  have scope_set:
      "comma_crt_set (comma_crt_source_scope_column (period, slot)) =
       {point. point < 924 \<and> point mod period = slot}"
    using comma_crt_source_scope_column_set[OF scope period_fst]
    by (simp add: comma_semantic_b1_crt_scope_holds_def)
  show ?thesis using scope_set phase
    by (auto simp: comma_crt_set_def)
qed

ML \<open>
  val _ = Thm.consolidate @{thms comma_semantic_b1_crt_lift_column_eval
    comma_semantic_b1_crt_lift_scope_admitted comma_semantic_b1_crt_lift_scope_eval}
  val _ = Comma_Proof_Profile.report
    "Lift bindings stage=column-evaluation"
\<close>

lemma comma_semantic_b1_crt_lift_positive_shift_asymmetric:
  "comma_semantic_b1_crt_lift_columns_option
      [[comma_crt_source_axis_column 1 3 2]]
      (comma_semantic_b1_crt_lift_descriptor.make 3 1 0 1) =
      Some [comma_crt_apply_shifted Comma_CRT_And 1
        (comma_crt_source_scope_column (3, 1))
        (comma_crt_source_axis_column 1 3 2)] \<and>
    comma_crt_eval 1
      (comma_crt_apply_shifted Comma_CRT_And 1
        (comma_crt_source_scope_column (3, 1))
        (comma_crt_source_axis_column 1 3 2)) \<and>
    \<not> comma_crt_eval 1
      (comma_crt_apply_shifted Comma_CRT_And 923
        (comma_crt_source_scope_column (3, 1))
        (comma_crt_source_axis_column 1 3 2))"
proof -
  have axis_admitted: "comma_crt_admitted 0
      (comma_crt_source_axis_column 1 3 2)"
    by (rule comma_crt_source_axis_column_admitted) simp
  have axis_set: "comma_crt_set (comma_crt_source_axis_column 1 3 2) =
      {point. point < 924 \<and> point mod 3 = 2}"
    using comma_crt_source_axis_column_set
      [where level=1 and divisor=3 and residue=2]
    by (simp add: comma_crt_period_def)
  have axis_two_member: "2 \<in> comma_crt_set (comma_crt_source_axis_column 1 3 2)"
    by (subst axis_set) simp
  have axis_two: "comma_crt_eval 2 (comma_crt_source_axis_column 1 3 2)"
    using axis_two_member by (simp add: comma_crt_set_def)
    have axis_zero_not_member:
        "0 \<notin> comma_crt_set (comma_crt_source_axis_column 1 3 2)"
      by (subst axis_set) simp
    have axis_zero: "\<not> comma_crt_eval 0 (comma_crt_source_axis_column 1 3 2)"
      using axis_zero_not_member by (simp add: comma_crt_set_def)
  have resolved:
    "comma_semantic_b1_crt_lift_columns_option
      [[comma_crt_source_axis_column 1 3 2]]
      (comma_semantic_b1_crt_lift_descriptor.make 3 1 0 1) =
      Some [comma_crt_apply_shifted Comma_CRT_And 1
        (comma_crt_source_scope_column (3, 1))
        (comma_crt_source_axis_column 1 3 2)]"
    by (simp add: comma_semantic_b1_crt_lift_columns_option_def
        comma_semantic_b1_crt_lift_descriptor.make_def
        comma_semantic_b1_crt_lift_descriptor_valid_def
        comma_semantic_b1_crt_source_periods_def)
  have positive_eval:
    "comma_crt_eval 1
      (comma_crt_apply_shifted Comma_CRT_And 1
        (comma_crt_source_scope_column (3, 1))
        (comma_crt_source_axis_column 1 3 2)) = True"
  proof -
    have eval:
      "comma_crt_eval 1
        (comma_crt_apply_shifted Comma_CRT_And 1
          (comma_crt_source_scope_column (3, 1))
          (comma_crt_source_axis_column 1 3 2)) =
        ((1::nat) mod 3=1 \<and>
          comma_crt_eval 2 (comma_crt_source_axis_column 1 3 2))"
      using comma_semantic_b1_crt_lift_column_eval
        [where period=3 and slot=1 and net=1 and phase=1
          and child_column="comma_crt_source_axis_column 1 3 2"]
        axis_admitted
      by (simp add: comma_semantic_b1_crt_source_periods_def numeral_2_eq_2)
    show ?thesis using eval axis_two by simp
  qed
  have negative_eval:
    "comma_crt_eval 1
      (comma_crt_apply_shifted Comma_CRT_And 923
        (comma_crt_source_scope_column (3, 1))
        (comma_crt_source_axis_column 1 3 2)) = False"
  proof -
    have shifted:
      "comma_crt_eval 1
        (comma_crt_apply_shifted Comma_CRT_And 923
          (comma_crt_source_scope_column (3, 1))
          (comma_crt_source_axis_column 1 3 2)) =
       ((1::nat) mod 3 = 1 \<and>
        comma_crt_eval (1 + 923) (comma_crt_source_axis_column 1 3 2))"
      using comma_semantic_b1_crt_lift_column_eval[where period=3 and slot=1
          and net=923 and phase=1 and child_column="comma_crt_source_axis_column 1 3 2"]
        axis_admitted by (simp add: comma_semantic_b1_crt_source_periods_def)
    have periodic: "comma_crt_eval 924 (comma_crt_source_axis_column 1 3 2) =
        comma_crt_eval 0 (comma_crt_source_axis_column 1 3 2)"
      using comma_crt_eval_periodic[OF axis_admitted, where phase=924] by simp
    show ?thesis using shifted periodic axis_zero by simp
  qed
  show ?thesis using resolved positive_eval negative_eval by simp
qed

lemma comma_semantic_b1_crt_lift_rejects_foreign_template_cid:
  "comma_semantic_b1_crt_lift_columns_option [[Comma_CRT_Bool True]]
      (comma_semantic_b1_crt_lift_descriptor.make 3 1 1 1) = None"
  by (simp add: comma_semantic_b1_crt_lift_columns_option_def
      comma_semantic_b1_crt_lift_descriptor.make_def
      comma_semantic_b1_crt_lift_descriptor_valid_def
      comma_semantic_b1_crt_source_periods_def)

ML \<open>
  val _ = Thm.consolidate @{thms
    comma_semantic_b1_crt_lift_positive_shift_asymmetric
    comma_semantic_b1_crt_lift_rejects_foreign_template_cid}
  val _ = Comma_Proof_Profile.report
    "Lift bindings stage=asymmetric-shift-fixtures"
\<close>


ML \<open>
val checked = @{thms
    comma_semantic_b1_crt_lift_rejects_malformed_descriptor
    comma_semantic_b1_crt_lift_slot_rejects_foreign_child
    comma_semantic_b1_crt_lift_slot_rejects_out_of_range_child
    comma_semantic_b1_crt_lift_slot_rejects_terminal_goto
    comma_semantic_b1_crt_lift_column_eval
    comma_semantic_b1_crt_lift_scope_admitted
    comma_semantic_b1_crt_lift_scope_eval
    comma_semantic_b1_crt_lift_positive_shift_asymmetric
    comma_semantic_b1_crt_lift_rejects_foreign_template_cid
  }
val _ = Thm.consolidate checked
val _ = Comma_Proof_Profile.report
  "Lift bindings stage=final claims consolidated"
val _ = if null (Thm_Deps.all_oracles checked) then ()
  else error "Comma_Semantic_B1_CRT_Lift_Bindings local oracle audit failed"
val _ = Comma_Proof_Profile.report "Lift bindings stage=oracle audit checked"
\<close>
end
