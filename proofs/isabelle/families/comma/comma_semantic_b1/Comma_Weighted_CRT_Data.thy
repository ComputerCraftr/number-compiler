theory Comma_Weighted_CRT_Data
  imports Comma_Semantic_Weighted_CRT_Selector_Laws
    Comma_Entry_Arithmetic.Comma_Entry_Arithmetic
begin

definition comma_crt_payload ::
    "'a comma_semantic_weighted_crt_dag \<Rightarrow> nat \<Rightarrow> 'a option" where
  "comma_crt_payload tree phase =
    map_option fst (comma_weighted_crt_eval tree phase)"

lemma comma_weighted_crt_apply_payload_projection:
  "map_option fst (comma_weighted_crt_apply action phase) =
    comma_crt_payload (snd action) phase"
proof (cases action)
  case (Pair offset tree)
  show ?thesis
    by (cases "comma_weighted_crt_eval tree phase")
      (auto simp: Pair comma_weighted_crt_apply_def comma_crt_payload_def
        split: prod.splits)
qed

lemma comma_weighted_crt_cofactor_selected_apply:
  assumes axis: "axis<4"
    and slot: "slot=phase mod comma_crt_axis_radix axis"
    and shape: "comma_weighted_crt_shape lower tree"
  shows "comma_weighted_crt_apply
      (comma_weighted_crt_cofactor_all_raw axis slot tree) phase =
    comma_weighted_crt_apply (0,tree) phase"
proof -
  have slot_bound: "slot<comma_crt_axis_radix axis"
    using axis slot comma_weighted_crt_axis_positive by simp
  have wellformed: "comma_weighted_crt_wellformed tree"
    by (rule comma_weighted_crt_shape_wellformed[OF shape])
  have selected: "comma_crt_rebase axis slot phase=phase mod 924"
    by (rule comma_crt_rebase_selected[OF axis slot_bound slot])
  have cofactor:
    "comma_weighted_crt_apply
      (comma_weighted_crt_cofactor_all_raw axis slot tree) phase =
      comma_weighted_crt_eval tree phase"
    using comma_weighted_crt_cofactor_all_raw_apply
      [OF axis slot_bound wellformed, of phase]
      comma_weighted_crt_eval_mod_924[OF wellformed, of phase]
    by (simp only: selected)
  show ?thesis using cofactor
    by (simp add: comma_weighted_crt_apply_def option.map_id
      split: option.splits prod.splits)
qed

lemma comma_crt_payload_cofactor_selected:
  assumes axis: "axis<4"
    and slot: "slot=phase mod comma_crt_axis_radix axis"
    and shape: "comma_weighted_crt_shape lower tree"
  shows "comma_crt_payload
      (snd (comma_weighted_crt_cofactor_all_raw axis slot tree)) phase =
    comma_crt_payload tree phase"
proof -
  have projected: "map_option fst (comma_weighted_crt_apply
      (comma_weighted_crt_cofactor_all_raw axis slot tree) phase) =
      map_option fst (comma_weighted_crt_apply (0,tree) phase)"
    by (rule arg_cong[OF
      comma_weighted_crt_cofactor_selected_apply[OF axis slot shape]])
  show ?thesis using projected
    by (simp only: comma_weighted_crt_apply_payload_projection snd_conv)
qed

lemma comma_weighted_crt_apply_cofactor_list_cover:
  fixes tree :: "'a comma_semantic_weighted_crt_dag"
    and expected :: "('a \<times> nat) option"
  assumes axis: "axis<4"
    and shape: "comma_weighted_crt_shape 0 tree"
    and branches: "list_all
      (\<lambda>slot. phase mod comma_crt_axis_radix axis=slot \<longrightarrow>
        comma_weighted_crt_apply
          (comma_weighted_crt_cofactor_all_raw axis slot tree) phase=expected)
      [0..<comma_crt_axis_radix axis]"
  shows "comma_weighted_crt_apply (0,tree) phase=expected"
proof -
  let ?slot = "phase mod comma_crt_axis_radix axis"
  have member: "?slot\<in>set [0..<comma_crt_axis_radix axis]"
    using comma_weighted_crt_axis_positive[OF axis] by simp
  have selected: "comma_weighted_crt_apply
      (comma_weighted_crt_cofactor_all_raw axis ?slot tree) phase=expected"
    using branches member by (auto simp: list_all_iff)
  show ?thesis using selected
    comma_weighted_crt_cofactor_selected_apply[OF axis refl shape] by simp
qed

lemma comma_weighted_crt_apply_bind_slot_cover:
  fixes axis phase :: nat
    and target :: "'a comma_semantic_weighted_crt_dag"
    and children :: "'a comma_semantic_weighted_crt_dag list"
  assumes axis: "axis<4"
    and rows: "list_all
      (\<lambda>slot. phase mod comma_crt_axis_radix axis=slot \<longrightarrow>
        comma_weighted_crt_apply (0,target) phase=
          comma_weighted_crt_apply (0,children!slot) phase)
      [0..<comma_crt_axis_radix axis]"
  shows "comma_weighted_crt_apply (0,target) phase =
    comma_weighted_crt_apply
      (0,children!(phase mod comma_crt_axis_radix axis)) phase"
proof -
  have member: "phase mod comma_crt_axis_radix axis \<in>
      set [0..<comma_crt_axis_radix axis]"
    using comma_weighted_crt_axis_positive[OF axis] by simp
  show ?thesis using rows member by (auto simp: list_all_iff)
qed

text \<open>
Bottom-up normalization transports a completed child action through its
parent row.  The row's edge weight is included in the incoming offset, so the
equivalence preserves the chronological weight accumulated before the child.
The premise is uniform in both that offset and the phase; it can therefore be
reused unchanged when the normalized parent itself becomes a child.
\<close>

lemma comma_weighted_crt_branch_all_offsets_congruence:
  fixes axis :: nat
    and left right :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes axis: "axis<4"
    and left_extent: "length left=comma_crt_axis_radix axis"
    and right_extent: "length right=comma_crt_axis_radix axis"
    and rows: "\<forall>slot. slot<comma_crt_axis_radix axis \<longrightarrow>
      (\<forall>root_offset phase.
        comma_weighted_crt_apply
          (root_offset+fst (left!slot),snd (left!slot)) phase =
        comma_weighted_crt_apply
          (root_offset+fst (right!slot),snd (right!slot)) phase)"
  shows "\<And>root_offset phase.
    comma_weighted_crt_apply
      (root_offset,Comma_Weighted_CRT_Branch axis left) phase =
    comma_weighted_crt_apply
      (root_offset,Comma_Weighted_CRT_Branch axis right) phase"
proof -
  fix root_offset phase
  show "comma_weighted_crt_apply
      (root_offset,Comma_Weighted_CRT_Branch axis left) phase =
    comma_weighted_crt_apply
      (root_offset,Comma_Weighted_CRT_Branch axis right) phase"
  proof (rule comma_weighted_crt_branch_congruence
      [OF axis left_extent right_extent])
    fix slot
    assume slot: "slot<comma_crt_axis_radix axis"
    have row_all:
      "\<forall>root_offset phase.
        comma_weighted_crt_apply
          (root_offset+fst (left!slot),snd (left!slot)) phase =
        comma_weighted_crt_apply
          (root_offset+fst (right!slot),snd (right!slot)) phase"
      using rows slot by blast
    have row_zero:
      "\<forall>phase.
        comma_weighted_crt_apply
          (0+fst (left!slot),snd (left!slot)) phase =
        comma_weighted_crt_apply
          (0+fst (right!slot),snd (right!slot)) phase"
      using row_all by (rule spec[where x=0])
    have row_phase:
      "\<forall>phase.
        comma_weighted_crt_apply (left!slot) phase =
          comma_weighted_crt_apply (right!slot) phase"
      using row_zero by (simp add: prod.collapse)
    have row:
      "comma_weighted_crt_apply (left!slot) phase =
        comma_weighted_crt_apply (right!slot) phase"
      using row_phase by (rule spec[where x=phase])
    show "comma_weighted_crt_apply (left!slot) phase =
        comma_weighted_crt_apply (right!slot) phase"
      by (rule row)
  qed
qed

lemma comma_weighted_crt_literal_branch_all_offsets:
  fixes axis bound :: nat
    and source_rows target_rows ::
      "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes axis: "axis<4"
    and radix: "bound=comma_crt_axis_radix axis"
    and source_extent: "length source_rows=bound"
    and target_extent: "length target_rows=bound"
    and rows: "\<forall>slot. slot<bound \<longrightarrow>
      (\<forall>incoming phase.
        comma_weighted_crt_apply
          (incoming+fst (source_rows!slot),snd (source_rows!slot)) phase =
        comma_weighted_crt_apply
          (incoming+fst (target_rows!slot),snd (target_rows!slot)) phase)"
  shows "\<forall>incoming phase.
      comma_weighted_crt_apply
        (incoming,Comma_Weighted_CRT_Branch axis source_rows) phase =
      comma_weighted_crt_apply
        (incoming,Comma_Weighted_CRT_Branch axis target_rows) phase"
proof (intro allI)
  fix incoming phase
  have source: "length source_rows=comma_crt_axis_radix axis"
    using source_extent radix by simp
  have target: "length target_rows=comma_crt_axis_radix axis"
    using target_extent radix by simp
  have children: "\<forall>slot. slot<comma_crt_axis_radix axis \<longrightarrow>
      (\<forall>incoming phase.
        comma_weighted_crt_apply
          (incoming+fst (source_rows!slot),snd (source_rows!slot)) phase =
        comma_weighted_crt_apply
          (incoming+fst (target_rows!slot),snd (target_rows!slot)) phase)"
    using rows radix by simp
  show "comma_weighted_crt_apply
        (incoming,Comma_Weighted_CRT_Branch axis source_rows) phase =
      comma_weighted_crt_apply
        (incoming,Comma_Weighted_CRT_Branch axis target_rows) phase"
    by (rule comma_weighted_crt_branch_all_offsets_congruence
      [OF axis source target children])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Shared weighted CRT data transports"
    @{thms comma_weighted_crt_branch_all_offsets_congruence
      comma_weighted_crt_literal_branch_all_offsets
      comma_weighted_crt_cofactor_selected_apply
      comma_weighted_crt_apply_cofactor_list_cover
      comma_crt_payload_cofactor_selected
      comma_weighted_crt_apply_payload_projection
      comma_weighted_crt_apply_bind_slot_cover};
\<close>

ML_file "semantic_weighted_crt_data_transport.ML"
ML_file "semantic_weighted_crt_branch_transport.ML"
ML_file "semantic_weighted_crt_selector_transport.ML"
ML_file "semantic_weighted_crt_data_contract.ML"
ML_file "semantic_weighted_crt_certificate_builder.ML"
ML_file "semantic_weighted_crt_data.ML"
ML_file "semantic_weighted_crt_shallow_certificate.ML"

end
