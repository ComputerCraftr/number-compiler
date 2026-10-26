theory Comma_Semantic_Weighted_CRT_Selector_Laws
  imports Comma_Semantic_B1.Comma_Semantic_Graph_Weighted_CRT_DAG
    Comma_Semantic_B1.Comma_Weighted_CRT_Cofactor
begin

text \<open>
Guarded first-port and selector diagonal laws for weighted CRT actions.
These state only pointwise action equivalence under the selector's phase
condition; they do not claim termination, minimality, or unrestricted closure.
\<close>

lemma comma_weighted_crt_branch_guarded_congruence:
  fixes axis top_axis top_slot incoming phase :: nat
    and source_rows target_rows ::
      "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes axis: "axis<4"
    and top_axis: "top_axis<4"
    and top_slot: "top_slot<comma_crt_axis_radix top_axis"
    and source_extent:
      "length source_rows=comma_crt_axis_radix axis"
    and target_extent:
      "length target_rows=comma_crt_axis_radix axis"
    and rows:
      "\<And>row. row<comma_crt_axis_radix axis \<Longrightarrow>
        phase mod comma_crt_axis_radix top_axis=top_slot \<Longrightarrow>
        comma_weighted_crt_apply
          (source_rows!row) phase =
        comma_weighted_crt_apply
          (target_rows!row) phase"
    and phase_slot:
    "phase mod comma_crt_axis_radix top_axis=top_slot"
  shows "comma_weighted_crt_apply
      (incoming,Comma_Weighted_CRT_Branch axis source_rows) phase =
    comma_weighted_crt_apply
      (incoming,Comma_Weighted_CRT_Branch axis target_rows) phase"
proof -
  have row_equality:
    "\<And>row. row<comma_crt_axis_radix axis \<Longrightarrow>
      comma_weighted_crt_apply (source_rows!row) phase =
        comma_weighted_crt_apply (target_rows!row) phase"
  proof -
    fix row
    assume row: "row<comma_crt_axis_radix axis"
    show "comma_weighted_crt_apply (source_rows!row) phase =
        comma_weighted_crt_apply (target_rows!row) phase"
      by (rule rows[OF row phase_slot])
  qed
  show ?thesis
    by (rule comma_weighted_crt_branch_congruence
        [OF axis source_extent target_extent row_equality])
qed

lemma comma_weighted_crt_branch_apply_offset:
  fixes axis offset phase :: nat
    and rows :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes axis: "axis<4"
    and extent: "length rows=comma_crt_axis_radix axis"
  shows "comma_weighted_crt_apply
      (offset,Comma_Weighted_CRT_Branch axis rows) phase =
    comma_weighted_crt_apply
      (offset+fst (rows!(phase mod comma_crt_axis_radix axis)),
        snd (rows!(phase mod comma_crt_axis_radix axis))) phase"
proof -
  let ?selected = "rows!(phase mod comma_crt_axis_radix axis)"
  have branch_eval:
    "comma_weighted_crt_eval (Comma_Weighted_CRT_Branch axis rows) phase =
      comma_weighted_crt_apply ?selected phase"
    by (rule comma_weighted_crt_branch_apply[OF axis extent])
  have mapped:
    "map_option (\<lambda>(control,elapsed). (control,offset+elapsed))
        (comma_weighted_crt_eval (Comma_Weighted_CRT_Branch axis rows) phase) =
      map_option (\<lambda>(control,elapsed). (control,offset+elapsed))
        (comma_weighted_crt_apply ?selected phase)"
    by (rule arg_cong[OF branch_eval])
  have shifted:
    "comma_weighted_crt_apply (offset+fst ?selected,snd ?selected) phase =
      map_option (\<lambda>(control,elapsed). (control,offset+elapsed))
        (comma_weighted_crt_apply ?selected phase)"
    by (rule comma_weighted_crt_apply_add_offset)
  have source_head:
    "comma_weighted_crt_apply
        (offset,Comma_Weighted_CRT_Branch axis rows) phase =
      map_option (\<lambda>(control,elapsed). (control,offset+elapsed))
        (comma_weighted_crt_eval (Comma_Weighted_CRT_Branch axis rows) phase)"
    by (simp only: comma_weighted_crt_apply_def fst_conv snd_conv)
  have joined:
    "map_option (\<lambda>(control,elapsed). (control,offset+elapsed))
        (comma_weighted_crt_eval (Comma_Weighted_CRT_Branch axis rows) phase) =
      comma_weighted_crt_apply (offset+fst ?selected,snd ?selected) phase"
    by (rule trans[OF mapped shifted[symmetric]])
  show ?thesis by (rule trans[OF source_head joined])
qed

text \<open>
Canonical selector transport uses the first port at one ordered axis.  The
selector can use this restriction at the current root or recursively on a
child.  Every first-port equality is guarded by its selected clock phase; it
is not an unconditional equality.
\<close>

definition comma_weighted_crt_first_port_action ::
    "nat \<Rightarrow> nat \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      nat \<times> 'a comma_semantic_weighted_crt_dag" where
  "comma_weighted_crt_first_port_action axis slot tree =
    (case tree of
       Comma_Weighted_CRT_Leaf control \<Rightarrow> (0,tree)
     | Comma_Weighted_CRT_Branch branch_axis rows \<Rightarrow>
         (if branch_axis=axis \<and> slot<length rows then rows!slot else (0,tree)))"

definition comma_weighted_crt_first_port_rows ::
    "nat \<Rightarrow> nat \<Rightarrow>
      (nat \<times> 'a comma_semantic_weighted_crt_dag) list \<Rightarrow>
      (nat \<times> 'a comma_semantic_weighted_crt_dag) list" where
  "comma_weighted_crt_first_port_rows axis slot rows =
    map (\<lambda>(weight,child).
      (weight+fst (comma_weighted_crt_first_port_action axis slot child),
        snd (comma_weighted_crt_first_port_action axis slot child))) rows"

lemma comma_weighted_crt_first_port_action_leaf:
  "comma_weighted_crt_first_port_action axis slot
      (Comma_Weighted_CRT_Leaf control) = (0, Comma_Weighted_CRT_Leaf control)"
  by (simp add: comma_weighted_crt_first_port_action_def)

lemma comma_weighted_crt_first_port_action_same_branch:
  fixes axis slot bound :: nat
  assumes slot: "slot<bound"
    and extent: "size rows=bound"
  shows "comma_weighted_crt_first_port_action axis slot
      (Comma_Weighted_CRT_Branch axis rows) = rows!slot"
  using slot extent
  by (simp add: comma_weighted_crt_first_port_action_def list.size)

lemma comma_weighted_crt_first_port_action_other_branch:
  assumes axes: "branch_axis\<noteq>axis"
  shows "comma_weighted_crt_first_port_action axis slot
      (Comma_Weighted_CRT_Branch branch_axis rows) =
    (0, Comma_Weighted_CRT_Branch branch_axis rows)"
  using axes by (simp add: comma_weighted_crt_first_port_action_def)

lemma comma_weighted_crt_first_port_rows_length:
  "length (comma_weighted_crt_first_port_rows axis slot rows) = length rows"
  by (simp add: comma_weighted_crt_first_port_rows_def)

lemma comma_weighted_crt_first_port_rows_nth:
  fixes axis slot index :: nat
  assumes index: "index<length rows"
  shows "comma_weighted_crt_first_port_rows axis slot rows!index =
    (case rows!index of (weight,child) =>
      (weight+fst (comma_weighted_crt_first_port_action axis slot child),
        snd (comma_weighted_crt_first_port_action axis slot child)))"
  using index by (simp add: comma_weighted_crt_first_port_rows_def)

lemma comma_weighted_crt_first_port_rows_nth_action:
  fixes axis slot index bound weight delta :: nat
    and rows :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
    and child target :: "'a comma_semantic_weighted_crt_dag"
  assumes index: "index<bound"
    and extent: "size rows=bound"
    and selected: "rows!index=(weight,child)"
    and action: "comma_weighted_crt_first_port_action axis slot child=(delta,target)"
  shows "comma_weighted_crt_first_port_rows axis slot rows!index =
    (weight+delta,target)"
proof -
  have row_bound: "index<length rows" using index extent by (simp add: list.size)
  show ?thesis
    using comma_weighted_crt_first_port_rows_nth[OF row_bound] selected action
    by (simp add: case_prod_unfold)
qed


fun comma_weighted_crt_first_port_admissible ::
    "nat \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow> bool" where
  "comma_weighted_crt_first_port_admissible axis
      (Comma_Weighted_CRT_Leaf control) = True"
| "comma_weighted_crt_first_port_admissible axis
      (Comma_Weighted_CRT_Branch branch_axis rows) =
    (branch_axis\<noteq>axis \<or> length rows=comma_crt_axis_radix axis)"

lemma comma_weighted_crt_first_port_action_guarded:
  fixes axis slot phase :: nat
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and admissible: "comma_weighted_crt_first_port_admissible axis tree"
    and phase_slot: "phase mod comma_crt_axis_radix axis=slot"
  shows "comma_weighted_crt_apply
      (comma_weighted_crt_first_port_action axis slot tree) phase =
    comma_weighted_crt_apply (0,tree) phase"
proof (cases tree)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?thesis
    by (simp add: comma_weighted_crt_first_port_action_def
        comma_weighted_crt_apply_def)
next
  case (Comma_Weighted_CRT_Branch branch_axis rows)
  show ?thesis
  proof (cases "branch_axis=axis")
    case True
    have extent: "length rows=comma_crt_axis_radix axis"
      using admissible True Comma_Weighted_CRT_Branch by simp
    have branch_selected:
      "comma_weighted_crt_apply (0,Comma_Weighted_CRT_Branch axis rows) phase =
        comma_weighted_crt_apply (rows!slot) phase"
      using comma_weighted_crt_branch_apply_offset[OF axis extent] phase_slot
      by simp
    show ?thesis
      using branch_selected True Comma_Weighted_CRT_Branch extent slot
      by (simp add: comma_weighted_crt_first_port_action_def)
  next
    case False
    show ?thesis
      using False Comma_Weighted_CRT_Branch
      by (simp add: comma_weighted_crt_first_port_action_def)
  qed
qed

lemma comma_weighted_crt_first_port_action_guarded_offset:
  fixes axis slot phase incoming :: nat
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and admissible: "comma_weighted_crt_first_port_admissible axis tree"
    and phase_slot: "phase mod comma_crt_axis_radix axis=slot"
  shows "comma_weighted_crt_apply
      (incoming+fst (comma_weighted_crt_first_port_action axis slot tree),
        snd (comma_weighted_crt_first_port_action axis slot tree)) phase =
    comma_weighted_crt_apply (incoming,tree) phase"
proof -
  have guarded: "comma_weighted_crt_apply
      (comma_weighted_crt_first_port_action axis slot tree) phase =
      comma_weighted_crt_apply (0,tree) phase"
    by (rule comma_weighted_crt_first_port_action_guarded
      [OF axis slot admissible phase_slot])
  have left_shift:
      "comma_weighted_crt_apply
        (incoming+fst (comma_weighted_crt_first_port_action axis slot tree),
          snd (comma_weighted_crt_first_port_action axis slot tree)) phase =
       map_option (\<lambda>(control,elapsed). (control,incoming+elapsed))
         (comma_weighted_crt_apply
           (comma_weighted_crt_first_port_action axis slot tree) phase)"
    by (simp add: comma_weighted_crt_apply_add_offset)
  have right_shift:
      "comma_weighted_crt_apply (incoming,tree) phase =
       map_option (\<lambda>(control,elapsed). (control,incoming+elapsed))
         (comma_weighted_crt_apply (0,tree) phase)"
    using comma_weighted_crt_apply_add_offset
      [where extra=incoming and action="(0,tree)" and phase=phase]
    by simp
  have middle:
      "map_option (\<lambda>(control,elapsed). (control,incoming+elapsed))
        (comma_weighted_crt_apply
          (comma_weighted_crt_first_port_action axis slot tree) phase) =
       map_option (\<lambda>(control,elapsed). (control,incoming+elapsed))
        (comma_weighted_crt_apply (0,tree) phase)"
    by (simp only: guarded)
  have finish:
      "map_option (\<lambda>(control,elapsed). (control,incoming+elapsed))
        (comma_weighted_crt_apply
          (comma_weighted_crt_first_port_action axis slot tree) phase) =
       comma_weighted_crt_apply (incoming,tree) phase"
    by (rule trans[OF middle right_shift[symmetric]])
  show ?thesis by (rule trans[OF left_shift finish])
qed

lemma comma_weighted_crt_branch_first_port_guarded:
  fixes parent_axis axis slot incoming phase :: nat
    and rows :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes parent_axis: "parent_axis<4"
    and axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and extent: "length rows=comma_crt_axis_radix parent_axis"
    and children:
      "list_all (\<lambda>(weight,child).
        comma_weighted_crt_first_port_admissible axis child) rows"
    and phase_slot: "phase mod comma_crt_axis_radix axis=slot"
  shows "comma_weighted_crt_apply
      (incoming,Comma_Weighted_CRT_Branch parent_axis rows) phase =
    comma_weighted_crt_apply
      (incoming,Comma_Weighted_CRT_Branch parent_axis
        (comma_weighted_crt_first_port_rows axis slot rows)) phase"
proof -
  have restricted_rows_extent:
      "length (comma_weighted_crt_first_port_rows axis slot rows) =
        comma_crt_axis_radix parent_axis"
    using extent by (simp add: comma_weighted_crt_first_port_rows_def)
  have row_equality:
    "\<And>row. row<comma_crt_axis_radix parent_axis \<Longrightarrow>
      comma_weighted_crt_apply (rows!row) phase =
        comma_weighted_crt_apply
          (comma_weighted_crt_first_port_rows axis slot rows!row) phase"
  proof -
    fix row
    assume row: "row<comma_crt_axis_radix parent_axis"
    obtain weight child where selected: "rows!row=(weight,child)"
      using row extent by (cases "rows!row") auto
    have row_bound: "row<length rows"
      using row extent by simp
    have member: "(weight,child)\<in>set rows"
      using nth_mem[OF row_bound] selected by simp
    have child_admissible: "comma_weighted_crt_first_port_admissible axis child"
      using children member by (auto simp: list_all_iff prod_set_defs)
    show "comma_weighted_crt_apply (rows!row) phase =
        comma_weighted_crt_apply
          (comma_weighted_crt_first_port_rows axis slot rows!row) phase"
      using comma_weighted_crt_first_port_action_guarded_offset
        [OF axis slot child_admissible phase_slot, of weight]
        selected row row_bound
      by (simp add: comma_weighted_crt_first_port_rows_def algebra_simps)
  qed
  show ?thesis
    by (rule comma_weighted_crt_branch_guarded_congruence
        [OF parent_axis axis slot extent restricted_rows_extent row_equality phase_slot])
qed

lemma comma_weighted_crt_branch_selected_first_port_guarded:
  fixes axis slot incoming phase :: nat
    and rows :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and extent: "length rows=comma_crt_axis_radix axis"
    and children:
      "list_all (\<lambda>(weight,child).
        comma_weighted_crt_first_port_admissible axis child) rows"
    and phase_slot: "phase mod comma_crt_axis_radix axis=slot"
  shows "comma_weighted_crt_apply
      (incoming,Comma_Weighted_CRT_Branch axis rows) phase =
    comma_weighted_crt_apply
      (incoming+fst (comma_weighted_crt_first_port_rows axis slot rows!slot),
        snd (comma_weighted_crt_first_port_rows axis slot rows!slot)) phase"
proof -
  have restricted_extent:
      "length (comma_weighted_crt_first_port_rows axis slot rows)=
        comma_crt_axis_radix axis"
    using extent by (simp add: comma_weighted_crt_first_port_rows_def)
  have source_to_restricted:
      "comma_weighted_crt_apply
        (incoming,Comma_Weighted_CRT_Branch axis rows) phase =
       comma_weighted_crt_apply
        (incoming,Comma_Weighted_CRT_Branch axis
          (comma_weighted_crt_first_port_rows axis slot rows)) phase"
    by (rule comma_weighted_crt_branch_first_port_guarded
      [OF axis axis slot extent children phase_slot])
  have restricted_selected:
      "comma_weighted_crt_apply
        (incoming,Comma_Weighted_CRT_Branch axis
          (comma_weighted_crt_first_port_rows axis slot rows)) phase =
       comma_weighted_crt_apply
        (incoming+fst (comma_weighted_crt_first_port_rows axis slot rows!slot),
          snd (comma_weighted_crt_first_port_rows axis slot rows!slot)) phase"
    using comma_weighted_crt_branch_apply_offset
      [OF axis restricted_extent] phase_slot
    by simp
  show ?thesis using source_to_restricted restricted_selected by simp
qed

lemma comma_weighted_crt_guarded_port_diagonal:
  fixes axis offset phase :: nat
    and source_tree :: "'a comma_semantic_weighted_crt_dag"
    and ports :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes axis: "axis<4"
    and extent: "length ports=comma_crt_axis_radix axis"
    and guarded_ports:
      "\<And>slot incoming phase. slot<comma_crt_axis_radix axis \<Longrightarrow>
        phase mod comma_crt_axis_radix axis=slot \<Longrightarrow>
        comma_weighted_crt_apply (incoming,source_tree) phase =
          comma_weighted_crt_apply
            (incoming+fst (ports!slot),snd (ports!slot)) phase"
  shows "comma_weighted_crt_apply (offset,source_tree) phase =
    comma_weighted_crt_apply
      (offset,Comma_Weighted_CRT_Branch axis ports) phase"
proof -
  have slot_bound: "phase mod comma_crt_axis_radix axis<
      comma_crt_axis_radix axis"
    using comma_weighted_crt_axis_positive[OF axis] by simp
  have selected:
    "comma_weighted_crt_apply (offset,source_tree) phase =
      comma_weighted_crt_apply
        (offset+fst (ports!(phase mod comma_crt_axis_radix axis)),
          snd (ports!(phase mod comma_crt_axis_radix axis))) phase"
    by (rule guarded_ports[OF slot_bound refl])
  have branch_selected:
    "comma_weighted_crt_apply
       (offset,Comma_Weighted_CRT_Branch axis ports) phase =
      comma_weighted_crt_apply
        (offset+fst (ports!(phase mod comma_crt_axis_radix axis)),
          snd (ports!(phase mod comma_crt_axis_radix axis))) phase"
    by (rule comma_weighted_crt_branch_apply_offset[OF axis extent])
  show ?thesis using selected branch_selected by simp
qed

lemma comma_weighted_crt_guarded_port_diagonal_forall:
  fixes axis radix offset :: nat
    and source_tree :: "'a comma_semantic_weighted_crt_dag"
    and ports :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes axis: "axis<4"
    and radix: "radix=comma_crt_axis_radix axis"
    and extent: "length ports=radix"
    and guarded_ports:
      "\<forall>slot<radix.
        \<forall>incoming phase. phase mod comma_crt_axis_radix axis=slot \<longrightarrow>
          comma_weighted_crt_apply (incoming,source_tree) phase =
            comma_weighted_crt_apply
              (incoming+fst (ports!slot),snd (ports!slot)) phase"
  shows "comma_weighted_crt_apply (offset,source_tree) phase =
    comma_weighted_crt_apply
      (offset,Comma_Weighted_CRT_Branch axis ports) phase"
proof -
  have guarded_numeric:
    "\<forall>slot<comma_crt_axis_radix axis.
      \<forall>incoming phase. phase mod comma_crt_axis_radix axis=slot \<longrightarrow>
        comma_weighted_crt_apply (incoming,source_tree) phase =
          comma_weighted_crt_apply
            (incoming+fst (ports!slot),snd (ports!slot)) phase"
    using guarded_ports radix by blast
  have guarded:
    "\<And>slot incoming phase. slot<comma_crt_axis_radix axis \<Longrightarrow>
      phase mod comma_crt_axis_radix axis=slot \<Longrightarrow>
        comma_weighted_crt_apply (incoming,source_tree) phase =
          comma_weighted_crt_apply
            (incoming+fst (ports!slot),snd (ports!slot)) phase"
    using guarded_numeric by blast
  have exact_extent: "length ports=comma_crt_axis_radix axis"
    using extent radix by simp
  show ?thesis
    by (rule comma_weighted_crt_guarded_port_diagonal[OF axis exact_extent guarded])
qed

lemma comma_weighted_crt_first_port_completed:
  fixes rows resolved_rows ::
    "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes parent_axis: "parent_axis<4"
    and axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and extent: "length rows=comma_crt_axis_radix parent_axis"
    and children: "list_all (\<lambda>(weight,child).
      comma_weighted_crt_first_port_admissible axis child) rows"
    and resolved: "comma_weighted_crt_first_port_rows axis slot rows=resolved_rows"
    and completed: "\<forall>incoming phase.
      comma_weighted_crt_apply
        (incoming,Comma_Weighted_CRT_Branch parent_axis resolved_rows) phase =
      comma_weighted_crt_apply (incoming+weight,result_tree) phase"
    and guard: "phase mod comma_crt_axis_radix axis=slot"
  shows "comma_weighted_crt_apply
      (incoming,Comma_Weighted_CRT_Branch parent_axis rows) phase =
    comma_weighted_crt_apply (incoming+weight,result_tree) phase"
proof -
  have first: "comma_weighted_crt_apply
      (incoming,Comma_Weighted_CRT_Branch parent_axis rows) phase =
    comma_weighted_crt_apply
      (incoming,Comma_Weighted_CRT_Branch parent_axis resolved_rows) phase"
    using comma_weighted_crt_branch_first_port_guarded
      [OF parent_axis axis slot extent children guard] resolved by simp
  have second: "comma_weighted_crt_apply
      (incoming,Comma_Weighted_CRT_Branch parent_axis resolved_rows) phase =
    comma_weighted_crt_apply (incoming+weight,result_tree) phase"
    using completed by blast
  show ?thesis by (rule trans[OF first second])
qed

lemma comma_weighted_crt_branch_add_common:
  fixes rows :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes axis: "axis<4"
    and extent: "length rows=comma_crt_axis_radix axis"
  shows "comma_weighted_crt_apply
      (offset,Comma_Weighted_CRT_Branch axis
        (map (\<lambda>(weight,child). (common+weight,child)) rows)) phase =
    comma_weighted_crt_apply
      (offset+common,Comma_Weighted_CRT_Branch axis rows) phase"
proof -
  have bounds: "\<forall>edge\<in>set
      (map (\<lambda>(weight,child). (common+weight,child)) rows).
      common\<le>fst edge"
    by auto
  have restore: "map (\<lambda>(weight,child). (weight-common,child))
      (map (\<lambda>(weight,child). (common+weight,child)) rows) = rows"
    by (induction rows) auto
  show ?thesis
    using comma_weighted_crt_recenter_exact[OF axis, of
      "map (\<lambda>(weight,child). (common+weight,child)) rows" common offset phase]
      extent bounds restore by simp
qed

lemma comma_weighted_crt_child_row_offset:
  fixes source target :: "'a comma_semantic_weighted_crt_dag"
    and weight delta total :: nat
  assumes child: "\<forall>incoming phase.
      comma_weighted_crt_apply (incoming,source) phase =
      comma_weighted_crt_apply (incoming+delta,target) phase"
    and offset: "weight+delta=total"
  shows "\<forall>incoming phase.
      comma_weighted_crt_apply (incoming+weight,source) phase =
      comma_weighted_crt_apply (incoming+total,target) phase"
proof (intro allI)
  fix incoming phase
  have "comma_weighted_crt_apply (incoming+weight,source) phase =
      comma_weighted_crt_apply ((incoming+weight)+delta,target) phase"
    using child by blast
  then show "comma_weighted_crt_apply (incoming+weight,source) phase =
      comma_weighted_crt_apply (incoming+total,target) phase"
    using offset by (simp add: add.assoc)
qed

lemma comma_weighted_crt_child_row_identity:
  fixes source target :: "'a comma_semantic_weighted_crt_dag"
    and weight :: nat
  assumes child: "\<forall>incoming phase.
      comma_weighted_crt_apply (incoming,source) phase =
      comma_weighted_crt_apply (incoming,target) phase"
  shows "\<forall>incoming phase.
      comma_weighted_crt_apply (incoming+weight,source) phase =
      comma_weighted_crt_apply (incoming+weight,target) phase"
  using child by blast

lemma comma_weighted_crt_selected_row_all_offsets:
  fixes source_rows target_rows ::
    "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes source: "source_rows!slot=(source_weight,source_tree)"
    and target: "target_rows!slot=(target_weight,target_tree)"
    and exact: "\<forall>incoming phase.
      comma_weighted_crt_apply (incoming+source_weight,source_tree) phase =
      comma_weighted_crt_apply (incoming+target_weight,target_tree) phase"
  shows "slot<bound \<longrightarrow> (\<forall>incoming phase.
    comma_weighted_crt_apply
      (incoming+fst (source_rows!slot),snd (source_rows!slot)) phase =
    comma_weighted_crt_apply
      (incoming+fst (target_rows!slot),snd (target_rows!slot)) phase)"
  using source target exact by simp

lemma comma_weighted_crt_list_all_upt_implies_forall:
  fixes n :: nat and predicate :: "nat \<Rightarrow> bool"
  assumes checked:
    "list_all (\<lambda>index. index<n \<longrightarrow> predicate index) [0..<n]"
  shows "\<forall>index<n. predicate index"
  using checked by (auto simp: list_all_iff set_upt)

lemma comma_weighted_crt_selected_port_rebase:
  fixes axis slot weight :: nat
    and source target :: "'a comma_semantic_weighted_crt_dag"
    and ports :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes selected: "ports!slot=(weight,target)"
    and action: "\<forall>incoming phase.
      phase mod comma_crt_axis_radix axis=slot \<longrightarrow>
      comma_weighted_crt_apply (incoming,source) phase =
        comma_weighted_crt_apply (incoming+weight,target) phase"
  shows "\<forall>incoming phase.
      phase mod comma_crt_axis_radix axis=slot \<longrightarrow>
      comma_weighted_crt_apply (incoming,source) phase =
        comma_weighted_crt_apply
          (incoming+fst (ports!slot),snd (ports!slot)) phase"
proof (intro allI impI)
  fix incoming phase
  assume guard: "phase mod comma_crt_axis_radix axis=slot"
  have exact: "comma_weighted_crt_apply (incoming,source) phase =
      comma_weighted_crt_apply (incoming+weight,target) phase"
    using action guard by blast
  show "comma_weighted_crt_apply (incoming,source) phase =
      comma_weighted_crt_apply
        (incoming+fst (ports!slot),snd (ports!slot)) phase"
    using exact selected by simp
qed

lemma comma_weighted_crt_first_port_rows_nil:
  "comma_weighted_crt_first_port_rows axis slot [] = []"
  by (simp add: comma_weighted_crt_first_port_rows_def)

lemma comma_weighted_crt_first_port_rows_cons_transport:
  fixes axis slot input_weight delta actual_weight :: nat
    and child target :: "'a comma_semantic_weighted_crt_dag"
    and input_rows actual_rows ::
      "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes action:
      "comma_weighted_crt_first_port_action axis slot child=(delta,target)"
    and weight: "input_weight+delta=actual_weight"
    and tail:
      "comma_weighted_crt_first_port_rows axis slot input_rows=actual_rows"
  shows "comma_weighted_crt_first_port_rows axis slot
      ((input_weight,child)#input_rows) =
    (actual_weight,target)#actual_rows"
  using action weight tail
  by (simp add: comma_weighted_crt_first_port_rows_def)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Weighted CRT guarded selector laws preserve pointwise actions"
    @{thms comma_weighted_crt_branch_guarded_congruence
      comma_weighted_crt_branch_apply_offset
      comma_weighted_crt_first_port_admissible.simps
      comma_weighted_crt_first_port_action_guarded
      comma_weighted_crt_first_port_action_guarded_offset
      comma_weighted_crt_first_port_action_leaf
      comma_weighted_crt_first_port_action_same_branch
      comma_weighted_crt_first_port_action_other_branch
      comma_weighted_crt_first_port_rows_nth_action
      comma_weighted_crt_first_port_rows_length
      comma_weighted_crt_first_port_rows_nth
      comma_weighted_crt_branch_first_port_guarded
      comma_weighted_crt_branch_selected_first_port_guarded
      comma_weighted_crt_guarded_port_diagonal
      comma_weighted_crt_guarded_port_diagonal_forall
      comma_weighted_crt_child_row_offset
      comma_weighted_crt_child_row_identity
      comma_weighted_crt_selected_row_all_offsets
      comma_weighted_crt_list_all_upt_implies_forall
      comma_weighted_crt_selected_port_rebase
      comma_weighted_crt_first_port_rows_nil
      comma_weighted_crt_first_port_rows_cons_transport};
\<close>

end
