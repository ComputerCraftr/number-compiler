theory Comma_Weighted_CRT_Cofactor
  imports Comma_Semantic_Graph_Weighted_CRT_DAG
begin

text \<open>
All-occurrence CRT cofactoring works on weighted decision trees whose axes
may repeat and need not be ordered.  Selecting one coordinate must therefore
specialize every matching branch, including matching branches below other
matching branches.  Root offsets and edge weights are retained exactly.
\<close>

fun comma_weighted_crt_axis_absent ::
    "nat \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow> bool" where
  "comma_weighted_crt_axis_absent axis (Comma_Weighted_CRT_Leaf control) = True"
| "comma_weighted_crt_axis_absent axis
      (Comma_Weighted_CRT_Branch branch_axis rows) =
    (branch_axis\<noteq>axis \<and>
      list_all (\<lambda>(weight,child). comma_weighted_crt_axis_absent axis child) rows)"

lemma comma_weighted_crt_branch_child_size_less:
  fixes axis :: nat
    and rows :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
    and weight :: nat
    and child :: "'a comma_semantic_weighted_crt_dag"
  assumes member: "(weight,child)\<in>set rows"
  shows "size child < size (Comma_Weighted_CRT_Branch axis rows)"
proof -
  let ?pair_size = "size_prod (\<lambda>(_::nat). 0) size"
  have pair_bound: "size child < ?pair_size (weight,child)"
    by simp
  have list_bound: "size child < size_list ?pair_size rows"
    by (rule size_list_estimation
      [where f="?pair_size" and y="size child", OF member pair_bound])
  have branch_size:
      "size (Comma_Weighted_CRT_Branch axis rows) =
        Suc (size_list ?pair_size rows)"
    by simp
  show ?thesis using pair_bound list_bound branch_size by arith
qed

function comma_weighted_crt_cofactor_all_raw ::
    "nat \<Rightarrow> nat \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      nat \<times> 'a comma_semantic_weighted_crt_dag" where
  "comma_weighted_crt_cofactor_all_raw axis slot
      (Comma_Weighted_CRT_Leaf control) =
    (0,Comma_Weighted_CRT_Leaf control)"
| "comma_weighted_crt_cofactor_all_raw axis slot
      (Comma_Weighted_CRT_Branch branch_axis rows) =
    (if branch_axis=axis then
       (if slot<length rows then
          (case rows!slot of (weight,child) \<Rightarrow>
            (let restricted=comma_weighted_crt_cofactor_all_raw axis slot child
             in (weight+fst restricted,snd restricted)))
        else (0,Comma_Weighted_CRT_Branch branch_axis rows))
     else (0,Comma_Weighted_CRT_Branch branch_axis
       (map (\<lambda>(weight,child).
         (let restricted=comma_weighted_crt_cofactor_all_raw axis slot child
          in (weight+fst restricted,snd restricted))) rows)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(axis,slot,tree). size tree)")
   apply (rule wf_measure)
  subgoal
    apply (simp only: in_measure case_prod_beta fst_conv snd_conv)
    by (metis nth_mem comma_weighted_crt_branch_child_size_less)
  subgoal
    apply (simp only: in_measure case_prod_beta fst_conv snd_conv)
    by (metis comma_weighted_crt_branch_child_size_less)
  done

lemma comma_weighted_crt_cofactor_all_raw_axis_absent:
  assumes absent: "comma_weighted_crt_axis_absent axis tree"
  shows "comma_weighted_crt_cofactor_all_raw axis slot tree = (0,tree)"
  using absent
proof (induction tree)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch branch_axis rows)
  have different: "branch_axis\<noteq>axis"
    using Comma_Weighted_CRT_Branch.prems by simp
  have children: "\<And>weight child. (weight,child)\<in>set rows \<Longrightarrow>
      comma_weighted_crt_cofactor_all_raw axis slot child=(0,child)"
    using Comma_Weighted_CRT_Branch by (auto simp: list_all_iff)
  have mapped: "map (\<lambda>(weight,child).
      let restricted=comma_weighted_crt_cofactor_all_raw axis slot child
      in (weight+fst restricted,snd restricted)) rows=rows"
  proof (rule map_idI)
    fix entry
    assume member: "entry\<in>set rows"
    obtain weight child where entry: "entry=(weight,child)"
      by (cases entry) auto
    show "(case entry of (weight,child) \<Rightarrow>
        let restricted=comma_weighted_crt_cofactor_all_raw axis slot child
        in (weight+fst restricted,snd restricted))=entry"
      using children[OF member[unfolded entry]]
      by (simp add: entry)
  qed
  show ?case
    using different mapped
    by (simp only: comma_weighted_crt_cofactor_all_raw.simps
      if_False mapped)
qed

lemma comma_weighted_crt_shape_axis_below_absent:
  assumes shape: "comma_weighted_crt_shape lower tree"
    and below: "axis<lower"
  shows "comma_weighted_crt_axis_absent axis tree"
  using shape below
  by (induction tree arbitrary: lower)
    (auto simp: list_all_iff)

lemma comma_weighted_crt_cofactor_all_raw_axis_below:
  assumes shape: "comma_weighted_crt_shape lower tree"
    and below: "axis<lower"
  shows "comma_weighted_crt_cofactor_all_raw axis slot tree=(0,tree)"
  by (rule comma_weighted_crt_cofactor_all_raw_axis_absent
    [OF comma_weighted_crt_shape_axis_below_absent[OF shape below]])

definition comma_weighted_crt_cofactor_all ::
    "nat \<Rightarrow> nat \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      (nat \<times> 'a comma_semantic_weighted_crt_dag) option" where
  "comma_weighted_crt_cofactor_all axis slot tree =
    (if axis<4 \<and> slot<comma_crt_axis_radix axis
        \<and> comma_weighted_crt_wellformed tree
     then Some (comma_weighted_crt_cofactor_all_raw axis slot tree)
     else None)"

lemma comma_weighted_crt_wellformed_shape:
  assumes "comma_weighted_crt_shape lower tree"
  shows "comma_weighted_crt_wellformed tree"
  using assms
  by (induction tree arbitrary: lower)
    (auto simp: list_all_iff prod_set_defs)

lemma comma_weighted_crt_cofactor_all_guarded_exact:
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and tree: "comma_weighted_crt_wellformed tree"
  shows "comma_weighted_crt_cofactor_all axis slot tree =
    Some (comma_weighted_crt_cofactor_all_raw axis slot tree)"
  using axis slot tree
  by (simp add: comma_weighted_crt_cofactor_all_def)

lemma comma_weighted_crt_cofactor_all_rejects:
  assumes "axis\<ge>4 \<or> slot\<ge>comma_crt_axis_radix axis
    \<or> \<not> comma_weighted_crt_wellformed tree"
  shows "comma_weighted_crt_cofactor_all axis slot tree=None"
  using assms by (auto simp: comma_weighted_crt_cofactor_all_def)

lemma comma_weighted_crt_cofactor_all_raw_wellformed:
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and tree: "comma_weighted_crt_wellformed tree"
  shows "comma_weighted_crt_wellformed
      (snd (comma_weighted_crt_cofactor_all_raw axis slot tree))"
  using tree
proof (induction tree)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch branch_axis rows)
  have branch_axis: "branch_axis<4"
    and length_rows: "length rows=comma_crt_axis_radix branch_axis"
    and children:
      "list_all (\<lambda>(weight,child). comma_weighted_crt_wellformed child) rows"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  show ?case
  proof (cases "branch_axis=axis")
    case True
    have selected_bound: "slot<length rows"
      using slot length_rows True by simp
    obtain weight child where selected:
        "rows!slot=(weight,child)"
      by (cases "rows!slot") auto
    have child_member: "(weight,child)\<in>set rows"
      using nth_mem[OF selected_bound] selected by simp
    have child_wellformed: "comma_weighted_crt_wellformed child"
      using children child_member by (auto simp: list_all_iff prod_set_defs)
    have child_result:
      "comma_weighted_crt_wellformed
        (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
      using Comma_Weighted_CRT_Branch.IH child_member child_wellformed
      by (auto simp: prod_set_defs)
    show ?thesis
      using True selected selected_bound child_result
      by (simp add: Let_def)
  next
    case False
    have children_result:
      "list_all (\<lambda>(weight,child).
        comma_weighted_crt_wellformed
          (snd (comma_weighted_crt_cofactor_all_raw axis slot child))) rows"
    proof (unfold list_all_iff, intro ballI)
      fix edge
      assume edge: "edge\<in>set rows"
      obtain weight child where edge_pair: "edge=(weight,child)"
        by (cases edge)
      have child_wellformed: "comma_weighted_crt_wellformed child"
        using children edge edge_pair
        by (auto simp: list_all_iff prod_set_defs)
      have "comma_weighted_crt_wellformed
          (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
        using Comma_Weighted_CRT_Branch.IH edge child_wellformed edge_pair
        by (auto simp: prod_set_defs)
      then show "case edge of (weight, child) \<Rightarrow>
          comma_weighted_crt_wellformed
            (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
        using edge_pair by simp
    qed
    show ?thesis using False branch_axis length_rows children_result
      by (simp add: Let_def case_prod_unfold list_all_iff prod_set_defs)
  qed
qed

lemma comma_weighted_crt_cofactor_all_raw_absent:
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and tree: "comma_weighted_crt_wellformed tree"
  shows "comma_weighted_crt_axis_absent axis
      (snd (comma_weighted_crt_cofactor_all_raw axis slot tree))"
  using tree
proof (induction tree)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch branch_axis rows)
  have branch_axis: "branch_axis<4"
    and length_rows: "length rows=comma_crt_axis_radix branch_axis"
    and children:
      "list_all (\<lambda>(weight,child). comma_weighted_crt_wellformed child) rows"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  show ?case
  proof (cases "branch_axis=axis")
    case True
    have selected_bound: "slot<length rows"
      using slot length_rows True by simp
    obtain weight child where selected: "rows!slot=(weight,child)"
      by (cases "rows!slot") auto
    have member: "(weight,child)\<in>set rows"
      using nth_mem[OF selected_bound] selected by simp
    have child_wellformed: "comma_weighted_crt_wellformed child"
      using children member by (auto simp: list_all_iff prod_set_defs)
    have child_absent:
      "comma_weighted_crt_axis_absent axis
        (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
      using Comma_Weighted_CRT_Branch.IH member child_wellformed
      by (auto simp: prod_set_defs)
    show ?thesis using True selected selected_bound child_absent
      by (simp add: Let_def)
  next
    case False
    have children_absent:
      "list_all (\<lambda>(weight,child).
        comma_weighted_crt_axis_absent axis
          (snd (comma_weighted_crt_cofactor_all_raw axis slot child))) rows"
    proof (unfold list_all_iff, intro ballI)
      fix edge
      assume edge: "edge\<in>set rows"
      obtain weight child where edge_pair: "edge=(weight,child)"
        by (cases edge)
      have child_wellformed: "comma_weighted_crt_wellformed child"
        using children edge edge_pair
        by (auto simp: list_all_iff prod_set_defs)
      have "comma_weighted_crt_axis_absent axis
          (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
        using Comma_Weighted_CRT_Branch.IH edge child_wellformed edge_pair
        by (auto simp: prod_set_defs)
      then show "case edge of (weight, child) \<Rightarrow>
          comma_weighted_crt_axis_absent axis
            (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
        using edge_pair by simp
    qed
    show ?thesis using False children_absent
      by (simp add: Let_def case_prod_unfold list_all_iff prod_set_defs)
  qed
qed

lemma comma_weighted_crt_shape_lower_mono:
  assumes lower: "lower\<le>upper"
    and shape: "comma_weighted_crt_shape upper tree"
  shows "comma_weighted_crt_shape lower tree"
  using shape lower
  by (induction tree arbitrary: lower upper)
    (auto simp: list_all_iff prod_set_defs)

lemma comma_weighted_crt_cofactor_all_raw_shape:
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and shape: "comma_weighted_crt_shape lower tree"
  shows "comma_weighted_crt_shape lower
      (snd (comma_weighted_crt_cofactor_all_raw axis slot tree))"
  using shape
proof (induction tree arbitrary: lower)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch branch_axis rows)
  have lower_branch: "lower\<le>branch_axis"
    and branch_axis: "branch_axis<4"
    and length_rows: "length rows=comma_crt_axis_radix branch_axis"
    and children:
      "list_all (\<lambda>(weight,child).
        comma_weighted_crt_shape (Suc branch_axis) child) rows"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  show ?case
  proof (cases "branch_axis=axis")
    case True
    have selected_bound: "slot<length rows"
      using slot length_rows True by simp
    obtain weight child where selected: "rows!slot=(weight,child)"
      by (cases "rows!slot") auto
    have child_member: "(weight,child)\<in>set rows"
      using nth_mem[OF selected_bound] selected by simp
    have child_shape:
      "comma_weighted_crt_shape (Suc branch_axis) child"
      using children child_member by (auto simp: list_all_iff prod_set_defs)
    have restricted_shape:
      "comma_weighted_crt_shape (Suc branch_axis)
        (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
      using Comma_Weighted_CRT_Branch.IH child_member child_shape
      by (auto simp: prod_set_defs)
    have lower_child: "lower\<le>Suc branch_axis"
      using lower_branch by arith
    have result_shape:
      "comma_weighted_crt_shape lower
        (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
      by (rule comma_weighted_crt_shape_lower_mono[OF lower_child restricted_shape])
    show ?thesis
      using True selected selected_bound result_shape
      by (simp add: Let_def)
  next
    case False
    have children_shape:
      "list_all (\<lambda>(weight,child).
        comma_weighted_crt_shape (Suc branch_axis)
          (snd (comma_weighted_crt_cofactor_all_raw axis slot child))) rows"
    proof (unfold list_all_iff, intro ballI)
      fix edge
      assume edge: "edge\<in>set rows"
      obtain weight child where edge_pair: "edge=(weight,child)"
        by (cases edge)
      have child_shape:
        "comma_weighted_crt_shape (Suc branch_axis) child"
        using children edge edge_pair
        by (auto simp: list_all_iff prod_set_defs)
      have "comma_weighted_crt_shape (Suc branch_axis)
          (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
        using Comma_Weighted_CRT_Branch.IH edge child_shape edge_pair
        by (auto simp: prod_set_defs)
      then show "case edge of (weight, child) \<Rightarrow>
          comma_weighted_crt_shape (Suc branch_axis)
            (snd (comma_weighted_crt_cofactor_all_raw axis slot child))"
        using edge_pair by simp
    qed
    show ?thesis
      using False lower_branch branch_axis length_rows children_shape
      by (simp add: Let_def case_prod_unfold list_all_iff prod_set_defs)
  qed
qed

lemma comma_weighted_crt_eval_mod_924:
  assumes tree: "comma_weighted_crt_wellformed tree"
  shows "comma_weighted_crt_eval tree (phase mod 924) =
    comma_weighted_crt_eval tree phase"
  using tree
proof (induction tree)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by simp
next
  case (Comma_Weighted_CRT_Branch axis rows)
  have axis: "axis<4"
    and extent: "length rows=comma_crt_axis_radix axis"
    and children:
      "list_all (\<lambda>(weight,child). comma_weighted_crt_wellformed child) rows"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  have radix_divides: "comma_crt_axis_radix axis dvd 924"
    by (rule comma_crt_axis_radices_divide_924[OF axis])
  have index:
    "(phase mod 924) mod comma_crt_axis_radix axis =
      phase mod comma_crt_axis_radix axis"
    by (rule mod_mod_cancel[OF radix_divides])
  have selected_bound:
      "phase mod comma_crt_axis_radix axis<length rows"
    using comma_weighted_crt_axis_positive[OF axis] extent by simp
  obtain weight child where selected:
      "rows!(phase mod comma_crt_axis_radix axis)=(weight,child)"
    by (cases "rows!(phase mod comma_crt_axis_radix axis)") auto
  have child_member: "(weight,child)\<in>set rows"
    using nth_mem[OF selected_bound] selected by simp
  have child_wellformed: "comma_weighted_crt_wellformed child"
    using children child_member by (auto simp: list_all_iff prod_set_defs)
  have child_periodic:
      "comma_weighted_crt_eval child (phase mod 924) =
        comma_weighted_crt_eval child phase"
    using Comma_Weighted_CRT_Branch.IH child_member child_wellformed
    by (auto simp: prod_set_defs)
  have evaluated_at_phase:
      "comma_weighted_crt_eval
          (Comma_Weighted_CRT_Branch axis rows) phase =
        map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
          (comma_weighted_crt_eval child phase)"
    using comma_weighted_crt_eval_branch[OF axis extent, of phase] selected
      selected_bound by simp
  have evaluated_at_reduced_phase:
      "comma_weighted_crt_eval
          (Comma_Weighted_CRT_Branch axis rows) (phase mod 924) =
        map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
          (comma_weighted_crt_eval child (phase mod 924))"
    using comma_weighted_crt_eval_branch[OF axis extent, of "phase mod 924"]
      selected index selected_bound by simp
  show ?case using evaluated_at_phase evaluated_at_reduced_phase child_periodic
    by simp
qed

lemma comma_weighted_crt_cofactor_all_raw_apply:
  assumes axis: "axis<4"
    and slot: "slot<comma_crt_axis_radix axis"
    and tree: "comma_weighted_crt_wellformed tree"
  shows "comma_weighted_crt_apply
      (comma_weighted_crt_cofactor_all_raw axis slot tree) phase =
    comma_weighted_crt_eval tree (comma_crt_rebase axis slot phase)"
  using tree
proof (induction tree arbitrary: phase)
  case (Comma_Weighted_CRT_Leaf control)
  then show ?case by (simp add: comma_weighted_crt_apply_def)
next
  case (Comma_Weighted_CRT_Branch branch_axis rows)
  have branch_axis: "branch_axis<4"
    and length_rows: "length rows=comma_crt_axis_radix branch_axis"
    and children:
      "list_all (\<lambda>(weight,child). comma_weighted_crt_wellformed child) rows"
    using Comma_Weighted_CRT_Branch.prems by simp_all
  show ?case
  proof (cases "branch_axis=axis")
    case True
    have selected_bound: "slot<length rows"
      using slot length_rows True by simp
    obtain weight child where selected: "rows!slot=(weight,child)"
      by (cases "rows!slot") auto
    have child_member: "(weight,child)\<in>set rows"
      using nth_mem[OF selected_bound] selected by simp
    have child_wellformed: "comma_weighted_crt_wellformed child"
      using children child_member by (auto simp: list_all_iff prod_set_defs)
    have child_exact:
      "comma_weighted_crt_apply
          (comma_weighted_crt_cofactor_all_raw axis slot child) phase =
        comma_weighted_crt_eval child (comma_crt_rebase axis slot phase)"
      using Comma_Weighted_CRT_Branch.IH child_member child_wellformed
      by (auto simp: prod_set_defs)
    have selected_rebase:
      "comma_crt_rebase axis slot phase mod comma_crt_axis_radix axis=slot"
      by (rule comma_crt_rebase_selected_axis[OF axis slot])
    have original_eval:
      "comma_weighted_crt_eval
          (Comma_Weighted_CRT_Branch branch_axis rows)
          (comma_crt_rebase axis slot phase) =
        map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
          (comma_weighted_crt_eval child (comma_crt_rebase axis slot phase))"
      using True branch_axis length_rows selected selected_bound selected_rebase
      by (simp add: comma_weighted_crt_eval_branch)
    show ?thesis
      using True selected selected_bound child_exact original_eval
      by (simp add: Let_def comma_weighted_crt_apply_add_offset algebra_simps)
  next
    case False
    have index_bound:
      "phase mod comma_crt_axis_radix branch_axis<length rows"
      using length_rows comma_weighted_crt_axis_positive[OF branch_axis]
      by simp
    obtain weight child where selected:
        "rows!(phase mod comma_crt_axis_radix branch_axis)=(weight,child)"
      by (cases "rows!(phase mod comma_crt_axis_radix branch_axis)") auto
    have child_member: "(weight,child)\<in>set rows"
      using nth_mem[OF index_bound] selected by simp
    have child_wellformed: "comma_weighted_crt_wellformed child"
      using children child_member by (auto simp: list_all_iff prod_set_defs)
    have child_exact:
      "comma_weighted_crt_apply
          (comma_weighted_crt_cofactor_all_raw axis slot child) phase =
        comma_weighted_crt_eval child (comma_crt_rebase axis slot phase)"
      using Comma_Weighted_CRT_Branch.IH child_member child_wellformed
      by (auto simp: prod_set_defs)
    have other_coordinate:
      "comma_crt_rebase axis slot phase mod
          comma_crt_axis_radix branch_axis =
        phase mod comma_crt_axis_radix branch_axis"
    proof -
      have distinct: "axis\<noteq>branch_axis" using False by auto
      show ?thesis
        by (rule comma_crt_rebase_other_axis[OF axis branch_axis distinct])
    qed
    have original_eval:
      "comma_weighted_crt_eval
          (Comma_Weighted_CRT_Branch branch_axis rows)
          (comma_crt_rebase axis slot phase) =
        map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
          (comma_weighted_crt_eval child (comma_crt_rebase axis slot phase))"
      using False branch_axis length_rows other_coordinate selected index_bound
      by (simp add: comma_weighted_crt_eval_branch)
    have restricted_eval:
      "comma_weighted_crt_eval
          (Comma_Weighted_CRT_Branch branch_axis
            (map (\<lambda>(old_weight,old_child).
              (old_weight+
                 fst (comma_weighted_crt_cofactor_all_raw axis slot old_child),
               snd (comma_weighted_crt_cofactor_all_raw axis slot old_child))) rows))
          phase =
        map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
          (comma_weighted_crt_eval child
            (comma_crt_rebase axis slot phase))"
    proof -
      let ?restricted_rows = "map (\<lambda>(old_weight,old_child).
        (old_weight+
          fst (comma_weighted_crt_cofactor_all_raw axis slot old_child),
         snd (comma_weighted_crt_cofactor_all_raw axis slot old_child))) rows"
      let ?child_action = "comma_weighted_crt_cofactor_all_raw axis slot child"
      have child_apply:
        "map_option (\<lambda>(control,elapsed). (control,fst ?child_action+elapsed))
            (comma_weighted_crt_eval (snd ?child_action) phase) =
          comma_weighted_crt_eval child (comma_crt_rebase axis slot phase)"
        using child_exact by (simp add: comma_weighted_crt_apply_def)
      have branch_eval:
        "comma_weighted_crt_eval
            (Comma_Weighted_CRT_Branch branch_axis ?restricted_rows) phase =
          map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
            (map_option (\<lambda>(control,elapsed).
              (control,fst ?child_action+elapsed))
              (comma_weighted_crt_eval (snd ?child_action) phase))"
        using branch_axis length_rows index_bound selected False
        by (simp add: comma_weighted_crt_eval_branch nth_map
          option.map_comp o_def case_prod_unfold algebra_simps)
      have lifted_child:
        "map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
            (map_option (\<lambda>(control,elapsed).
              (control,fst ?child_action+elapsed))
              (comma_weighted_crt_eval (snd ?child_action) phase)) =
          map_option (\<lambda>(control,elapsed). (control,weight+elapsed))
            (comma_weighted_crt_eval child
              (comma_crt_rebase axis slot phase))"
        by (rule arg_cong[OF child_apply])
      show ?thesis
        using branch_eval lifted_child by simp
    qed
    show ?thesis
      using False branch_axis child_exact original_eval restricted_eval
      by (simp add: comma_weighted_crt_apply_def Let_def option.map_id)
  qed
qed

definition comma_weighted_crt_reconstruct_all_cofactors ::
    "nat \<Rightarrow> 'a comma_semantic_weighted_crt_dag \<Rightarrow>
      'a comma_semantic_weighted_crt_dag" where
  "comma_weighted_crt_reconstruct_all_cofactors axis tree =
    Comma_Weighted_CRT_Branch axis
      (map (\<lambda>slot.
        comma_weighted_crt_cofactor_all_raw axis slot tree)
        [0..<comma_crt_axis_radix axis])"

lemma comma_weighted_crt_reconstruct_all_cofactors_exact:
  assumes axis: "axis<4"
    and tree: "comma_weighted_crt_wellformed tree"
  shows "comma_weighted_crt_eval
      (comma_weighted_crt_reconstruct_all_cofactors axis tree) phase =
    comma_weighted_crt_eval tree phase"
proof -
  let ?radix = "comma_crt_axis_radix axis"
  let ?rows = "map (\<lambda>slot.
    comma_weighted_crt_cofactor_all_raw axis slot tree) [0..<?radix]"
  have radix_positive: "0<?radix"
    by (rule comma_weighted_crt_axis_positive[OF axis])
  have extent: "length ?rows=?radix" by simp
  have index_bound: "phase mod ?radix<length ?rows"
    using radix_positive extent by simp
  have selected_slot: "phase mod ?radix< ?radix"
    using radix_positive by simp
  have selected_row:
      "?rows!(phase mod ?radix) =
        comma_weighted_crt_cofactor_all_raw axis (phase mod ?radix) tree"
    using index_bound by (simp add: nth_map)
  have branch_eval:
      "comma_weighted_crt_eval
          (Comma_Weighted_CRT_Branch axis ?rows) phase =
        comma_weighted_crt_apply
          (comma_weighted_crt_cofactor_all_raw axis (phase mod ?radix) tree) phase"
    using comma_weighted_crt_branch_apply[OF axis extent, of phase]
      selected_row by simp
  have exact_cofactor:
      "comma_weighted_crt_apply
          (comma_weighted_crt_cofactor_all_raw axis (phase mod ?radix) tree) phase =
        comma_weighted_crt_eval tree
          (comma_crt_rebase axis (phase mod ?radix) phase)"
    by (rule comma_weighted_crt_cofactor_all_raw_apply
      [OF axis selected_slot tree])
  have selected_rebase:
      "comma_crt_rebase axis (phase mod ?radix) phase = phase mod 924"
    by (rule comma_crt_rebase_selected[OF axis selected_slot refl])
  have periodic:
      "comma_weighted_crt_eval tree (phase mod 924) =
        comma_weighted_crt_eval tree phase"
    by (rule comma_weighted_crt_eval_mod_924[OF tree])
  show ?thesis
    unfolding comma_weighted_crt_reconstruct_all_cofactors_def
    using branch_eval exact_cofactor selected_rebase periodic by simp
qed

lemma comma_weighted_crt_reconstruct_rows_apply:
  fixes offset axis phase :: nat
    and tree :: "'a comma_semantic_weighted_crt_dag"
    and rows :: "(nat \<times> 'a comma_semantic_weighted_crt_dag) list"
  assumes axis: "axis<4"
    and tree: "comma_weighted_crt_wellformed tree"
    and extent: "length rows=comma_crt_axis_radix axis"
    and row_exact:
      "\<And>slot. slot<comma_crt_axis_radix axis \<Longrightarrow>
        comma_weighted_crt_apply
          (comma_weighted_crt_cofactor_all_raw axis slot tree) phase =
        comma_weighted_crt_apply (rows!slot) phase"
  shows "comma_weighted_crt_apply (offset,tree) phase =
    comma_weighted_crt_apply
      (offset,Comma_Weighted_CRT_Branch axis rows) phase"
proof -
  let ?radix = "comma_crt_axis_radix axis"
  let ?cofactors = "map (\<lambda>slot.
    comma_weighted_crt_cofactor_all_raw axis slot tree) [0..<?radix]"
  have cofactor_extent: "length ?cofactors=?radix"
    by simp
  have cofactor_selected:
      "\<And>slot. slot<?radix \<Longrightarrow>
        ?cofactors!slot=comma_weighted_crt_cofactor_all_raw axis slot tree"
  proof -
    fix slot assume slot: "slot<?radix"
    show "?cofactors!slot=comma_weighted_crt_cofactor_all_raw axis slot tree"
      using slot by (simp add: nth_map)
  qed
  have branch_exact:
      "comma_weighted_crt_apply (offset,Comma_Weighted_CRT_Branch axis
          ?cofactors) phase =
        comma_weighted_crt_apply (offset,Comma_Weighted_CRT_Branch axis rows)
          phase"
  proof (rule comma_weighted_crt_branch_congruence
      [OF axis cofactor_extent extent])
    fix slot assume slot: "slot<?radix"
    show "comma_weighted_crt_apply (?cofactors!slot) phase =
        comma_weighted_crt_apply (rows!slot) phase"
      using row_exact[OF slot] cofactor_selected[OF slot] by simp
  qed
  have reconstructed:
      "comma_weighted_crt_apply (offset,tree) phase =
        comma_weighted_crt_apply
          (offset,Comma_Weighted_CRT_Branch axis ?cofactors) phase"
    using comma_weighted_crt_reconstruct_all_cofactors_exact[OF axis tree,
        of phase]
    by (simp add: comma_weighted_crt_apply_def
        comma_weighted_crt_reconstruct_all_cofactors_def)
  show ?thesis
    by (rule trans[OF reconstructed branch_exact])
qed

lemma comma_weighted_crt_reconstruct_all_cofactors_shape:
  assumes axis: "axis<4"
    and children:
      "list_all (\<lambda>slot. comma_weighted_crt_shape (Suc axis)
        (snd (comma_weighted_crt_cofactor_all_raw axis slot tree)))
        [0..<comma_crt_axis_radix axis]"
  shows "comma_weighted_crt_shape axis
      (comma_weighted_crt_reconstruct_all_cofactors axis tree)"
  using axis children
  by (simp add: comma_weighted_crt_reconstruct_all_cofactors_def
      list_all_iff prod_set_defs case_prod_unfold)

text \<open>
This adversarial diagram repeats coordinate 0 below coordinate 1.  The test
selects slot 1 at coordinate 0 while evaluating at phase 0; a one-level
cofactor would incorrectly select nested slot 0.  Distinct edge weights also
check that the selected nested weight is added to the root offset.
\<close>

definition comma_weighted_crt_cofactor_adversarial_tree ::
    "nat comma_semantic_weighted_crt_dag" where
  "comma_weighted_crt_cofactor_adversarial_tree =
    Comma_Weighted_CRT_Branch 0
      (map (\<lambda>outer.
        (Suc outer,
          Comma_Weighted_CRT_Branch 1
            (map (\<lambda>middle.
              (10*middle,
                Comma_Weighted_CRT_Branch 0
                  (map (\<lambda>inner.
                    (100*inner, Comma_Weighted_CRT_Leaf
                      (100*outer+10*middle+inner))) [0..<4])))
              [0..<3]))) [0..<4])"

lemma comma_weighted_crt_cofactor_adversarial_tree_wellformed:
  "comma_weighted_crt_wellformed
    comma_weighted_crt_cofactor_adversarial_tree"
  unfolding comma_weighted_crt_cofactor_adversarial_tree_def
  by code_simp

lemma comma_weighted_crt_cofactor_repeated_axis_selects_every_occurrence:
  "comma_weighted_crt_apply
      (comma_weighted_crt_cofactor_all_raw 0 1
        comma_weighted_crt_cofactor_adversarial_tree) 0 = Some (101,102)"
  unfolding comma_weighted_crt_cofactor_adversarial_tree_def
  by code_simp

lemma comma_weighted_crt_cofactor_guard_rejects_invalid_shapes:
  "comma_weighted_crt_cofactor_all 4 0
      comma_weighted_crt_cofactor_adversarial_tree = None
    \<and> comma_weighted_crt_cofactor_all 0 4
      comma_weighted_crt_cofactor_adversarial_tree = None
    \<and> comma_weighted_crt_cofactor_all 0 0
      (Comma_Weighted_CRT_Branch 0
        [(0,Comma_Weighted_CRT_Leaf 1),
         (0,Comma_Weighted_CRT_Leaf 2),
         (0,Comma_Weighted_CRT_Leaf 3)]) = None"
  unfolding comma_weighted_crt_cofactor_all_def
    comma_weighted_crt_cofactor_adversarial_tree_def
  by code_simp

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "All-occurrence weighted CRT cofactor and reconstruction laws"
    @{thms comma_weighted_crt_cofactor_all_guarded_exact
      comma_weighted_crt_cofactor_all_rejects
      comma_weighted_crt_cofactor_all_raw_wellformed
      comma_weighted_crt_cofactor_all_raw_absent
      comma_weighted_crt_cofactor_all_raw_shape
      comma_weighted_crt_shape_lower_mono
      comma_weighted_crt_eval_mod_924
      comma_weighted_crt_cofactor_all_raw_apply
      comma_weighted_crt_reconstruct_all_cofactors_exact
      comma_weighted_crt_reconstruct_rows_apply
      comma_weighted_crt_reconstruct_all_cofactors_shape
      comma_weighted_crt_cofactor_adversarial_tree_wellformed
      comma_weighted_crt_cofactor_repeated_axis_selects_every_occurrence
      comma_weighted_crt_cofactor_guard_rejects_invalid_shapes};
\<close>

end
