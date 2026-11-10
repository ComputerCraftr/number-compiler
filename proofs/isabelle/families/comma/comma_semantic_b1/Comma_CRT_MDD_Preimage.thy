theory Comma_CRT_MDD_Preimage
  imports Comma_CRT_MDD_Extension
begin

text \<open>A cofactor leaves a diagram unchanged when its next axis is later than
the requested axis, and selects exactly one child when the axes agree.  It
rejects requests that would skip an earlier axis or select an invalid slot.\<close>

definition comma_crt_mdd_cofactor ::
    "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_crt_mdd_cofactor radices nodes axis slot root =
    (if axis < length radices \<and> 0 < radices ! axis \<and>
         slot < radices ! axis \<and> root < length nodes then
       (case nodes ! root of
          Comma_CRT_MDD_Leaf _ \<Rightarrow> Some root
        | Comma_CRT_MDD_Branch node_axis children \<Rightarrow>
            if node_axis < length radices \<and> 0 < radices ! node_axis \<and>
                 length children = radices ! node_axis then
              (if node_axis = axis then Some (children ! slot)
               else if axis < node_axis then Some root else None)
            else None)
     else None)"

lemma comma_crt_mdd_cofactor_below:
  assumes node_bound: "root < length nodes"
    and ordered: "comma_crt_mdd_node_ordered radices nodes root"
    and cofactor: "comma_crt_mdd_cofactor radices nodes axis slot root = Some root"
  shows "case nodes ! root of
    Comma_CRT_MDD_Leaf _ \<Rightarrow> True
  | Comma_CRT_MDD_Branch node_axis _ \<Rightarrow> axis < node_axis"
  using node_bound ordered cofactor
  by (auto simp: comma_crt_mdd_cofactor_def comma_crt_mdd_node_ordered_def
      split: comma_crt_mdd_node.splits if_splits)

lemma comma_crt_mdd_eval_raw_irrelevant_below:
  assumes root_bound: "root < length nodes"
    and wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and below: "case nodes ! root of
      Comma_CRT_MDD_Leaf _ \<Rightarrow> True
    | Comma_CRT_MDD_Branch node_axis _ \<Rightarrow> axis < node_axis"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate root =
    comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot)) root"
  using root_bound wellformed below
proof (induction root rule: less_induct)
  case (less root)
  have root_order:
    "comma_crt_mdd_node_ordered radices nodes root"
    using less.prems(2) less.prems(1)
    unfolding comma_crt_mdd_table_wellformed_def by blast
  show ?case
  proof (cases "nodes ! root")
    case (Comma_CRT_MDD_Leaf payload)
    have original_leaf:
      "comma_crt_mdd_eval_raw radices nodes coordinate root = Some payload"
      by (rule comma_crt_mdd_eval_raw_leaf[OF less.prems(1)
        Comma_CRT_MDD_Leaf])
    have changed_leaf:
      "comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot)) root =
        Some payload"
      by (rule comma_crt_mdd_eval_raw_leaf[OF less.prems(1)
        Comma_CRT_MDD_Leaf])
    show ?thesis by (simp only: original_leaf changed_leaf)
  next
    case (Comma_CRT_MDD_Branch node_axis children)
    have axis_before: "axis < node_axis"
      using less.prems(3) Comma_CRT_MDD_Branch by simp
    have node_order_facts:
      "node_axis < length radices"
      "0 < radices ! node_axis"
      "length children = radices ! node_axis"
      "\<forall>child\<in>set children. child < root \<and>
        (case comma_crt_mdd_node_axis (nodes ! child) of
           None \<Rightarrow> True
         | Some child_axis \<Rightarrow> node_axis < child_axis)"
      using root_order Comma_CRT_MDD_Branch less.prems(1)
      by (auto simp: comma_crt_mdd_node_ordered_def)
    let ?child = "children ! (coordinate node_axis mod radices ! node_axis)"
    have child_position:
      "coordinate node_axis mod radices ! node_axis < length children"
      using node_order_facts(2-3) by simp
    have child_member: "?child \<in> set children"
      using child_position by (rule nth_mem)
    have child_bound_root: "?child < root"
      using node_order_facts(4) node_order_facts(3)
      using child_member by blast
    have child_bound_table: "?child < length nodes"
      using child_bound_root less.prems(1) by arith
    have child_below:
      "case nodes ! ?child of
        Comma_CRT_MDD_Leaf _ \<Rightarrow> True
      | Comma_CRT_MDD_Branch child_axis _ \<Rightarrow> axis < child_axis"
      using node_order_facts(4) child_member axis_before
      by (cases "nodes ! ?child") (auto simp: comma_crt_mdd_node_axis.simps)
    have child_irrelevant:
      "comma_crt_mdd_eval_raw radices nodes coordinate ?child =
        comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot)) ?child"
      by (rule less.IH[OF child_bound_root child_bound_table
        less.prems(2) child_below])
    have coordinate_same:
      "(coordinate(axis := slot)) node_axis = coordinate node_axis"
      using axis_before by simp
    have source_step:
      "comma_crt_mdd_eval_raw radices nodes coordinate root =
        comma_crt_mdd_eval_raw radices nodes coordinate ?child"
    proof (rule comma_crt_mdd_eval_raw_branch)
      show "root < length nodes" by (rule less.prems(1))
      show "nodes ! root = Comma_CRT_MDD_Branch node_axis children"
        by (rule Comma_CRT_MDD_Branch)
      show "node_axis < length radices" by (rule node_order_facts(1))
      show "0 < radices ! node_axis" by (rule node_order_facts(2))
      show "length children = radices ! node_axis" by (rule node_order_facts(3))
      show "?child = children ! (coordinate node_axis mod radices ! node_axis)"
        by simp
      show "?child < root" by (rule child_bound_root)
    qed
    have changed_step:
      "comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot)) root =
        comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot)) ?child"
    proof (rule comma_crt_mdd_eval_raw_branch)
      show "root < length nodes" by (rule less.prems(1))
      show "nodes ! root = Comma_CRT_MDD_Branch node_axis children"
        by (rule Comma_CRT_MDD_Branch)
      show "node_axis < length radices" by (rule node_order_facts(1))
      show "0 < radices ! node_axis" by (rule node_order_facts(2))
      show "length children = radices ! node_axis" by (rule node_order_facts(3))
      show "?child = children ! ((coordinate(axis := slot)) node_axis mod
          radices ! node_axis)"
        using axis_before by simp
      show "?child < root" by (rule child_bound_root)
    qed
    show ?thesis
    proof -
      have "comma_crt_mdd_eval_raw radices nodes coordinate root =
          comma_crt_mdd_eval_raw radices nodes coordinate ?child"
        by (rule source_step)
      also have "... = comma_crt_mdd_eval_raw radices nodes
          (coordinate(axis := slot)) ?child"
        by (rule child_irrelevant)
      also have "... = comma_crt_mdd_eval_raw radices nodes
          (coordinate(axis := slot)) root"
        by (rule changed_step[symmetric])
      finally show ?thesis .
    qed
  qed
qed

lemma comma_crt_mdd_cofactor_select:
  assumes node_bound: "root < length nodes"
    and radix: "axis < length radices"
    and positive: "0 < radices ! axis"
    and slot: "slot < radices ! axis"
    and wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and selected: "comma_crt_mdd_cofactor radices nodes axis slot root = Some child"
  shows "comma_crt_mdd_eval_raw radices nodes
      (coordinate(axis := slot)) root =
    comma_crt_mdd_eval_raw radices nodes coordinate child"
proof (cases "nodes ! root")
  case (Comma_CRT_MDD_Leaf payload)
  then have child: "child = root"
    using selected node_bound radix positive slot
    by (simp add: comma_crt_mdd_cofactor_def)
  have original:
    "comma_crt_mdd_eval_raw radices nodes
        (coordinate(axis := slot)) root = Some payload"
    by (rule comma_crt_mdd_eval_raw_leaf[OF node_bound Comma_CRT_MDD_Leaf])
  have selected_value:
    "comma_crt_mdd_eval_raw radices nodes coordinate child = Some payload"
  proof -
    have "comma_crt_mdd_eval_raw radices nodes coordinate root = Some payload"
      by (rule comma_crt_mdd_eval_raw_leaf[OF node_bound Comma_CRT_MDD_Leaf])
    then show ?thesis using child by simp
  qed
  show ?thesis using original selected_value by simp
next
  case (Comma_CRT_MDD_Branch node_axis children)
  show ?thesis
  proof (cases "axis = node_axis")
    case True
    have ordered:
      "comma_crt_mdd_node_ordered radices nodes root"
      using wellformed node_bound
      unfolding comma_crt_mdd_table_wellformed_def by blast
    have node_width: "length children = radices ! node_axis"
      using ordered node_bound Comma_CRT_MDD_Branch
      by (auto simp: comma_crt_mdd_node_ordered_def)
    have child: "child = children ! slot"
      using selected node_bound radix positive slot node_width True
        Comma_CRT_MDD_Branch
      by (auto simp: comma_crt_mdd_cofactor_def)
    have width: "length children = radices ! axis"
      and child_order: "\<forall>child\<in>set children. child < root"
      using ordered node_bound Comma_CRT_MDD_Branch True
      by (auto simp: comma_crt_mdd_node_ordered_def)
    have child_axis_order:
      "\<forall>item\<in>set children. item < root \<and>
        (case comma_crt_mdd_node_axis (nodes ! item) of
           None \<Rightarrow> True | Some child_axis \<Rightarrow> axis < child_axis)"
      using ordered node_bound Comma_CRT_MDD_Branch True
      by (auto simp: comma_crt_mdd_node_ordered_def)
    have selected_bound: "children ! slot < root"
    proof -
      have position: "slot < length children" using width slot by simp
      have member: "children ! slot \<in> set children" by (rule nth_mem[OF position])
      show ?thesis using child_order member by blast
    qed
    have selected_member: "children ! slot \<in> set children"
      using width slot positive by (auto intro: nth_mem)
    have child_later:
      "case nodes ! (children ! slot) of
        Comma_CRT_MDD_Leaf _ \<Rightarrow> True
      | Comma_CRT_MDD_Branch child_axis _ \<Rightarrow> axis < child_axis"
      using child_axis_order selected_member
      by (cases "nodes ! (children ! slot)")
        (auto simp: comma_crt_mdd_node_axis.simps)
    have original_step:
      "comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot)) root =
        comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot))
          (children ! slot)"
    proof (rule comma_crt_mdd_eval_raw_branch)
      show "root < length nodes" by (rule node_bound)
      show "nodes ! root = Comma_CRT_MDD_Branch node_axis children"
        by (rule Comma_CRT_MDD_Branch)
      show "node_axis < length radices" using True radix by simp
      show "0 < radices ! node_axis" using True positive by simp
      show "length children = radices ! node_axis"
        using True width by simp
      show "children ! slot = children ! ((coordinate(axis := slot)) node_axis mod
          radices ! node_axis)"
        using True slot positive by simp
      show "children ! slot < root" by (rule selected_bound)
    qed
    have selected_in_table: "children ! slot < length nodes"
      using selected_bound node_bound by arith
    have child_irrelevant:
      "comma_crt_mdd_eval_raw radices nodes coordinate (children ! slot) =
        comma_crt_mdd_eval_raw radices nodes
          (coordinate(axis := slot)) (children ! slot)"
      by (rule comma_crt_mdd_eval_raw_irrelevant_below
        [OF selected_in_table wellformed child_later])
    have selected_eval:
      "comma_crt_mdd_eval_raw radices nodes coordinate child =
        comma_crt_mdd_eval_raw radices nodes coordinate (children ! slot)"
      using child by simp
    show ?thesis using original_step child_irrelevant selected_eval by simp
  next
    case False
    have axis_below: "axis < node_axis"
      using selected node_bound False Comma_CRT_MDD_Branch
      by (auto simp: comma_crt_mdd_cofactor_def split: if_splits)
    have child: "child = root"
      using selected node_bound axis_below Comma_CRT_MDD_Branch
      by (auto simp: comma_crt_mdd_cofactor_def split: if_splits)
    have below:
      "case nodes ! root of
        Comma_CRT_MDD_Leaf _ \<Rightarrow> True
      | Comma_CRT_MDD_Branch branch_axis _ \<Rightarrow> axis < branch_axis"
      using Comma_CRT_MDD_Branch axis_below by simp
    have irrelevant:
      "comma_crt_mdd_eval_raw radices nodes coordinate root =
        comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot)) root"
      by (rule comma_crt_mdd_eval_raw_irrelevant_below
        [OF node_bound wellformed below])
    show ?thesis using child irrelevant by simp
  qed
qed

lemma comma_crt_mdd_cofactor_current_eval:
  assumes node_bound: "root < length nodes"
    and wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and radix: "axis < length radices"
    and positive: "0 < radices ! axis"
    and slot: "slot < radices ! axis"
    and coordinate_slot: "coordinate axis mod radices ! axis = slot"
    and selected:
      "comma_crt_mdd_cofactor radices nodes axis slot root = Some child"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate root =
    comma_crt_mdd_eval_raw radices nodes coordinate child"
proof -
  have congruent:
    "\<And>current_axis. current_axis < length radices \<Longrightarrow>
      coordinate current_axis mod radices ! current_axis =
        (coordinate(axis := slot)) current_axis mod radices ! current_axis"
  proof -
    fix current_axis
    assume current_axis: "current_axis < length radices"
    show "coordinate current_axis mod radices ! current_axis =
        (coordinate(axis := slot)) current_axis mod radices ! current_axis"
    proof (cases "current_axis = axis")
      case True
      then show ?thesis using coordinate_slot slot by simp
    next
      case False then show ?thesis by simp
    qed
  qed
  have coordinate_evaluation:
    "comma_crt_mdd_eval_raw radices nodes coordinate root =
      comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot)) root"
    by (rule comma_crt_mdd_eval_raw_coordinate_congruent[OF wellformed congruent])
  have selected_update:
    "comma_crt_mdd_eval_raw radices nodes (coordinate(axis := slot)) root =
      comma_crt_mdd_eval_raw radices nodes coordinate child"
    by (rule comma_crt_mdd_cofactor_select
      [OF node_bound radix positive slot wellformed selected])
  show ?thesis using coordinate_evaluation selected_update by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Shared MDD cofactor preserves selected coordinates"
    @{thms comma_crt_mdd_eval_raw_irrelevant_below
      comma_crt_mdd_cofactor_select comma_crt_mdd_cofactor_current_eval};
\<close>

end
