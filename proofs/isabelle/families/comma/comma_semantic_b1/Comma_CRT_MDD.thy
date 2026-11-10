theory Comma_CRT_MDD
  imports Main
begin

lemma comma_crt_mdd_indexed_allD:
  assumes checked: "list_all P [0..<n]" and index: "i<n"
  shows "P i"
  using checked index by (auto simp: list_all_iff)

ML_file "../comma_entry_arithmetic/Proof_Dependency_Audit.ML"

text \<open>
Compact reduced ordered MDDs use a flat, immutable node table.  Branches refer
to earlier node identifiers, retaining DAG sharing.  Axis numbers index an
explicit radix list, so [3,4,11,7] is represented directly rather than being
coerced into the legacy comma_crt_column ordering.  Evaluation returns an
outer option: None means malformed table/root; a valid leaf may itself carry
None to mean that the certified one-step action is not Continue.
\<close>

datatype 'a comma_crt_mdd_node =
    Comma_CRT_MDD_Leaf 'a
  | Comma_CRT_MDD_Branch nat "nat list"

fun comma_crt_mdd_node_map :: "('a \<Rightarrow> 'b) \<Rightarrow>
    'a comma_crt_mdd_node \<Rightarrow> 'b comma_crt_mdd_node" where
  "comma_crt_mdd_node_map project (Comma_CRT_MDD_Leaf value) =
      Comma_CRT_MDD_Leaf (project value)"
| "comma_crt_mdd_node_map project (Comma_CRT_MDD_Branch axis children) =
      Comma_CRT_MDD_Branch axis children"

fun comma_crt_mdd_node_axis :: "'a comma_crt_mdd_node \<Rightarrow> nat option" where
  "comma_crt_mdd_node_axis (Comma_CRT_MDD_Leaf _) = None"
| "comma_crt_mdd_node_axis (Comma_CRT_MDD_Branch axis _) = Some axis"

lemma comma_crt_mdd_node_axis_map:
  "comma_crt_mdd_node_axis (comma_crt_mdd_node_map project node) =
    comma_crt_mdd_node_axis node"
  by (cases node) simp_all

definition comma_crt_mdd_map_nodes :: "('a \<Rightarrow> 'b) \<Rightarrow>
    'a comma_crt_mdd_node list \<Rightarrow> 'b comma_crt_mdd_node list" where
  "comma_crt_mdd_map_nodes project nodes = map (comma_crt_mdd_node_map project) nodes"

definition comma_crt_mdd_node_ordered ::
    "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_crt_mdd_node_ordered radices nodes root \<longleftrightarrow>
    (root < length nodes \<longrightarrow>
      (case nodes ! root of
         Comma_CRT_MDD_Leaf _ \<Rightarrow> True
       | Comma_CRT_MDD_Branch axis children \<Rightarrow>
           axis < length radices \<and> 0 < radices ! axis \<and>
           length children = radices ! axis \<and>
           (\<forall>child\<in>set children. child < root \<and>
             (case comma_crt_mdd_node_axis (nodes ! child) of
                None \<Rightarrow> True
              | Some child_axis \<Rightarrow> axis < child_axis))))"

lemma comma_crt_mdd_node_ordered_leaf_intro:
  assumes root: "root < length nodes"
    and node: "nodes ! root = Comma_CRT_MDD_Leaf payload"
  shows "comma_crt_mdd_node_ordered radices nodes root"
  using root node by (simp add: comma_crt_mdd_node_ordered_def)

lemma comma_crt_mdd_node_ordered_branch_intro:
  assumes root: "root < length nodes"
    and node: "nodes ! root = Comma_CRT_MDD_Branch axis children"
    and axis: "axis < length radices"
    and positive: "0 < radices ! axis"
    and width: "length children = radices ! axis"
    and child_order:
      "list_all (\<lambda>child. child < root \<and>
        (case comma_crt_mdd_node_axis (nodes ! child) of
           None \<Rightarrow> True
         | Some child_axis \<Rightarrow> axis < child_axis)) children"
  shows "comma_crt_mdd_node_ordered radices nodes root"
  using assms
  by (simp add: comma_crt_mdd_node_ordered_def list_all_iff)

definition comma_crt_mdd_table_wellformed ::
    "nat list \<Rightarrow> 'a comma_crt_mdd_node list \<Rightarrow> bool" where
  "comma_crt_mdd_table_wellformed radices nodes \<longleftrightarrow>
    (\<forall>root < length nodes. comma_crt_mdd_node_ordered radices nodes root)"

definition comma_crt_mdd_table_reduced ::
    "nat list \<Rightarrow> 'a::equal comma_crt_mdd_node list \<Rightarrow> bool" where
  "comma_crt_mdd_table_reduced radices nodes \<longleftrightarrow>
    comma_crt_mdd_table_wellformed radices nodes \<and> distinct nodes \<and>
    (\<forall>root < length nodes. case nodes ! root of
       Comma_CRT_MDD_Leaf _ \<Rightarrow> True
     | Comma_CRT_MDD_Branch _ children \<Rightarrow>
         children \<noteq> [] \<and>
         \<not> list_all (\<lambda>child. child = hd children) children)"

function comma_crt_mdd_eval_raw :: "nat list \<Rightarrow>
    'a comma_crt_mdd_node list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    nat \<Rightarrow> 'a option" where
  "comma_crt_mdd_eval_raw radices nodes coordinate root =
    (if root < length nodes then
       (case nodes ! root of
          Comma_CRT_MDD_Leaf value \<Rightarrow> Some value
        | Comma_CRT_MDD_Branch axis children \<Rightarrow>
            if axis < length radices \<and> 0 < radices ! axis \<and>
                length children = radices ! axis then
              (let child = children ! (coordinate axis mod radices ! axis)
               in if child < root then
                    comma_crt_mdd_eval_raw radices nodes coordinate child
                  else None)
            else None)
     else None)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(radices,nodes,coordinate,root). root)") auto

text \<open>The recursive equation is for selected evaluation, not unrestricted
simplification beneath a symbolic coordinate or an induction hypothesis.\<close>
declare comma_crt_mdd_eval_raw.simps [simp del]

lemma comma_crt_mdd_eval_raw_leaf:
  assumes bound: "root < length nodes"
    and binding: "nodes ! root = Comma_CRT_MDD_Leaf value"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate root = Some value"
  using comma_crt_mdd_eval_raw.simps[of radices nodes coordinate root]
  by (simp only: bound if_True binding comma_crt_mdd_node.case)

lemma comma_crt_mdd_eval_raw_branch:
  assumes bound: "root < length nodes"
    and binding: "nodes ! root = Comma_CRT_MDD_Branch axis children"
    and axis: "axis < length radices"
    and positive: "0 < radices ! axis"
    and width: "length children = radices ! axis"
    and child: "child = children ! (coordinate axis mod radices ! axis)"
    and earlier: "child < root"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate root =
    comma_crt_mdd_eval_raw radices nodes coordinate child"
  using comma_crt_mdd_eval_raw.simps[of radices nodes coordinate root]
  by (simp only: bound if_True binding comma_crt_mdd_node.case
      axis positive width simp_thms Let_def child[symmetric] earlier)

lemma comma_crt_mdd_branch_facts:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and root_bound: "root < length nodes"
    and branch: "nodes ! root = Comma_CRT_MDD_Branch axis children"
  shows "axis < length radices"
    and "0 < radices ! axis"
    and "length children = radices ! axis"
    and "\<forall>child\<in>set children. child < root \<and>
      (case comma_crt_mdd_node_axis (nodes ! child) of
         None \<Rightarrow> True
       | Some child_axis \<Rightarrow> axis < child_axis)"
proof -
  have ordered: "comma_crt_mdd_node_ordered radices nodes root"
    using wellformed root_bound
    unfolding comma_crt_mdd_table_wellformed_def by blast
  show "axis < length radices"
    and "0 < radices ! axis"
    and "length children = radices ! axis"
    and "\<forall>child\<in>set children. child < root \<and>
      (case comma_crt_mdd_node_axis (nodes ! child) of
         None \<Rightarrow> True
       | Some child_axis \<Rightarrow> axis < child_axis)"
    using ordered root_bound branch
    by (auto simp: comma_crt_mdd_node_ordered_def)
qed

lemma comma_crt_mdd_eval_raw_branch_selected:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and root_bound: "root < length nodes"
    and branch: "nodes ! root = Comma_CRT_MDD_Branch axis children"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate root =
    comma_crt_mdd_eval_raw radices nodes coordinate
      (children ! (coordinate axis mod radices ! axis))"
proof -
  have facts:
      "axis < length radices"
      "0 < radices ! axis"
      "length children = radices ! axis"
      "\<forall>child\<in>set children. child < root \<and>
        (case comma_crt_mdd_node_axis (nodes ! child) of
           None \<Rightarrow> True
         | Some child_axis \<Rightarrow> axis < child_axis)"
    by (rule comma_crt_mdd_branch_facts[OF wellformed root_bound branch])+
  let ?child = "children ! (coordinate axis mod radices ! axis)"
  have index_bound: "coordinate axis mod radices ! axis < length children"
    using facts(2,3) by simp
  have child_member: "?child \<in> set children"
    by (rule nth_mem[OF index_bound])
  have child_bound: "?child < root"
    using facts(4) child_member by blast
  show ?thesis
    by (rule comma_crt_mdd_eval_raw_branch
        [where coordinate=coordinate,
         OF root_bound branch facts(1,2,3) refl child_bound])
qed

inductive comma_crt_mdd_payload_support ::
    "'a comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> bool"
  for nodes where
  payload_support_leaf:
    "\<lbrakk>root < length nodes;
      nodes ! root = Comma_CRT_MDD_Leaf payload\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_payload_support nodes root payload"
| payload_support_branch:
    "\<lbrakk>root < length nodes;
      nodes ! root = Comma_CRT_MDD_Branch axis children;
      child \<in> set children; child < root;
      comma_crt_mdd_payload_support nodes child payload\<rbrakk>
      \<Longrightarrow> comma_crt_mdd_payload_support nodes root payload"

lemma comma_crt_mdd_eval_raw_total:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
  shows "root < length nodes \<Longrightarrow>
    \<exists>payload. comma_crt_mdd_eval_raw radices nodes coordinate root = Some payload"
proof (induction root rule: less_induct)
  case (less root)
  assume root_bound: "root < length nodes"
  show "\<exists>payload. comma_crt_mdd_eval_raw radices nodes coordinate root = Some payload"
  proof (cases "nodes ! root")
    case (Comma_CRT_MDD_Leaf payload)
    have result:
        "comma_crt_mdd_eval_raw radices nodes coordinate root = Some payload"
      by (rule comma_crt_mdd_eval_raw_leaf[OF root_bound Comma_CRT_MDD_Leaf])
    then show ?thesis by blast
  next
    case (Comma_CRT_MDD_Branch axis children)
    have axis_bound: "axis < length radices"
      and positive: "0 < radices ! axis"
      and width: "length children = radices ! axis"
      and children_ordered:
        "\<forall>child\<in>set children. child < root \<and>
          (case comma_crt_mdd_node_axis (nodes ! child) of
             None \<Rightarrow> True
           | Some child_axis \<Rightarrow> axis < child_axis)"
      by (rule comma_crt_mdd_branch_facts[OF wellformed root_bound
          Comma_CRT_MDD_Branch])+
    let ?index = "coordinate axis mod radices ! axis"
    let ?child = "children ! ?index"
    have index_bound: "?index < length children"
      using positive width by simp
    have child_mem: "?child \<in> set children"
      by (rule nth_mem[OF index_bound])
    have child_bound: "?child < root"
      using children_ordered child_mem by blast
    have child_in_table: "?child < length nodes"
      using child_bound root_bound by arith
    obtain payload where child_result:
        "comma_crt_mdd_eval_raw radices nodes coordinate ?child = Some payload"
      using less.IH[OF child_bound child_in_table] by blast
    have step:
        "comma_crt_mdd_eval_raw radices nodes coordinate root =
          comma_crt_mdd_eval_raw radices nodes coordinate ?child"
      by (rule comma_crt_mdd_eval_raw_branch_selected
          [OF wellformed root_bound Comma_CRT_MDD_Branch])
    have exact:
        "comma_crt_mdd_eval_raw radices nodes coordinate root = Some payload"
      by (rule trans[OF step child_result])
    show ?thesis by (rule exI[of _ payload], rule exact)
  qed
qed

lemma comma_crt_mdd_eval_raw_some_supported:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
  shows "root < length nodes \<Longrightarrow>
    comma_crt_mdd_eval_raw radices nodes coordinate root = Some payload \<Longrightarrow>
    comma_crt_mdd_payload_support nodes root payload"
proof (induction root rule: less_induct)
  case (less root)
  assume root_bound: "root < length nodes"
    and result: "comma_crt_mdd_eval_raw radices nodes coordinate root = Some payload"
  show "comma_crt_mdd_payload_support nodes root payload"
  proof (cases "nodes ! root")
    case (Comma_CRT_MDD_Leaf label)
    have payload_eq: "label = payload"
      using result comma_crt_mdd_eval_raw_leaf[OF root_bound Comma_CRT_MDD_Leaf]
      by simp
    have support:
        "comma_crt_mdd_payload_support nodes root label"
      by (rule comma_crt_mdd_payload_support.payload_support_leaf
          [OF root_bound Comma_CRT_MDD_Leaf])
    show ?thesis using support payload_eq by simp
  next
    case (Comma_CRT_MDD_Branch axis children)
    have facts:
        "axis < length radices"
        "0 < radices ! axis"
        "length children = radices ! axis"
        "\<forall>child\<in>set children. child < root \<and>
          (case comma_crt_mdd_node_axis (nodes ! child) of
             None \<Rightarrow> True
           | Some child_axis \<Rightarrow> axis < child_axis)"
      by (rule comma_crt_mdd_branch_facts[OF wellformed root_bound
          Comma_CRT_MDD_Branch])+
    let ?child = "children ! (coordinate axis mod radices ! axis)"
    have index_bound: "coordinate axis mod radices ! axis < length children"
      using facts(2,3) by simp
    have child_mem: "?child \<in> set children"
      by (rule nth_mem[OF index_bound])
    have child_bound: "?child < root"
      using facts(4) child_mem by blast
    have child_in_table: "?child < length nodes"
      using child_bound root_bound by arith
    have step:
        "comma_crt_mdd_eval_raw radices nodes coordinate root =
          comma_crt_mdd_eval_raw radices nodes coordinate ?child"
      by (rule comma_crt_mdd_eval_raw_branch_selected
          [OF wellformed root_bound Comma_CRT_MDD_Branch])
    have child_result:
        "comma_crt_mdd_eval_raw radices nodes coordinate ?child = Some payload"
      using result step by simp
    have child_support:
        "comma_crt_mdd_payload_support nodes ?child payload"
      by (rule less.IH[OF child_bound child_in_table child_result])
    show ?thesis
      by (rule comma_crt_mdd_payload_support.payload_support_branch
          [OF root_bound Comma_CRT_MDD_Branch child_mem child_bound child_support])
  qed
qed

definition comma_crt_mdd_payload_cover ::
    "'a comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> bool"
  where
  "comma_crt_mdd_payload_cover nodes root labels \<longleftrightarrow>
    (\<forall>payload. comma_crt_mdd_payload_support nodes root payload \<longrightarrow>
      payload \<in> set labels)"

lemma comma_crt_mdd_payload_cover_leaf:
  assumes root_bound: "root < length nodes"
    and leaf: "nodes ! root = Comma_CRT_MDD_Leaf payload"
    and member: "payload \<in> set labels"
  shows "comma_crt_mdd_payload_cover nodes root labels"
  using root_bound leaf member
  unfolding comma_crt_mdd_payload_cover_def
  by (auto elim: comma_crt_mdd_payload_support.cases)

lemma comma_crt_mdd_payload_cover_branch:
  assumes root_bound: "root < length nodes"
    and branch: "nodes ! root = Comma_CRT_MDD_Branch axis children"
    and children_bounded: "\<forall>child\<in>set children. child < root"
    and child_covers:
      "\<forall>child\<in>set children. comma_crt_mdd_payload_cover nodes child labels"
  shows "comma_crt_mdd_payload_cover nodes root labels"
  using root_bound branch children_bounded child_covers
  unfolding comma_crt_mdd_payload_cover_def
  by (auto elim: comma_crt_mdd_payload_support.cases)

lemma comma_crt_mdd_payload_cover_mono:
  assumes "comma_crt_mdd_payload_cover nodes root smaller"
    and "set smaller \<subseteq> set larger"
  shows "comma_crt_mdd_payload_cover nodes root larger"
  using assms by (auto simp: comma_crt_mdd_payload_cover_def)

lemma comma_crt_mdd_eval_raw_payload_covered:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and root_bound: "root < length nodes"
    and covered: "comma_crt_mdd_payload_cover nodes root labels"
    and result:
      "comma_crt_mdd_eval_raw radices nodes coordinate root = Some payload"
  shows "payload \<in> set labels"
  using comma_crt_mdd_eval_raw_some_supported[OF wellformed root_bound result]
    covered
  by (auto simp: comma_crt_mdd_payload_cover_def)

definition comma_crt_mdd_eval :: "nat list \<Rightarrow>
    'a comma_crt_mdd_node list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    nat \<Rightarrow> 'a option" where
  "comma_crt_mdd_eval radices nodes coordinate root =
    (if comma_crt_mdd_table_wellformed radices nodes then
       comma_crt_mdd_eval_raw radices nodes coordinate root
     else None)"

definition comma_crt_mdd_eval_phase :: "nat list \<Rightarrow>
    'a comma_crt_mdd_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a option" where
  "comma_crt_mdd_eval_phase radices nodes phase root =
    comma_crt_mdd_eval radices nodes (\<lambda>axis. phase) root"

lemma comma_crt_mdd_eval_phase_total:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and root_bound: "root < length nodes"
  shows "\<exists>payload. comma_crt_mdd_eval_phase radices nodes phase root = Some payload"
  using comma_crt_mdd_eval_raw_total[OF wellformed root_bound,
    where coordinate="\<lambda>axis. phase"] wellformed
  by (simp only: comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def if_True)

lemma comma_crt_mdd_eval_phase_leaf:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and root_bound: "root < length nodes"
    and leaf: "nodes ! root = Comma_CRT_MDD_Leaf value"
  shows "comma_crt_mdd_eval_phase radices nodes phase root = Some value"
proof -
  have raw:
      "comma_crt_mdd_eval_raw radices nodes (\<lambda>axis. phase) root = Some value"
    by (rule comma_crt_mdd_eval_raw_leaf[OF root_bound leaf])
  have evaluated:
      "comma_crt_mdd_eval radices nodes (\<lambda>axis. phase) root = Some value"
    unfolding comma_crt_mdd_eval_def
    using wellformed raw by (simp only: if_True)
  show ?thesis
    unfolding comma_crt_mdd_eval_phase_def
    by (rule evaluated)
qed

definition comma_crt_mdd_project_nodes :: "('a \<Rightarrow> 'b) \<Rightarrow>
    'a comma_crt_mdd_node list \<Rightarrow> 'b comma_crt_mdd_node list" where
  "comma_crt_mdd_project_nodes = comma_crt_mdd_map_nodes"

definition comma_crt_mdd_eval_project :: "nat list \<Rightarrow>
    'a comma_crt_mdd_node list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow>
    nat \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool option" where
  "comma_crt_mdd_eval_project radices nodes coordinate root project =
    comma_crt_mdd_eval radices (comma_crt_mdd_project_nodes project nodes)
      coordinate root"

lemma comma_crt_mdd_map_nodes_length:
  "length (comma_crt_mdd_map_nodes project nodes) = length nodes"
  by (simp add: comma_crt_mdd_map_nodes_def)

lemma comma_crt_mdd_map_nodes_nth:
  assumes "root < length nodes"
  shows "comma_crt_mdd_map_nodes project nodes ! root =
    comma_crt_mdd_node_map project (nodes ! root)"
  using assms by (simp add: comma_crt_mdd_map_nodes_def nth_map)

lemma comma_crt_mdd_map_child_axis:
  assumes child: "child < root" and root: "root < length nodes"
  shows "comma_crt_mdd_node_axis
      (comma_crt_mdd_map_nodes project nodes ! child) =
    comma_crt_mdd_node_axis (nodes ! child)"
proof -
  have child_bound: "child < length nodes" using child root by arith
  have mapped:
      "comma_crt_mdd_map_nodes project nodes ! child =
        comma_crt_mdd_node_map project (nodes ! child)"
    by (rule comma_crt_mdd_map_nodes_nth[OF child_bound])
  show ?thesis using mapped by (simp add: comma_crt_mdd_node_axis_map)
qed

lemma comma_crt_mdd_node_ordered_map_iff:
  "comma_crt_mdd_node_ordered radices (comma_crt_mdd_map_nodes project nodes) root =
    comma_crt_mdd_node_ordered radices nodes root"
proof (cases "root < length nodes")
  case False
  then show ?thesis
    by (simp add: comma_crt_mdd_node_ordered_def comma_crt_mdd_map_nodes_length)
next
  case True
  then show ?thesis
    by (cases "nodes ! root")
      (auto simp: comma_crt_mdd_node_ordered_def
        comma_crt_mdd_map_nodes_length comma_crt_mdd_map_nodes_nth Let_def
        comma_crt_mdd_map_child_axis comma_crt_mdd_node_axis_map
        split: comma_crt_mdd_node.splits option.splits)
qed

lemma comma_crt_mdd_table_wellformed_map_iff:
  "comma_crt_mdd_table_wellformed radices (comma_crt_mdd_map_nodes project nodes) =
    comma_crt_mdd_table_wellformed radices nodes"
  by (auto simp: comma_crt_mdd_table_wellformed_def
      comma_crt_mdd_node_ordered_map_iff comma_crt_mdd_map_nodes_length)

lemma comma_crt_mdd_eval_raw_map:
  "comma_crt_mdd_eval_raw radices (comma_crt_mdd_map_nodes project nodes)
      coordinate root =
    map_option project (comma_crt_mdd_eval_raw radices nodes coordinate root)"
proof (induction root rule: less_induct)
  case (less root)
  have child_exact:
      "comma_crt_mdd_eval_raw radices
          (comma_crt_mdd_map_nodes project nodes) coordinate child =
       map_option project (comma_crt_mdd_eval_raw radices nodes coordinate child)"
    if child_bound: "child < root" for child
    by (rule less.IH[OF child_bound])
  note left = comma_crt_mdd_eval_raw.simps[of radices
      "comma_crt_mdd_map_nodes project nodes" coordinate root]
  note right = comma_crt_mdd_eval_raw.simps[of radices nodes coordinate root]
  show ?case
    by (subst left, subst right)
      (cases "root < length nodes";
       cases "nodes ! root";
       auto simp only: comma_crt_mdd_map_nodes_length
         comma_crt_mdd_map_nodes_nth comma_crt_mdd_node_map.simps
         comma_crt_mdd_node.case Let_def option.map child_exact
         if_True if_False split: if_splits)
qed

lemma comma_crt_mdd_eval_project:
  "comma_crt_mdd_eval_project radices nodes coordinate root project =
    map_option project (comma_crt_mdd_eval radices nodes coordinate root)"
  by (simp add: comma_crt_mdd_eval_project_def comma_crt_mdd_project_nodes_def
      comma_crt_mdd_eval_def
      comma_crt_mdd_table_wellformed_map_iff comma_crt_mdd_eval_raw_map)

lemma comma_crt_mdd_eval_project_true_iff:
  "comma_crt_mdd_eval_project radices nodes coordinate root project = Some True
    \<longleftrightarrow> (\<exists>label. comma_crt_mdd_eval radices nodes coordinate root = Some label
        \<and> project label)"
  by (auto simp: comma_crt_mdd_eval_project)

lemma comma_crt_mdd_eval_target_iff:
  "comma_crt_mdd_eval_project radices nodes coordinate root
      (\<lambda>label::nat option. label = Some target) = Some True \<longleftrightarrow>
    comma_crt_mdd_eval radices nodes coordinate root = Some (Some target)"
  by (auto simp: comma_crt_mdd_eval_project_true_iff)

definition comma_crt_mdd_shift_coordinate :: "nat list \<Rightarrow>
    (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_crt_mdd_shift_coordinate radices coordinate amount axis =
    ((coordinate axis + amount) mod (radices ! axis))"

lemma comma_crt_mdd_eval_raw_coordinate_congruent:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and congruent: "\<And>axis. axis < length radices \<Longrightarrow>
      coordinate_left axis mod radices ! axis =
        coordinate_right axis mod radices ! axis"
  shows "comma_crt_mdd_eval_raw radices nodes coordinate_left root =
    comma_crt_mdd_eval_raw radices nodes coordinate_right root"
proof (induction root rule: less_induct)
  case (less root)
  have child_exact:
      "comma_crt_mdd_eval_raw radices nodes coordinate_left child =
       comma_crt_mdd_eval_raw radices nodes coordinate_right child"
    if child_bound: "child < root" for child
    using less.IH[OF child_bound] .
  show ?case
  proof (cases "root < length nodes")
    case False
    have left:
        "comma_crt_mdd_eval_raw radices nodes coordinate_left root = None"
      using False by (subst (1) comma_crt_mdd_eval_raw.simps) simp
    have right:
        "comma_crt_mdd_eval_raw radices nodes coordinate_right root = None"
      using False by (subst (1) comma_crt_mdd_eval_raw.simps) simp
    show ?thesis using left right by simp
  next
    case True
    show ?thesis
    proof (cases "nodes ! root")
      case (Comma_CRT_MDD_Leaf payload)
      have left:
          "comma_crt_mdd_eval_raw radices nodes coordinate_left root = Some payload"
        by (rule comma_crt_mdd_eval_raw_leaf[OF True Comma_CRT_MDD_Leaf])
      have right:
          "comma_crt_mdd_eval_raw radices nodes coordinate_right root = Some payload"
        by (rule comma_crt_mdd_eval_raw_leaf[OF True Comma_CRT_MDD_Leaf])
      show ?thesis using left right by simp
    next
      case (Comma_CRT_MDD_Branch axis children)
      have axis_bound: "axis < length radices"
        and positive: "0 < radices ! axis"
        and width: "length children = radices ! axis"
        and children_ordered:
          "\<forall>child\<in>set children. child < root \<and>
            (case comma_crt_mdd_node_axis (nodes ! child) of
               None \<Rightarrow> True
             | Some child_axis \<Rightarrow> axis < child_axis)"
        by (rule comma_crt_mdd_branch_facts[OF wellformed True
            Comma_CRT_MDD_Branch])+
      let ?radix = "radices ! axis"
      let ?index = "coordinate_left axis mod ?radix"
      let ?child = "children ! ?index"
      have index_bound: "?index < length children"
        using positive width by simp
      have child_member: "?child \<in> set children"
        by (rule nth_mem[OF index_bound])
      have earlier: "?child < root"
        using children_ordered child_member by blast
      have same_index: "coordinate_left axis mod ?radix =
          coordinate_right axis mod ?radix"
        by (rule congruent[OF axis_bound])
      have selected_left: "?child = children ! (coordinate_left axis mod ?radix)"
        by simp
      have selected_right: "?child = children ! (coordinate_right axis mod ?radix)"
        using same_index by simp
      have left:
          "comma_crt_mdd_eval_raw radices nodes coordinate_left root =
            comma_crt_mdd_eval_raw radices nodes coordinate_left ?child"
        by (rule comma_crt_mdd_eval_raw_branch
            [where coordinate=coordinate_left,
             OF True Comma_CRT_MDD_Branch axis_bound positive width
              selected_left earlier])
      have right:
          "comma_crt_mdd_eval_raw radices nodes coordinate_right root =
            comma_crt_mdd_eval_raw radices nodes coordinate_right ?child"
        by (rule comma_crt_mdd_eval_raw_branch
            [where coordinate=coordinate_right,
             OF True Comma_CRT_MDD_Branch axis_bound positive width
              selected_right earlier])
      show ?thesis using left right child_exact[OF earlier] by simp
    qed
  qed
qed

lemma comma_crt_mdd_eval_coordinate_congruent:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and congruent: "\<And>axis. axis < length radices \<Longrightarrow>
      coordinate_left axis mod radices ! axis =
        coordinate_right axis mod radices ! axis"
  shows "comma_crt_mdd_eval radices nodes coordinate_left root =
    comma_crt_mdd_eval radices nodes coordinate_right root"
  using wellformed comma_crt_mdd_eval_raw_coordinate_congruent[OF wellformed congruent]
  by (simp add: comma_crt_mdd_eval_def)

lemma comma_crt_mdd_eval_phase_periodic:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and period_divides: "\<And>axis. axis < length radices \<Longrightarrow>
      radices ! axis dvd period"
  shows "comma_crt_mdd_eval_phase radices nodes (phase mod period) root =
    comma_crt_mdd_eval_phase radices nodes phase root"
  unfolding comma_crt_mdd_eval_phase_def
proof (rule comma_crt_mdd_eval_coordinate_congruent[OF wellformed])
  fix axis
  assume axis: "axis < length radices"
  show "(phase mod period) mod radices ! axis = phase mod radices ! axis"
    by (rule mod_mod_cancel[OF period_divides[OF axis]])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "flat CRT MDD evaluation, phase congruence, and payload support"
    @{thms comma_crt_mdd_indexed_allD comma_crt_mdd_branch_facts comma_crt_mdd_eval_raw_leaf
      comma_crt_mdd_eval_raw_branch comma_crt_mdd_eval_raw_branch_selected
      comma_crt_mdd_eval_raw_total
      comma_crt_mdd_eval_raw_some_supported comma_crt_mdd_payload_cover_leaf
      comma_crt_mdd_payload_cover_mono
      comma_crt_mdd_payload_cover_branch comma_crt_mdd_eval_raw_payload_covered
      comma_crt_mdd_eval_raw_coordinate_congruent
      comma_crt_mdd_eval_coordinate_congruent
      comma_crt_mdd_eval_phase_total
      comma_crt_mdd_eval_phase_leaf comma_crt_mdd_eval_phase_periodic
      comma_crt_mdd_eval_project_true_iff
      comma_crt_mdd_eval_target_iff}
\<close>

end
