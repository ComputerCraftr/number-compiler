theory Comma_Semantic_B1_CRT_Mass_Annotations
  imports Comma_Semantic_B1_CRT_Mass_Transport
begin

text \<open>
A sparse, child-closed AVL search tree carries the exact level and mass for
each demanded nonterminal CID.  It contains only the dependency closure of
the requested roots; it need not certify unrelated entries in the global
column directory.  The search tree is balanced and strictly ordered so a
checker lookup is logarithmic.  Child vectors remain in their source order,
including repetitions, in the mass recurrence.
\<close>

datatype comma_semantic_b1_crt_mass_tree =
    Comma_B1_CRT_Mass_Tree_Empty
  | Comma_B1_CRT_Mass_Tree_Node nat nat nat
      comma_semantic_b1_crt_mass_tree comma_semantic_b1_crt_mass_tree

fun comma_semantic_b1_crt_mass_tree_lookup ::
    "comma_semantic_b1_crt_mass_tree \<Rightarrow> nat \<Rightarrow> (nat \<times> nat) option" where
  "comma_semantic_b1_crt_mass_tree_lookup Comma_B1_CRT_Mass_Tree_Empty cid = None"
| "comma_semantic_b1_crt_mass_tree_lookup
      (Comma_B1_CRT_Mass_Tree_Node key level mass left right) cid =
    (if cid=key then Some (level,mass)
     else if cid<key then comma_semantic_b1_crt_mass_tree_lookup left cid
     else comma_semantic_b1_crt_mass_tree_lookup right cid)"

fun comma_semantic_b1_crt_mass_tree_height ::
    "comma_semantic_b1_crt_mass_tree \<Rightarrow> nat" where
  "comma_semantic_b1_crt_mass_tree_height Comma_B1_CRT_Mass_Tree_Empty = 0"
| "comma_semantic_b1_crt_mass_tree_height
      (Comma_B1_CRT_Mass_Tree_Node key level mass left right) =
    Suc (max (comma_semantic_b1_crt_mass_tree_height left)
      (comma_semantic_b1_crt_mass_tree_height right))"

fun comma_semantic_b1_crt_mass_tree_ordered ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_crt_mass_tree \<Rightarrow> bool" where
  "comma_semantic_b1_crt_mass_tree_ordered lower upper
      Comma_B1_CRT_Mass_Tree_Empty = True"
| "comma_semantic_b1_crt_mass_tree_ordered lower upper
      (Comma_B1_CRT_Mass_Tree_Node cid level mass left right) =
    (lower\<le>cid \<and> cid<upper \<and>
      comma_semantic_b1_crt_mass_tree_height left \<le>
        Suc (comma_semantic_b1_crt_mass_tree_height right) \<and>
      comma_semantic_b1_crt_mass_tree_height right \<le>
        Suc (comma_semantic_b1_crt_mass_tree_height left) \<and>
      comma_semantic_b1_crt_mass_tree_ordered lower cid left \<and>
      comma_semantic_b1_crt_mass_tree_ordered (Suc cid) upper right)"

fun comma_semantic_b1_crt_mass_tree_value ::
    "comma_semantic_b1_crt_mass_tree \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_semantic_b1_crt_mass_tree_value tree cid =
    (if cid=0 then 0 else if cid=1 then 924 else
      case comma_semantic_b1_crt_mass_tree_lookup tree cid of
        None \<Rightarrow> 0
      | Some (level,mass) \<Rightarrow> mass)"

definition comma_semantic_b1_crt_mass_tree_child_valid ::
    "comma_semantic_b1_crt_column_dag \<Rightarrow>
      comma_semantic_b1_crt_mass_tree \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_mass_tree_child_valid dag tree parent parent_level child \<longleftrightarrow>
    child<parent \<and>
    (if child<2 then True else
      (\<exists>child_level child_mass.
        comma_semantic_b1_crt_mass_tree_lookup tree child =
          Some (child_level,child_mass) \<and>
        Suc parent_level\<le>child_level))"

definition comma_semantic_b1_crt_mass_tree_row_valid ::
    "comma_semantic_b1_crt_column_dag \<Rightarrow>
      comma_semantic_b1_crt_mass_tree \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_mass_tree_row_valid dag tree cid level mass \<longleftrightarrow>
    cid\<ge>2 \<and>
    (case comma_semantic_b1_crt_column_dag_lookup dag cid of
       None \<Rightarrow> False
     | Some (source_level,children) \<Rightarrow>
         level=source_level \<and> level<4 \<and>
         length children=comma_crt_period level \<and>
         list_all (comma_semantic_b1_crt_mass_tree_child_valid
           dag tree cid level) children \<and>
         mass=sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children) div
           comma_crt_period level)"

(* A compact summary of one exact, ordered child vector.  The level sentinel
   4 is above every valid parent level and is used for terminal CIDs, which
   have no mass-tree row.  A missing nonterminal lookup yields None; it is
   never assigned a default mass. *)
datatype comma_semantic_b1_crt_child_vector_summary =
  Comma_Semantic_B1_CRT_Child_Vector_Summary nat nat nat nat

fun comma_semantic_b1_crt_child_vector_summary_of ::
    "comma_semantic_b1_crt_mass_tree \<Rightarrow> nat list \<Rightarrow>
      comma_semantic_b1_crt_child_vector_summary option" where
  "comma_semantic_b1_crt_child_vector_summary_of tree [] =
      Some (Comma_Semantic_B1_CRT_Child_Vector_Summary 0 0 4 0)"
| "comma_semantic_b1_crt_child_vector_summary_of tree (child # children) =
    (case comma_semantic_b1_crt_child_vector_summary_of tree children of
       None \<Rightarrow> None
     | Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
          vector_count vector_maximum vector_minimum vector_total) \<Rightarrow>
         if child < 2 then
           Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
             (Suc vector_count) (max child vector_maximum) (min 4 vector_minimum)
             ((if child = 0 then 0 else 924) + vector_total))
         else
           (case comma_semantic_b1_crt_mass_tree_lookup tree child of
              None \<Rightarrow> None
            | Some (child_level,child_mass) \<Rightarrow>
                Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
                  (Suc vector_count) (max child vector_maximum) (min child_level vector_minimum)
                  (child_mass + vector_total))))"

lemma comma_semantic_b1_crt_child_vector_summary_empty:
  "comma_semantic_b1_crt_child_vector_summary_of tree [] =
    Some (Comma_Semantic_B1_CRT_Child_Vector_Summary 0 0 4 0)"
  by simp

lemma comma_semantic_b1_crt_child_vector_summary_terminal_zero:
  assumes tail:
    "comma_semantic_b1_crt_child_vector_summary_of tree children =
      Some (Comma_Semantic_B1_CRT_Child_Vector_Summary vector_count vector_maximum vector_minimum vector_total)"
  shows "comma_semantic_b1_crt_child_vector_summary_of tree (0 # children) =
    Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
      (Suc vector_count) (max 0 vector_maximum) (min 4 vector_minimum) vector_total)"
  using tail by simp

lemma comma_semantic_b1_crt_child_vector_summary_terminal_one:
  assumes tail:
    "comma_semantic_b1_crt_child_vector_summary_of tree children =
      Some (Comma_Semantic_B1_CRT_Child_Vector_Summary vector_count vector_maximum vector_minimum vector_total)"
  shows "comma_semantic_b1_crt_child_vector_summary_of tree (1 # children) =
    Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
      (Suc vector_count) (max 1 vector_maximum) (min 4 vector_minimum) (924 + vector_total))"
  using tail by simp

lemma comma_semantic_b1_crt_child_vector_summary_node:
  assumes tail:
    "comma_semantic_b1_crt_child_vector_summary_of tree children =
      Some (Comma_Semantic_B1_CRT_Child_Vector_Summary vector_count vector_maximum vector_minimum vector_total)"
    and child: "2 \<le> child"
    and lookup:
      "comma_semantic_b1_crt_mass_tree_lookup tree child = Some (child_level,child_mass)"
  shows "comma_semantic_b1_crt_child_vector_summary_of tree (child # children) =
    Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
      (Suc vector_count) (max child vector_maximum) (min child_level vector_minimum)
      (child_mass + vector_total))"
  using tail child lookup by simp

lemma comma_semantic_b1_crt_child_vector_summary_facts:
  assumes summary:
    "comma_semantic_b1_crt_child_vector_summary_of tree children =
      Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
        vector_count vector_maximum vector_minimum vector_total)"
  shows "length children = vector_count \<and>
      (\<forall>child \<in> set children. child \<le> vector_maximum) \<and>
      (\<forall>child \<in> set children. child < 2 \<or>
        (\<exists>child_level child_mass.
          comma_semantic_b1_crt_mass_tree_lookup tree child =
            Some (child_level,child_mass) \<and> vector_minimum \<le> child_level)) \<and>
      sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children) = vector_total"
  using summary
proof (induction children arbitrary: vector_count vector_maximum vector_minimum vector_total)
  case Nil
  then show ?case by simp
next
  case (Cons child children)
  obtain tail_vector_count tail_vector_maximum tail_vector_minimum tail_vector_total where tail:
    "comma_semantic_b1_crt_child_vector_summary_of tree children =
      Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
        tail_vector_count tail_vector_maximum tail_vector_minimum tail_vector_total)"
    using Cons.prems
    by (cases "comma_semantic_b1_crt_child_vector_summary_of tree children")
      (auto split: option.splits comma_semantic_b1_crt_child_vector_summary.splits)
  have tail_facts:
    "length children = tail_vector_count \<and>
      (\<forall>entry \<in> set children. entry \<le> tail_vector_maximum) \<and>
      (\<forall>entry \<in> set children. entry < 2 \<or>
        (\<exists>child_level child_mass.
          comma_semantic_b1_crt_mass_tree_lookup tree entry =
            Some (child_level,child_mass) \<and> tail_vector_minimum \<le> child_level)) \<and>
      sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children) = tail_vector_total"
    using Cons.IH[OF tail] .
  have sum_cons:
    "sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) (child # children)) =
      comma_semantic_b1_crt_mass_tree_value tree child +
        sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children)"
    by (simp only: list.map(2) sum_list.Cons)
  show ?case
  proof (cases "child < 2")
    case True
    have fields:
      "vector_count = Suc tail_vector_count \<and> vector_maximum = max child tail_vector_maximum \<and>
       vector_minimum = min 4 tail_vector_minimum \<and>
       vector_total = (if child = 0 then 0 else 924) + tail_vector_total"
      using Cons.prems tail True by simp
    have head_value:
      "comma_semantic_b1_crt_mass_tree_value tree child =
        (if child = 0 then 0 else 924)"
      using True by (cases child) (simp_all add: comma_semantic_b1_crt_mass_tree_value.simps)
    show ?thesis
      using fields tail_facts True head_value sum_cons
      by (auto simp: max_def min_def
          simp del: comma_semantic_b1_crt_mass_tree_value.simps)
  next
    case False
    obtain child_level child_mass where lookup:
      "comma_semantic_b1_crt_mass_tree_lookup tree child =
        Some (child_level,child_mass)"
      using Cons.prems tail False
      by (cases "comma_semantic_b1_crt_mass_tree_lookup tree child")
        (auto split: option.splits prod.splits)
    have fields:
      "vector_count = Suc tail_vector_count \<and> vector_maximum = max child tail_vector_maximum \<and>
       vector_minimum = min child_level tail_vector_minimum \<and>
       vector_total = child_mass + tail_vector_total"
      using Cons.prems tail False lookup by simp
    have head_value:
      "comma_semantic_b1_crt_mass_tree_value tree child = child_mass"
      using False lookup by (simp add: comma_semantic_b1_crt_mass_tree_value.simps)
    show ?thesis
      using fields tail_facts False lookup head_value sum_cons
      by (auto simp: max_def min_def
          simp del: comma_semantic_b1_crt_mass_tree_value.simps)
  qed
qed

lemma comma_semantic_b1_crt_child_vector_summary_child_valid:
  assumes summary:
      "comma_semantic_b1_crt_child_vector_summary_of tree children =
        Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
          vector_count vector_maximum vector_minimum vector_total)"
    and max_bound: "vector_maximum < parent"
    and min_bound: "Suc parent_level \<le> vector_minimum"
  shows "list_all (comma_semantic_b1_crt_mass_tree_child_valid
      dag tree parent parent_level) children"
proof -
  have facts:
    "length children = vector_count \<and>
      (\<forall>child \<in> set children. child \<le> vector_maximum) \<and>
      (\<forall>child \<in> set children. child < 2 \<or>
        (\<exists>child_level child_mass.
          comma_semantic_b1_crt_mass_tree_lookup tree child =
            Some (child_level,child_mass) \<and> vector_minimum \<le> child_level)) \<and>
      sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children) = vector_total"
    by (rule comma_semantic_b1_crt_child_vector_summary_facts[OF summary])
  have each_valid:
    "\<forall>child \<in> set children.
      comma_semantic_b1_crt_mass_tree_child_valid dag tree parent parent_level child"
  proof (intro ballI)
    fix child
    assume member: "child \<in> set children"
    have child_bound: "child \<le> vector_maximum" using facts member by blast
    have child_level:
      "child < 2 \<or>
        (\<exists>child_level child_mass.
          comma_semantic_b1_crt_mass_tree_lookup tree child =
            Some (child_level,child_mass) \<and> vector_minimum \<le> child_level)"
      using facts member by blast
    show "comma_semantic_b1_crt_mass_tree_child_valid dag tree parent parent_level child"
      unfolding comma_semantic_b1_crt_mass_tree_child_valid_def
      using child_bound max_bound child_level min_bound
      by (auto intro: order_trans)
  qed
  show ?thesis using each_valid by (simp add: list_all_iff)
qed

lemma comma_semantic_b1_crt_mass_tree_row_valid_of_child_vector_summary:
  assumes source:
      "comma_semantic_b1_crt_column_dag_lookup dag cid = Some (level,children)"
    and cid_bound: "2 \<le> cid"
    and level_bound: "level < 4"
    and summary:
      "comma_semantic_b1_crt_child_vector_summary_of tree children =
        Some (Comma_Semantic_B1_CRT_Child_Vector_Summary
          vector_count vector_maximum vector_minimum vector_total)"
    and width: "vector_count = comma_crt_period level"
    and max_bound: "vector_maximum < cid"
    and min_bound: "Suc level \<le> vector_minimum"
    and mass: "mass = vector_total div comma_crt_period level"
  shows "comma_semantic_b1_crt_mass_tree_row_valid dag tree cid level mass"
proof -
  have facts:
    "length children = vector_count \<and>
      (\<forall>child \<in> set children. child \<le> vector_maximum) \<and>
      (\<forall>child \<in> set children. child < 2 \<or>
        (\<exists>child_level child_mass.
          comma_semantic_b1_crt_mass_tree_lookup tree child =
            Some (child_level,child_mass) \<and> vector_minimum \<le> child_level)) \<and>
      sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children) = vector_total"
    by (rule comma_semantic_b1_crt_child_vector_summary_facts[OF summary])
  have children_valid:
    "list_all (comma_semantic_b1_crt_mass_tree_child_valid dag tree cid level) children"
    by (rule comma_semantic_b1_crt_child_vector_summary_child_valid[OF summary max_bound min_bound])
  have length_fact: "length children = comma_crt_period level"
    using facts width by simp
  have mass_fact:
    "mass = sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children) div
      comma_crt_period level"
    using facts mass by simp
  show ?thesis
    unfolding comma_semantic_b1_crt_mass_tree_row_valid_def
    using source cid_bound level_bound length_fact children_valid mass_fact
    by simp
qed

fun comma_semantic_b1_crt_mass_tree_rows_valid where
  "comma_semantic_b1_crt_mass_tree_rows_valid dag tree
      Comma_B1_CRT_Mass_Tree_Empty = True"
| "comma_semantic_b1_crt_mass_tree_rows_valid dag tree
      (Comma_B1_CRT_Mass_Tree_Node cid level mass left right) =
    (comma_semantic_b1_crt_mass_tree_row_valid dag tree cid level mass \<and>
      comma_semantic_b1_crt_mass_tree_rows_valid dag tree left \<and>
      comma_semantic_b1_crt_mass_tree_rows_valid dag tree right)"

definition comma_semantic_b1_crt_column_mass_annotation_tree_valid ::
    "comma_semantic_b1_crt_column_dag \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_crt_mass_tree \<Rightarrow> bool" where
  "comma_semantic_b1_crt_column_mass_annotation_tree_valid dag node_count tree \<longleftrightarrow>
    comma_semantic_b1_crt_mass_tree_ordered 2 node_count tree \<and>
    comma_semantic_b1_crt_mass_tree_rows_valid dag tree tree"

ML \<open>comma_semantic_b1_column_at_admitted_timer "mass-tree-row-valid-start"\<close>

lemma comma_semantic_b1_crt_mass_tree_lookup_row_valid:
  assumes rows:
      "comma_semantic_b1_crt_mass_tree_rows_valid dag tree subtree"
    and lookup:
      "comma_semantic_b1_crt_mass_tree_lookup subtree cid = Some (level,mass)"
  shows "comma_semantic_b1_crt_mass_tree_row_valid dag tree cid level mass"
  using rows lookup
proof (induction subtree arbitrary: cid level mass)
  case Comma_B1_CRT_Mass_Tree_Empty
  then show ?case by simp
next
  case (Comma_B1_CRT_Mass_Tree_Node key node_level node_mass left right)
  have root_row:
      "comma_semantic_b1_crt_mass_tree_row_valid dag tree key node_level node_mass"
    and left_rows:
      "comma_semantic_b1_crt_mass_tree_rows_valid dag tree left"
    and right_rows:
      "comma_semantic_b1_crt_mass_tree_rows_valid dag tree right"
    using Comma_B1_CRT_Mass_Tree_Node.prems(1) by simp_all
  have selected:
      "(cid=key \<and> level=node_level \<and> mass=node_mass) \<or>
       (cid<key \<and> comma_semantic_b1_crt_mass_tree_lookup left cid = Some (level,mass)) \<or>
       (key<cid \<and> comma_semantic_b1_crt_mass_tree_lookup right cid = Some (level,mass))"
    using Comma_B1_CRT_Mass_Tree_Node.prems(2) by (auto split: if_splits)
  then show ?case
  proof (elim disjE conjE)
    assume "cid=key" "level=node_level" "mass=node_mass"
    then show ?thesis using root_row by simp
  next
    assume "cid<key" "comma_semantic_b1_crt_mass_tree_lookup left cid = Some (level,mass)"
    then show ?thesis using Comma_B1_CRT_Mass_Tree_Node.IH(1)[OF left_rows] by blast
  next
    assume "key<cid" "comma_semantic_b1_crt_mass_tree_lookup right cid = Some (level,mass)"
    then show ?thesis using Comma_B1_CRT_Mass_Tree_Node.IH(2)[OF right_rows] by blast
  qed
qed

ML \<open>comma_semantic_b1_column_at_admitted_timer "mass-tree-row-valid-done"\<close>

lemma comma_semantic_b1_crt_mass_tree_lookup_row_source:
  assumes rows:
      "comma_semantic_b1_crt_mass_tree_rows_valid dag tree subtree"
    and lookup:
      "comma_semantic_b1_crt_mass_tree_lookup subtree cid = Some (level,mass)"
  shows "\<exists>children. comma_semantic_b1_crt_column_dag_lookup dag cid =
      Some (level,children)"
proof -
  have row:
      "comma_semantic_b1_crt_mass_tree_row_valid dag tree cid level mass"
    by (rule comma_semantic_b1_crt_mass_tree_lookup_row_valid[OF rows lookup])
  from row show ?thesis
    by (auto simp: comma_semantic_b1_crt_mass_tree_row_valid_def
      split: option.splits prod.splits)
qed

ML \<open>comma_semantic_b1_column_at_admitted_timer "mass-tree-row-source-done"\<close>

lemma comma_semantic_b1_crt_mass_tree_lookup_node_shape:
  assumes cid_bound: "2\<le>cid"
    and source: "comma_semantic_b1_crt_column_dag_lookup dag cid = Some (level,children)"
    and level_bound: "level<4"
    and width: "length children=comma_crt_period level"
    and decreasing:
      "list_all (\<lambda>child. child<cid) children"
    and admitted:
      "list_all (\<lambda>child. comma_crt_admitted (Suc level)
        (comma_semantic_b1_crt_column_at dag child)) children"
  shows "comma_semantic_b1_crt_column_at dag cid =
      Comma_CRT_Node level (map (comma_semantic_b1_crt_column_at dag) children)"
proof -
  let ?rhs = "(if cid=0 then Comma_CRT_Bool False
    else if cid=1 then Comma_CRT_Bool True
    else case comma_semantic_b1_crt_column_dag_lookup dag cid of
      None \<Rightarrow> Comma_CRT_Bool False
    | Some (source_level,source_children) \<Rightarrow>
        if list_all (\<lambda>child. child<cid) source_children then
          comma_semantic_b1_crt_guarded_node source_level
            (map (comma_semantic_b1_crt_column_at dag) source_children)
        else Comma_CRT_Bool False)"
  have equation: "comma_semantic_b1_crt_column_at dag cid=?rhs"
    by (rule comma_semantic_b1_crt_column_at.simps)
  have cid_not_zero: "cid\<noteq>0" using cid_bound by arith
  have cid_not_one: "cid\<noteq>1" using cid_bound by arith
  have selected:
      "?rhs=comma_semantic_b1_crt_guarded_node level
        (map (comma_semantic_b1_crt_column_at dag) children)"
    using cid_not_zero cid_not_one source decreasing by simp
  have mapped_admitted:
      "list_all (comma_crt_admitted (Suc level))
        (map (comma_semantic_b1_crt_column_at dag) children)"
    using admitted by (simp add: list_all_iff)
  have node_admitted:
      "comma_crt_admitted 0 (Comma_CRT_Node level
        (map (comma_semantic_b1_crt_column_at dag) children))"
    using mapped_admitted level_bound width
    by (simp add: comma_crt_admitted.simps)
  have guarded:
      "comma_semantic_b1_crt_guarded_node level
        (map (comma_semantic_b1_crt_column_at dag) children) =
       Comma_CRT_Node level (map (comma_semantic_b1_crt_column_at dag) children)"
    unfolding comma_semantic_b1_crt_guarded_node_def
    using node_admitted by simp
  show ?thesis by (simp only: equation selected guarded)
qed

ML \<open>comma_semantic_b1_column_at_admitted_timer "mass-tree-node-shape-done"\<close>

lemma comma_semantic_b1_crt_column_mass_annotation_tree_sound:
  assumes valid:
      "comma_semantic_b1_crt_column_mass_annotation_tree_valid dag node_count tree"
  shows "\<forall>cid level mass.
      comma_semantic_b1_crt_mass_tree_lookup tree cid = Some (level,mass) \<longrightarrow>
      (comma_crt_admitted 0 (comma_semantic_b1_crt_column_at dag cid) \<and>
       comma_semantic_b1_crt_column_mass (comma_semantic_b1_crt_column_at dag cid)=mass)"
proof -
  have rows: "comma_semantic_b1_crt_mass_tree_rows_valid dag tree tree"
    using valid by (simp add: comma_semantic_b1_crt_column_mass_annotation_tree_valid_def)
  show ?thesis
  proof (rule allI)
    fix cid
    show "\<forall>level mass.
        comma_semantic_b1_crt_mass_tree_lookup tree cid = Some (level,mass) \<longrightarrow>
        (comma_crt_admitted 0 (comma_semantic_b1_crt_column_at dag cid) \<and>
         comma_semantic_b1_crt_column_mass (comma_semantic_b1_crt_column_at dag cid)=mass)"
    proof (induction cid rule: less_induct)
      case (less cid)
      show ?case
      proof (intro allI)
        fix level mass
        show "comma_semantic_b1_crt_mass_tree_lookup tree cid = Some (level,mass) \<longrightarrow>
            (comma_crt_admitted 0 (comma_semantic_b1_crt_column_at dag cid) \<and>
             comma_semantic_b1_crt_column_mass (comma_semantic_b1_crt_column_at dag cid)=mass)"
        proof
          assume lookup:
              "comma_semantic_b1_crt_mass_tree_lookup tree cid = Some (level,mass)"
          have row:
              "comma_semantic_b1_crt_mass_tree_row_valid dag tree cid level mass"
            by (rule comma_semantic_b1_crt_mass_tree_lookup_row_valid[OF rows lookup])
          have data:
              "\<exists>children. comma_semantic_b1_crt_column_dag_lookup dag cid =
                  Some (level,children) \<and>
                2\<le>cid \<and> level<4 \<and>
                length children=comma_crt_period level \<and>
                list_all (comma_semantic_b1_crt_mass_tree_child_valid
                  dag tree cid level) children \<and>
                mass=sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children) div
                  comma_crt_period level"
            using row
            by (auto simp: comma_semantic_b1_crt_mass_tree_row_valid_def
              split: option.splits prod.splits)
          then obtain children where source:
              "comma_semantic_b1_crt_column_dag_lookup dag cid = Some (level,children)"
            and cid_bound: "2\<le>cid"
            and level_bound: "level<4"
            and width: "length children=comma_crt_period level"
            and children_valid:
              "list_all (comma_semantic_b1_crt_mass_tree_child_valid
                dag tree cid level) children"
            and recurrence:
              "mass=sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children) div
                comma_crt_period level"
            by blast
          have decreasing: "list_all (\<lambda>child. child<cid) children"
            using children_valid
            by (auto simp: list_all_iff
              comma_semantic_b1_crt_mass_tree_child_valid_def)
          have child_admitted:
              "\<forall>child\<in>set children.
                comma_crt_admitted (Suc level)
                  (comma_semantic_b1_crt_column_at dag child)"
          proof (intro ballI)
            fix child
            assume child_in: "child\<in>set children"
            have child_valid:
                "comma_semantic_b1_crt_mass_tree_child_valid dag tree cid level child"
              using children_valid child_in by (simp add: list_all_iff)
            show "comma_crt_admitted (Suc level)
                (comma_semantic_b1_crt_column_at dag child)"
            proof (cases "child<2")
              case True
              then have child_zero_or_one: "child=0 \<or> child=1" by arith
              then show ?thesis
              proof
                assume child_zero: "child=0"
                have "comma_crt_admitted (Suc level)
                    (comma_semantic_b1_crt_column_at dag 0)"
                  by (simp only: comma_semantic_b1_crt_column_at_false
                      comma_crt_admitted.simps)
                then show ?thesis using child_zero by simp
              next
                assume child_one: "child=1"
                have "comma_crt_admitted (Suc level)
                    (comma_semantic_b1_crt_column_at dag 1)"
                  by (simp only: comma_semantic_b1_crt_column_at_true
                      comma_crt_admitted.simps)
                then show ?thesis using child_one by simp
              qed
            next
              case False
              then obtain child_level child_mass where child_header:
                  "comma_semantic_b1_crt_mass_tree_lookup tree child =
                     Some (child_level,child_mass)"
                and child_level_bound: "Suc level\<le>child_level"
                using child_valid
                by (auto simp: comma_semantic_b1_crt_mass_tree_child_valid_def)
              then obtain child_children where child_source:
                  "comma_semantic_b1_crt_column_dag_lookup dag child =
                     Some (child_level,child_children)"
                using comma_semantic_b1_crt_mass_tree_lookup_row_source
                  [OF rows child_header]
                by blast
              show ?thesis
                by (rule comma_semantic_b1_crt_column_at_admitted_at
                  [OF child_source child_level_bound])
            qed
          qed
          have admitted_list:
              "list_all (\<lambda>child. comma_crt_admitted (Suc level)
                  (comma_semantic_b1_crt_column_at dag child)) children"
            using child_admitted by (simp add: list_all_iff)
          have node_shape:
              "comma_semantic_b1_crt_column_at dag cid =
                Comma_CRT_Node level (map (comma_semantic_b1_crt_column_at dag) children)"
            by (rule comma_semantic_b1_crt_mass_tree_lookup_node_shape
              [OF cid_bound source level_bound width decreasing admitted_list])
          have child_mass_agreement:
              "\<forall>child\<in>set children.
                comma_semantic_b1_crt_column_mass
                    (comma_semantic_b1_crt_column_at dag child) =
                  comma_semantic_b1_crt_mass_tree_value tree child"
          proof (intro ballI)
            fix child
            assume child_in: "child\<in>set children"
            have child_valid:
                "comma_semantic_b1_crt_mass_tree_child_valid dag tree cid level child"
              using children_valid child_in by (simp add: list_all_iff)
            have child_smaller: "child<cid"
              using child_valid by (simp add: comma_semantic_b1_crt_mass_tree_child_valid_def)
            show "comma_semantic_b1_crt_column_mass
                (comma_semantic_b1_crt_column_at dag child) =
                comma_semantic_b1_crt_mass_tree_value tree child"
            proof (cases "child<2")
              case True
              then have child_zero_or_one: "child=0 \<or> child=1" by arith
              then show ?thesis
              proof
                assume child_zero: "child=0"
                have mass_eq:
                    "comma_semantic_b1_crt_column_mass
                      (comma_semantic_b1_crt_column_at dag 0) =
                     comma_semantic_b1_crt_mass_tree_value tree 0"
                  by (simp add: comma_semantic_b1_crt_column_at_false
                      comma_semantic_b1_crt_column_mass.simps
                      comma_semantic_b1_crt_mass_tree_value.simps)
                then show ?thesis using child_zero by simp
              next
                assume child_one: "child=1"
                have mass_eq:
                    "comma_semantic_b1_crt_column_mass
                      (comma_semantic_b1_crt_column_at dag 1) =
                     comma_semantic_b1_crt_mass_tree_value tree 1"
                  by (subst comma_semantic_b1_crt_column_at_true)
                    (simp add: comma_semantic_b1_crt_column_mass.simps
                      comma_semantic_b1_crt_mass_tree_value.simps)
                then show ?thesis using child_one by simp
              qed
            next
              case False
              then obtain child_level child_mass where child_annotation:
                  "comma_semantic_b1_crt_mass_tree_lookup tree child =
                     Some (child_level,child_mass)"
                and child_level_bound: "Suc level\<le>child_level"
                using child_valid
                by (auto simp: comma_semantic_b1_crt_mass_tree_child_valid_def)
              have child_mass_sound:
                  "comma_semantic_b1_crt_column_mass
                    (comma_semantic_b1_crt_column_at dag child)=child_mass"
                using less.IH[OF child_smaller] child_annotation by blast
              have child_ge_two: "2\<le>child" using False by simp
              have child_not_terminals: "child\<noteq>0" "child\<noteq>1"
                using child_ge_two by arith+
              have annotation_mass:
                  "comma_semantic_b1_crt_mass_tree_value tree child=child_mass"
                using child_not_terminals child_annotation
                by (simp add: comma_semantic_b1_crt_mass_tree_value.simps)
              show ?thesis using child_mass_sound annotation_mass by simp
            qed
          qed
          have mapped_masses:
              "map (\<lambda>child. comma_semantic_b1_crt_column_mass
                    (comma_semantic_b1_crt_column_at dag child)) children =
                map (comma_semantic_b1_crt_mass_tree_value tree) children"
            by (rule map_cong[OF refl]) (use child_mass_agreement in blast)
          have mass_step:
              "comma_semantic_b1_crt_column_mass
                  (comma_semantic_b1_crt_column_at dag cid) =
                sum_list (map (comma_semantic_b1_crt_mass_tree_value tree) children) div
                  comma_crt_period level"
            using node_shape mapped_masses
            by (simp only: comma_semantic_b1_crt_column_mass.simps(2) map_map comp_def)
          show "comma_crt_admitted 0 (comma_semantic_b1_crt_column_at dag cid) \<and>
              comma_semantic_b1_crt_column_mass (comma_semantic_b1_crt_column_at dag cid)=mass"
          proof
            show "comma_crt_admitted 0 (comma_semantic_b1_crt_column_at dag cid)"
              using source by (rule comma_semantic_b1_crt_column_at_admitted_at) simp
            show "comma_semantic_b1_crt_column_mass
                (comma_semantic_b1_crt_column_at dag cid)=mass"
              using mass_step recurrence by simp
          qed
        qed
      qed
    qed
  qed
qed

ML \<open>comma_semantic_b1_column_at_admitted_timer "mass-tree-sound-done"\<close>

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_mass_tree_lookup_row_valid
    comma_semantic_b1_crt_mass_tree_lookup_node_shape
    comma_semantic_b1_crt_column_mass_annotation_tree_sound}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "B1 annotated mass tree theorem depends on an oracle"
\<close>

end
