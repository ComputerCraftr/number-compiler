theory Comma_Semantic_B1_CRT_Mass_Layout
  imports Comma_Semantic_B1_CRT_Mass_Annotations
begin

text \<open>
The concrete producer certifies this summary bottom-up on the exact annotation
terms it already holds. A summary records the recursive interval/AVL claim,
the computed height, and the exact root key (or the empty-tree marker). The
node introduction below mentions only the two immediate child terms; it does
not normalize or reconstruct either subtree.
\<close>

definition comma_semantic_b1_crt_mass_tree_summary ::
  "nat \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> nat \<Rightarrow>
    comma_semantic_b1_crt_mass_tree \<Rightarrow> bool" where
  "comma_semantic_b1_crt_mass_tree_summary lower upper root height tree \<longleftrightarrow>
    comma_semantic_b1_crt_mass_tree_ordered lower upper tree \<and>
    comma_semantic_b1_crt_mass_tree_height tree = height \<and>
    (case tree of
      Comma_B1_CRT_Mass_Tree_Empty \<Rightarrow> root = None
    | Comma_B1_CRT_Mass_Tree_Node cid level mass left right \<Rightarrow>
        root = Some cid)"

definition comma_semantic_b1_crt_mass_tree_lookup_transport ::
    "comma_semantic_b1_crt_mass_tree \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_crt_mass_tree \<Rightarrow> bool" where
  "comma_semantic_b1_crt_mass_tree_lookup_transport root lower upper subtree \<longleftrightarrow>
    (\<forall>cid. lower\<le>cid \<and> cid<upper \<longrightarrow>
      comma_semantic_b1_crt_mass_tree_lookup root cid =
        comma_semantic_b1_crt_mass_tree_lookup subtree cid)"

lemma comma_semantic_b1_crt_mass_tree_lookup_transport_root:
  assumes root: "root = tree"
  shows "comma_semantic_b1_crt_mass_tree_lookup_transport root lower upper tree"
  using root by (auto simp: comma_semantic_b1_crt_mass_tree_lookup_transport_def)

lemma comma_semantic_b1_crt_mass_tree_lookup_transport_left:
  assumes ordered:
      "comma_semantic_b1_crt_mass_tree_ordered lower upper
        (Comma_B1_CRT_Mass_Tree_Node key level mass left right)"
    and transport:
      "comma_semantic_b1_crt_mass_tree_lookup_transport root lower upper
        (Comma_B1_CRT_Mass_Tree_Node key level mass left right)"
  shows "comma_semantic_b1_crt_mass_tree_lookup_transport root lower key left"
proof -
  have key_lower: "lower \<le> key" and key_upper: "key < upper"
    using ordered by simp_all
  show ?thesis
    unfolding comma_semantic_b1_crt_mass_tree_lookup_transport_def
  proof (intro allI impI)
    fix cid
    assume range: "lower \<le> cid \<and> cid < key"
    have parent_range: "lower \<le> cid \<and> cid < upper"
      using range key_upper by auto
    have carried:
      "comma_semantic_b1_crt_mass_tree_lookup root cid =
        comma_semantic_b1_crt_mass_tree_lookup
          (Comma_B1_CRT_Mass_Tree_Node key level mass left right) cid"
      using transport parent_range
      by (simp add: comma_semantic_b1_crt_mass_tree_lookup_transport_def)
    have selected:
      "comma_semantic_b1_crt_mass_tree_lookup
          (Comma_B1_CRT_Mass_Tree_Node key level mass left right) cid =
        comma_semantic_b1_crt_mass_tree_lookup left cid"
      using range by simp
    show "comma_semantic_b1_crt_mass_tree_lookup root cid =
        comma_semantic_b1_crt_mass_tree_lookup left cid"
      using carried selected by simp
  qed
qed

lemma comma_semantic_b1_crt_mass_tree_lookup_transport_right:
  assumes ordered:
      "comma_semantic_b1_crt_mass_tree_ordered lower upper
        (Comma_B1_CRT_Mass_Tree_Node key level mass left right)"
    and transport:
      "comma_semantic_b1_crt_mass_tree_lookup_transport root lower upper
        (Comma_B1_CRT_Mass_Tree_Node key level mass left right)"
  shows "comma_semantic_b1_crt_mass_tree_lookup_transport root (Suc key) upper right"
proof -
  have key_lower: "lower \<le> key" and key_upper: "key < upper"
    using ordered by simp_all
  show ?thesis
    unfolding comma_semantic_b1_crt_mass_tree_lookup_transport_def
  proof (intro allI impI)
    fix cid
    assume range: "Suc key \<le> cid \<and> cid < upper"
    have key_cid: "key < cid" using range by simp
    have lower_cid: "lower \<le> cid" using key_lower key_cid by arith
    have parent_range: "lower \<le> cid \<and> cid < upper"
      using lower_cid range by simp
    have carried:
      "comma_semantic_b1_crt_mass_tree_lookup root cid =
        comma_semantic_b1_crt_mass_tree_lookup
          (Comma_B1_CRT_Mass_Tree_Node key level mass left right) cid"
      using transport parent_range
      by (simp add: comma_semantic_b1_crt_mass_tree_lookup_transport_def)
    have selected:
      "comma_semantic_b1_crt_mass_tree_lookup
          (Comma_B1_CRT_Mass_Tree_Node key level mass left right) cid =
        comma_semantic_b1_crt_mass_tree_lookup right cid"
      using key_cid by simp
    show "comma_semantic_b1_crt_mass_tree_lookup root cid =
        comma_semantic_b1_crt_mass_tree_lookup right cid"
      using carried selected by simp
  qed
qed

lemma comma_semantic_b1_crt_mass_tree_lookup_transport_node_key:
  assumes ordered:
      "comma_semantic_b1_crt_mass_tree_ordered lower upper
        (Comma_B1_CRT_Mass_Tree_Node key level mass left right)"
    and transport:
      "comma_semantic_b1_crt_mass_tree_lookup_transport root lower upper
        (Comma_B1_CRT_Mass_Tree_Node key level mass left right)"
  shows "comma_semantic_b1_crt_mass_tree_lookup root key = Some (level,mass)"
proof -
  have key_range: "lower \<le> key \<and> key < upper" using ordered by simp
  have carried:
      "comma_semantic_b1_crt_mass_tree_lookup root key =
        comma_semantic_b1_crt_mass_tree_lookup
          (Comma_B1_CRT_Mass_Tree_Node key level mass left right) key"
    using transport key_range
    by (simp add: comma_semantic_b1_crt_mass_tree_lookup_transport_def)
  show ?thesis using carried by simp
qed

lemma comma_semantic_b1_crt_mass_tree_ordered_children:
  assumes ordered:
      "comma_semantic_b1_crt_mass_tree_ordered lower upper
        (Comma_B1_CRT_Mass_Tree_Node key level mass left right)"
  shows "comma_semantic_b1_crt_mass_tree_ordered lower key left \<and>
    comma_semantic_b1_crt_mass_tree_ordered (Suc key) upper right"
  using ordered by simp


lemma comma_semantic_b1_crt_mass_tree_lookup_transport_split:
  assumes ordered:
      "comma_semantic_b1_crt_mass_tree_ordered lower upper
        (Comma_B1_CRT_Mass_Tree_Node key level mass left right)"
    and transport:
      "comma_semantic_b1_crt_mass_tree_lookup_transport root lower upper
        (Comma_B1_CRT_Mass_Tree_Node key level mass left right)"
  shows "comma_semantic_b1_crt_mass_tree_lookup root key = Some (level,mass) \<and>
    (comma_semantic_b1_crt_mass_tree_ordered lower key left \<and>
      (comma_semantic_b1_crt_mass_tree_ordered (Suc key) upper right \<and>
        (comma_semantic_b1_crt_mass_tree_lookup_transport root lower key left \<and>
          comma_semantic_b1_crt_mass_tree_lookup_transport root (Suc key) upper right)))"
proof -
  have key_fact:
    "comma_semantic_b1_crt_mass_tree_lookup root key = Some (level,mass)"
    by (rule comma_semantic_b1_crt_mass_tree_lookup_transport_node_key
      [OF ordered transport])
  have ordered_children:
    "comma_semantic_b1_crt_mass_tree_ordered lower key left \<and>
      comma_semantic_b1_crt_mass_tree_ordered (Suc key) upper right"
    by (rule comma_semantic_b1_crt_mass_tree_ordered_children [OF ordered])
  have left_ordered:
    "comma_semantic_b1_crt_mass_tree_ordered lower key left"
    using ordered_children by (rule conjunct1)
  have right_ordered:
    "comma_semantic_b1_crt_mass_tree_ordered (Suc key) upper right"
    using ordered_children by (rule conjunct2)
  have left_transport:
    "comma_semantic_b1_crt_mass_tree_lookup_transport root lower key left"
    by (rule comma_semantic_b1_crt_mass_tree_lookup_transport_left
      [OF ordered transport])
  have right_transport:
    "comma_semantic_b1_crt_mass_tree_lookup_transport root (Suc key) upper right"
    by (rule comma_semantic_b1_crt_mass_tree_lookup_transport_right
      [OF ordered transport])
  show ?thesis
  proof (rule conjI)
    show "comma_semantic_b1_crt_mass_tree_lookup root key = Some (level,mass)"
      by (rule key_fact)
  next
    show "comma_semantic_b1_crt_mass_tree_ordered lower key left \<and>
        (comma_semantic_b1_crt_mass_tree_ordered (Suc key) upper right \<and>
          (comma_semantic_b1_crt_mass_tree_lookup_transport root lower key left \<and>
            comma_semantic_b1_crt_mass_tree_lookup_transport root (Suc key) upper right))"
    proof (rule conjI)
      show "comma_semantic_b1_crt_mass_tree_ordered lower key left"
        by (rule left_ordered)
    next
      show "comma_semantic_b1_crt_mass_tree_ordered (Suc key) upper right \<and>
          (comma_semantic_b1_crt_mass_tree_lookup_transport root lower key left \<and>
            comma_semantic_b1_crt_mass_tree_lookup_transport root (Suc key) upper right)"
      proof (rule conjI)
        show "comma_semantic_b1_crt_mass_tree_ordered (Suc key) upper right"
          by (rule right_ordered)
      next
        show "comma_semantic_b1_crt_mass_tree_lookup_transport root lower key left \<and>
            comma_semantic_b1_crt_mass_tree_lookup_transport root (Suc key) upper right"
          by (rule conjI [OF left_transport right_transport])
      qed
    qed
  qed
qed

text \<open>
The source block directory is authenticated independently from the sparse
mass tree.  These interval facts let the concrete producer derive each
source-row theorem while visiting a block node once, rather than restarting a
root lookup for every CID.
\<close>

definition comma_semantic_b1_crt_mass_source_lookup_transport ::
    "comma_semantic_b1_crt_column_dag \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_crt_column_block \<Rightarrow> bool" where
  "comma_semantic_b1_crt_mass_source_lookup_transport dag lower upper subtree \<longleftrightarrow>
    (\<forall>cid. lower\<le>cid \<and> cid<upper \<longrightarrow>
      comma_semantic_b1_crt_column_dag_lookup dag cid =
        comma_semantic_b1_crt_column_block_lookup subtree cid)"

lemma comma_semantic_b1_crt_mass_source_lookup_transport_root:
  assumes interval:
      "\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
        comma_semantic_b1_crt_column_dag_lookup dag cid =
          comma_semantic_b1_crt_column_block_lookup constant cid"
    and root: "constant = subtree"
  shows "comma_semantic_b1_crt_mass_source_lookup_transport dag lower upper subtree"
  using interval root
  by (auto simp: comma_semantic_b1_crt_mass_source_lookup_transport_def)

lemma comma_semantic_b1_crt_mass_source_lookup_transport_left:
  assumes lower_key: "lower \<le> key"
    and key_upper: "key < upper"
    and transport:
      "comma_semantic_b1_crt_mass_source_lookup_transport dag lower upper
        (Comma_B1_CRT_Column_Block_Node key level children left right)"
  shows "comma_semantic_b1_crt_mass_source_lookup_transport dag lower key left"
proof -
  show ?thesis
    unfolding comma_semantic_b1_crt_mass_source_lookup_transport_def
  proof (intro allI impI)
    fix cid
    assume range: "lower \<le> cid \<and> cid < key"
    have parent_range: "lower \<le> cid \<and> cid < upper"
      using range key_upper by auto
    have carried:
      "comma_semantic_b1_crt_column_dag_lookup dag cid =
        comma_semantic_b1_crt_column_block_lookup
          (Comma_B1_CRT_Column_Block_Node key level children left right) cid"
      using transport parent_range
      by (simp add: comma_semantic_b1_crt_mass_source_lookup_transport_def)
    have selected:
      "comma_semantic_b1_crt_column_block_lookup
          (Comma_B1_CRT_Column_Block_Node key level children left right) cid =
        comma_semantic_b1_crt_column_block_lookup left cid"
      using range by simp
    show "comma_semantic_b1_crt_column_dag_lookup dag cid =
        comma_semantic_b1_crt_column_block_lookup left cid"
      using carried selected by simp
  qed
qed

lemma comma_semantic_b1_crt_mass_source_lookup_transport_right:
  assumes lower_key: "lower \<le> key"
    and key_upper: "key < upper"
    and transport:
      "comma_semantic_b1_crt_mass_source_lookup_transport dag lower upper
        (Comma_B1_CRT_Column_Block_Node key level children left right)"
  shows "comma_semantic_b1_crt_mass_source_lookup_transport dag (Suc key) upper right"
proof -
  show ?thesis
    unfolding comma_semantic_b1_crt_mass_source_lookup_transport_def
  proof (intro allI impI)
    fix cid
    assume range: "Suc key \<le> cid \<and> cid < upper"
    have key_cid: "key < cid" using range by simp
    have lower_cid: "lower \<le> cid" using lower_key key_cid by arith
    have parent_range: "lower \<le> cid \<and> cid < upper"
      using lower_cid range by simp
    have carried:
      "comma_semantic_b1_crt_column_dag_lookup dag cid =
        comma_semantic_b1_crt_column_block_lookup
          (Comma_B1_CRT_Column_Block_Node key level children left right) cid"
      using transport parent_range
      by (simp add: comma_semantic_b1_crt_mass_source_lookup_transport_def)
    have selected:
      "comma_semantic_b1_crt_column_block_lookup
          (Comma_B1_CRT_Column_Block_Node key level children left right) cid =
        comma_semantic_b1_crt_column_block_lookup right cid"
      using key_cid by simp
    show "comma_semantic_b1_crt_column_dag_lookup dag cid =
        comma_semantic_b1_crt_column_block_lookup right cid"
      using carried selected by simp
  qed
qed

lemma comma_semantic_b1_crt_mass_source_lookup_transport_node_key:
  assumes lower_key: "lower \<le> key"
    and key_upper: "key < upper"
    and transport:
      "comma_semantic_b1_crt_mass_source_lookup_transport dag lower upper
        (Comma_B1_CRT_Column_Block_Node key level children left right)"
  shows "comma_semantic_b1_crt_column_dag_lookup dag key = Some (level,children)"
proof -
  have carried:
    "comma_semantic_b1_crt_column_dag_lookup dag key =
      comma_semantic_b1_crt_column_block_lookup
        (Comma_B1_CRT_Column_Block_Node key level children left right) key"
    using transport lower_key key_upper
    by (simp add: comma_semantic_b1_crt_mass_source_lookup_transport_def)
  show ?thesis using carried by simp
qed

lemma comma_semantic_b1_crt_mass_source_lookup_transport_split:
  assumes lower_key: "lower \<le> key"
    and key_upper: "key < upper"
    and transport:
      "comma_semantic_b1_crt_mass_source_lookup_transport dag lower upper
        (Comma_B1_CRT_Column_Block_Node key level children left right)"
  shows "comma_semantic_b1_crt_column_dag_lookup dag key = Some (level,children) \<and>
    (comma_semantic_b1_crt_mass_source_lookup_transport dag lower key left \<and>
      comma_semantic_b1_crt_mass_source_lookup_transport dag (Suc key) upper right)"
proof -
  have key_fact:
    "comma_semantic_b1_crt_column_dag_lookup dag key = Some (level,children)"
    by (rule comma_semantic_b1_crt_mass_source_lookup_transport_node_key
      [OF lower_key key_upper transport])
  have left_transport:
    "comma_semantic_b1_crt_mass_source_lookup_transport dag lower key left"
    by (rule comma_semantic_b1_crt_mass_source_lookup_transport_left
      [OF lower_key key_upper transport])
  have right_transport:
    "comma_semantic_b1_crt_mass_source_lookup_transport dag (Suc key) upper right"
    by (rule comma_semantic_b1_crt_mass_source_lookup_transport_right
      [OF lower_key key_upper transport])
  show ?thesis
  proof (rule conjI)
    show "comma_semantic_b1_crt_column_dag_lookup dag key = Some (level,children)"
      by (rule key_fact)
  next
    show "comma_semantic_b1_crt_mass_source_lookup_transport dag lower key left \<and>
        comma_semantic_b1_crt_mass_source_lookup_transport dag (Suc key) upper right"
      by (rule conjI [OF left_transport right_transport])
  qed
qed


lemma comma_semantic_b1_crt_mass_tree_summary_empty:
  "comma_semantic_b1_crt_mass_tree_summary lower upper None 0
    Comma_B1_CRT_Mass_Tree_Empty"
  by (simp add: comma_semantic_b1_crt_mass_tree_summary_def)

lemma comma_semantic_b1_crt_mass_tree_summary_node:
  assumes root_lower: "lower \<le> cid"
    and root_upper: "cid < upper"
    and left_balance:
      "left_height \<le> Suc right_height"
    and right_balance:
      "right_height \<le> Suc left_height"
    and left_summary:
      "comma_semantic_b1_crt_mass_tree_summary lower cid left_root
        left_height left"
    and right_summary:
      "comma_semantic_b1_crt_mass_tree_summary (Suc cid) upper right_root
        right_height right"
  shows "comma_semantic_b1_crt_mass_tree_summary lower upper (Some cid)
    (Suc (max left_height right_height))
    (Comma_B1_CRT_Mass_Tree_Node cid level mass left right)"
proof -
  have left_ordered:
    "comma_semantic_b1_crt_mass_tree_ordered lower cid left"
    and left_height_fact:
      "comma_semantic_b1_crt_mass_tree_height left = left_height"
    using left_summary
    by (auto simp: comma_semantic_b1_crt_mass_tree_summary_def)
  have right_ordered:
    "comma_semantic_b1_crt_mass_tree_ordered (Suc cid) upper right"
    and right_height_fact:
      "comma_semantic_b1_crt_mass_tree_height right = right_height"
    using right_summary
    by (auto simp: comma_semantic_b1_crt_mass_tree_summary_def)
  show ?thesis
    unfolding comma_semantic_b1_crt_mass_tree_summary_def
    using root_lower root_upper left_balance right_balance
      left_ordered right_ordered left_height_fact right_height_fact
    by simp
qed

lemma comma_semantic_b1_crt_mass_tree_summary_ordered:
  assumes summary:
    "comma_semantic_b1_crt_mass_tree_summary lower upper root height tree"
  shows "comma_semantic_b1_crt_mass_tree_ordered lower upper tree"
  using summary by (simp add: comma_semantic_b1_crt_mass_tree_summary_def)

lemma comma_semantic_b1_crt_mass_tree_summary_height:
  assumes summary:
    "comma_semantic_b1_crt_mass_tree_summary lower upper root height tree"
  shows "comma_semantic_b1_crt_mass_tree_height tree = height"
  using summary by (simp add: comma_semantic_b1_crt_mass_tree_summary_def)

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_mass_tree_summary_empty
    comma_semantic_b1_crt_mass_tree_summary_node
    comma_semantic_b1_crt_mass_tree_summary_ordered
    comma_semantic_b1_crt_mass_tree_summary_height
    comma_semantic_b1_crt_mass_tree_lookup_transport_root
    comma_semantic_b1_crt_mass_tree_lookup_transport_left
    comma_semantic_b1_crt_mass_tree_lookup_transport_right
    comma_semantic_b1_crt_mass_tree_lookup_transport_node_key
    comma_semantic_b1_crt_mass_tree_lookup_transport_split
    comma_semantic_b1_crt_mass_source_lookup_transport_root
    comma_semantic_b1_crt_mass_source_lookup_transport_left
    comma_semantic_b1_crt_mass_source_lookup_transport_right
    comma_semantic_b1_crt_mass_source_lookup_transport_node_key
    comma_semantic_b1_crt_mass_source_lookup_transport_split
    comma_semantic_b1_crt_mass_tree_ordered_children}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "B1 mass layout theorem depends on an oracle"
  val _ = Comma_Proof_Profile.report "Mass layout stage=kernel-checked"
\<close>

end
