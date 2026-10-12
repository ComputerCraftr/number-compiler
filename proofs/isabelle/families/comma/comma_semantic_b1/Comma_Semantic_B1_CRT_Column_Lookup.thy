theory Comma_Semantic_B1_CRT_Column_Lookup
  imports Comma_Semantic_B1_CRT_Column_DAG
begin

text \<open>
  Transfer lookup from a checked block root to a selected subtree over a
  numeric interval.  The interval facts let a caller cache one theorem for
  each visited subtree and reuse it for every CID in that subtree's range.
\<close>

lemma comma_semantic_b1_crt_column_block_lookup_interval_cong:
  assumes equal: "root = subtree"
  shows "(\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
      comma_semantic_b1_crt_column_block_lookup root cid =
        comma_semantic_b1_crt_column_block_lookup subtree cid)"
  using equal by simp

lemma comma_semantic_b1_crt_column_block_lookup_interval_left:
  assumes lower_key: "lower \<le> key"
    and key_upper: "key < upper"
    and parent:
      "(\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
        comma_semantic_b1_crt_column_block_lookup root cid =
          comma_semantic_b1_crt_column_block_lookup
            (Comma_B1_CRT_Column_Block_Node key level children left right) cid)"
  shows
    "(\<forall>cid. lower \<le> cid \<and> cid < key \<longrightarrow>
      comma_semantic_b1_crt_column_block_lookup root cid =
        comma_semantic_b1_crt_column_block_lookup left cid)"
  using lower_key key_upper parent
  by (auto simp: comma_semantic_b1_crt_column_block_lookup.simps)

lemma comma_semantic_b1_crt_column_block_lookup_interval_right:
  assumes lower_key: "lower \<le> key"
    and key_upper: "key < upper"
    and parent:
      "(\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
        comma_semantic_b1_crt_column_block_lookup root cid =
          comma_semantic_b1_crt_column_block_lookup
            (Comma_B1_CRT_Column_Block_Node key level children left right) cid)"
  shows
    "(\<forall>cid. Suc key \<le> cid \<and> cid < upper \<longrightarrow>
      comma_semantic_b1_crt_column_block_lookup root cid =
        comma_semantic_b1_crt_column_block_lookup right cid)"
  using lower_key key_upper parent
  by (auto simp: comma_semantic_b1_crt_column_block_lookup.simps)

lemma comma_semantic_b1_crt_column_block_lookup_node_key:
  "comma_semantic_b1_crt_column_block_lookup
      (Comma_B1_CRT_Column_Block_Node key level children left right) key =
    Some (level, children)"
  by simp

lemmas comma_semantic_b1_crt_column_lookup_oracle_audit_bundle =
  comma_semantic_b1_crt_column_block_lookup_interval_cong
  comma_semantic_b1_crt_column_block_lookup_interval_left
  comma_semantic_b1_crt_column_block_lookup_interval_right
  comma_semantic_b1_crt_column_block_lookup_node_key

text \<open>
  Transfer a checked directory lookup over a fixed CID interval.  Unlike a
  pointwise directory walk, these facts let the ML owner cache one proof per
  selected block and specialize it for every CID in that block.
\<close>

lemma comma_semantic_b1_crt_column_dag_lookup_interval_refl:
  "\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
    comma_semantic_b1_crt_column_dag_lookup root cid =
      comma_semantic_b1_crt_column_dag_lookup root cid"
  by simp

lemma comma_semantic_b1_crt_column_dag_lookup_interval_rootdef:
  assumes root_equation: "root = body"
  shows "\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
    comma_semantic_b1_crt_column_dag_lookup root cid =
      comma_semantic_b1_crt_column_dag_lookup body cid"
  using root_equation by simp

lemma comma_semantic_b1_crt_column_dag_lookup_interval_left:
  assumes upper_split: "upper \<le> split"
    and parent:
      "(\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
        comma_semantic_b1_crt_column_dag_lookup root cid =
          comma_semantic_b1_crt_column_dag_lookup
            (Comma_B1_CRT_Column_DAG_Branch split left right) cid)"
  shows "(\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
    comma_semantic_b1_crt_column_dag_lookup root cid =
      comma_semantic_b1_crt_column_dag_lookup left cid)"
  using upper_split parent
  by (auto simp: comma_semantic_b1_crt_column_dag_lookup.simps; arith)

lemma comma_semantic_b1_crt_column_dag_lookup_interval_right:
  assumes split_lower: "split \<le> lower"
    and parent:
      "(\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
        comma_semantic_b1_crt_column_dag_lookup root cid =
          comma_semantic_b1_crt_column_dag_lookup
            (Comma_B1_CRT_Column_DAG_Branch split left right) cid)"
  shows "(\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
    comma_semantic_b1_crt_column_dag_lookup root cid =
      comma_semantic_b1_crt_column_dag_lookup right cid)"
  using split_lower parent
  by (auto simp: comma_semantic_b1_crt_column_dag_lookup.simps; arith)

lemma comma_semantic_b1_crt_column_dag_lookup_interval_block:
  assumes base_lower: "base \<le> lower"
    and upper_bound: "upper \<le> base + extent"
    and parent:
      "(\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
        comma_semantic_b1_crt_column_dag_lookup root cid =
          comma_semantic_b1_crt_column_dag_lookup
            (Comma_B1_CRT_Column_DAG_Block base extent block) cid)"
  shows "(\<forall>cid. lower \<le> cid \<and> cid < upper \<longrightarrow>
    comma_semantic_b1_crt_column_dag_lookup root cid =
      comma_semantic_b1_crt_column_block_lookup block cid)"
  using base_lower upper_bound parent
  by (auto simp: comma_semantic_b1_crt_column_dag_lookup.simps; arith)

lemmas comma_semantic_b1_crt_column_dag_interval_oracle_audit_bundle =
  comma_semantic_b1_crt_column_dag_lookup_interval_refl
  comma_semantic_b1_crt_column_dag_lookup_interval_rootdef
  comma_semantic_b1_crt_column_dag_lookup_interval_left
  comma_semantic_b1_crt_column_dag_lookup_interval_right
  comma_semantic_b1_crt_column_dag_lookup_interval_block

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_column_dag_interval_oracle_audit_bundle}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Column DAG interval transfer depends on an oracle"
\<close>

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_column_lookup_oracle_audit_bundle}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Column lookup transfer depends on an oracle"
\<close>

end
