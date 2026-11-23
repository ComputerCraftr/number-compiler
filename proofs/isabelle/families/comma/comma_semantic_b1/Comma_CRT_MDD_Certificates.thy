theory Comma_CRT_MDD_Certificates
  imports Comma_CRT_MDD_Shift Comma_Continue_Frontier24_Core_Guard
begin

text \<open>
The proposal arena owns shared node storage. The certificate store freezes
one named table and checks its topology with the existing indexed selector.
Neither proposal construction nor table wellformedness authenticates a source
transition; source and preimage consumers must provide their own refinements.
\<close>

lemma comma_crt_mdd_segment_root:
  fixes nodes rows :: "'a list"
  assumes "nodes = rows"
  shows "\<forall>i<length rows. nodes ! (0+i) = rows ! i"
  using assms by simp

lemma comma_crt_mdd_segment_left_sized:
  fixes nodes left right :: "'a list" and offset :: nat
  assumes segment:
      "\<forall>i<length (left @ right).
        nodes ! (offset+i) = (left @ right) ! i"
  shows "\<forall>i<length left. nodes ! (offset+i) = left ! i"
proof (intro allI impI)
  fix i assume bound: "i < length left"
  have parent_bound: "i < length (left @ right)"
    using bound by (simp only: length_append; arith)
  have row: "nodes ! (offset+i) = (left @ right) ! i"
    using segment parent_bound by blast
  show "nodes ! (offset+i) = left ! i"
    using row bound by (simp add: nth_append)
qed

lemma comma_crt_mdd_segment_right_sized:
  fixes nodes left right :: "'a list" and offset right_offset :: nat
  assumes segment:
      "\<forall>i<length (left @ right).
        nodes ! (offset+i) = (left @ right) ! i"
    and rebase: "offset + length left = right_offset"
  shows "\<forall>i<length right.
    nodes ! (right_offset+i) = right ! i"
proof (intro allI impI)
  fix i assume bound: "i < length right"
  have parent_bound: "length left+i < length (left @ right)"
    using bound by simp
  have row:
      "nodes ! (offset+(length left+i)) = (left @ right) ! (length left+i)"
    using segment parent_bound by blast
  have indexed: "nodes ! ((offset+length left)+i) = right ! i"
    using row by (simp add: nth_append add.assoc)
  show "nodes ! (right_offset+i) = right ! i"
    using indexed rebase by simp
qed

text \<open>A single authenticated table bound suffices when every listed
operand is no greater than the checked ceiling.  The list, including its
order and repeated roots, remains part of the conclusion.\<close>
lemma comma_crt_mdd_operands_bounded_by_ceiling:
  fixes upper :: nat and nodes :: "'a list" and operands :: "nat list"
  assumes ceiling: "upper < length nodes"
    and below: "\<forall>root\<in>set operands. root \<le> upper"
  shows "\<forall>root\<in>set operands. root < length nodes"
  using assms by (meson order_le_less_trans)

definition comma_crt_mdd_payload_cap where
  "comma_crt_mdd_payload_cap nodes root (limit::nat) \<longleftrightarrow>
    (\<forall>payload. comma_crt_mdd_payload_support nodes root payload \<longrightarrow> payload \<le> limit)"

lemma comma_crt_mdd_payload_cap_leaf:
  assumes "root < length nodes" "nodes ! root = Comma_CRT_MDD_Leaf payload"
    and "payload \<le> limit"
  shows "comma_crt_mdd_payload_cap nodes root limit"
  using assms unfolding comma_crt_mdd_payload_cap_def
  by (auto elim: comma_crt_mdd_payload_support.cases)

lemma comma_crt_mdd_payload_branch_child_order:
  assumes "comma_crt_mdd_table_wellformed radices nodes"
    and "root < length nodes" "nodes ! root = Comma_CRT_MDD_Branch axis children"
  shows "\<forall>child\<in>set children. child < root"
  using assms
  by (auto simp: comma_crt_mdd_table_wellformed_def comma_crt_mdd_node_ordered_def list_all_iff)

lemma comma_crt_mdd_payload_cap_branch:
  assumes "root < length nodes" "nodes ! root = Comma_CRT_MDD_Branch axis children"
    and "\<forall>child\<in>set children. child < root"
    and "\<forall>child\<in>set children. comma_crt_mdd_payload_cap nodes child limit"
  shows "comma_crt_mdd_payload_cap nodes root limit"
  using assms unfolding comma_crt_mdd_payload_cap_def
  by (auto elim: comma_crt_mdd_payload_support.cases)

lemma comma_crt_mdd_payload_cap_eval:
  assumes wellformed: "comma_crt_mdd_table_wellformed radices nodes"
    and bound: "root < length nodes" and cap: "comma_crt_mdd_payload_cap nodes root limit"
    and evaluation: "comma_crt_mdd_eval_phase radices nodes phase root = Some value"
  shows "value \<le> limit"
proof -
  have raw: "comma_crt_mdd_eval_raw radices nodes (\<lambda>_. phase) root = Some value"
    using evaluation wellformed by (simp only: comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def if_True)
  show ?thesis using comma_crt_mdd_eval_raw_some_supported[OF wellformed bound raw] cap
    by (simp add: comma_crt_mdd_payload_cap_def)
qed

ML_file "crt_mdd_arena.ML"
ML_file "crt_mdd_proof_utils.ML"
ML_file "crt_balanced_table.ML"
ML_file "crt_mdd_certificate_store.ML"
ML_file "crt_mdd_operation_replay.ML"
ML_file "crt_mdd_indexed_slots.ML"
lemma comma_crt_mdd_selected_branch_cofactor:
  assumes "axis < length radices" "0 < radices ! axis"
    "slot < radices ! axis" "root < length nodes"
    "nodes ! root = Comma_CRT_MDD_Branch axis children"
    "length children = radices ! axis" "children ! slot = child"
  shows "comma_crt_mdd_cofactor radices nodes axis slot root = Some child"
  using assms by (simp add: comma_crt_mdd_cofactor_def)

ML_file "crt_mdd_bind_replay.ML"

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Frozen-table segment transport"
    @{thms comma_crt_mdd_segment_root comma_crt_mdd_segment_left_sized
      comma_crt_mdd_segment_right_sized};
\<close>

end
