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

ML_file "crt_mdd_arena.ML"
ML_file "crt_mdd_proof_utils.ML"
ML_file "crt_mdd_certificate_store.ML"
ML_file "crt_mdd_operation_replay.ML"
ML_file "crt_mdd_bind_replay.ML"

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Frozen-table segment transport"
    @{thms comma_crt_mdd_segment_root comma_crt_mdd_segment_left_sized
      comma_crt_mdd_segment_right_sized};
\<close>

end
