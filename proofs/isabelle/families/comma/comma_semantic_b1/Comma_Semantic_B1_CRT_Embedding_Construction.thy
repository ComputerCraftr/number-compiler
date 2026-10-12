theory Comma_Semantic_B1_CRT_Embedding_Construction
  imports Comma_Semantic_B1_CRT_Indexed_Labels
begin

text \<open>
A boolean flags list is a constructive occurrence projection.  A @{term True} head keeps
an arbitrary column, while a @{term False} head deletes a supplied false
column.  The offset is the absolute source position of the current head.
Consequently, the constructors prepend positions without repeatedly mapping
successor over the already-built tail.  In particular, the relation does not
require kept columns to be non-false.
\<close>

inductive comma_semantic_b1_crt_indexed_mask ::
    "nat \<Rightarrow> bool list \<Rightarrow> comma_crt_column list \<Rightarrow> nat list \<Rightarrow>
      comma_crt_column list \<Rightarrow> bool" where
  comma_semantic_b1_crt_indexed_mask_nil:
    "comma_semantic_b1_crt_indexed_mask offset [] [] [] []"
| comma_semantic_b1_crt_indexed_mask_keep:
    "comma_semantic_b1_crt_indexed_mask
       (Suc offset) flags columns positions compact \<Longrightarrow>
     comma_semantic_b1_crt_indexed_mask
       offset (True#flags) (column#columns)
       (offset#positions) (column#compact)"
| comma_semantic_b1_crt_indexed_mask_drop:
    "column=Comma_CRT_Bool False \<Longrightarrow>
     comma_semantic_b1_crt_indexed_mask
       (Suc offset) flags columns positions compact \<Longrightarrow>
     comma_semantic_b1_crt_indexed_mask
       offset (False#flags) (column#columns) positions compact"

lemma comma_semantic_b1_crt_indexed_mask_position_length:
  assumes flags:
    "comma_semantic_b1_crt_indexed_mask
       offset flags columns positions compact"
  shows "length positions=length compact"
  using flags
proof (induction rule: comma_semantic_b1_crt_indexed_mask.induct)
  case comma_semantic_b1_crt_indexed_mask_nil
  then show ?case by simp
next
  case comma_semantic_b1_crt_indexed_mask_keep
  then show ?case by simp
next
  case comma_semantic_b1_crt_indexed_mask_drop
  then show ?case by simp
qed

lemma comma_semantic_b1_crt_indexed_mask_source_length:
  assumes flags:
    "comma_semantic_b1_crt_indexed_mask
       offset flags columns positions compact"
  shows "length flags=length columns"
  using flags
proof (induction rule: comma_semantic_b1_crt_indexed_mask.induct)
  case comma_semantic_b1_crt_indexed_mask_nil
  then show ?case by simp
next
  case comma_semantic_b1_crt_indexed_mask_keep
  then show ?case by simp
next
  case comma_semantic_b1_crt_indexed_mask_drop
  then show ?case by simp
qed

lemma comma_semantic_b1_crt_indexed_mask_drop_false:
  assumes flags:
    "comma_semantic_b1_crt_indexed_mask
       offset flags columns positions compact"
  shows "comma_semantic_b1_crt_partition_drop_false compact =
    comma_semantic_b1_crt_partition_drop_false columns"
  using flags
proof (induction rule: comma_semantic_b1_crt_indexed_mask.induct)
  case comma_semantic_b1_crt_indexed_mask_nil
  then show ?case by simp
next
  case comma_semantic_b1_crt_indexed_mask_keep
  then show ?case by simp
next
  case comma_semantic_b1_crt_indexed_mask_drop
  then show ?case by simp
qed

lemma comma_semantic_b1_crt_indexed_mask_position_lower:
  assumes flags:
    "comma_semantic_b1_crt_indexed_mask
       offset flags columns positions compact"
  shows "\<forall>position\<in>set positions. offset\<le>position"
  using flags
proof (induction rule: comma_semantic_b1_crt_indexed_mask.induct)
  case comma_semantic_b1_crt_indexed_mask_nil
  then show ?case by simp
next
  case (comma_semantic_b1_crt_indexed_mask_keep
      offset flags columns positions compact column)
  have tail:
      "\<forall>position\<in>set positions. Suc offset\<le>position"
    by (rule comma_semantic_b1_crt_indexed_mask_keep.IH)
  show ?case using tail
    by (auto simp: list_all_iff dest: Suc_leD)
next
  case (comma_semantic_b1_crt_indexed_mask_drop
      column offset flags columns positions compact)
  have tail:
      "\<forall>position\<in>set positions. Suc offset\<le>position"
    by (rule comma_semantic_b1_crt_indexed_mask_drop.IH)
  show ?case using tail
    by (auto dest: Suc_leD)
qed

lemma comma_semantic_b1_crt_indexed_mask_alignment:
  assumes flags:
    "comma_semantic_b1_crt_indexed_mask
       offset flags columns positions compact"
  shows "\<forall>j<length compact.
    offset\<le>positions!j \<and>
    positions!j<offset+length columns \<and>
    columns!(positions!j-offset)=compact!j"
  using flags
proof (induction rule: comma_semantic_b1_crt_indexed_mask.induct)
  case comma_semantic_b1_crt_indexed_mask_nil
  then show ?case by simp
next
  case (comma_semantic_b1_crt_indexed_mask_keep
      offset flags columns positions compact column)
  show ?case
  proof (intro allI impI)
    fix j
    assume j: "j<length (column#compact)"
    show "offset\<le>(offset#positions)!j \<and>
      (offset#positions)!j < offset+length (column#columns) \<and>
      (column#columns)!((offset#positions)!j-offset)=(column#compact)!j"
    proof (cases j)
      case 0
      then show ?thesis by simp
    next
      case (Suc k)
      have k: "k<length compact" using j Suc by simp
      have tail:
          "Suc offset\<le>positions!k \<and>
           positions!k<Suc offset+length columns \<and>
           columns!(positions!k-Suc offset)=compact!k"
        using comma_semantic_b1_crt_indexed_mask_keep.IH[rule_format, OF k] .
      have difference:
          "positions!k-offset=Suc (positions!k-Suc offset)"
        using tail(1) by arith
      show ?thesis using tail difference Suc by (simp add: add_Suc)
    qed
  qed
next
  case (comma_semantic_b1_crt_indexed_mask_drop
      column offset flags columns positions compact)
  show ?case
  proof (intro allI impI)
    fix j
    assume j: "j<length compact"
    have tail:
        "Suc offset\<le>positions!j \<and>
         positions!j<Suc offset+length columns \<and>
         columns!(positions!j-Suc offset)=compact!j"
      using comma_semantic_b1_crt_indexed_mask_drop.IH[rule_format, OF j] .
    have difference:
        "positions!j-offset=Suc (positions!j-Suc offset)"
      using tail(1) by arith
    show "offset\<le>positions!j \<and>
      positions!j < offset+length (column#columns) \<and>
      (column#columns)!(positions!j-offset)=compact!j"
      using tail difference by (simp add: add_Suc)
  qed
qed

lemma comma_semantic_b1_crt_indexed_mask_omitted_false:
  assumes flags:
    "comma_semantic_b1_crt_indexed_mask
       offset flags columns positions compact"
  shows "\<forall>i<length columns. offset+i\<notin>set positions \<longrightarrow>
    columns!i=Comma_CRT_Bool False"
  using flags
proof (induction rule: comma_semantic_b1_crt_indexed_mask.induct)
  case comma_semantic_b1_crt_indexed_mask_nil
  then show ?case by simp
next
  case (comma_semantic_b1_crt_indexed_mask_keep
      offset flags columns positions compact column)
  show ?case
  proof (intro allI impI impI)
    fix i
    assume i: "i<length (column#columns)"
    assume absent: "offset+i\<notin>set (offset#positions)"
    show "(column#columns)!i=Comma_CRT_Bool False"
    proof (cases i)
      case 0
      then show ?thesis using absent by simp
    next
      case (Suc k)
      have k_bound: "k<length columns" using i Suc by simp
      have tail_absent: "Suc offset+k\<notin>set positions"
      proof
        assume member: "Suc offset+k\<in>set positions"
        have member': "offset+Suc k\<in>set (offset#positions)"
          using member by (auto simp: add_Suc)
        show False using absent member' Suc by simp
      qed
      have tail:
          "columns!k=Comma_CRT_Bool False"
        using comma_semantic_b1_crt_indexed_mask_keep.IH[rule_format,
          OF k_bound tail_absent] .
      show ?thesis using tail Suc by simp
    qed
  qed
next
  case (comma_semantic_b1_crt_indexed_mask_drop
      column offset flags columns positions compact)
  show ?case
  proof (intro allI impI impI)
    fix i
    assume i: "i<length (column#columns)"
    assume absent: "offset+i\<notin>set positions"
    show "(column#columns)!i=Comma_CRT_Bool False"
    proof (cases i)
      case 0
      then show ?thesis
        using comma_semantic_b1_crt_indexed_mask_drop.hyps(1) by simp
    next
      case (Suc k)
      have k_bound: "k<length columns" using i Suc by simp
      have tail_absent: "Suc offset+k\<notin>set positions"
        using absent Suc by (simp add: add_Suc)
      have tail:
          "columns!k=Comma_CRT_Bool False"
        using comma_semantic_b1_crt_indexed_mask_drop.IH[rule_format,
          OF k_bound tail_absent] .
      show ?thesis using tail Suc by simp
    qed
  qed
qed

lemma comma_semantic_b1_crt_indexed_mask_distinct:
  assumes flags:
    "comma_semantic_b1_crt_indexed_mask
       offset flags columns positions compact"
  shows "distinct positions"
  using flags
proof (induction rule: comma_semantic_b1_crt_indexed_mask.induct)
  case comma_semantic_b1_crt_indexed_mask_nil
  then show ?case by simp
next
  case (comma_semantic_b1_crt_indexed_mask_keep
      offset flags columns positions compact column)
  have tail:
      "distinct positions"
    by (rule comma_semantic_b1_crt_indexed_mask_keep.IH)
  have lower:
      "\<forall>position\<in>set positions. Suc offset\<le>position"
    by (rule comma_semantic_b1_crt_indexed_mask_position_lower
      [OF comma_semantic_b1_crt_indexed_mask_keep.hyps(1)])
  have absent: "offset\<notin>set positions"
    using lower by auto
  show ?case using tail absent by simp
next
  case comma_semantic_b1_crt_indexed_mask_drop
  then show ?case by simp
qed

lemma comma_semantic_b1_crt_indexed_mask_embedding:
  assumes flags:
    "comma_semantic_b1_crt_indexed_mask
       0 flags columns positions compact"
  shows "comma_semantic_b1_crt_indexed_embedding positions compact columns"
proof -
  have width:
      "length positions=length compact"
    by (rule comma_semantic_b1_crt_indexed_mask_position_length[OF flags])
  have dropped:
      "comma_semantic_b1_crt_partition_drop_false compact =
       comma_semantic_b1_crt_partition_drop_false columns"
    by (rule comma_semantic_b1_crt_indexed_mask_drop_false[OF flags])
  have distinct:
      "distinct positions"
    by (rule comma_semantic_b1_crt_indexed_mask_distinct[OF flags])
  have aligned:
      "\<forall>j<length compact. positions!j<length columns \<and>
        columns!(positions!j)=compact!j"
    using comma_semantic_b1_crt_indexed_mask_alignment[OF flags]
    by simp
  have omitted:
      "\<forall>i<length columns. i\<notin>set positions \<longrightarrow>
        columns!i=Comma_CRT_Bool False"
    using comma_semantic_b1_crt_indexed_mask_omitted_false[OF flags]
    by simp
  show ?thesis using width dropped aligned omitted distinct
    by (simp add: comma_semantic_b1_crt_indexed_embedding_def)
qed

lemma comma_semantic_b1_crt_indexed_mask_retained_false_fixture:
  "comma_semantic_b1_crt_indexed_embedding
      [1] [Comma_CRT_Bool False]
      [Comma_CRT_Bool False, Comma_CRT_Bool False]"
proof -
  have terminal:
      "comma_semantic_b1_crt_indexed_mask
        (Suc (Suc 0)) [] [] [] []"
    by (rule comma_semantic_b1_crt_indexed_mask_nil)
  have retained:
      "comma_semantic_b1_crt_indexed_mask
        (Suc 0) [True] [Comma_CRT_Bool False] [Suc 0]
        [Comma_CRT_Bool False]"
    by (rule comma_semantic_b1_crt_indexed_mask_keep[OF terminal])
  have witness:
      "comma_semantic_b1_crt_indexed_mask
        0 [False,True]
        [Comma_CRT_Bool False, Comma_CRT_Bool False]
        [Suc 0] [Comma_CRT_Bool False]"
    by (rule comma_semantic_b1_crt_indexed_mask_drop[OF refl retained])
  show ?thesis
    using comma_semantic_b1_crt_indexed_mask_embedding[OF witness]
    by (simp only: One_nat_def)

qed

lemma comma_semantic_b1_crt_indexed_mask_omitted_true_rejected_fixture:
  "\<not> (\<exists>flags.
      comma_semantic_b1_crt_indexed_mask
        0 flags [Comma_CRT_Bool False, Comma_CRT_Bool True] [] [])"
proof
  assume witness:
    "\<exists>flags.
      comma_semantic_b1_crt_indexed_mask
        0 flags [Comma_CRT_Bool False, Comma_CRT_Bool True] [] []"
  then obtain flags where witness_flags:
      "comma_semantic_b1_crt_indexed_mask
        0 flags [Comma_CRT_Bool False, Comma_CRT_Bool True] [] []"
    by blast
  have omitted:
      "\<forall>i<length [Comma_CRT_Bool False, Comma_CRT_Bool True].
        i\<notin>set [] \<longrightarrow>
        [Comma_CRT_Bool False, Comma_CRT_Bool True]!i =
          Comma_CRT_Bool False"
    using comma_semantic_b1_crt_indexed_mask_omitted_false[OF witness_flags]
    by simp
  have false_at_one:
      "[Comma_CRT_Bool False, Comma_CRT_Bool True]!1 =
        Comma_CRT_Bool False"
    using omitted[rule_format, of 1] by simp
  show False using false_at_one by simp
qed

lemma comma_semantic_b1_crt_indexed_mask_identity_offset:
  "comma_semantic_b1_crt_indexed_mask
      offset (map (\<lambda>column. True) columns) columns
      [offset..<offset+length columns] columns"
proof (induction columns arbitrary: offset)
  case Nil
  have nil:
      "comma_semantic_b1_crt_indexed_mask offset [] [] [] []"
    by (rule comma_semantic_b1_crt_indexed_mask_nil)
  then show ?case by simp
next
  case (Cons column columns)
  have tail:
      "comma_semantic_b1_crt_indexed_mask
        (Suc offset) (map (\<lambda>column. True) columns) columns
        [Suc offset..<offset+Suc (length columns)] columns"
  proof -
    have tail0:
        "comma_semantic_b1_crt_indexed_mask
          (Suc offset) (map (\<lambda>column. True) columns) columns
          [Suc offset..<Suc offset+length columns] columns"
      by (rule Cons.IH)
    have upper:
        "Suc offset+length columns = offset+Suc (length columns)"
      by simp
    then show ?thesis using tail0 by (simp only: upper)
  qed
  have nonempty: "offset<offset+Suc (length columns)"
    by simp
  have range:
      "[offset..<offset+Suc (length columns)] =
        offset#[Suc offset..<offset+Suc (length columns)]"
    by (rule upt_conv_Cons[OF nonempty])
  have kept:
      "comma_semantic_b1_crt_indexed_mask
        offset (True#map (\<lambda>column. True) columns) (column#columns)
        (offset#[Suc offset..<offset+Suc (length columns)]) (column#columns)"
    by (rule comma_semantic_b1_crt_indexed_mask_keep[OF tail])
  show ?case using kept range
    by (simp only: range list.map length_Cons)
qed

lemma comma_semantic_b1_crt_indexed_mask_identity:
  "comma_semantic_b1_crt_indexed_mask
      0 (map (\<lambda>column. True) columns) columns
      [0..<length columns] columns"
  using comma_semantic_b1_crt_indexed_mask_identity_offset[of 0 columns] by simp

lemma comma_semantic_b1_crt_indexed_mask_identity_embedding:
  "comma_semantic_b1_crt_indexed_embedding
      [0..<length columns] columns columns"
  by (rule comma_semantic_b1_crt_indexed_mask_embedding
    [OF comma_semantic_b1_crt_indexed_mask_identity])

lemmas comma_semantic_b1_crt_indexed_mask_oracle_audit_bundle =
  comma_semantic_b1_crt_indexed_mask_position_length
  comma_semantic_b1_crt_indexed_mask_source_length
  comma_semantic_b1_crt_indexed_mask_drop_false
  comma_semantic_b1_crt_indexed_mask_position_lower
  comma_semantic_b1_crt_indexed_mask_alignment
  comma_semantic_b1_crt_indexed_mask_omitted_false
  comma_semantic_b1_crt_indexed_mask_distinct
  comma_semantic_b1_crt_indexed_mask_embedding
  comma_semantic_b1_crt_indexed_mask_retained_false_fixture
  comma_semantic_b1_crt_indexed_mask_omitted_true_rejected_fixture
  comma_semantic_b1_crt_indexed_mask_identity_offset
  comma_semantic_b1_crt_indexed_mask_identity
  comma_semantic_b1_crt_indexed_mask_identity_embedding

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_indexed_mask_oracle_audit_bundle}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Comma indexed mask embedding proof bundle depends on an oracle"
\<close>

end
