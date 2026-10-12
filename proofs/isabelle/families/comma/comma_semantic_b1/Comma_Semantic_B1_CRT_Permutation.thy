theory Comma_Semantic_B1_CRT_Permutation
  imports Comma_Semantic_B1_CRT_Embedding_Construction
begin

text \<open>
A finite occurrence permutation transports a labelled zipper witness while
retaining the order-sensitive indexed embedding.  The forward list maps a
target column position to its source position; the backward list maps source
labels back to target labels.  Both round trips are required, preserving
multiplicity rather than merely comparing sets.
\<close>

definition comma_semantic_b1_crt_indexed_permutation ::
    "nat list \<Rightarrow> nat list \<Rightarrow>
      'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "comma_semantic_b1_crt_indexed_permutation perm backward source target \<longleftrightarrow>
    length perm=length source \<and>
    length backward=length source \<and>
    length target=length source \<and>
    (\<forall>j<length source. perm!j<length source) \<and>
    (\<forall>j<length source. backward!j<length source) \<and>
    (\<forall>j<length source. backward!(perm!j)=j) \<and>
    (\<forall>j<length source. perm!(backward!j)=j) \<and>
    (\<forall>j<length source. target!j=source!(perm!j))"

text \<open>The executable check enumerates only the finite occurrence indices.
Its semantic definition remains the bounded universal relation above.\<close>

declare comma_semantic_b1_crt_indexed_permutation_def[code del]

lemma comma_semantic_b1_crt_indexed_permutation_code[code]:
  "comma_semantic_b1_crt_indexed_permutation perm backward source target =
    (length perm=length source \<and>
     length backward=length source \<and>
     length target=length source \<and>
     list_all (\<lambda>j. perm!j<length source \<and>
       backward!j<length source \<and>
       backward!(perm!j)=j \<and>
       perm!(backward!j)=j \<and>
       target!j=source!(perm!j)) [0..<length source])"
  by (auto simp: comma_semantic_b1_crt_indexed_permutation_def list_all_iff)

lemma comma_semantic_b1_crt_indexed_permutation_lengths:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  shows "length perm=length source"
    "length backward=length source"
    "length target=length source"
  using permutation by (auto simp: comma_semantic_b1_crt_indexed_permutation_def)

lemma comma_semantic_b1_crt_indexed_permutation_bounds:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  shows "\<forall>j<length source. perm!j<length source"
    "\<forall>j<length source. backward!j<length source"
  using permutation by (auto simp: comma_semantic_b1_crt_indexed_permutation_def)

lemma comma_semantic_b1_crt_indexed_permutation_roundtrips:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  shows "\<forall>j<length source. backward!(perm!j)=j"
    "\<forall>j<length source. perm!(backward!j)=j"
  using permutation by (auto simp: comma_semantic_b1_crt_indexed_permutation_def)

lemma comma_semantic_b1_crt_indexed_permutation_target_nth:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
    and bound: "j<length source"
  shows "target!j=source!(perm!j)"
  using permutation bound
  by (auto simp: comma_semantic_b1_crt_indexed_permutation_def)

lemma comma_semantic_b1_crt_indexed_permutation_eq_iff:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
    and i: "i<length source"
    and j: "j<length source"
  shows "perm!j=i \<longleftrightarrow> j=backward!i"
proof -
  have inverse_roundtrip:
      "\<forall>k<length source. backward!(perm!k)=k"
    by (rule comma_semantic_b1_crt_indexed_permutation_roundtrips(1)[OF permutation])
  have perm_roundtrip:
      "\<forall>k<length source. perm!(backward!k)=k"
    by (rule comma_semantic_b1_crt_indexed_permutation_roundtrips(2)[OF permutation])
  show ?thesis
  proof
    assume equal: "perm!j=i"
    have roundtrip: "backward!(perm!j)=j"
      using inverse_roundtrip[rule_format, OF j] .
    show "j=backward!i"
      using roundtrip equal by simp
  next
    assume equal: "j=backward!i"
    have roundtrip: "perm!(backward!i)=i"
      using perm_roundtrip[rule_format, OF i] .
    show "perm!j=i"
      using roundtrip equal by simp
  qed
qed

ML \<open>
  val _ = Comma_Proof_Profile.report "permutation eq_iff-start"
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_indexed_permutation_eq_iff}
  val _ = Comma_Proof_Profile.report "permutation eq_iff-done"
\<close>

lemma comma_semantic_b1_crt_indexed_permutation_set:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  shows "set target=set source"
proof -
  have source_length: "length source=length target"
    by (rule sym, rule comma_semantic_b1_crt_indexed_permutation_lengths(3)[OF permutation])
  have target_nth:
      "target!j=source!(perm!j)"
    if j: "j<length target" for j
  proof -
    have source_bound: "j<length source" using j source_length by simp
    show ?thesis
      by (rule comma_semantic_b1_crt_indexed_permutation_target_nth
        [OF permutation source_bound])
  qed
  have perm_bound:
      "perm!j<length source"
    if j: "j<length source" for j
    using comma_semantic_b1_crt_indexed_permutation_bounds(1)[OF permutation]
      j by blast
  have inverse_bound:
      "backward!i<length source"
    if i: "i<length source" for i
    using comma_semantic_b1_crt_indexed_permutation_bounds(2)[OF permutation]
      i by blast
  have perm_roundtrip:
      "perm!(backward!i)=i"
    if i: "i<length source" for i
    using comma_semantic_b1_crt_indexed_permutation_roundtrips(2)[OF permutation]
      i by blast
  have target_subset: "set target \<subseteq> set source"
  proof (intro subsetI)
    fix element
    assume member: "element\<in>set target"
    then obtain j where j: "j<length target" and element: "target!j=element"
      by (auto simp: in_set_conv_nth)
    have source_bound: "j<length source" using j source_length by simp
    have source_member: "source!(perm!j)\<in>set source"
      by (rule nth_mem[OF perm_bound[OF source_bound]])
    show "element\<in>set source"
      using element target_nth[OF j] source_member by simp
  qed
  have source_subset: "set source \<subseteq> set target"
  proof (intro subsetI)
    fix element
    assume member: "element\<in>set source"
    then obtain i where i: "i<length source" and element: "source!i=element"
      by (auto simp: in_set_conv_nth)
    have inverse_bound': "backward!i<length target"
      using inverse_bound[OF i] source_length by simp
    have target_member: "target!(backward!i)\<in>set target"
      by (rule nth_mem[OF inverse_bound'])
    have target_value:
        "target!(backward!i)=source!i"
      using target_nth[OF inverse_bound'] perm_roundtrip[OF i] by simp
    show "element\<in>set target"
      using element target_member target_value by simp
  qed
  show ?thesis by (rule subset_antisym[OF target_subset source_subset])
qed

ML \<open>
  val _ = Comma_Proof_Profile.report "permutation indexed_permutation_set-start"
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_indexed_permutation_set}
  val _ = Comma_Proof_Profile.report "permutation indexed_permutation_set-done"
\<close>

lemma comma_semantic_b1_crt_indexed_permutation_list_all:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
    and source_all: "list_all predicate source"
  shows "list_all predicate target"
  using source_all comma_semantic_b1_crt_indexed_permutation_set[OF permutation]
  by (simp add: list_all_iff)

lemma comma_semantic_b1_crt_partition_node_at_column:
  "comma_semantic_b1_crt_partition_has_node_at level columns \<longleftrightarrow>
    (\<exists>column\<in>set columns.
      (\<exists>node_level children.
        column=Comma_CRT_Node node_level children \<and> node_level=level))"
proof (induction columns)
  case Nil
  then show ?case by simp
next
  case (Cons column columns)
  show ?case
  proof (cases column)
    case (Comma_CRT_Bool element)
    then show ?thesis
      by (simp add: comma_semantic_b1_crt_partition_has_node_at.simps Cons.IH)
  next
    case (Comma_CRT_Node node_level children)
    then show ?thesis
      by (simp add: comma_semantic_b1_crt_partition_has_node_at.simps Cons.IH)
  qed
qed

lemma comma_semantic_b1_crt_indexed_permutation_has_node:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  shows "comma_semantic_b1_crt_partition_has_node_at level target =
    comma_semantic_b1_crt_partition_has_node_at level source"
  using comma_semantic_b1_crt_indexed_permutation_set[OF permutation]
  by (simp add: comma_semantic_b1_crt_partition_node_at_column)

lemma comma_semantic_b1_crt_indexed_permutation_map:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  shows "comma_semantic_b1_crt_indexed_permutation perm backward
      (map f source) (map f target)"
proof -
  have source_length: "length source=length target"
    by (rule sym, rule comma_semantic_b1_crt_indexed_permutation_lengths(3)[OF permutation])
  have target_nth:
      "(map f target)!j=(map f source)!(perm!j)"
    if j: "j<length source" for j
  proof -
    have target_bound: "j<length target" using j source_length by simp
    have perm_bound: "perm!j<length source"
      using comma_semantic_b1_crt_indexed_permutation_bounds(1)[OF permutation]
        j by blast
    have target_value: "target!j=source!(perm!j)"
      by (rule comma_semantic_b1_crt_indexed_permutation_target_nth
        [OF permutation j])
    show ?thesis using target_value target_bound perm_bound
      by (simp add: nth_map)
  qed
  have source_map_length: "length (map f source)=length source" by simp
  have perm_map_length: "length perm=length (map f source)"
    using comma_semantic_b1_crt_indexed_permutation_lengths(1)[OF permutation]
    by simp
  have backward_map_length: "length backward=length (map f source)"
    using comma_semantic_b1_crt_indexed_permutation_lengths(2)[OF permutation]
    by simp
  have target_map_length: "length (map f target)=length source"
    using source_length by simp
  have target_map_length':
      "length (map f target)=length (map f source)"
    using target_map_length source_map_length by simp
  have target_nth_map:
      "(map f target)!j=(map f source)!(perm!j)"
    if j: "j<length (map f source)" for j
  proof -
    have source_bound: "j<length source" using j source_map_length by simp
    show ?thesis using target_nth[OF source_bound] by simp
  qed
  have target_all:
      "\<forall>j<length (map f source).
        (map f target)!j=(map f source)!(perm!j)"
    by (intro allI impI, rule target_nth_map)
  have perm_bound:
      "\<forall>j<length (map f source). perm!j<length (map f source)"
    using comma_semantic_b1_crt_indexed_permutation_bounds(1)[OF permutation]
      by simp
  have backward_bound:
      "\<forall>j<length (map f source). backward!j<length (map f source)"
    using comma_semantic_b1_crt_indexed_permutation_bounds(2)[OF permutation]
      by simp
  have backward_roundtrip:
      "\<forall>j<length (map f source). backward!(perm!j)=j"
    using comma_semantic_b1_crt_indexed_permutation_roundtrips(1)[OF permutation]
      by simp
  have perm_roundtrip:
      "\<forall>j<length (map f source). perm!(backward!j)=j"
    using comma_semantic_b1_crt_indexed_permutation_roundtrips(2)[OF permutation]
      by simp
  show ?thesis
    unfolding comma_semantic_b1_crt_indexed_permutation_def
    using perm_map_length backward_map_length target_map_length'
      perm_bound backward_bound backward_roundtrip perm_roundtrip target_all
    by blast
qed

ML \<open>
  val _ = Comma_Proof_Profile.report "permutation indexed_permutation_map-start"
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_indexed_permutation_map}
  val _ = Comma_Proof_Profile.report "permutation indexed_permutation_map-done"
\<close>

lemma comma_semantic_b1_crt_indexed_permutation_cofactor:
  assumes permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  shows "comma_semantic_b1_crt_indexed_permutation perm backward
      (map (comma_crt_cofactor_or_false level digit) source)
      (map (comma_crt_cofactor_or_false level digit) target)"
  by (rule comma_semantic_b1_crt_indexed_permutation_map[OF permutation])

lemma comma_semantic_b1_crt_labelled_zip_witness_indexed_permutation:
  assumes witness:
    "comma_semantic_b1_crt_labelled_zip_witness level source selector"
  shows "\<forall>perm backward target.
    comma_semantic_b1_crt_indexed_permutation perm backward source target \<longrightarrow>
    comma_semantic_b1_crt_labelled_zip_witness level target
      (comma_semantic_b1_crt_mdd_map_payload
        (map_option (\<lambda>index. backward!index)) selector)"
  using witness
proof (induction rule: comma_semantic_b1_crt_labelled_zip_witness.induct)
  case (labelled_zip_terminal index source level)
  show ?case
  proof (intro allI allI allI impI)
    fix perm backward target
    assume permutation:
      "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  have source_length:
      "length source=length target"
    by (rule sym, rule comma_semantic_b1_crt_indexed_permutation_lengths(3)
      [OF permutation])
  have index_target:
      "backward!index<length target"
    using comma_semantic_b1_crt_indexed_permutation_bounds(2)
      [OF permutation] labelled_zip_terminal.hyps(1)
      source_length by simp
  have one_hot:
      "target!j=Comma_CRT_Bool (j=backward!index)"
    if j: "j<length target" for j
  proof -
    have source_bound: "j<length source" using j source_length by simp
    have target_value:
        "target!j=source!(perm!j)"
      by (rule comma_semantic_b1_crt_indexed_permutation_target_nth
        [OF permutation source_bound])
    have perm_bound:
        "perm!j<length source"
      using comma_semantic_b1_crt_indexed_permutation_bounds(1)
        [OF permutation] source_bound by blast
    have source_value:
        "source!(perm!j)=Comma_CRT_Bool (perm!j=index)"
      by (rule labelled_zip_terminal.hyps(2)[OF perm_bound])
    have equal:
        "perm!j=index \<longleftrightarrow> j=backward!index"
      by (rule comma_semantic_b1_crt_indexed_permutation_eq_iff
        [OF permutation labelled_zip_terminal.hyps(1)
          source_bound])
    show ?thesis
      using target_value source_value equal by simp
  qed
  have selector_map:
      "comma_semantic_b1_crt_mdd_map_payload
          (map_option (\<lambda>index. backward!index))
          (Comma_CRT_MDD_Leaf (Some index)) =
        Comma_CRT_MDD_Leaf (Some (backward!index))"
    by simp
  show "comma_semantic_b1_crt_labelled_zip_witness level target
      (comma_semantic_b1_crt_mdd_map_payload
        (map_option (\<lambda>index. backward!index))
        (Comma_CRT_MDD_Leaf (Some index)))"
    unfolding selector_map
    by (rule comma_semantic_b1_crt_labelled_zip_witness.intros(1)
      [OF index_target one_hot])
  qed
next
  case (labelled_zip_skip level source selector)
  show ?case
  proof (intro allI allI allI impI)
    fix perm backward target
    assume permutation:
      "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  have target_admitted:
      "list_all (comma_crt_admitted level) target"
    by (rule comma_semantic_b1_crt_indexed_permutation_list_all
      [OF permutation labelled_zip_skip.hyps(2)])
  have target_no_node:
      "\<not> comma_semantic_b1_crt_partition_has_node_at level target"
    using comma_semantic_b1_crt_indexed_permutation_has_node
      [OF permutation] labelled_zip_skip.hyps(3) by simp
  have child:
      "comma_semantic_b1_crt_labelled_zip_witness (Suc level) target
        (comma_semantic_b1_crt_mdd_map_payload
          (map_option (\<lambda>index. backward!index)) selector)"
    using labelled_zip_skip.IH[rule_format, OF permutation] .
  show "comma_semantic_b1_crt_labelled_zip_witness level target
      (comma_semantic_b1_crt_mdd_map_payload
        (map_option (\<lambda>index. backward!index)) selector)"
    by (rule comma_semantic_b1_crt_labelled_zip_witness.intros(2)
      [OF labelled_zip_skip.hyps(1) target_admitted target_no_node child])
  qed
next
  case (labelled_zip_node level source children)
  show ?case
  proof (intro allI allI allI impI)
    fix perm backward target
    assume permutation:
      "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  have target_admitted:
      "list_all (comma_crt_admitted level) target"
    by (rule comma_semantic_b1_crt_indexed_permutation_list_all
      [OF permutation labelled_zip_node.hyps(2)])
  have target_node:
      "comma_semantic_b1_crt_partition_has_node_at level target"
    using comma_semantic_b1_crt_indexed_permutation_has_node
      [OF permutation] labelled_zip_node.hyps(3) by simp
  have child_witness:
      "comma_semantic_b1_crt_labelled_zip_witness (Suc level)
        (map (comma_crt_cofactor_or_false level digit) target)
        (comma_semantic_b1_crt_mdd_map_payload
          (map_option (\<lambda>index. backward!index)) (children!digit))"
    if digit: "digit<comma_crt_period level" for digit
  proof -
    have child_permutation:
        "comma_semantic_b1_crt_indexed_permutation perm backward
          (map (comma_crt_cofactor_or_false level digit) source)
          (map (comma_crt_cofactor_or_false level digit) target)"
      by (rule comma_semantic_b1_crt_indexed_permutation_cofactor
        [OF permutation])
    have child:
        "comma_semantic_b1_crt_labelled_zip_witness (Suc level)
          (map (comma_crt_cofactor_or_false level digit) target)
          (comma_semantic_b1_crt_mdd_map_payload
            (map_option (\<lambda>index. backward!index)) (children!digit))"
      using labelled_zip_node.IH[rule_format, OF digit child_permutation] .
    show ?thesis using child .
  qed
  have result:
      "comma_semantic_b1_crt_labelled_zip_witness level target
        (comma_crt_mdd_node level
          (map (comma_semantic_b1_crt_mdd_map_payload
            (map_option (\<lambda>index. backward!index))) children))"
  proof (rule comma_semantic_b1_crt_labelled_zip_witness.intros(3)
      [OF labelled_zip_node.hyps(1) target_admitted target_node])
    show "length (map (comma_semantic_b1_crt_mdd_map_payload
          (map_option (\<lambda>index. backward!index))) children) =
        comma_crt_period level"
      using labelled_zip_node.hyps(4) by simp
    fix digit
    assume digit: "digit<comma_crt_period level"
    have child:
        "comma_semantic_b1_crt_labelled_zip_witness (Suc level)
          (map (comma_crt_cofactor_or_false level digit) target)
          (comma_semantic_b1_crt_mdd_map_payload
            (map_option (\<lambda>index. backward!index)) (children!digit))"
      by (rule child_witness[OF digit])
    show "comma_semantic_b1_crt_labelled_zip_witness (Suc level)
        (map (comma_crt_cofactor_or_false level digit) target)
        ((map (comma_semantic_b1_crt_mdd_map_payload
          (map_option (\<lambda>index. backward!index))) children)!digit)"
      using child labelled_zip_node.hyps(4) digit by (simp add: nth_map)
  qed
  have map_node:
      "comma_semantic_b1_crt_mdd_map_payload
          (map_option (\<lambda>index. backward!index))
          (comma_crt_mdd_node level children) =
       comma_crt_mdd_node level
          (map (comma_semantic_b1_crt_mdd_map_payload
            (map_option (\<lambda>index. backward!index))) children)"
    by (simp add: comma_semantic_b1_crt_mdd_map_payload_node)
  show "comma_semantic_b1_crt_labelled_zip_witness level target
      (comma_semantic_b1_crt_mdd_map_payload
        (map_option (\<lambda>index. backward!index))
        (comma_crt_mdd_node level children))"
    using result map_node by simp
  qed
qed

ML \<open>
  val _ = Comma_Proof_Profile.report
    "permutation labelled_zip_witness_transport-start"
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_labelled_zip_witness_indexed_permutation}
  val _ = Comma_Proof_Profile.report
    "permutation labelled_zip_witness_transport-done"
\<close>

lemma comma_semantic_b1_crt_partition_witness_indexed_permutation:
  assumes witness:
    "comma_semantic_b1_crt_partition_witness level source"
    and permutation:
      "comma_semantic_b1_crt_indexed_permutation perm backward source target"
  shows "comma_semantic_b1_crt_partition_witness level target"
proof -
  obtain selector where selector:
      "comma_semantic_b1_crt_labelled_zip_witness level source selector"
    using witness unfolding comma_semantic_b1_crt_partition_witness_def by blast
  have transported:
      "comma_semantic_b1_crt_labelled_zip_witness level target
        (comma_semantic_b1_crt_mdd_map_payload
          (map_option (\<lambda>index. backward!index)) selector)"
  proof -
    have transport_all:
        "\<forall>perm backward target.
          comma_semantic_b1_crt_indexed_permutation perm backward source target \<longrightarrow>
          comma_semantic_b1_crt_labelled_zip_witness level target
            (comma_semantic_b1_crt_mdd_map_payload
              (map_option (\<lambda>index. backward!index)) selector)"
      by (rule comma_semantic_b1_crt_labelled_zip_witness_indexed_permutation
        [OF selector])
    show ?thesis using transport_all[rule_format, OF permutation] .
  qed
  show ?thesis
    unfolding comma_semantic_b1_crt_partition_witness_def
    by (rule exI[where x="comma_semantic_b1_crt_mdd_map_payload
      (map_option (\<lambda>index. backward!index)) selector"]; rule transported)
qed

ML \<open>
  val _ = Comma_Proof_Profile.report
    "permutation partition_witness_transport-start"
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_partition_witness_indexed_permutation}
  val _ = Comma_Proof_Profile.report
    "permutation partition_witness_transport-done"
\<close>

lemma comma_semantic_b1_crt_indexed_permutation_duplicate_rejected:
  assumes unequal: "A\<noteq>B"
  shows "\<not> comma_semantic_b1_crt_indexed_permutation perm backward
      [A,B] [A,A]"
proof
  assume permutation:
    "comma_semantic_b1_crt_indexed_permutation perm backward [A,B] [A,A]"
  have same_set:
      "set [A,A] = set [A,B]"
    by (rule comma_semantic_b1_crt_indexed_permutation_set[OF permutation])
  have B_mem_source: "B \<in> set [A,B]" by simp
  have B_mem_target: "B \<in> set [A,A]"
    using same_set B_mem_source by blast
  have equal: "B=A" using B_mem_target by simp
  show False using unequal equal by blast
qed

ML \<open>
  val _ = Comma_Proof_Profile.report "permutation duplicate_rejection-start"
  val _ = Thm.consolidate
    @{thms comma_semantic_b1_crt_indexed_permutation_duplicate_rejected}
  val _ = Comma_Proof_Profile.report "permutation duplicate_rejection-done"
\<close>

lemmas comma_semantic_b1_crt_permutation_oracle_audit_bundle =
  comma_semantic_b1_crt_indexed_permutation_code
  comma_semantic_b1_crt_indexed_permutation_lengths
  comma_semantic_b1_crt_indexed_permutation_bounds
  comma_semantic_b1_crt_indexed_permutation_roundtrips
  comma_semantic_b1_crt_indexed_permutation_target_nth
  comma_semantic_b1_crt_indexed_permutation_eq_iff
  comma_semantic_b1_crt_indexed_permutation_set
  comma_semantic_b1_crt_indexed_permutation_list_all
  comma_semantic_b1_crt_partition_node_at_column
  comma_semantic_b1_crt_indexed_permutation_has_node
  comma_semantic_b1_crt_indexed_permutation_cofactor
  comma_semantic_b1_crt_labelled_zip_witness_indexed_permutation
  comma_semantic_b1_crt_partition_witness_indexed_permutation
  comma_semantic_b1_crt_indexed_permutation_duplicate_rejected

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_permutation_oracle_audit_bundle}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Comma indexed permutation proof bundle depends on an oracle"
\<close>

end
