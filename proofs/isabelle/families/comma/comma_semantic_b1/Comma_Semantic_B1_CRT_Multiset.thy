theory Comma_Semantic_B1_CRT_Multiset
  imports Comma_Semantic_B1_CRT_Permutation "HOL-Combinatorics.Permutations"
begin

text \<open>
Multiset equality preserves the occurrence count of every column while
forgetting only list order.  The witness is existential, so an occurrence
matching can rebase its labels when the column list is reordered.
\<close>

lemma comma_semantic_b1_crt_indexed_permutation_of_mset:
  fixes source target :: "'a list"
  assumes mset_eq: "mset source = mset target"
  shows "\<exists>forward backward.
    comma_semantic_b1_crt_indexed_permutation forward backward source target"
proof -
  have length_eq: "length source = length target"
    using mset_eq by (rule mset_eq_length)
  obtain p where p: "p permutes {..<length target}"
    and permuted: "permute_list p target = source"
    using mset_eq by (rule mset_eq_permutation)
  let ?positions = "[0..<length target]"
  let ?range = "{..<length target}"
  let ?forward = "map (inv_into ?range p) ?positions"
  let ?backward = "map p [0..<length source]"
  have p_bij: "bij_betw p ?range ?range"
    by (rule permutes_imp_bij[OF p])
  have inverse_bij: "bij_betw (inv_into ?range p) ?range ?range"
    by (rule bij_betw_inv_into[OF p_bij])
  have p_inj: "inj_on p ?range"
    using p_bij by (simp add: bij_betw_def)
  have p_image: "p ` ?range = ?range"
    using p_bij by (simp add: bij_betw_def)
  have p_range: "p i \<in> ?range" if "i \<in> ?range" for i
    using p_image that by blast
  have inverse_range: "inv_into ?range p i \<in> ?range"
    if "i \<in> ?range" for i
    using inverse_bij that by (auto simp: bij_betw_def)
  have forward_nth:
      "?forward ! j = inv_into ?range p j"
    if j: "j < length target" for j
    using j by simp
  have backward_nth:
      "?backward ! i = p i"
    if i: "i < length source" for i
    using i by simp
  have source_nth:
      "source ! i = target ! (p i)"
    if i: "i < length source" for i
  proof -
    have "source ! i = permute_list p target ! i"
      using permuted by simp
    also have "... = target ! (p i)"
      by (rule permute_list_nth[OF p]) (use i length_eq in simp)
    finally show ?thesis .
  qed
  have inverse_left:
      "p (inv_into ?range p j) = j"
    if j: "j < length target" for j
  proof -
    have j_range: "j \<in> p ` ?range"
      using p_image j by simp
    show ?thesis by (rule f_inv_into_f[OF j_range])
  qed
  have inverse_right:
      "inv_into ?range p (p i) = i"
    if i: "i < length source" for i
  proof -
    have i_range: "i \<in> ?range"
      using i length_eq by simp
    show ?thesis by (rule inv_into_f_f[OF p_inj i_range])
  qed
  have forward_bound:
      "?forward ! j < length source"
    if j: "j < length source" for j
  proof -
    have j_range: "j \<in> ?range"
      using j length_eq by simp
    have forward_range: "inv_into ?range p j \<in> ?range"
      by (rule inverse_range[OF j_range])
    show ?thesis using forward_nth[of j] forward_range j length_eq by simp
  qed
  have backward_bound:
      "?backward ! i < length source"
    if i: "i < length source" for i
  proof -
    have i_range: "i \<in> ?range"
      using i length_eq by simp
    have backward_range: "p i \<in> ?range"
      by (rule p_range[OF i_range])
    show ?thesis using backward_nth[OF i] backward_range length_eq by simp
  qed
  have target_nth:
      "target ! j = source ! (inv_into ?range p j)"
    if j: "j < length target" for j
  proof -
    have i_bound: "inv_into ?range p j < length source"
      using inverse_range[of j] j length_eq by simp
    have "source ! (inv_into ?range p j) =
        target ! (p (inv_into ?range p j))"
      by (rule source_nth[OF i_bound])
    also have "... = target ! j"
      using inverse_left[OF j] by simp
    finally show ?thesis by simp
  qed
  have indexed:
      "comma_semantic_b1_crt_indexed_permutation ?forward ?backward source target"
    unfolding comma_semantic_b1_crt_indexed_permutation_def
    using length_eq forward_bound backward_bound inverse_left inverse_right
      target_nth
    by (auto simp: nth_map)
  show ?thesis by (intro exI[of _ ?forward] exI[of _ ?backward]; rule indexed)
qed

lemma comma_semantic_b1_crt_partition_witness_mset:
  assumes mset_eq: "mset source = mset target"
    and witness: "comma_semantic_b1_crt_partition_witness level source"
  shows "comma_semantic_b1_crt_partition_witness level target"
proof -
  obtain forward backward where permutation:
      "comma_semantic_b1_crt_indexed_permutation forward backward source target"
    using comma_semantic_b1_crt_indexed_permutation_of_mset[OF mset_eq] by blast
  show ?thesis
    by (rule comma_semantic_b1_crt_partition_witness_indexed_permutation
      [OF witness permutation])
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_crt_indexed_permutation_of_mset
    comma_semantic_b1_crt_partition_witness_mset}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "B1 multiset witness transport depends on a theorem oracle"
\<close>

end
