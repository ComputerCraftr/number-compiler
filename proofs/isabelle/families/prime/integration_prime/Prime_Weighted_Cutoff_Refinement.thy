theory Prime_Weighted_Cutoff_Refinement
  imports Prime_Birth_Innovation_Refinement Prime_Prefix_Image_Projection_Refinement
begin

text \<open>Finite source-bound interval arithmetic for the sparse single-multiple
guard. The factor prefix and wheel ranking remain separate source obligations.\<close>

lemma prime_sparse_interval_empty:
  fixes high width q :: nat
  assumes positive: "q > 0" and width: "width < q" "width \<le> high"
    and empty: "width \<le> high mod q"
  shows "(high - width) div q = high div q"
proof -
  have bound: "high mod q < q" using positive by simp
  have rem: "high mod q - width < q" using bound by arith
  have decomposition: "high - width = (high div q) * q + (high mod q - width)"
    using div_mult_mod_eq[of high q] empty by arith
  have divided: "((high div q) * q + (high mod q - width)) div q = high div q"
    using positive rem by simp
  show ?thesis using decomposition divided by simp
qed

lemma prime_sparse_interval_single:
  fixes high width q :: nat
  assumes positive: "q > 0" and width: "width < q" "width \<le> high"
    and hit: "high mod q < width"
  shows "(high - width) div q + 1 = high div q"
proof -
  have rem_bound: "high mod q < q" using positive by simp
  have high_decomp: "high div q * q + high mod q = high"
    by (rule div_mult_mod_eq)
  have quotient_pos: "high div q > 0" using high_decomp hit width by (cases "high div q") auto
  have rem: "q + high mod q - width < q" using hit width by arith
  have products: "(high div q - 1) * q + q = (high div q) * q"
    using quotient_pos by (cases "high div q") (simp_all add: algebra_simps)
  have decomposition:
    "high - width = (high div q - 1) * q + (q + high mod q - width)"
    using high_decomp products hit width by arith
  have divided:
    "((high div q - 1) * q + (q + high mod q - width)) div q = high div q - 1"
    using positive rem by simp
  show ?thesis using decomposition divided quotient_pos by simp
qed

lemma prime_weighted_cutoff_cancellation:
  fixes weight adjustment response :: int
  shows "weight * response + adjustment * response = (weight + adjustment) * response"
  by (simp add: algebra_simps)

lemma prime_weighted_empty_cutoff:
  fixes response :: int
  shows "0 * response = 0" by simp

lemma prime_weighted_singleton_projection:
  fixes rank :: "nat \<Rightarrow> nat"
  assumes "rank k = rank (k - 1) + (if eligible then 1 else 0)"
  shows "rank k - rank (k - 1) = (if eligible then 1 else 0)"
  using assms by simp

lemma prime_weighted_child_descends:
  fixes high q :: nat
  assumes "1 < q" "0 < high"
  shows "high div q < high"
  using assms by simp

lemma prime_weighted_interval_child_order:
  fixes low high q :: nat
  assumes "low \<le> high" "0 < high" "1 < q"
  shows "low div q \<le> high div q \<and> high div q < high"
  using assms prime_weighted_child_descends by (simp add: div_le_mono)

lemma prime_mask_interval_count:
  fixes excluded :: "nat set"
  assumes "finite positions"
  shows "card (positions - excluded) = card positions - card (positions \<inter> excluded)"
proof -
  have subset: "positions \<inter> excluded \<subseteq> positions" by blast
  have finite_removed: "finite (positions \<inter> excluded)"
    by (rule finite_subset[OF subset assms])
  have difference: "positions - excluded = positions - (positions \<inter> excluded)" by blast
  show ?thesis unfolding difference by (rule card_Diff_subset[OF finite_removed subset])
qed

definition prime_signed_row_response ::
  "(nat \<times> int) list \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> int" where
  "prime_signed_row_response row response =
    sum_list (map (\<lambda>(cutoff, weight). weight * response cutoff) row)"

lemma prime_signed_row_append:
  "prime_signed_row_response (left @ right) response =
    prime_signed_row_response left response + prime_signed_row_response right response"
  by (simp add: prime_signed_row_response_def sum_list_append)

lemma prime_signed_row_resolve_child:
  fixes response :: "nat \<Rightarrow> int"
  assumes transition: "response parent = response kept - response removed"
  shows "prime_signed_row_response ((parent, weight) # rest) response =
    prime_signed_row_response ((kept, weight) # (removed, -weight) # rest) response"
proof -
  have weighted:
    "weight * response parent = weight * response kept - weight * response removed"
    by (subst transition) (simp add: algebra_simps)
  show ?thesis by (simp add: prime_signed_row_response_def weighted algebra_simps)
qed

lemma prime_signed_row_cancel:
  "prime_signed_row_response ((cutoff, weight) # (cutoff, -weight) # rest) response =
    prime_signed_row_response rest response"
  by (simp add: prime_signed_row_response_def)

definition prime_weighted_worklist_response ::
  "nat list \<Rightarrow> (nat \<times> nat \<times> int) list \<Rightarrow> int" where
  "prime_weighted_worklist_response factors work =
    sum_list (map (\<lambda>(depth, cutoff, weight).
      weight * int (numerical_Phi factors depth cutoff)) work)"

lemma prime_weighted_worklist_expand_exact:
  assumes depth: "depth < length factors"
    and distinct: "distinct factors"
    and primes: "\<forall>p \<in> set factors. prime p"
  defines "q \<equiv> factors ! depth"
  shows "prime_weighted_worklist_response factors ((Suc depth, cutoff, weight) # rest) =
    prime_weighted_worklist_response factors
      ((depth, cutoff, weight) # (depth, cutoff div q, - weight) # rest)"
proof -
  have parent_depth: "depth \<le> length factors" using depth by simp
  have quotient: "cutoff div q \<le> cutoff" by simp
  have monotone:
    "numerical_Phi factors depth (cutoff div q) \<le>
      numerical_Phi factors depth cutoff"
    by (rule numerical_Phi_mono_limit[OF quotient parent_depth distinct primes])
  have recurrence:
    "int (numerical_Phi factors (Suc depth) cutoff) =
      int (numerical_Phi factors depth cutoff) -
      int (numerical_Phi factors depth (cutoff div q))"
    using monotone by (simp add: q_def of_nat_diff)
  have weighted:
    "weight * int (numerical_Phi factors (Suc depth) cutoff) =
      weight * int (numerical_Phi factors depth cutoff) -
      weight * int (numerical_Phi factors depth (cutoff div q))"
    by (simp only: recurrence right_diff_distrib)
  show ?thesis
    by (simp only: prime_weighted_worklist_response_def list.map sum_list.Cons
        prod.case weighted; simp add: algebra_simps)
qed

lemma prime_weighted_worklist_cancel:
  "prime_weighted_worklist_response factors
      ((depth, cutoff, weight) # (depth, cutoff, -weight) # rest) =
    prime_weighted_worklist_response factors rest"
  by (simp add: prime_weighted_worklist_response_def)

lemma prime_prefix_mask_closed_interval_exact:
  assumes order: "low \<le> high" and cached: "high \<le> W"
    and distinct: "distinct (parent @ [q])"
    and primes: "\<forall>p \<in> set (parent @ [q]). prime p"
  shows "mark_rank_before (zero_phase_prefix_word parent q W) high -
      mark_rank_before (zero_phase_prefix_word parent q W) low =
    card (wheel_half_open (q # rev parent) (Suc low) (Suc high))"
  using zero_phase_prefix_rank_interval[of "Suc low" "Suc high" W parent q]
    order cached distinct primes by simp

ML \<open>
  val checked = @{thms prime_sparse_interval_empty prime_sparse_interval_single
    prime_weighted_cutoff_cancellation prime_weighted_singleton_projection
    prime_weighted_child_descends prime_weighted_interval_child_order prime_mask_interval_count
    prime_signed_row_append prime_signed_row_resolve_child prime_signed_row_cancel
    prime_weighted_worklist_expand_exact prime_weighted_worklist_cancel
    prime_prefix_mask_closed_interval_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Prime weighted cutoff refinement depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped prime weighted cutoff refinement" else ();
\<close>

end
