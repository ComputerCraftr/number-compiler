theory Prime_Selected_Prefix_Rank_Refinement
  imports "Prime_Deterministic_Refinement.Prime_Prefix_Image_Projection_Refinement"
begin

text \<open>This theory models the sorted-list rank used by Python's
\<open>CoprimeRankDAG.factor_rank\<close> and the selected-depth restoration term in
\<open>PrimePartialSuccessorQuery.count_primes\<close>.  A workspace may retain a
longer consecutive prime prefix than the action selected by \<open>depth\<close>;
the outer minimum is therefore part of the executable expression, rather than
an arithmetic simplification made by the proof.\<close>

definition sorted_factor_rank :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
  "sorted_factor_rank ps limit = length (filter (\<lambda>p. p \<le> limit) ps)"

definition selected_known ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "selected_known ps depth lo hi =
    min depth (sorted_factor_rank ps (hi - 1)) -
      min depth (sorted_factor_rank ps (lo - 1))"

lemma filter_le_empty:
  fixes ps :: "nat list" and limit :: nat
  assumes "\<forall>p \<in> set ps. limit < p"
  shows "filter (\<lambda>p. p \<le> limit) ps = []"
  using assms by (induction ps) auto

lemma selected_prefix_rank_length:
  assumes sorted: "sorted ps" and depth: "depth \<le> length ps"
  shows "min depth (sorted_factor_rank ps limit) =
    length (filter (\<lambda>p. p \<le> limit) (take depth ps))"
  using sorted depth
proof (induction ps arbitrary: depth)
  case Nil
  then show ?case by (simp add: sorted_factor_rank_def)
next
  case (Cons first rest)
  show ?case
  proof (cases depth)
    case 0
    then show ?thesis by (simp add: sorted_factor_rank_def)
  next
    case (Suc smaller)
    then have smaller_bound: "smaller \<le> length rest"
      using Cons.prems by simp
    have rest_sorted: "sorted rest" using Cons.prems by simp
    have induction:
        "min smaller (sorted_factor_rank rest limit) =
          length (filter (\<lambda>p. p \<le> limit) (take smaller rest))"
      by (rule Cons.IH[OF rest_sorted smaller_bound])
    show ?thesis
    proof (cases "first \<le> limit")
      case True
      then show ?thesis
        using Suc induction by (simp add: sorted_factor_rank_def)
    next
      case False
      have later: "\<forall>p \<in> set rest. limit < p"
        using Cons.prems False by auto
      have rest_empty: "filter (\<lambda>p. p \<le> limit) rest = []"
        by (rule filter_le_empty[OF later])
      have take_later:
          "\<forall>p \<in> set (take smaller rest). limit < p"
        using later set_take_subset[of smaller rest] by blast
      have take_empty:
          "filter (\<lambda>p. p \<le> limit) (take smaller rest) = []"
        by (rule filter_le_empty[OF take_later])
      show ?thesis
        using Suc False rest_empty take_empty
        by (simp add: sorted_factor_rank_def)
    qed
  qed
qed

lemma selected_prefix_rank_card:
  assumes sorted: "sorted ps" and distinct: "distinct ps"
    and depth: "depth \<le> length ps"
  shows "min depth (sorted_factor_rank ps limit) =
    card {p \<in> set (take depth ps). p \<le> limit}"
proof -
  have filtered_distinct:
      "distinct (filter (\<lambda>p. p \<le> limit) (take depth ps))"
    using distinct by simp
  have set_filtered:
      "set (filter (\<lambda>p. p \<le> limit) (take depth ps)) =
        {p \<in> set (take depth ps). p \<le> limit}"
    by auto
  show ?thesis
    using selected_prefix_rank_length[OF sorted depth]
      distinct_card[OF filtered_distinct] set_filtered
    by simp
qed

lemma selected_known_empty [simp]:
  "selected_known ps depth lo lo = 0"
  by (simp add: selected_known_def)

theorem selected_known_half_open_exact:
  assumes sorted: "sorted ps" and distinct: "distinct ps"
    and depth: "depth \<le> length ps"
    and positive: "0 < lo" and order: "lo \<le> hi"
  shows "selected_known ps depth lo hi =
    card {p \<in> set (take depth ps). lo \<le> p \<and> p < hi}"
proof -
  let ?selected = "set (take depth ps)"
  let ?upper = "{p \<in> ?selected. p \<le> hi - 1}"
  let ?lower = "{p \<in> ?selected. p \<le> lo - 1}"
  have lower_subset: "?lower \<subseteq> ?upper" using order by auto
  have lower_finite: "finite ?lower" by simp
  have difference:
      "?upper - ?lower = {p \<in> ?selected. lo \<le> p \<and> p < hi}"
    using positive order by auto
  have upper_rank:
      "min depth (sorted_factor_rank ps (hi - 1)) = card ?upper"
    by (rule selected_prefix_rank_card[OF sorted distinct depth])
  have lower_rank:
      "min depth (sorted_factor_rank ps (lo - 1)) = card ?lower"
    by (rule selected_prefix_rank_card[OF sorted distinct depth])
  show ?thesis
    unfolding selected_known_def
    using upper_rank lower_rank card_Diff_subset[OF lower_finite lower_subset]
      difference
    by simp
qed

text \<open>\<open>sorted_factor_rank\<close> is an executable mathematical model of
the value returned by \<open>bisect_right(ps, limit)\<close> for a sorted list.  This
theory proves the arithmetic selected-depth identity, including an empty
interval.  It does not yet simulate CPython's mutable binary-search loop or
authenticate the Python list object and its retained arena binding.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms selected_prefix_rank_length selected_prefix_rank_card
      selected_known_half_open_exact}) then ()
    else error "Selected prime prefix rank refinement depends on an oracle";
\<close>

end
