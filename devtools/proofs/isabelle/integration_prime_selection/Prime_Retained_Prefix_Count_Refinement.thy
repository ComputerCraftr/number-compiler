theory Prime_Retained_Prefix_Count_Refinement
  imports Prime_Selected_Prefix_Rank_Refinement
begin

text \<open>A retained consecutive prefix through root \<open>R\<close> remains a
complete descriptor for every smaller query when it is viewed at the maximal
horizon immediately below the next square.  The horizon is
\<open>(R+1)^2 - 1\<close>; using \<open>R^2\<close> would incorrectly move the
square-root boundary for retained prefixes.\<close>

definition retained_root_horizon :: "nat \<Rightarrow> nat" where
  "retained_root_horizon R = (Suc R)^2 - 1"

lemma floor_sqrt_retained_root_horizon:
  "floor_sqrt (retained_root_horizon R) = R"
proof (rule antisym)
  show "floor_sqrt (retained_root_horizon R) \<le> R"
  proof (rule ccontr)
    assume "\<not> floor_sqrt (retained_root_horizon R) \<le> R"
    then have next_le:
        "Suc R \<le> floor_sqrt (retained_root_horizon R)" by simp
    then have square_le: "(Suc R)^2 \<le> retained_root_horizon R"
      using le_floor_sqrt_iff[of "Suc R" "retained_root_horizon R"] by simp
    have square_positive: "0 < (Suc R)^2" by simp
    show False using square_le square_positive
      unfolding retained_root_horizon_def by arith
  qed
  show "R \<le> floor_sqrt (retained_root_horizon R)"
    using le_floor_sqrt_iff[of R "retained_root_horizon R"]
    by (simp add: retained_root_horizon_def power2_eq_square; arith)
qed

theorem retained_consecutive_prefix_is_complete:
  assumes retained: "ps = primes_upto R"
  shows "complete_prime_prefix ps (retained_root_horizon R)"
  using retained floor_sqrt_retained_root_horizon[of R]
  by (simp add: complete_prime_prefix_def)

theorem retained_prefix_trims_to_smaller_query:
  assumes retained: "ps = primes_upto R"
    and smaller: "h \<le> retained_root_horizon R"
  shows "complete_prime_prefix (trim_prime_prefix ps h) h"
  by (rule complete_prefix_smaller_horizon[
        OF retained_consecutive_prefix_is_complete[OF retained] smaller])

text \<open>The next theorem composes the selected-depth restoration term with
the already checked zero-phase prefix-image ranks.  Its left side is the exact
arithmetic expression returned by \<open>PrimePartialSuccessorQuery.count_primes\<close>:
the two image projections plus \<open>selected_known\<close>, including the outer
minimum needed when the workspace retains factors beyond the selected stage.\<close>

theorem selected_stage_cached_image_count_exact:
  assumes sorted: "sorted retained" and distinct: "distinct retained"
    and depth: "depth \<le> length retained"
    and selected: "take depth retained = parent @ [q]"
    and prefix: "complete_prime_prefix (parent @ [q]) H"
    and lower: "2 \<le> lo" and order: "lo \<le> hi"
    and upper: "hi \<le> Suc H" and cached: "hi - 1 \<le> W"
  shows
    "selected_known retained depth lo hi +
       (mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) -
        mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1)) =
     card {p. prime p \<and> lo \<le> p \<and> p < hi}"
proof -
  have known:
      "selected_known retained depth lo hi =
        card {p \<in> set (take depth retained). lo \<le> p \<and> p < hi}"
    by (rule selected_known_half_open_exact[OF sorted distinct depth])
      (use lower order in auto)
  have image:
      "card {p \<in> set (parent @ [q]). lo \<le> p \<and> p < hi} +
         (mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) -
          mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1)) =
       card {p. prime p \<and> lo \<le> p \<and> p < hi}"
    by (rule complete_prefix_cached_image_interval_exact[
          OF prefix lower order upper cached])
  show ?thesis using known image selected by simp
qed

corollary retained_full_stage_count_exact:
  assumes retained: "ps = primes_upto R" and nonempty: "ps \<noteq> []"
    and selected: "ps = parent @ [q]"
    and lower: "2 \<le> lo" and order: "lo \<le> hi"
    and covered: "hi - 1 \<le> retained_root_horizon R"
    and cached: "hi - 1 \<le> W"
  shows
    "selected_known ps (length ps) lo hi +
       (mark_rank_before (zero_phase_prefix_word parent q W) (hi - 1) -
        mark_rank_before (zero_phase_prefix_word parent q W) (lo - 1)) =
     card {p. prime p \<and> lo \<le> p \<and> p < hi}"
proof -
  have prefix: "complete_prime_prefix ps (retained_root_horizon R)"
    by (rule retained_consecutive_prefix_is_complete[OF retained])
  have sorted: "sorted ps" and distinct: "distinct ps"
    using complete_prime_prefix_distinct_sorted[OF prefix] by auto
  have upper: "hi \<le> Suc (retained_root_horizon R)"
    using covered by arith
  show ?thesis
    by (rule selected_stage_cached_image_count_exact[
          where retained=ps and depth="length ps" and parent=parent and q=q
            and H="retained_root_horizon R" and W=W,
          OF sorted distinct _ _ _ lower order upper cached])
      (use selected prefix in simp_all)
qed

text \<open>The full-stage corollary matches \<open>select.py:256-267\<close> after
\<open>cover(upper-1)\<close> has retained \<open>primes_upto R\<close>, and
\<open>partial_successor_image.py:165-181\<close> with
\<open>depth = factor_count\<close>.  A later smaller query remains covered while
\<open>hi-1 \<le> (R+1)^2-1\<close>, even if the retained prefix is longer than
the query's minimal square-root prefix.

The proof models the source-derived consecutive list and exact arithmetic
count expression.  It does not authenticate a cached Python manifest, prove
the mutable \<open>covered_root\<close> update loop, bind arena handles to the
retained list, or discharge scheduler and resource-budget behavior.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms floor_sqrt_retained_root_horizon
      retained_consecutive_prefix_is_complete
      retained_prefix_trims_to_smaller_query
      selected_stage_cached_image_count_exact
      retained_full_stage_count_exact}) then ()
    else error "Retained prime prefix count refinement depends on an oracle";
\<close>

end
