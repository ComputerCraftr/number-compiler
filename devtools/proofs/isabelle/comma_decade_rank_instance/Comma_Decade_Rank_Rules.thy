theory Comma_Decade_Rank_Rules
  imports Comma_Round_Witness_Check.Comma_Round_Witness
begin

text \<open>Rank rows consume exact observed successors. Candidate ranks supply
only natural values; neither successor choices nor successful checks are
premises hidden in these rules. Interval composition changes proof shape,
not row coverage.\<close>

lemma comma_observed_rank_continueI:
  assumes observation: "comma_decade_observed_control source=Comma_Decade_Continue target"
    and admitted: "comma_decade_admitted target"
    and decrease: "rank target<rank source"
  shows "comma_decade_observed_rank_step rank source"
  using admitted decrease
  by (simp only: comma_decade_observed_rank_step_def observation
    comma_decade_outcome.case HOL.simp_thms)

lemma comma_observed_rank_continue_valuesI:
  assumes observation: "comma_decade_observed_control source=Comma_Decade_Continue target"
    and admitted: "comma_decade_admitted target"
    and target_rank: "rank target=target_value"
    and source_rank: "rank source=source_value"
    and decrease: "target_value<source_value"
  shows "comma_decade_observed_rank_step rank source"
proof (rule comma_observed_rank_continueI[OF observation admitted])
  show "rank target<rank source"
    using decrease by (simp only: target_rank source_rank)
qed

lemma comma_observed_rank_forkI:
  assumes "comma_decade_observed_control source=Comma_Decade_Fork a d"
  shows "comma_decade_observed_rank_step rank source"
  by (simp only: comma_decade_observed_rank_step_def assms
    comma_decade_outcome.case HOL.simp_thms)

lemma comma_observed_rank_landmineI:
  assumes "comma_decade_observed_control source=Comma_Decade_Landmine d"
  shows "comma_decade_observed_rank_step rank source"
  by (simp only: comma_decade_observed_rank_step_def assms
    comma_decade_outcome.case HOL.simp_thms)

definition comma_rank_interval :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_rank_interval P lo hi=(\<forall>i. lo\<le>i \<longrightarrow> i<hi \<longrightarrow> P i)"

lemma comma_rank_interval_empty:
  "comma_rank_interval P a a"
  by (simp add: comma_rank_interval_def)

lemma comma_rank_interval_singleton:
  assumes "P a"
  shows "comma_rank_interval P a (Suc a)"
  unfolding comma_rank_interval_def
proof (intro allI impI)
  fix i assume "a\<le>i" "i<Suc a"
  then have "i=a" by arith
  then show "P i" using assms by simp
qed

lemma comma_rank_interval_append:
  assumes left: "comma_rank_interval P lo middle"
    and right: "comma_rank_interval P middle hi"
  shows "comma_rank_interval P lo hi"
  using left right unfolding comma_rank_interval_def by (metis not_le)

lemma comma_rank_interval_zero_prefix:
  assumes "comma_rank_interval P 0 n"
  shows "\<forall>i<n. P i"
  using assms by (simp add: comma_rank_interval_def)

lemma comma_rank_range_append:
  assumes left: "\<forall>i<a. P (i::nat)"
    and right: "\<forall>i<b. P (a+i)"
  shows "\<forall>i<a+b. P i"
proof (intro allI impI)
  fix i assume bound: "i<a+b"
  show "P i"
  proof (cases "i<a")
    case True
    then show ?thesis using left by blast
  next
    case False
    have offset: "i-a<b" "a+(i-a)=i" using False bound by arith+
    show ?thesis using right offset by metis
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_observed_rank_continueI comma_observed_rank_continue_valuesI
      comma_observed_rank_forkI comma_observed_rank_landmineI
      comma_rank_interval_empty comma_rank_interval_singleton
      comma_rank_interval_append comma_rank_interval_zero_prefix
      comma_rank_range_append})
    then () else error "Decade rank rules depend on an oracle";
\<close>
end
