theory Comma_Future_Infinite_Lift
  imports Comma_Future_Losing_Lift
begin

definition comma_literal_unbounded :: "nat \<Rightarrow> bool" where
  "comma_literal_unbounded source = (\<forall>bound. \<exists>weight\<ge>bound. \<exists>target.
    comma_literal_path weight source target)"

lemma comma_literal_children_finite:
  "finite {v. comma_child source v}"
proof (rule finite_subset)
  show "{v. comma_child source v} \<subseteq>
      {source+10*(source mod 10)+1..source+10*(source mod 10)+9}"
    by (auto simp: comma_child_def comma_sector_def)
  show "finite {source+10*(source mod 10)+1..source+10*(source mod 10)+9}"
    by simp
qed

lemma comma_literal_unbounded_has_child:
  assumes unbounded: "comma_literal_unbounded source"
  shows "\<exists>successor. comma_child source successor \<and> comma_literal_unbounded successor"
proof (rule ccontr)
  assume no_child: "\<not>(\<exists>successor. comma_child source successor \<and> comma_literal_unbounded successor)"
  let ?C = "{v. comma_child source v}"
  have bounds: "\<forall>v\<in>?C. \<exists>bound. \<forall>weight\<ge>bound. \<forall>target.
      \<not>comma_literal_path weight v target"
    using no_child by (auto simp: comma_literal_unbounded_def)
  obtain bound where bound: "\<forall>v\<in>?C. \<forall>weight\<ge>bound v. \<forall>target.
      \<not>comma_literal_path weight v target"
    using bounds by (metis bchoice)
  have finite: "finite (bound ` ?C)"
    using comma_literal_children_finite by simp
  have maximum_exists: "\<exists>m. \<forall>n\<in>bound ` ?C. n\<le>m"
    using finite by (simp only: finite_nat_set_iff_bounded_le)
  obtain maximum where maximum: "\<forall>n\<in>bound ` ?C. n\<le>maximum"
    using maximum_exists by blast
  obtain weight target where large: "Suc maximum\<le>weight"
    and path: "comma_literal_path weight source target"
    using spec[OF unbounded[unfolded comma_literal_unbounded_def], of "Suc maximum"]
    by blast
  obtain successor rest where edge: "comma_child source successor"
    and tail: "comma_literal_path rest successor target" and weight: "weight=Suc rest"
    using path large by (cases rule: comma_literal_path.cases) auto
  have "bound successor\<le>maximum" using maximum edge by blast
  then have "bound successor\<le>rest" using large weight by arith
  then show False using bound edge tail by blast
qed

theorem comma_literal_unbounded_infinite_path:
  assumes unbounded: "comma_literal_unbounded source"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=source \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have initial: "\<exists>x. comma_literal_unbounded x \<and> ((0::nat)=0 \<longrightarrow> x=source)"
    using unbounded by blast
  have next_exists: "\<And>x n. comma_literal_unbounded x \<and> (n=0 \<longrightarrow> x=source) \<Longrightarrow>
    \<exists>y. (comma_literal_unbounded y \<and> (Suc n=0 \<longrightarrow> y=source)) \<and>
      comma_child x y"
    using comma_literal_unbounded_has_child by auto
  obtain path :: "nat \<Rightarrow> nat" where path: "\<forall>n.
      (comma_literal_unbounded (path n) \<and> (n=0 \<longrightarrow> path n=source)) \<and>
      comma_child (path n) (path (Suc n))"
    using dependent_nat_choice[
      where P="\<lambda>n x. comma_literal_unbounded x \<and> (n=0 \<longrightarrow> x=source)"
        and Q="\<lambda>n x y. comma_child x y", OF initial next_exists] by blast
  show ?thesis using path by blast
qed

lemma comma_literal_unbounded_prefix:
  assumes path: "comma_literal_path weight source target"
    and unbounded: "comma_literal_unbounded target"
  shows "comma_literal_unbounded source"
  unfolding comma_literal_unbounded_def
proof (intro allI)
  fix bound
  obtain tail final_state where large: "bound\<le>tail"
    and tail: "comma_literal_path tail target final_state"
    using spec[OF unbounded[unfolded comma_literal_unbounded_def], of bound] by blast
  have joined: "comma_literal_path (weight+tail) source final_state"
    by (rule comma_literal_path_append[OF path tail])
  have "bound\<le>weight+tail" using large by arith
  then show "\<exists>weight\<ge>bound. \<exists>target. comma_literal_path weight source target"
    using joined by blast
qed

theorem comma_checked_cycle_unbounded:
  assumes cert: "comma_rank_witness comma_total_children (set comma_boundary_states) rank"
    and cycle: "comma_surviving_delta_path rank 314 q q 924"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p" and phase: "p mod 924 = snd (snd q)"
  shows "comma_literal_unbounded (comma_boundary_value q p)"
  unfolding comma_literal_unbounded_def
proof (intro allI)
  fix bound
  obtain weight where large: "bound*314\<le>weight"
    and path: "comma_literal_path weight (comma_boundary_value q p)
      (comma_boundary_value q (p+bound*924))"
    using comma_checked_cycle_literal_returns[where k=bound, OF assms] by blast
  have "bound\<le>weight" using large by arith
  then show "\<exists>weight\<ge>bound. \<exists>target.
      comma_literal_path weight (comma_boundary_value q p) target"
    using path by blast
qed

corollary comma_checked_cycle_infinite_literal_path:
  assumes "comma_rank_witness comma_total_children (set comma_boundary_states) rank"
    "comma_surviving_delta_path rank 314 q q 924"
    "comma_boundary_valid q" "5\<le>p" "p mod 924 = snd (snd q)"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  by (rule comma_literal_unbounded_infinite_path[OF comma_checked_cycle_unbounded[OF assms]])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_literal_unbounded_infinite_path comma_checked_cycle_unbounded
      comma_checked_cycle_infinite_literal_path})
    then () else error "Comma infinite lift depends on an oracle";
\<close>
end
