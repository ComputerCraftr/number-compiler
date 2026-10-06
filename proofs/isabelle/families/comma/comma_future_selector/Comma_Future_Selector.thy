theory Comma_Future_Selector
  imports Comma_Cylinder.Comma_Future_Safety
begin

text \<open>Representation-independent selector completeness.  No numeric rank,
finite-state table or stabilization bound is required.  A concrete constructor
must still establish every locale assumption, including complete children and
well-founded descent; this theory does not define the comma survivor selector.\<close>

locale comma_future_selector =
  fixes children :: "'a \<Rightarrow> 'a list"
    and valid :: "'a \<Rightarrow> bool"
    and dead :: "'a \<Rightarrow> bool"
    and selected :: "'a \<Rightarrow> 'a"
    and descent :: "('a \<times> 'a) set"
  assumes closed: "valid q \<Longrightarrow> r \<in> set (children q) \<Longrightarrow> valid r"
    and wellfounded: "wf descent"
    and dead_children: "valid q \<Longrightarrow> dead q \<Longrightarrow>
      r \<in> set (children q) \<Longrightarrow> dead r \<and> (r,q) \<in> descent"
    and live_child: "valid q \<Longrightarrow> \<not> dead q \<Longrightarrow>
      selected q \<in> set (children q) \<and> \<not> dead (selected q)"
    and rejected_dead: "valid q \<Longrightarrow> \<not> dead q \<Longrightarrow>
      r \<in> set (children q) \<Longrightarrow> r \<noteq> selected q \<Longrightarrow> dead r"
begin


lemma dead_terminates:
  assumes "valid q" "dead q"
  shows "comma_all_branches_terminate children q"
  using assms
proof (induction q rule: wf_induct_rule[OF wellfounded, case_names less])
  case (less q)
  show ?case
  proof (cases "children q = []")
    case True
    then show ?thesis by (rule comma_all_branches_terminate.terminal)
  next
    case False
    show ?thesis
    proof (rule comma_all_branches_terminate.branch[where children=children and q=q, OF False])
      fix r assume child: "r \<in> set (children q)"
      have lower: "dead r" "(r,q) \<in> descent"
        using dead_children[OF less.prems child] by auto
      have admitted: "valid r" by (rule closed[OF less.prems(1) child])
      show "comma_all_branches_terminate children r"
        by (rule less.IH[OF lower(2) admitted lower(1)])
    qed
  qed
qed


lemma selected_orbit_live:
  assumes "valid q" "\<not> dead q"
  shows "valid ((selected ^^ n) q) \<and> \<not> dead ((selected ^^ n) q)"
proof (induction n)
  case 0
  then show ?case using assms by simp
next
  case (Suc n)
  have edge: "selected ((selected ^^ n) q) \<in> set (children ((selected ^^ n) q))"
    and live: "\<not> dead (selected ((selected ^^ n) q))"
    using live_child Suc.IH by auto
  have admitted: "valid (selected ((selected ^^ n) q))"
    using closed Suc.IH edge by blast
  show ?case using admitted live by (simp add: funpow_Suc_right)
qed


lemma live_infinite_path:
  assumes "valid q" "\<not> dead q"
  shows "\<exists>path :: nat \<Rightarrow> 'a. path 0 = q \<and>
    (\<forall>n. path (Suc n) \<in> set (children (path n)))"
proof -
  let ?path = "\<lambda>n. (selected ^^ n) q"
  have edge: "\<And>n. ?path (Suc n) \<in> set (children (?path n))"
    using selected_orbit_live[OF assms] live_child
    by (simp add: funpow_Suc_right)
  have edges: "\<forall>n. ?path (Suc n) \<in> set (children (?path n))"
    using edge by blast
  show ?thesis by (rule exI[of _ ?path], rule conjI) (simp, rule edges)
qed


lemma live_not_terminating:
  assumes "valid q" "\<not> dead q"
  shows "\<not> comma_all_branches_terminate children q"
  using live_infinite_path[OF assms] comma_termination_excludes_infinite_path[where children=children and q=q]
  by blast


lemma selector_complete:
  assumes "valid q"
  shows "(dead q \<longleftrightarrow> comma_all_branches_terminate children q) \<and>
    (\<not> dead q \<longleftrightarrow> (\<exists>path :: nat \<Rightarrow> 'a.
       path 0 = q \<and> (\<forall>n. path (Suc n) \<in> set (children (path n)))))"
  using dead_terminates[OF assms] live_not_terminating[OF assms]
    live_infinite_path[OF assms] comma_termination_excludes_infinite_path[where children=children and q=q]
  by blast


lemma selected_unique_nonterminating:
  assumes admitted: "valid q" and live: "\<not> dead q"
  shows "\<exists>!r. r \<in> set (children q) \<and>
    \<not> comma_all_branches_terminate children r"
proof -
  have chosen: "selected q \<in> set (children q)" "\<not> dead (selected q)"
    using live_child[OF admitted live] by auto
  have chosen_valid: "valid (selected q)"
    by (rule closed[OF admitted chosen(1)])
  have chosen_live: "\<not> comma_all_branches_terminate children (selected q)"
    by (rule live_not_terminating[OF chosen_valid chosen(2)])
  have unique: "\<And>r. r \<in> set (children q) \<Longrightarrow>
      \<not> comma_all_branches_terminate children r \<Longrightarrow> r = selected q"
  proof -
    fix r assume child: "r \<in> set (children q)"
      and infinite: "\<not> comma_all_branches_terminate children r"
    show "r = selected q"
    proof (rule ccontr)
      assume other: "r \<noteq> selected q"
      have dead_r: "dead r" by (rule rejected_dead[OF admitted live child other])
      have valid_r: "valid r" by (rule closed[OF admitted child])
      show False using dead_terminates[OF valid_r dead_r] infinite by blast
    qed
  qed
  show ?thesis using chosen(1) chosen_live unique by blast
qed

end

ML \<open>
  val _ = if null (Thm_Deps.all_oracles @{thms
    comma_future_selector.dead_terminates
    comma_future_selector.live_infinite_path
    comma_future_selector.selector_complete
    comma_future_selector.selected_unique_nonterminating})
    then () else error "Future selector completeness depends on an oracle";
\<close>
end
