theory Comma_Literal_Path
  imports Comma_Boundary_Primitives
begin

text \<open>Literal path concatenation and safe-cycle paths independent of
any scalar or weighted boundary macro implementation.\<close>

inductive comma_literal_path :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  zero: "comma_literal_path 0 k k"
| step: "comma_child k k' \<Longrightarrow>
    comma_literal_path n k' target \<Longrightarrow>
    comma_literal_path (Suc n) k target"

lemma comma_literal_path_append:
  assumes first: "comma_literal_path n source middle"
    and second: "comma_literal_path m middle target"
  shows "comma_literal_path (n + m) source target"
  using first second
proof (induction arbitrary: m target rule: comma_literal_path.induct)
  case (zero k)
  then show ?case by simp
next
  case (step k k' n middle)
  then show ?case
    by (simp add: comma_literal_path.step)
qed

lemma comma_literal_path_snoc:
  assumes path: "comma_literal_path n source middle"
    and edge: "comma_child middle target"
  shows "comma_literal_path (Suc n) source target"
proof -
  have one: "comma_literal_path 1 middle target"
    using edge by (auto intro: comma_literal_path.intros)
  have "comma_literal_path (n + 1) source target"
    using comma_literal_path_append[OF path one] .
  then show ?thesis by simp
qed

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
  shows "\<exists>successor. comma_child source successor \<and>
    comma_literal_unbounded successor"
proof (rule ccontr)
  assume no_child:
    "\<not>(\<exists>successor. comma_child source successor \<and>
      comma_literal_unbounded successor)"
  let ?C = "{v. comma_child source v}"
  have bounds: "\<forall>v\<in>?C. \<exists>bound. \<forall>weight\<ge>bound. \<forall>target.
      \<not>comma_literal_path weight v target"
    using no_child by (auto simp: comma_literal_unbounded_def)
  obtain bound where bound:
    "\<forall>v\<in>?C. \<forall>weight\<ge>bound v. \<forall>target.
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
    and tail: "comma_literal_path rest successor target"
    and weight: "weight=Suc rest"
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
  have initial_state_fact:
    "\<exists>x. comma_literal_unbounded x \<and> ((0::nat)=0 \<longrightarrow> x=source)"
    using unbounded by blast
  have successor_exists_fact:
    "\<And>x n. comma_literal_unbounded x \<and> (n=0 \<longrightarrow> x=source)
      \<Longrightarrow>
      \<exists>y. (comma_literal_unbounded y \<and> (Suc n=0 \<longrightarrow> y=source))
        \<and> comma_child x y"
    using comma_literal_unbounded_has_child by auto
  obtain path :: "nat \<Rightarrow> nat" where path: "\<forall>n.
      (comma_literal_unbounded (path n) \<and>
        (n=0 \<longrightarrow> path n=source)) \<and>
      comma_child (path n) (path (Suc n))"
    using dependent_nat_choice[
      where P="\<lambda>n x. comma_literal_unbounded x \<and> (n=0 \<longrightarrow> x=source)"
        and Q="\<lambda>n x y. comma_child x y", OF initial_state_fact successor_exists_fact] by blast
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
    using spec[OF unbounded[unfolded comma_literal_unbounded_def], of bound]
    by blast
  have joined: "comma_literal_path (weight+tail) source final_state"
    by (rule comma_literal_path_append[OF path tail])
  have "bound\<le>weight+tail" using large by arith
  then show "\<exists>weight\<ge>bound. \<exists>target.
      comma_literal_path weight source target"
    using joined by blast
qed

lemma comma_infinite_literal_prefix:
  assumes edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "comma_literal_path n (path 0) (path n)"
proof (induction n)
  case 0
  then show ?case by (rule comma_literal_path.zero)
next
  case (Suc n)
  show ?case by (rule comma_literal_path_snoc[OF Suc.IH edges])
qed

lemma comma_literal_infinite_path_unbounded:
  assumes initial: "path 0=source"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "comma_literal_unbounded source"
  unfolding comma_literal_unbounded_def
proof (intro allI)
  fix bound
  have prefix: "comma_literal_path bound (path 0) (path bound)"
    by (rule comma_infinite_literal_prefix[where path=path, OF edges])
  show "\<exists>weight\<ge>bound. \<exists>target.
      comma_literal_path weight source target"
    using prefix initial by blast
qed

lemma comma_fixed_iter_literal_path:
  assumes edges: "\<forall>j<N. comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k)"
  shows "\<forall>n\<le>N. comma_literal_path n k (comma_fixed_iter f n k)"
proof -
  have path: "comma_literal_path n k (comma_fixed_iter f n k)"
    if n: "n \<le> N" for n
    using n
  proof (induction n)
    case 0
    then show ?case by (simp add: comma_literal_path.zero)
  next
    case (Suc n)
    have prefix: "n \<le> N" using Suc.prems by simp
    have edge: "comma_child (comma_fixed_iter f n k)
        (comma_fixed_iter f (Suc n) k)"
      using edges Suc.prems by auto
    show ?case using comma_literal_path_snoc[OF Suc.IH[OF prefix] edge] .
  qed
  then show ?thesis by blast
qed

lemma comma_safe_cycles_literal_path:
  fixes H G P c target :: nat
  assumes source: "comma_sector f p k" and exponent: "2 \<le> p"
    and closes: "10 dvd L * f" and period: "0 < L"
    and displacement: "0 < comma_period_displacement f (k mod 10) L"
  defines "H \<equiv> comma_headroom f p k"
    and "P \<equiv> comma_period_displacement f (k mod 10) L"
    and "G \<equiv> comma_phase_max_guard f (k mod 10) L"
    and "c \<equiv> comma_safe_cycle_count H G P target"
  shows "comma_literal_path (c * L) k (k + c * P)"
    "comma_sector f p (k + c * P)"
proof -
  have guarded: "\<forall>j<c * L. comma_child (comma_fixed_iter f j k)
      (comma_fixed_iter f (Suc j) k)"
    using comma_safe_complete_cycles_refine(3)
      [OF source exponent closes period displacement,
        where target=target]
    by (simp add: H_def P_def G_def c_def)
  have end_sector: "comma_sector f p (comma_fixed_iter f (c * L) k)"
    using comma_safe_complete_cycles_refine(2)
      [OF source exponent closes period displacement,
        where target=target]
    by (simp add: H_def P_def G_def c_def)
  have endpoint: "comma_fixed_iter f (c * L) k = k + c * P"
    using comma_fixed_iter_complete_cycles[OF closes]
    by (simp add: P_def)
  show "comma_literal_path (c * L) k (k + c * P)"
    using comma_fixed_iter_literal_path[OF guarded] endpoint by auto
  show "comma_sector f p (k + c * P)"
    using end_sector endpoint by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_literal_path_append comma_literal_path_snoc
      comma_literal_unbounded_has_child comma_literal_unbounded_infinite_path
      comma_literal_unbounded_prefix comma_infinite_literal_prefix
      comma_literal_infinite_path_unbounded comma_literal_children_finite
      comma_fixed_iter_literal_path comma_safe_cycles_literal_path})
    then () else error "Comma literal-path proof depends on an oracle";
\<close>

end
