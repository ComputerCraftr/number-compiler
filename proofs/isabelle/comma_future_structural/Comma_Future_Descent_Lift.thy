theory Comma_Future_Descent_Lift
  imports Comma_Future_Structural_Check
begin

text \<open>
Generic bridges for the weaker structural future certificate.  The certificate
requires closure, strict rank decrease on every child of a ranked state, and a
unique unranked child.  These lemmas intentionally do not recover the legacy
exact-rank predecessor law or make any claim about a concrete cycle or source
root.
\<close>

lemma comma_structural_descent_ranked_no_infinite_path:
  assumes cert: "comma_descent_witness children states rank"
    and state: "q \<in> states"
    and ranked: "rank q = Some n"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> 'a. path 0=q \<and>
    (\<forall>j. path (Suc j) \<in> set (children (path j))))"
  by (rule comma_termination_excludes_infinite_path
    [OF comma_descent_ranked_state_terminates[OF cert state ranked]])

lemma comma_structural_descent_unique_survivor:
  assumes cert: "comma_descent_witness children states rank"
    and state: "q \<in> states"
    and live: "rank q = None"
  shows "\<exists>!r. r \<in> set (children q) \<and> r \<in> states \<and>
    rank r = None"
  by (rule comma_descent_witness_unranked_child[OF cert state live])

lemma comma_structural_descent_survivor_path_lift:
  assumes edge: "survivor \<in> set (children q)"
    and survivor_path: "path 0=survivor"
    and path_edges: "\<And>j. path (Suc j) \<in> set (children (path j))"
  shows "\<exists>lifted :: nat \<Rightarrow> 'a. lifted 0=q \<and>
    (\<forall>j. lifted (Suc j) \<in> set (children (lifted j)))"
proof -
  let ?lifted = "\<lambda>j. case j of 0 \<Rightarrow> q | Suc k \<Rightarrow> path k"
  have initial: "?lifted 0=q" by simp
  have edges: "\<forall>j. ?lifted (Suc j) \<in> set (children (?lifted j))"
  proof (intro allI)
    fix j
    show "?lifted (Suc j) \<in> set (children (?lifted j))"
    proof (cases j)
      case 0
      then show ?thesis using edge survivor_path by simp
    next
      case (Suc k)
      then show ?thesis using path_edges[of k] by simp
    qed
  qed
  show ?thesis by (rule exI[of _ ?lifted]) (use initial edges in blast)
qed

theorem comma_structural_loser_no_infinite_literal_path:
  assumes checked: "comma_future_structural_witness rank"
    and valid: "comma_boundary_valid q" and ranked: "rank q=Some n"
    and exponent: "5\<le>p" and phase: "p mod 924=snd (snd q)"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
proof -
  have cert: "comma_descent_witness comma_total_children (set comma_boundary_states) rank"
    by (rule comma_future_structural_descent[OF checked])
  have lower: "\<And>q n child. comma_boundary_valid q \<Longrightarrow> rank q=Some n \<Longrightarrow>
      child\<in>set (comma_total_children q) \<Longrightarrow>
      comma_boundary_valid child \<and> (\<exists>m<n. rank child=Some m)"
  proof -
    fix q n child
    assume valid: "comma_boundary_valid q" and ranked: "rank q=Some n"
      and child: "child\<in>set (comma_total_children q)"
    have state: "q\<in>set comma_boundary_states"
      using valid by (simp add: comma_boundary_states_set)
    have descent: "\<exists>m<n. rank child=Some m"
      using comma_descent_witness_ranked_children[OF cert state ranked] child by blast
    have closed: "comma_boundary_valid child"
      using comma_descent_witness_closed[OF cert state] child
      by (auto simp: comma_boundary_states_set)
    show "comma_boundary_valid child \<and> (\<exists>m<n. rank child=Some m)"
      using descent closed by blast
  qed
  show ?thesis by (rule comma_descending_loser_no_infinite_literal_path
    [OF comma_future_structural_defined[OF checked] lower valid ranked exponent phase])
qed

text \<open>Infinitude needs a closed surviving set, not a census of its
cycle. Induction extends any admitted survivor by one complete macro with
strictly positive literal weight. Actual exponents are transported on each
edge; no equality of absolute endpoints or weights is assumed.\<close>

lemma comma_structural_survivor_literal_prefix:
  assumes checked: "comma_future_structural_witness rank"
    and valid: "comma_boundary_valid q" and live: "rank q=None"
    and exponent: "5\<le>p" and phase: "p mod 924=snd (snd q)"
  shows "\<exists>weight\<ge>n. \<exists>target.
    comma_literal_path weight (comma_boundary_value q p) target"
  using valid live exponent phase
proof (induction n arbitrary: q p)
  case 0
  show ?case by (auto intro: comma_literal_path.zero)
next
  case (Suc n)
  have cert: "comma_descent_witness comma_total_children
      (set comma_boundary_states) rank"
    by (rule comma_future_structural_descent[OF checked])
  have state: "q\<in>set comma_boundary_states"
    using Suc.prems(1) by (simp add: comma_boundary_states_set)
  obtain child where edge: "child\<in>set (comma_total_children q)"
    and child_state: "child\<in>set comma_boundary_states"
    and child_live: "rank child=None"
    using comma_descent_witness_unranked_child[OF cert state Suc.prems(2)] by blast
  have child_valid: "comma_boundary_valid child"
    using child_state by (simp add: comma_boundary_states_set)
  have defined: "comma_macro_defined q"
    by (rule comma_future_structural_defined[OF checked Suc.prems(1)])
  obtain a d where outcome: "comma_total_macro q=Comma_Fork_At a d"
    using edge by (cases "comma_total_macro q")
      (auto simp: comma_total_children_def)
  obtain weight where positive: "0<weight"
    and prefix: "comma_literal_path weight (comma_boundary_value q p)
      (comma_boundary_value child (p+d))"
    using comma_total_macro_selected_literal_path(1)
      [OF defined Suc.prems(1,3,4) outcome edge] by blast
  have next_phase: "(p+d) mod 924=snd (snd child)"
    by (rule comma_total_macro_selected_literal_path(2)
      [OF defined Suc.prems(1,3,4) outcome edge])
  have next_exponent: "5\<le>p+d" using Suc.prems(3) by arith
  obtain tail target where bound: "n\<le>tail"
    and suffix: "comma_literal_path tail (comma_boundary_value child (p+d)) target"
    using Suc.IH[OF child_valid child_live next_exponent next_phase] by blast
  have path: "comma_literal_path (weight+tail) (comma_boundary_value q p) target"
    by (rule comma_literal_path_append[OF prefix suffix])
  have "Suc n\<le>weight+tail" using positive bound by arith
  then show ?case using path by blast
qed

theorem comma_structural_survivor_infinite_literal_path:
  assumes "comma_future_structural_witness rank"
    "comma_boundary_valid q" "rank q=None"
    "5\<le>p" "p mod 924=snd (snd q)"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have "comma_literal_unbounded (comma_boundary_value q p)"
    unfolding comma_literal_unbounded_def
    using comma_structural_survivor_literal_prefix[OF assms] by blast
  then show ?thesis by (rule comma_literal_unbounded_infinite_path)
qed

text \<open>
The existing weighted literal bridge needs only child closure from the
certificate.  This corollary keeps that transport available without importing
the exact-rank witness.  The cycle itself remains an explicit premise.
\<close>

theorem comma_structural_descent_cycle_literal_returns:
  assumes cert: "comma_descent_witness comma_total_children
      (set comma_boundary_states) rank"
    and cycle: "comma_surviving_delta_path rank 314 q q 924"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924 = snd (snd q)"
  shows "\<exists>weight\<ge>k*314. comma_literal_path weight
    (comma_boundary_value q p) (comma_boundary_value q (p+k*924))"
proof -
  have closed: "\<And>q. comma_boundary_valid q \<Longrightarrow>
      set (comma_total_children q) \<subseteq> {r. comma_boundary_valid r}"
  proof -
    fix q assume q_valid: "comma_boundary_valid q"
    have state: "q \<in> set comma_boundary_states"
      using q_valid by (simp add: comma_boundary_states_set)
    have state_children: "set (comma_total_children q) \<subseteq>
        set comma_boundary_states"
      by (rule comma_descent_witness_closed[OF cert state])
    show "set (comma_total_children q) \<subseteq>
        {r. comma_boundary_valid r}"
      using state_children by (simp only: comma_boundary_states_set)
  qed
  show ?thesis
    by (rule comma_surviving_delta_path_literal
      [OF comma_surviving_cycle_repeats[OF cycle] closed valid exponent phase])
qed

theorem comma_structural_descent_cycle_unbounded:
  assumes cert: "comma_descent_witness comma_total_children
      (set comma_boundary_states) rank"
    and cycle: "comma_surviving_delta_path rank 314 q q 924"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924 = snd (snd q)"
  shows "comma_literal_unbounded (comma_boundary_value q p)"
  unfolding comma_literal_unbounded_def
proof (intro allI)
  fix bound
  obtain weight where large: "bound*314\<le>weight"
    and path: "comma_literal_path weight
      (comma_boundary_value q p) (comma_boundary_value q (p+bound*924))"
    using comma_structural_descent_cycle_literal_returns
      [OF cert cycle valid exponent phase, where k=bound] by blast
  have "bound\<le>weight" using large by arith
  then show "\<exists>weight\<ge>bound. \<exists>target.
      comma_literal_path weight (comma_boundary_value q p) target"
    using path by blast
qed

corollary comma_structural_descent_cycle_infinite_literal_path:
  assumes cert: "comma_descent_witness comma_total_children
      (set comma_boundary_states) rank"
    and cycle: "comma_surviving_delta_path rank 314 q q 924"
    and valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924 = snd (snd q)"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  by (rule comma_literal_unbounded_infinite_path
    [OF comma_structural_descent_cycle_unbounded[OF assms]])

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_structural_loser_no_infinite_literal_path
      comma_structural_survivor_literal_prefix
      comma_structural_survivor_infinite_literal_path
      comma_structural_descent_ranked_no_infinite_path
      comma_structural_descent_unique_survivor
      comma_structural_descent_survivor_path_lift
      comma_structural_descent_cycle_literal_returns
      comma_structural_descent_cycle_unbounded
      comma_structural_descent_cycle_infinite_literal_path})
    then () else error "Structural comma descent lift depends on an oracle";
\<close>

end
