theory Comma_Future_Safety
  imports "Comma_Arithmetic.Comma_Child_Cylinder"
begin

text \<open>A finite quotient is useful for an infinite-path argument only after
its complete child relation has been refined to literal comma steps.  The
following fixed-point argument is independent of the representation of a
boundary macro.  In particular, a list of experimentally observed choices
does not satisfy any of its premises.\<close>

primrec comma_losing_levels ::
  "('a \<Rightarrow> 'a list) \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set" where
  "comma_losing_levels children states 0 =
    {q \<in> states. children q = []}"
| "comma_losing_levels children states (Suc n) =
    comma_losing_levels children states n \<union>
    {q \<in> states. children q \<noteq> [] \<and>
      set (children q) \<subseteq> comma_losing_levels children states n}"

lemma comma_losing_levels_subset:
  "comma_losing_levels children states n \<subseteq> states"
  by (induction n) auto

lemma comma_losing_levels_mono:
  "comma_losing_levels children states n \<subseteq>
    comma_losing_levels children states (Suc n)"
  by simp

lemma comma_losing_levels_zero_subset:
  "comma_losing_levels children states 0 \<subseteq>
    comma_losing_levels children states n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by auto
qed

inductive comma_all_branches_terminate ::
  "('a \<Rightarrow> 'a list) \<Rightarrow> 'a \<Rightarrow> bool" for children where
  terminal: "children q = [] \<Longrightarrow> comma_all_branches_terminate children q"
| branch: "children q \<noteq> [] \<Longrightarrow>
    (\<And>r. r \<in> set (children q) \<Longrightarrow>
      comma_all_branches_terminate children r) \<Longrightarrow>
    comma_all_branches_terminate children q"

lemma comma_losing_levels_terminate:
  assumes "q \<in> comma_losing_levels children states n"
  shows "comma_all_branches_terminate children q"
  using assms
proof (induction n arbitrary: q)
  case 0
  then show ?case
    by (auto intro: comma_all_branches_terminate.terminal)
next
  case (Suc n)
  then show ?case
    by (auto intro: comma_all_branches_terminate.branch)
qed

lemma comma_termination_excludes_infinite_path:
  assumes terminal: "comma_all_branches_terminate children q"
  shows "\<not> (\<exists>path :: nat \<Rightarrow> 'a.
    path 0 = q \<and>
    (\<forall>n. path (Suc n) \<in> set (children (path n))))"
  using terminal
proof (induction rule: comma_all_branches_terminate.induct)
  case (terminal q)
  show ?case
  proof
    assume "\<exists>path :: nat \<Rightarrow> 'a.
      path 0 = q \<and>
      (\<forall>n. path (Suc n) \<in> set (children (path n)))"
    then obtain path :: "nat \<Rightarrow> 'a" where
      head: "path 0 = q" and
      edge: "path (Suc 0) \<in> set (children (path 0))"
      by blast
    show False using terminal.hyps head edge by simp
  qed
next
  case (branch q)
  show ?case
  proof
    assume "\<exists>path :: nat \<Rightarrow> 'a.
      path 0 = q \<and>
      (\<forall>n. path (Suc n) \<in> set (children (path n)))"
    then obtain path :: "nat \<Rightarrow> 'a" where
      head: "path 0 = q" and
      edges: "\<And>n. path (Suc n) \<in> set (children (path n))"
      by blast
    let ?tail = "\<lambda>n. path (Suc n)"
    have child: "path 1 \<in> set (children q)"
      using edges[of 0] head by simp
    have stop: "\<not> (\<exists>other :: nat \<Rightarrow> 'a.
      other 0 = path 1 \<and>
      (\<forall>n. other (Suc n) \<in> set (children (other n))))"
      using branch.IH[OF child] .
    have tail_head: "?tail 0 = path 1" by simp
    have tail_edges: "\<forall>n. ?tail (Suc n) \<in> set (children (?tail n))"
      using edges by simp
    have "\<exists>other :: nat \<Rightarrow> 'a.
      other 0 = path 1 \<and>
      (\<forall>n. other (Suc n) \<in> set (children (other n)))"
      using tail_head tail_edges by (rule_tac x="?tail" in exI) simp
    then show False using stop by contradiction
  qed
qed

corollary comma_losing_state_has_no_infinite_path:
  assumes "q \<in> comma_losing_levels children states n"
  shows "\<not> (\<exists>path :: nat \<Rightarrow> 'a.
    path 0 = q \<and>
    (\<forall>j. path (Suc j) \<in> set (children (path j))))"
proof -
  have terminal: "comma_all_branches_terminate children q"
    using comma_losing_levels_terminate[OF assms] .
  show ?thesis
    using comma_termination_excludes_infinite_path[OF terminal] .
qed

definition comma_winning_states ::
  "('a \<Rightarrow> 'a list) \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a set" where
  "comma_winning_states children states n =
    states - comma_losing_levels children states n"

lemma comma_winning_has_child:
  assumes stable: "comma_losing_levels children states (Suc n) =
      comma_losing_levels children states n"
    and closed: "\<And>q. q \<in> states \<Longrightarrow> set (children q) \<subseteq> states"
    and winner: "q \<in> comma_winning_states children states n"
  shows "\<exists>r \<in> set (children q).
    r \<in> comma_winning_states children states n"
proof -
  let ?L = "comma_losing_levels children states n"
  have q_state: "q \<in> states" and q_live: "q \<notin> ?L"
    using winner by (auto simp: comma_winning_states_def)
  have nonempty: "children q \<noteq> []"
  proof
    assume "children q = []"
    then have "q \<in> comma_losing_levels children states 0"
      using q_state by simp
    then show False using q_live comma_losing_levels_zero_subset[of children states n]
      by auto
  qed
  have outside: "\<not> set (children q) \<subseteq> ?L"
  proof
    assume "set (children q) \<subseteq> ?L"
    then have "q \<in> comma_losing_levels children states (Suc n)"
      using q_state nonempty by simp
    then have "q \<in> ?L" using stable by (simp only: stable)
    then show False using q_live by contradiction
  qed
  then obtain r where "r \<in> set (children q)" "r \<notin> ?L"
    by blast
  moreover have "r \<in> states" using closed[OF q_state] calculation by blast
  ultimately show ?thesis by (auto simp: comma_winning_states_def)
qed

definition comma_selected_winner ::
  "('a \<Rightarrow> 'a list) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a" where
  "comma_selected_winner children winners q =
    (SOME r. r \<in> set (children q) \<and> r \<in> winners)"

lemma comma_selected_winner_admitted:
  assumes "\<exists>r \<in> set (children q). r \<in> winners"
  shows "comma_selected_winner children winners q \<in> set (children q)"
    and "comma_selected_winner children winners q \<in> winners"
proof -
  have exists: "\<exists>r. r \<in> set (children q) \<and> r \<in> winners"
    using assms by blast
  have selected: "(SOME r. r \<in> set (children q) \<and> r \<in> winners)
    \<in> set (children q) \<and>
    (SOME r. r \<in> set (children q) \<and> r \<in> winners) \<in> winners"
    by (rule someI_ex[OF exists])
  then show "comma_selected_winner children winners q \<in> set (children q)"
    "comma_selected_winner children winners q \<in> winners"
    by (simp_all add: comma_selected_winner_def)
qed

primrec comma_winning_orbit ::
  "('a \<Rightarrow> 'a list) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a" where
  "comma_winning_orbit children winners first 0 = first"
| "comma_winning_orbit children winners first (Suc n) =
    comma_selected_winner children winners
      (comma_winning_orbit children winners first n)"

lemma comma_winning_orbit_stays_admitted:
  assumes stable: "comma_losing_levels children states (Suc k) =
      comma_losing_levels children states k"
    and closed: "\<And>q. q \<in> states \<Longrightarrow> set (children q) \<subseteq> states"
    and first: "first \<in> comma_winning_states children states k"
  defines "W \<equiv> comma_winning_states children states k"
  shows "comma_winning_orbit children W first n \<in> W"
    and "comma_winning_orbit children W first (Suc n) \<in>
      set (children (comma_winning_orbit children W first n))"
proof -
  have every: "\<And>q. q \<in> W \<Longrightarrow>
    comma_selected_winner children W q \<in> W \<and>
    comma_selected_winner children W q \<in> set (children q)"
  proof -
    fix q assume in_W: "q \<in> W"
    have admitted: "\<exists>r \<in> set (children q). r \<in> W"
      using comma_winning_has_child[OF stable closed]
        in_W by (simp add: W_def)
    have selected_W: "comma_selected_winner children W q \<in> W"
      using comma_selected_winner_admitted(2)
        [where children=children and q=q and winners=W, OF admitted] .
    have selected_child:
      "comma_selected_winner children W q \<in> set (children q)"
      using comma_selected_winner_admitted(1)
        [where children=children and q=q and winners=W, OF admitted] .
    show "comma_selected_winner children W q \<in> W \<and>
      comma_selected_winner children W q \<in> set (children q)"
      using selected_W selected_child by (rule conjI)
  qed
  have inside: "comma_winning_orbit children W first n \<in> W" for n
  proof (induction n)
    case 0
    then show ?case using first by (simp add: W_def)
  next
    case (Suc n)
    then show ?case using every by simp
  qed
  then show "comma_winning_orbit children W first n \<in> W" .
  show "comma_winning_orbit children W first (Suc n) \<in>
      set (children (comma_winning_orbit children W first n))"
    using every[OF inside] by simp
qed

corollary comma_winning_state_has_infinite_quotient_path:
  assumes stable: "comma_losing_levels children states (Suc k) =
      comma_losing_levels children states k"
    and closed: "\<And>q. q \<in> states \<Longrightarrow> set (children q) \<subseteq> states"
    and first: "first \<in> comma_winning_states children states k"
  shows "\<exists>path :: nat \<Rightarrow> 'a.
    path 0 = first \<and>
    (\<forall>n. path n \<in> comma_winning_states children states k \<and>
      path (Suc n) \<in> set (children (path n)))"
proof -
  let ?W = "comma_winning_states children states k"
  let ?path = "comma_winning_orbit children ?W first"
  have inside: "?path n \<in> ?W" for n
    using comma_winning_orbit_stays_admitted(1)[OF stable closed first]
    by simp
  have edge: "?path (Suc n) \<in> set (children (?path n))" for n
    using comma_winning_orbit_stays_admitted(2)[OF stable closed first]
    by simp
  show ?thesis
  proof (rule exI[of _ ?path], rule conjI)
    show "?path 0 = first" by simp
    show "\<forall>n. ?path n \<in> ?W \<and>
      ?path (Suc n) \<in> set (children (?path n))"
    proof (rule allI)
      fix n
      show "?path n \<in> ?W \<and>
        ?path (Suc n) \<in> set (children (?path n))"
      proof (rule conjI)
        show "?path n \<in> ?W" using inside[of n] .
        show "?path (Suc n) \<in> set (children (?path n))"
          using edge[of n] .
      qed
    qed
  qed
qed

text \<open>The concrete comma theorem must establish the fixed-point equality,
the finite cardinalities and the 314-step return by evaluating the *proved*
boundary constructor.  None is assumed by this theory.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_losing_levels_terminate
      comma_termination_excludes_infinite_path
      comma_losing_state_has_no_infinite_path comma_winning_has_child
      comma_winning_orbit_stays_admitted
      comma_winning_state_has_infinite_quotient_path})
    then () else error "Comma future-safety proof depends on an oracle";
\<close>

end
