theory Comma_Checked_Ranks
  imports Comma_Future_Safety
begin

text \<open>A candidate rank table is proof data, never an assumption about
the comma graph.  The executable checker below inspects every child of the
actual finite transition.  Rank zero means a literal landmine.  A positive
rank is exactly one above its largest child rank.  An unranked state has
exactly one unranked child.  None from a fuelled constructor must be
rejected before this checker is called.\<close>

definition comma_rank_witness ::
  "('a \<Rightarrow> 'a list) \<Rightarrow> 'a set \<Rightarrow>
    ('a \<Rightarrow> nat option) \<Rightarrow> bool" where
  "comma_rank_witness children states rank \<longleftrightarrow>
    (\<forall>q \<in> states.
      set (children q) \<subseteq> states \<and>
      (case rank q of
        None \<Rightarrow> (\<exists>!r. r \<in> set (children q) \<and> rank r = None)
      | Some n \<Rightarrow>
          if n = 0 then children q = []
          else children q \<noteq> [] \<and>
            (\<forall>r \<in> set (children q). \<exists>m<n. rank r = Some m) \<and>
            (\<exists>r \<in> set (children q). rank r = Some (n - 1))))"

lemma comma_rank_witness_closed:
  assumes "comma_rank_witness children states rank" "q \<in> states"
  shows "set (children q) \<subseteq> states"
  using assms by (auto simp: comma_rank_witness_def)

lemma comma_rank_zero_terminal:
  assumes "comma_rank_witness children states rank"
    "q \<in> states" "rank q = Some 0"
  shows "children q = []"
  using assms by (auto simp: comma_rank_witness_def)

lemma comma_rank_positive_children:
  assumes cert: "comma_rank_witness children states rank"
    and state: "q \<in> states"
    and positive: "rank q = Some n" "0 < n"
  shows "children q \<noteq> []"
    and "\<forall>r \<in> set (children q). \<exists>m<n. rank r = Some m"
    and "\<exists>r \<in> set (children q). rank r = Some (n - 1)"
  using cert state positive by (auto simp: comma_rank_witness_def)

lemma comma_ranked_state_terminates:
  assumes cert: "comma_rank_witness children states rank"
    and state: "q \<in> states"
    and ranked: "rank q = Some n"
  shows "comma_all_branches_terminate children q"
  using state ranked
proof (induction n arbitrary: q rule: less_induct)
  case (less n)
  show ?case
  proof (cases n)
    case 0
    have "children q = []"
      using comma_rank_zero_terminal[OF cert less.prems(1)]
        less.prems(2) 0 by simp
    then show ?thesis by (rule comma_all_branches_terminate.terminal)
  next
    case (Suc m)
    have positive: "0 < n" using Suc by simp
    have nonempty: "children q \<noteq> []"
      using comma_rank_positive_children(1)[OF cert less.prems
        positive] .
    have lower: "\<And>r. r \<in> set (children q) \<Longrightarrow>
      \<exists>k<n. rank r = Some k"
      using comma_rank_positive_children(2)[OF cert less.prems
        positive] by blast
    show ?thesis
    proof (rule comma_all_branches_terminate.branch
        [where children=children and q=q, OF nonempty])
      fix r assume child: "r \<in> set (children q)"
      obtain k where below: "k < n" and rank_r: "rank r = Some k"
        using lower[OF child] by blast
      have state_r: "r \<in> states"
        using comma_rank_witness_closed[OF cert less.prems(1)] child
        by blast
      show "comma_all_branches_terminate children r"
        using less.IH[OF below state_r rank_r] .
    qed
  qed
qed

lemma comma_unranked_has_unique_unranked_child:
  assumes cert: "comma_rank_witness children states rank"
    and state: "q \<in> states" and live: "rank q = None"
  shows "\<exists>!r. r \<in> set (children q) \<and> r \<in> states \<and>
    rank r = None"
proof -
  have all: "\<forall>x \<in> states.
    set (children x) \<subseteq> states \<and>
    (case rank x of
      None \<Rightarrow> (\<exists>!r. r \<in> set (children x) \<and> rank r = None)
    | Some n \<Rightarrow>
        if n = 0 then children x = []
        else children x \<noteq> [] \<and>
          (\<forall>r \<in> set (children x). \<exists>m<n. rank r = Some m) \<and>
          (\<exists>r \<in> set (children x). rank r = Some (n - 1)))"
    using cert by (simp only: comma_rank_witness_def)
  note local = bspec[OF all state]
  have unique: "\<exists>!r. r \<in> set (children q) \<and> rank r = None"
    using local live by simp
  have closed: "set (children q) \<subseteq> states"
    using comma_rank_witness_closed[OF cert state] .
  show ?thesis using unique closed by blast
qed

lemma comma_losing_levels_le:
  assumes "i \<le> j"
  shows "comma_losing_levels children states i \<subseteq>
    comma_losing_levels children states j"
  using assms
proof (induction j arbitrary: i)
  case 0
  then show ?case by simp
next
  case (Suc j)
  show ?case
  proof (cases "i \<le> j")
    case True
    have "comma_losing_levels children states i \<subseteq>
      comma_losing_levels children states j"
      using Suc.IH[OF True] .
    also have "... \<subseteq> comma_losing_levels children states (Suc j)"
      by (rule comma_losing_levels_mono)
    finally show ?thesis .
  next
    case False
    then have "i = Suc j" using Suc.prems by simp
    then show ?thesis by simp
  qed
qed

lemma comma_ranked_state_at_its_level:
  assumes cert: "comma_rank_witness children states rank"
    and state: "q \<in> states" and ranked: "rank q = Some n"
  shows "q \<in> comma_losing_levels children states n"
  using state ranked
proof (induction n arbitrary: q rule: less_induct)
  case (less n)
  show ?case
  proof (cases n)
    case 0
    have "children q = []"
      using comma_rank_zero_terminal[OF cert less.prems(1)]
        less.prems(2) 0 by simp
    then show ?thesis using less.prems(1) 0 by simp
  next
    case (Suc m)
    have positive: "0 < n" using Suc by simp
    have nonempty: "children q \<noteq> []"
      using comma_rank_positive_children(1)[OF cert less.prems
        positive] .
    have lower: "\<And>r. r \<in> set (children q) \<Longrightarrow>
      \<exists>k<n. rank r = Some k"
      using comma_rank_positive_children(2)[OF cert less.prems
        positive] by blast
    have all: "set (children q) \<subseteq>
      comma_losing_levels children states m"
    proof
      fix r assume child: "r \<in> set (children q)"
      obtain k where below: "k < n" and rank_r: "rank r = Some k"
        using lower[OF child] by blast
      have in_states: "r \<in> states"
        using comma_rank_witness_closed[OF cert less.prems(1)] child
        by blast
      have in_level: "r \<in> comma_losing_levels children states k"
        using less.IH[OF below in_states rank_r] .
      have "k \<le> m" using below Suc by simp
      then have "comma_losing_levels children states k \<subseteq>
        comma_losing_levels children states m"
        by (rule comma_losing_levels_le)
      then show "r \<in> comma_losing_levels children states m"
        using in_level by blast
    qed
    show ?thesis using less.prems(1) nonempty all Suc by simp
  qed
qed

lemma comma_unranked_state_outside_every_level:
  assumes cert: "comma_rank_witness children states rank"
    and state: "q \<in> states" and live: "rank q = None"
  shows "q \<notin> comma_losing_levels children states n"
  using state live
proof (induction n arbitrary: q)
  case 0
  have "\<exists>r. r \<in> set (children q) \<and> r \<in> states \<and>
    rank r = None"
    using comma_unranked_has_unique_unranked_child[OF cert "0.prems"]
    by blast
  then show ?case by auto
next
  case (Suc n)
  have not_before: "q \<notin> comma_losing_levels children states n"
    using Suc.IH[OF Suc.prems] .
  obtain r where child: "r \<in> set (children q)" and
    in_states: "r \<in> states" and rank_r: "rank r = None"
    using comma_unranked_has_unique_unranked_child[OF cert Suc.prems]
    by blast
  have not_child: "r \<notin> comma_losing_levels children states n"
    using Suc.IH[OF in_states rank_r] .
  show ?case using not_before child not_child by auto
qed

theorem comma_rank_witness_exact_fixed_point:
  assumes cert: "comma_rank_witness children states rank"
    and bounded: "\<And>q n. q \<in> states \<Longrightarrow> rank q = Some n
      \<Longrightarrow> n \<le> maximum"
  shows "comma_losing_levels children states maximum =
    {q \<in> states. rank q \<noteq> None}"
proof
  show "comma_losing_levels children states maximum \<subseteq>
      {q \<in> states. rank q \<noteq> None}"
  proof
    fix q assume in_level: "q \<in> comma_losing_levels children states maximum"
    have in_states: "q \<in> states"
      using subsetD[OF comma_losing_levels_subset
        [where children=children and states=states and n=maximum]
        in_level] .
    have "rank q \<noteq> None"
    proof
      assume unranked: "rank q = None"
      have outside: "q \<notin> comma_losing_levels children states maximum"
        using comma_unranked_state_outside_every_level
          [where n=maximum, OF cert in_states unranked] .
      then show False
        using in_level by contradiction
    qed
    then show "q \<in> {q \<in> states. rank q \<noteq> None}"
      using in_states by simp
  qed
  show "{q \<in> states. rank q \<noteq> None} \<subseteq>
      comma_losing_levels children states maximum"
  proof
    fix q assume q: "q \<in> {q \<in> states. rank q \<noteq> None}"
    obtain n where ranked: "rank q = Some n"
      using q by (cases "rank q") auto
    have at_rank: "q \<in> comma_losing_levels children states n"
      using comma_ranked_state_at_its_level[OF cert _ ranked] q
      by simp
    have "n \<le> maximum" using bounded[OF _ ranked] q by simp
    then have "comma_losing_levels children states n \<subseteq>
      comma_losing_levels children states maximum"
      by (rule comma_losing_levels_le)
    then show "q \<in> comma_losing_levels children states maximum"
      using at_rank by blast
  qed
qed

theorem comma_rank_witness_stable:
  assumes cert: "comma_rank_witness children states rank"
    and bounded: "\<And>q n. q \<in> states \<Longrightarrow> rank q = Some n
      \<Longrightarrow> n \<le> maximum"
  shows "comma_losing_levels children states (Suc maximum) =
    comma_losing_levels children states maximum"
proof (rule equalityI)
  have exact: "comma_losing_levels children states maximum =
    {q \<in> states. rank q \<noteq> None}"
    using comma_rank_witness_exact_fixed_point[OF cert bounded] .
  show "comma_losing_levels children states (Suc maximum) \<subseteq>
    comma_losing_levels children states maximum"
  proof
    fix q
    assume in_next: "q \<in> comma_losing_levels children states (Suc maximum)"
    have in_states: "q \<in> states"
      using subsetD[OF comma_losing_levels_subset
        [where children=children and states=states and n="Suc maximum"]
        in_next] .
    have ranked: "rank q \<noteq> None"
    proof
      assume unranked: "rank q = None"
      have "q \<notin> comma_losing_levels children states (Suc maximum)"
        using comma_unranked_state_outside_every_level[OF cert in_states
          unranked] .
      then show False using in_next by contradiction
    qed
    show "q \<in> comma_losing_levels children states maximum"
      using in_states ranked exact by simp
  qed
  show "comma_losing_levels children states maximum \<subseteq>
    comma_losing_levels children states (Suc maximum)"
    by (rule comma_losing_levels_mono)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_ranked_state_terminates
      comma_unranked_has_unique_unranked_child
      comma_rank_witness_exact_fixed_point comma_rank_witness_stable})
    then () else error "Comma rank checker proof depends on an oracle";
\<close>

end
