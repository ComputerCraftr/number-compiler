theory Comma_Future_Structural_Check
  imports Comma_Future_Check.Comma_Future_Infinite_Lift
    Comma_Decade_Summary_Transport.Comma_Decade_Summary_Transport
begin

text \<open>The future release checker consumes a certified decade summary.
It never replays a bounded sequence of decade rounds.  The numeric option is a
well-founded descent measure only: losing states require strict decrease on all
children, while survivor states require exactly one survivor child.\<close>

text \<open>A structural certificate records only closure, strict descent on
ranked states, and the unique unranked successor.  Unlike
comma_rank_witness, it deliberately does not impose a zero-rank terminal
case, a nonempty positive-rank row, or an exact predecessor rank.  Those
stronger clauses belong to the legacy exact-rank checker and are not needed
for well-founded termination.\<close>

definition comma_descent_witness ::
  "('a \<Rightarrow> 'a list) \<Rightarrow> 'a set \<Rightarrow>
    ('a \<Rightarrow> nat option) \<Rightarrow> bool" where
  "comma_descent_witness children states rank \<longleftrightarrow>
    (\<forall>q \<in> states.
      set (children q) \<subseteq> states \<and>
      (case rank q of
        None \<Rightarrow> (\<exists>!r. r \<in> set (children q) \<and> rank r = None)
      | Some n \<Rightarrow>
          (\<forall>r \<in> set (children q). \<exists>m<n. rank r = Some m)))"

lemma comma_descent_witness_closed:
  assumes cert: "comma_descent_witness children states rank"
    and state: "q \<in> states"
  shows "set (children q) \<subseteq> states"
  using cert state by (auto simp: comma_descent_witness_def)

lemma comma_descent_witness_ranked_children:
  assumes cert: "comma_descent_witness children states rank"
    and state: "q \<in> states"
    and ranked: "rank q = Some n"
  shows "\<forall>r \<in> set (children q). \<exists>m<n. rank r = Some m"
  using cert state ranked by (auto simp: comma_descent_witness_def)

lemma comma_descent_witness_unranked_child:
  assumes cert: "comma_descent_witness children states rank"
    and state: "q \<in> states"
    and live: "rank q = None"
  shows "\<exists>!r. r \<in> set (children q) \<and> r \<in> states \<and>
    rank r = None"
proof -
  have row: "case rank q of
      None \<Rightarrow> (\<exists>!r. r \<in> set (children q) \<and> rank r = None)
    | Some n \<Rightarrow> (\<forall>r \<in> set (children q). \<exists>m<n. rank r = Some m)"
    using cert state unfolding comma_descent_witness_def by blast
  have unique: "\<exists>!r. r \<in> set (children q) \<and> rank r = None"
    using row live by simp
  have closed: "set (children q) \<subseteq> states"
    using comma_descent_witness_closed[OF cert state] .
  show ?thesis using unique closed by blast
qed

lemma comma_descent_ranked_state_terminates:
  assumes cert: "comma_descent_witness children states rank"
    and state: "q \<in> states"
    and ranked: "rank q = Some n"
  shows "comma_all_branches_terminate children q"
  using state ranked
proof (induction n arbitrary: q rule: less_induct)
  case (less n)
  show ?case
  proof (cases "children q = []")
    case True
    then show ?thesis by (rule comma_all_branches_terminate.terminal)
  next
    case False
    have lower: "\<And>r. r \<in> set (children q) \<Longrightarrow>
        \<exists>k<n. rank r = Some k"
      using comma_descent_witness_ranked_children[OF cert less.prems] by blast
    show ?thesis
    proof (rule comma_all_branches_terminate.branch
        [where children=children and q=q, OF False])
      fix r assume child: "r \<in> set (children q)"
      obtain k where below: "k<n" and rank_r: "rank r = Some k"
        using lower[OF child] by blast
      have state_r: "r \<in> states"
        using comma_descent_witness_closed[OF cert less.prems(1)] child by blast
      show "comma_all_branches_terminate children r"
        using less.IH[OF below state_r rank_r] .
    qed
  qed
qed

definition comma_summary_boundary_children ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   comma_boundary_state \<Rightarrow> comma_boundary_state list option" where
  "comma_summary_boundary_children height terminal q =
    map_option (\<lambda>outcome. case outcome of
       Comma_Landmine_At d \<Rightarrow> []
     | Comma_Fork_At a d \<Rightarrow>
       [(Comma_N,a,(snd (snd q)+d) mod 924),
        (Comma_Z,a,(snd (snd q)+d) mod 924)])
      (comma_fast_total_boundary height terminal q)"

lemma comma_summary_boundary_children_sound:
  assumes checked: "comma_decade_summary_checked height terminal"
    and computed: "comma_summary_boundary_children height terminal q = Some children"
  shows "comma_macro_defined q" "comma_total_children q = children"
proof -
  obtain outcome where macro: "comma_fast_total_boundary height terminal q = Some outcome"
    using computed by (cases "comma_fast_total_boundary height terminal q")
      (auto simp: comma_summary_boundary_children_def)
  have valid: "comma_boundary_valid q"
    using macro by (auto simp: comma_fast_total_boundary_def split: if_splits)
  obtain fuel result where refined:
      "comma_fast_total_boundary height terminal q=Some result"
      "comma_finite_macro fuel q=Some result"
    using comma_fast_total_boundary_refines[OF checked valid] by blast
  show "comma_macro_defined q"
    using refined(2) by (auto simp: comma_macro_defined_def)
  have total: "comma_total_macro q=outcome"
    using comma_fast_total_boundary_correct[OF checked valid] macro by simp
  show "comma_total_children q=children"
    using computed macro total by (cases outcome)
      (simp_all add: comma_summary_boundary_children_def comma_total_children_def)
qed

definition comma_future_descent_row ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
   comma_boundary_state \<Rightarrow> bool" where
  "comma_future_descent_row height terminal rank q =
    (case comma_summary_boundary_children height terminal q of None \<Rightarrow> False
     | Some children \<Rightarrow>
       list_all comma_boundary_valid children \<and>
       (case rank q of
          None \<Rightarrow> list_ex (\<lambda>r. rank r=None \<and>
            list_all (\<lambda>s. rank s=None \<longrightarrow> s=r) children) children
        | Some n \<Rightarrow> list_all (\<lambda>r. case rank r of None \<Rightarrow> False
            | Some m \<Rightarrow> m<n) children))"

definition comma_future_descent_check ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> bool" where
  "comma_future_descent_check height terminal rank =
    list_all (comma_future_descent_row height terminal rank) comma_boundary_states"

definition comma_future_descent_phase_range ::
  "(comma_decade_state \<Rightarrow> nat) \<Rightarrow>
   (comma_decade_state \<Rightarrow> comma_decade_terminal) \<Rightarrow>
   (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
   nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_future_descent_phase_range height terminal rank lo hi =
    list_all (\<lambda>r. list_all (\<lambda>a.
      comma_future_descent_row height terminal rank (Comma_N,a,r) \<and>
      comma_future_descent_row height terminal rank (Comma_Z,a,r)) [2..<10]) [lo..<hi]"

lemma comma_future_descent_phase_range_join:
  assumes "lo\<le>mid" "mid\<le>hi"
  shows "comma_future_descent_phase_range height terminal rank lo hi =
    (comma_future_descent_phase_range height terminal rank lo mid \<and>
     comma_future_descent_phase_range height terminal rank mid hi)"
  using assms by (auto simp: comma_future_descent_phase_range_def list_all_iff)

lemma comma_future_descent_phase_range_full:
  "comma_future_descent_phase_range height terminal rank 0 924 =
    comma_future_descent_check height terminal rank"
  by (auto simp: comma_future_descent_phase_range_def comma_future_descent_check_def
    comma_boundary_states_def list_all_iff)

definition comma_future_structural_witness ::
  "(comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> bool" where
  "comma_future_structural_witness rank =
    ((\<forall>q\<in>set comma_boundary_states. comma_macro_defined q) \<and>
     comma_descent_witness comma_total_children (set comma_boundary_states) rank)"

lemma comma_future_descent_row_sound:
  assumes summary: "comma_decade_summary_checked height terminal"
    and row: "comma_future_descent_row height terminal rank q"
  shows "comma_macro_defined q" and
    "set (comma_total_children q) \<subseteq> set comma_boundary_states \<and>
     (case rank q of
       None \<Rightarrow> (\<exists>!r. r \<in> set (comma_total_children q) \<and> rank r=None)
     | Some n \<Rightarrow> (\<forall>r\<in>set (comma_total_children q). \<exists>m<n. rank r=Some m))"
proof -
  obtain children where children:
      "comma_summary_boundary_children height terminal q=Some children"
    using row by (auto simp: comma_future_descent_row_def split: option.splits)
  show "comma_macro_defined q"
    by (rule comma_summary_boundary_children_sound(1)[OF summary children])
  have equals: "comma_total_children q=children"
    by (rule comma_summary_boundary_children_sound(2)[OF summary children])
  show "set (comma_total_children q) \<subseteq> set comma_boundary_states \<and>
     (case rank q of
       None \<Rightarrow> (\<exists>!r. r \<in> set (comma_total_children q) \<and> rank r=None)
     | Some n \<Rightarrow> (\<forall>r\<in>set (comma_total_children q). \<exists>m<n. rank r=Some m))"
    using row by (auto simp: comma_future_descent_row_def children equals
      list_all_iff list_ex_iff comma_boundary_states_set split: option.splits)
qed

theorem comma_future_descent_check_sound:
  assumes summary: "comma_decade_summary_checked height terminal"
    and checked: "comma_future_descent_check height terminal rank"
  shows "comma_future_structural_witness rank"
proof -
  have rows: "\<And>q. q\<in>set comma_boundary_states \<Longrightarrow>
    comma_future_descent_row height terminal rank q"
    using checked by (auto simp: comma_future_descent_check_def list_all_iff)
  have defined: "\<forall>q\<in>set comma_boundary_states. comma_macro_defined q"
    using comma_future_descent_row_sound(1)[OF summary] rows by blast
  have descent: "comma_descent_witness comma_total_children
      (set comma_boundary_states) rank"
    unfolding comma_descent_witness_def
    using comma_future_descent_row_sound(2)[OF summary] rows by blast
  show ?thesis using defined descent
    by (simp add: comma_future_structural_witness_def)
qed

lemma comma_future_structural_defined:
  assumes "comma_future_structural_witness rank" "comma_boundary_valid q"
  shows "comma_macro_defined q"
proof -
  have "q \<in> set comma_boundary_states"
    using assms(2) by (simp add: comma_boundary_states_set)
  then show ?thesis using assms(1)
    unfolding comma_future_structural_witness_def by blast
qed

lemma comma_future_structural_descent:
  assumes "comma_future_structural_witness rank"
  shows "comma_descent_witness comma_total_children (set comma_boundary_states) rank"
  using assms by (simp add: comma_future_structural_witness_def)

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_summary_boundary_children_sound comma_future_descent_row_sound
      comma_future_descent_check_sound comma_future_structural_defined
      comma_future_structural_descent})
    then () else error "Future structural checker depends on an oracle";
\<close>

end
