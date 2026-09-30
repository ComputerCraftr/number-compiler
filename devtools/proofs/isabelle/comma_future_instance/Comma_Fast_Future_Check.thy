theory Comma_Fast_Future_Check
  imports Comma_Fast_Control.Comma_Fast_Control
    Comma_Total_Macro.Comma_Total_Macro Comma_Cylinder.Comma_Checked_Ranks
begin

text \<open>Future certificates use the same bounded sector control as decade
 totality. The outer bound counts decade crossings, never literal edges.
 A failed computation is rejected, including for candidate rank zero.
 No candidate outcome or Python success flag participates in the checker.\<close>

fun comma_fast_boundary_run ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_finite_outcome option" where
  "comma_fast_boundary_run 0 r source = None"
| "comma_fast_boundary_run (Suc rounds) r source =
    (case comma_fast_round_aux 9 r source of
       Comma_Round_Cross target \<Rightarrow> comma_fast_boundary_run rounds r target
     | Comma_Round_Fork a d \<Rightarrow> Some (Comma_Fork_At a d)
     | Comma_Round_Landmine d \<Rightarrow> Some (Comma_Landmine_At d)
     | Comma_Round_Invalid \<Rightarrow> None)"

lemma comma_fast_boundary_run_sound:
  assumes valid: "comma_round_admitted source"
    and computed: "comma_fast_boundary_run rounds r source = Some outcome"
  shows "\<exists>fuel. comma_finite_run fuel (r mod 924) source = Some outcome"
  using valid computed
proof (induction rounds arbitrary: source outcome)
  case 0
  then show ?case by simp
next
  case (Suc rounds)
  obtain n t event where close: "comma_round_close r source = (n,t,event)"
    by (cases "comma_round_close r source") auto
  have budget: "Suc (9-comma_sector_number source) \<le> 9"
    using Suc.prems(1) by (cases source) auto
  have fast: "comma_fast_round_aux 9 r source = event"
    using comma_fast_round_aux_correct[OF Suc.prems(1) budget, of r] close
    by simp
  show ?case
  proof (cases event)
    case (Comma_Round_Cross target)
    have prefix: "comma_round_prefix_steps (Suc n) r source target"
      by (rule comma_round_close_cross_prefix) (use close Comma_Round_Cross in simp)
    have admitted: "comma_round_admitted target"
      by (rule comma_round_prefix_admitted[OF prefix Suc.prems(1)])
    have tail: "comma_fast_boundary_run rounds r target = Some outcome"
      using Suc.prems(2) fast Comma_Round_Cross by simp
    obtain fuel where run: "comma_finite_run fuel (r mod 924) target = Some outcome"
      using Suc.IH[OF admitted tail] by blast
    have "comma_finite_run (Suc n + fuel) (r mod 924) source = Some outcome"
      using comma_round_prefix_finite_run[OF prefix, of fuel] run by simp
    then show ?thesis by blast
  next
    case (Comma_Round_Fork a d)
    have outcome: "outcome = Comma_Fork_At a d"
      using Suc.prems(2) fast Comma_Round_Fork by simp
    have "comma_finite_run (Suc n) (r mod 924) source = Some outcome"
      by (simp only: outcome; rule comma_round_close_fork_finite_run)
        (use close Comma_Round_Fork in simp)
    then show ?thesis by blast
  next
    case (Comma_Round_Landmine d)
    have outcome: "outcome = Comma_Landmine_At d"
      using Suc.prems(2) fast Comma_Round_Landmine by simp
    have "comma_finite_run (Suc n) (r mod 924) source = Some outcome"
      by (simp only: outcome; rule comma_round_close_landmine_finite_run)
        (use close Comma_Round_Landmine in simp)
    then show ?thesis by blast
  next
    case Comma_Round_Invalid
    then show ?thesis using Suc.prems(2) fast by simp
  qed
qed

definition comma_fast_boundary_macro ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow> comma_finite_outcome option" where
  "comma_fast_boundary_macro rounds q =
    (if comma_boundary_valid q then
      comma_fast_boundary_run rounds (snd (snd q)) (comma_finite_initial q)
     else None)"

lemma comma_fast_boundary_macro_sound:
  assumes computed: "comma_fast_boundary_macro rounds q = Some outcome"
  shows "\<exists>fuel. comma_finite_macro fuel q = Some outcome"
proof -
  obtain kind a r where q: "q = (kind,a,r)" by (cases q) auto
  have valid: "comma_boundary_valid q"
    and run: "comma_fast_boundary_run rounds r (comma_finite_initial q) = Some outcome"
    using computed by (auto simp: comma_fast_boundary_macro_def q split: if_splits)
  have admitted: "comma_round_admitted (comma_finite_initial q)"
    and phase: "r mod 924 = r"
    using valid by (cases kind; auto simp: q comma_boundary_valid_def comma_finite_initial_def)+
  obtain fuel where result: "comma_finite_run fuel r (comma_finite_initial q) = Some outcome"
    using comma_fast_boundary_run_sound[OF admitted run] phase by auto
  have "comma_finite_macro fuel q = Some outcome"
    using result valid by (simp add: comma_finite_macro_def q)
  then show ?thesis by blast
qed

corollary comma_fast_boundary_macro_total:
  assumes "comma_fast_boundary_macro rounds q = Some outcome"
  shows "comma_macro_defined q" "comma_total_macro q = outcome"
proof -
  obtain fuel where run: "comma_finite_macro fuel q = Some outcome"
    using comma_fast_boundary_macro_sound[OF assms] by blast
  show "comma_macro_defined q"
    using run by (auto simp: comma_macro_defined_def)
  show "comma_total_macro q = outcome"
    by (rule comma_total_macro_agrees[OF run])
qed

definition comma_fast_boundary_children ::
  "nat \<Rightarrow> comma_boundary_state \<Rightarrow> comma_boundary_state list option" where
  "comma_fast_boundary_children rounds q =
    map_option (\<lambda>outcome. case outcome of
       Comma_Landmine_At d \<Rightarrow> []
     | Comma_Fork_At a d \<Rightarrow>
       [(Comma_N,a,(snd (snd q)+d) mod 924),
        (Comma_Z,a,(snd (snd q)+d) mod 924)])
      (comma_fast_boundary_macro rounds q)"

lemma comma_fast_boundary_children_sound:
  assumes "comma_fast_boundary_children rounds q = Some children"
  shows "comma_macro_defined q" "comma_total_children q = children"
proof -
  obtain outcome where macro: "comma_fast_boundary_macro rounds q = Some outcome"
    using assms by (cases "comma_fast_boundary_macro rounds q")
      (auto simp: comma_fast_boundary_children_def)
  show "comma_macro_defined q"
    by (rule comma_fast_boundary_macro_total(1)[OF macro])
  have total: "comma_total_macro q = outcome"
    by (rule comma_fast_boundary_macro_total(2)[OF macro])
  show "comma_total_children q = children"
    using assms by (cases outcome)
      (simp_all add: comma_fast_boundary_children_def macro comma_total_children_def total)
qed

text \<open>Each rank is merely supplied data. The checker recomputes complete
 children from fast control, checks closure, and checks all rank inequalities.
 The unranked branch checks existence and uniqueness by executable list tests.\<close>

definition comma_future_rank_row ::
  "nat \<Rightarrow> (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow>
    comma_boundary_state \<Rightarrow> bool" where
  "comma_future_rank_row rounds rank q =
    (case comma_fast_boundary_children rounds q of None \<Rightarrow> False
     | Some children \<Rightarrow>
       list_all comma_boundary_valid children \<and>
       (case rank q of
          None \<Rightarrow> list_ex (\<lambda>r. rank r = None \<and>
            list_all (\<lambda>s. rank s = None \<longrightarrow> s = r) children) children
        | Some n \<Rightarrow>
            if n = 0 then children = []
            else children \<noteq> [] \<and>
              list_all (\<lambda>r. case rank r of None \<Rightarrow> False
                | Some m \<Rightarrow> m<n) children \<and>
              list_ex (\<lambda>r. rank r = Some (n-1)) children))"

definition comma_future_rank_check ::
  "nat \<Rightarrow> (comma_boundary_state \<Rightarrow> nat option) \<Rightarrow> bool" where
  "comma_future_rank_check rounds rank =
    list_all (comma_future_rank_row rounds rank) comma_boundary_states"

lemma comma_future_rank_row_sound:
  assumes row: "comma_future_rank_row rounds rank q"
  shows "comma_macro_defined q"
    and "set (comma_total_children q) \<subseteq> set comma_boundary_states \<and>
      (case rank q of
        None \<Rightarrow> (\<exists>!r. r \<in> set (comma_total_children q) \<and> rank r = None)
      | Some n \<Rightarrow>
          if n = 0 then comma_total_children q = []
          else comma_total_children q \<noteq> [] \<and>
            (\<forall>r \<in> set (comma_total_children q). \<exists>m<n. rank r = Some m) \<and>
            (\<exists>r \<in> set (comma_total_children q). rank r = Some (n-1)))"
proof -
  obtain children where children: "comma_fast_boundary_children rounds q = Some children"
    using row by (auto simp: comma_future_rank_row_def split: option.splits)
  show "comma_macro_defined q"
    by (rule comma_fast_boundary_children_sound(1)[OF children])
  have equals: "comma_total_children q = children"
    by (rule comma_fast_boundary_children_sound(2)[OF children])
  show "set (comma_total_children q) \<subseteq> set comma_boundary_states \<and>
      (case rank q of
        None \<Rightarrow> (\<exists>!r. r \<in> set (comma_total_children q) \<and> rank r = None)
      | Some n \<Rightarrow>
          if n = 0 then comma_total_children q = []
          else comma_total_children q \<noteq> [] \<and>
            (\<forall>r \<in> set (comma_total_children q). \<exists>m<n. rank r = Some m) \<and>
            (\<exists>r \<in> set (comma_total_children q). rank r = Some (n-1)))"
    using row by (auto simp: comma_future_rank_row_def children equals
      list_all_iff list_ex_iff comma_boundary_states_set split: option.splits if_splits)
qed

theorem comma_future_rank_check_sound:
  assumes checked: "comma_future_rank_check rounds rank"
  shows "comma_rank_witness comma_total_children (set comma_boundary_states) rank"
  unfolding comma_rank_witness_def
  apply (rule ballI)
  apply (rule comma_future_rank_row_sound(2)[where rounds=rounds])
  using checked
  by (auto simp: comma_future_rank_check_def list_all_iff)

corollary comma_future_checked_loser_terminates:
  assumes "comma_future_rank_check rounds rank" "comma_boundary_valid q"
    "rank q = Some n"
  shows "comma_all_branches_terminate comma_total_children q"
  by (rule comma_ranked_state_terminates
    [OF comma_future_rank_check_sound[OF assms(1)] _ assms(3)])
    (use assms(2) in \<open>simp add: comma_boundary_states_set\<close>)

corollary comma_future_checked_unique_survivor:
  assumes "comma_future_rank_check rounds rank" "comma_boundary_valid q"
    "rank q = None"
  shows "\<exists>!r. r \<in> set (comma_total_children q) \<and>
    r \<in> set comma_boundary_states \<and> rank r = None"
  by (rule comma_unranked_has_unique_unranked_child
    [OF comma_future_rank_check_sound[OF assms(1)] _ assms(3)])
    (use assms(2) in \<open>simp add: comma_boundary_states_set\<close>)

corollary comma_future_rank_check_defined:
  assumes "comma_future_rank_check rounds rank" "comma_boundary_valid q"
  shows "comma_macro_defined q"
proof -
  have rows: "\<forall>q\<in>set comma_boundary_states. comma_future_rank_row rounds rank q"
    using assms(1) by (simp only: comma_future_rank_check_def list_all_iff)
  have state: "q \<in> set comma_boundary_states"
    using assms(2) by (simp add: comma_boundary_states_set)
  have row: "comma_future_rank_row rounds rank q"
    by (rule bspec[OF rows state])
  show ?thesis by (rule comma_future_rank_row_sound(1)[OF row])
qed

corollary comma_future_checked_other_child_terminates:
  assumes checked: "comma_future_rank_check rounds rank"
    and valid: "comma_boundary_valid q"
    and live: "rank q = None"
    and selected: "winner \<in> set (comma_total_children q)" "rank winner = None"
    and sibling: "other \<in> set (comma_total_children q)" "other \<noteq> winner"
  shows "comma_all_branches_terminate comma_total_children other"
proof -
  have cert: "comma_rank_witness comma_total_children (set comma_boundary_states) rank"
    by (rule comma_future_rank_check_sound[OF checked])
  have state: "q \<in> set comma_boundary_states"
    using valid by (simp add: comma_boundary_states_set)
  have closed: "set (comma_total_children q) \<subseteq> set comma_boundary_states"
    by (rule comma_rank_witness_closed[OF cert state])
  have unique: "\<exists>!r. r \<in> set (comma_total_children q) \<and>
      r \<in> set comma_boundary_states \<and> rank r = None"
    by (rule comma_unranked_has_unique_unranked_child[OF cert state live])
  have other_state: "other \<in> set comma_boundary_states"
    by (rule subsetD[OF closed sibling(1)])
  have winner_state: "winner \<in> set comma_boundary_states"
    by (rule subsetD[OF closed selected(1)])
  let ?P = "\<lambda>r. r \<in> set (comma_total_children q) \<and>
    r \<in> set comma_boundary_states \<and> rank r = None"
  have winner_good: "?P winner" using selected winner_state by simp
  have ranked: "rank other \<noteq> None"
  proof
    assume other_live: "rank other = None"
    have other_good: "?P other" using sibling(1) other_state other_live by simp
    from unique show False
    proof (rule ex1E)
      fix chosen
      assume chosen: "?P chosen" and only: "\<forall>r. ?P r \<longrightarrow> r=chosen"
      have other_eq: "other=chosen"
        by (rule only[rule_format, OF other_good])
      have winner_eq: "winner=chosen"
        by (rule only[rule_format, OF winner_good])
      have "other=winner" by (rule trans[OF other_eq winner_eq[symmetric]])
      then show False using sibling(2) by contradiction
    qed
  qed
  obtain n where rank: "rank other = Some n"
    using ranked by (cases "rank other") auto
  show ?thesis
    by (rule comma_ranked_state_terminates[OF cert other_state rank])
qed

text \<open>No concrete certificate is asserted in this preparation theory.
 In particular, the 14470/314 partition, 314-step cycle, +924 exponent
 transport and positive literal return weight remain separate proof gates.\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_fast_boundary_run_sound comma_fast_boundary_macro_sound
      comma_fast_boundary_macro_total comma_fast_boundary_children_sound
      comma_future_rank_check_sound comma_future_checked_loser_terminates
      comma_future_checked_unique_survivor comma_future_rank_check_defined
      comma_future_checked_other_child_terminates})
    then () else error "Comma future checker depends on an oracle";
\<close>
end
