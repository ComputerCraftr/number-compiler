theory Comma_Global_Future_Safety
  imports Comma_Future_Checked_Instance.Comma_Future_Checked_Instance
    Comma_Future_Source.Comma_Future_Source
begin

text \<open>
This theory discharges the source-20 infinite-path and first-fork obligations
from the concrete checked boundary instance.  The source-20 claims below have
no certificate or checker assumptions in their exported statements.

The finite checker still uses 28 rounds as an evaluation bound for each
boundary macro.  That is part of the kernel-checked certificate computation,
not an assumption of these theorems.  This theory does not establish that 20
is the least starting integer with an infinite path, and it does not remove
production forest admission or the existing semantic finite-macro interface.
\<close>

lemma comma_future_concrete_rank_check:
  "comma_future_rank_check 28 comma_rank_candidate"
  using comma_future_instance_checked
  unfolding comma_future_instance_check_def by blast

lemma comma_future_concrete_zero_child_rank:
  "comma_rank_candidate (Comma_Z,2,10) = Some 7"
  by code_simp

lemma comma_future_concrete_near_child_unranked:
  "comma_rank_candidate (Comma_N,2,10) = None"
  using comma_future_instance_checked
  unfolding comma_future_instance_check_def by blast

lemma comma_future_concrete_rank_bound:
  assumes "q \<in> set comma_boundary_states"
    and "comma_rank_candidate q = Some n"
  shows "n \<le> 136"
  using comma_future_instance_rank_maximum(1)[OF comma_future_instance_checked]
    assms by blast

lemma comma_future_concrete_losing_fixed_point:
  "comma_losing_levels comma_total_children (set comma_boundary_states) 136 =
    {q \<in> set comma_boundary_states. comma_rank_candidate q \<noteq> None}"
  by (rule comma_future_instance_exact_losing_level[OF comma_future_instance_checked])

lemma comma_future_concrete_losing_stable:
  "comma_losing_levels comma_total_children (set comma_boundary_states) 137 =
    comma_losing_levels comma_total_children (set comma_boundary_states) 136"
proof (rule comma_rank_witness_stable[OF comma_future_concrete_rank_checked])
  fix q n
  assume "q \<in> set comma_boundary_states"
    "comma_rank_candidate q = Some n"
  then show "n \<le> 136" by (rule comma_future_concrete_rank_bound)
qed

lemma comma_future_global_ranked_boundary_no_infinite_literal_path:
  assumes valid: "comma_boundary_valid q"
    and ranked: "comma_rank_candidate q = Some n"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat.
    path 0 = comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  by (rule comma_checked_loser_no_infinite_literal_path
      [OF comma_future_concrete_rank_check valid ranked exponent phase])

lemma comma_source20_zero_child_has_no_infinite_literal_path:
  "\<not>(\<exists>path :: nat \<Rightarrow> nat.
    path 0 = 20000000000 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have valid: "comma_boundary_valid (Comma_Z,2,10)"
    by (simp add: comma_boundary_valid_def)
  have no_path: "\<not>(\<exists>path :: nat \<Rightarrow> nat.
      path 0 = comma_boundary_value (Comma_Z,2,10) 10 \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
    by (rule comma_future_global_ranked_boundary_no_infinite_literal_path
        [OF valid comma_future_concrete_zero_child_rank]) simp_all
  show ?thesis using no_path
    by (simp add: comma_boundary_value_def comma_zero_boundary_def)
qed

lemma comma_source20_near_child_has_infinite_literal_path:
  "\<exists>path :: nat \<Rightarrow> nat.
    path 0 = 19999999999 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have path: "\<exists>path :: nat \<Rightarrow> nat.
      path 0 = comma_boundary_value (Comma_N,2,10) 10 \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
    by (rule comma_checked_cycle_infinite_literal_path
        [OF comma_future_concrete_rank_checked comma_future_concrete_cycle_checked])
      (simp_all add: comma_boundary_valid_def)
  show ?thesis using path
    by (simp add: comma_boundary_value_def comma_near_boundary_def)
qed

theorem comma_source20_global_infinite_literal_path:
  "\<exists>path :: nat \<Rightarrow> nat. path 0 = 20 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  by (rule comma_source20_checked_infinite_path
      [OF comma_future_concrete_rank_checked comma_future_concrete_cycle_checked])

theorem comma_source20_global_first_choice_unique:
  assumes initial: "path 0 = 20"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "path 412987859 = 19999999999"
  by (rule comma_source20_checked_first_choice_unique
      [OF comma_future_concrete_rank_check comma_future_concrete_zero_child_rank
        initial edges])

theorem comma_source20_global_future_safety:
  "(\<exists>path :: nat \<Rightarrow> nat. path 0 = 20 \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))) \<and>
   (\<forall>path :: nat \<Rightarrow> nat.
      path 0 = 20 \<longrightarrow>
      (\<forall>j. comma_child (path j) (path (Suc j))) \<longrightarrow>
      path 412987859 = 19999999999)"
proof
  show "\<exists>path :: nat \<Rightarrow> nat. path 0 = 20 \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
    by (rule comma_source20_global_infinite_literal_path)
  show "\<forall>path :: nat \<Rightarrow> nat.
      path 0 = 20 \<longrightarrow>
      (\<forall>j. comma_child (path j) (path (Suc j))) \<longrightarrow>
      path 412987859 = 19999999999"
  proof (intro allI impI)
    fix path :: "nat \<Rightarrow> nat"
    assume initial: "path 0 = 20"
      and edges: "\<forall>j. comma_child (path j) (path (Suc j))"
    show "path 412987859 = 19999999999"
      by (rule comma_source20_global_first_choice_unique[OF initial])
        (use edges in blast)
  qed
qed

ML \<open>
  val checked = @{thms comma_future_concrete_rank_check
    comma_future_concrete_zero_child_rank
    comma_future_concrete_near_child_unranked
    comma_future_concrete_rank_bound
    comma_future_concrete_losing_fixed_point
    comma_future_concrete_losing_stable
    comma_future_global_ranked_boundary_no_infinite_literal_path
    comma_source20_zero_child_has_no_infinite_literal_path
    comma_source20_near_child_has_infinite_literal_path
    comma_source20_global_infinite_literal_path
    comma_source20_global_first_choice_unique
    comma_source20_global_future_safety}
  val _ = if null (Thm_Deps.all_oracles checked)
    then () else error "Global comma future-safety theorem depends on an oracle"
  val closed = @{thm comma_source20_global_future_safety}
  val _ = if null (Thm.prems_of closed)
    then () else error "Source-20 global future-safety theorem has hidden premises"
\<close>

end
