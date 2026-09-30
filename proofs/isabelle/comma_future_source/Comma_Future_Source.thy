theory Comma_Future_Source
  imports Comma_Future_Check.Comma_Future_Infinite_Lift
    Comma_Source_Uniqueness.Comma_Source_Unique
begin

text \<open>The source-specific prefix is downstream of the generic boundary
 future checker. This owner retains the checked source-20 connection without
 importing its heavy witness into finite rank or cycle checks. Exclusion of
 earlier roots remains a separate admission obligation.\<close>

theorem comma_source20_checked_infinite_path:
  assumes cert: "comma_rank_witness comma_total_children (set comma_boundary_states) rank"
    and cycle: "comma_surviving_delta_path rank 314 (Comma_N,2,10) (Comma_N,2,10) 924"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=20 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have boundary: "comma_literal_unbounded (comma_boundary_value (Comma_N,2,10) 10)"
    by (rule comma_checked_cycle_unbounded[OF cert cycle])
      (simp_all add: comma_boundary_valid_def)
  have unbounded: "comma_literal_unbounded 19999999999"
    using boundary by (simp add: comma_boundary_value_def comma_near_boundary_def)
  have edge: "comma_child 19999999918 19999999999"
    by (simp add: comma_source20_first_fork_children)
  have prefix: "comma_literal_path 412987859 20 19999999999"
    using comma_literal_path_snoc[OF
      comma_unique_literal_path_literal[OF comma_source20_to_fork_unique] edge] by simp
  show ?thesis by (rule comma_literal_unbounded_infinite_path
    [OF comma_literal_unbounded_prefix[OF prefix unbounded]])
qed

theorem comma_source20_checked_first_choice_unique:
  assumes checked: "comma_future_rank_check rounds rank"
    and loser: "rank (Comma_Z,2,10) = Some n"
    and initial: "path 0=20"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "path 412987859 = 19999999999"
proof -
  have prefix: "comma_literal_path 412987858 20 (path 412987858)"
    using comma_infinite_literal_prefix[where path=path and n=412987858, OF edges] initial by simp
  have terminal: "path 412987858 = 19999999918"
    by (rule comma_unique_literal_path_endpoint[OF comma_source20_to_fork_unique prefix])
  have alternatives: "path 412987859=19999999999 \<or> path 412987859=20000000000"
    using edges[of 412987858] terminal comma_source20_first_fork_children by simp
  have right: "\<not>(\<exists>tail :: nat \<Rightarrow> nat. tail 0=20000000000 \<and>
      (\<forall>j. comma_child (tail j) (tail (Suc j))))"
    using comma_checked_loser_no_infinite_literal_path
      [OF checked _ loser, where p=10]
    by (simp add: comma_boundary_valid_def comma_boundary_value_def comma_zero_boundary_def)
  show ?thesis
  proof (rule ccontr)
    assume "path 412987859\<noteq>19999999999"
    then have initial: "path 412987859=20000000000" using alternatives by blast
    have "\<exists>tail :: nat \<Rightarrow> nat. tail 0=20000000000 \<and>
      (\<forall>j. comma_child (tail j) (tail (Suc j)))"
      by (rule exI[of _ "\<lambda>j. path (412987859+j)"])
        (use initial edges in simp)
    then show False using right by contradiction
  qed
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_source20_checked_infinite_path
      comma_source20_checked_first_choice_unique})
    then () else error "Comma source future bridge depends on an oracle";
\<close>
end
