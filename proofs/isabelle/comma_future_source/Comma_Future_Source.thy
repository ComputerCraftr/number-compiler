theory Comma_Future_Source
  imports Comma_Future_Structural_Check.Comma_Future_Descent_Lift
    Comma_Source_Uniqueness.Comma_Source_Unique
begin

text \<open>The source-specific prefix is downstream of the generic boundary
 future checker. This owner retains the checked source-20 connection without
 importing its heavy witness into finite rank or cycle checks. Exclusion of
 earlier roots remains a separate admission obligation.\<close>

lemma comma_source20_infinite_from_boundary:
  assumes boundary: "comma_literal_unbounded (comma_boundary_value (Comma_N,2,10) 10)"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=20 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
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

theorem comma_source20_structural_infinite_path:
  assumes checked: "comma_future_structural_witness rank"
    and live: "rank (Comma_N,2,10)=None"
  shows "\<exists>path :: nat \<Rightarrow> nat. path 0=20 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have prefixes: "\<exists>weight\<ge>n. \<exists>target.
      comma_literal_path weight (comma_boundary_value (Comma_N,2,10) 10) target" for n
    by (rule comma_structural_survivor_literal_prefix[OF checked _ live])
      (simp_all add: comma_boundary_valid_def)
  have "comma_literal_unbounded (comma_boundary_value (Comma_N,2,10) 10)"
    using prefixes by (simp add: comma_literal_unbounded_def)
  then show ?thesis by (rule comma_source20_infinite_from_boundary)
qed

lemma comma_source20_first_choice_from_losing:
  assumes right: "\<not>(\<exists>tail :: nat \<Rightarrow> nat. tail 0=20000000000 \<and>
      (\<forall>j. comma_child (tail j) (tail (Suc j))))"
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
  show ?thesis
  proof (rule ccontr)
    assume "path 412987859\<noteq>19999999999"
    then have initial: "path 412987859=20000000000" using alternatives by blast
    have tail_edges: "\<forall>j. comma_child (path (412987859+j))
        (path (412987859+Suc j))"
    proof
      fix j
      show "comma_child (path (412987859+j)) (path (412987859+Suc j))"
        using edges[of "412987859+j"] by (simp only: add_Suc_right)
    qed
    have "\<exists>tail :: nat \<Rightarrow> nat. tail 0=20000000000 \<and>
      (\<forall>j. comma_child (tail j) (tail (Suc j)))"
      by (rule exI[of _ "\<lambda>j. path (412987859+j)"])
        (use initial tail_edges in simp)
    then show False using right by contradiction
  qed
qed

theorem comma_source20_checked_first_choice_unique:
  assumes checked: "comma_future_rank_check rounds rank"
    and loser: "rank (Comma_Z,2,10)=Some n"
    and initial: "path 0=20"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "path 412987859=19999999999"
proof (rule comma_source20_first_choice_from_losing[OF _ initial edges])
  show "\<not>(\<exists>tail :: nat \<Rightarrow> nat. tail 0=20000000000 \<and>
      (\<forall>j. comma_child (tail j) (tail (Suc j))))"
    using comma_checked_loser_no_infinite_literal_path
      [OF checked _ loser, where p=10]
    by (simp add: comma_boundary_valid_def comma_boundary_value_def comma_zero_boundary_def)
qed

theorem comma_source20_structural_first_choice_unique:
  assumes checked: "comma_future_structural_witness rank"
    and loser: "rank (Comma_Z,2,10)=Some n"
    and initial: "path 0=20"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "path 412987859=19999999999"
proof (rule comma_source20_first_choice_from_losing[OF _ initial edges])
  show "\<not>(\<exists>tail :: nat \<Rightarrow> nat. tail 0=20000000000 \<and>
      (\<forall>j. comma_child (tail j) (tail (Suc j))))"
    using comma_structural_loser_no_infinite_literal_path
      [OF checked _ loser, where p=10]
    by (simp add: comma_boundary_valid_def comma_boundary_value_def comma_zero_boundary_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_source20_infinite_from_boundary comma_source20_first_choice_from_losing
      comma_source20_structural_infinite_path comma_source20_structural_first_choice_unique
      comma_source20_checked_first_choice_unique})
    then () else error "Comma source future bridge depends on an oracle";
\<close>
end
