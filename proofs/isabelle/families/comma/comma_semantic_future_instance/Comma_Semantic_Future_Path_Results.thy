theory Comma_Semantic_Future_Path_Results
  imports Comma_Semantic_Future_Candidate_Provider_Closure
begin

lemma comma_semantic_concrete_future_paths_agree_if_provider_checked:
  assumes provider_check: "comma_semantic_future_candidate_provider_check"
  shows "\<forall>q p left right. comma_boundary_valid q \<longrightarrow>
    5 \<le> p \<longrightarrow> p mod 924 = snd (snd q) \<longrightarrow>
    comma_semantic_infinite_path comma_boundary_value q p left \<longrightarrow>
    comma_semantic_infinite_path comma_boundary_value q p right \<longrightarrow>
    (\<forall>n. left n = right n)"
proof -
  have rank_check:
    "comma_semantic_rank_check comma_boundary_valid
      comma_semantic_concrete_future_rank
      (comma_semantic_boundary_children comma_semantic_decade_summary)
      (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
    by (rule comma_semantic_future_provider_check_lifts_rank[OF provider_check])
  show ?thesis
    by (rule comma_semantic_infinite_paths_agree
      [OF comma_semantic_concrete_boundary_strong_occurrence_bridge rank_check])
qed

lemma comma_semantic_concrete_source20_infinite_path_if_provider_checked:
  assumes provider_check: "comma_semantic_future_candidate_provider_check"
  shows "\<exists>stream. comma_semantic_infinite_path comma_boundary_value
    (Comma_N,2,10) 10 stream"
proof -
  have rank_check:
    "comma_semantic_rank_check comma_boundary_valid
      comma_semantic_concrete_future_rank
      (comma_semantic_boundary_children comma_semantic_decade_summary)
      (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
    by (rule comma_semantic_future_provider_check_lifts_rank[OF provider_check])
  have source_valid: "comma_boundary_valid (Comma_N,2,10)"
    by (simp add: comma_boundary_valid_def)
  have phase_match: "10 mod 924 = snd (snd (Comma_N,2,10))"
    by simp
  show ?thesis
  proof (rule comma_semantic_unranked_state_has_infinite_path
      [where q="(Comma_N,2,10)" and p=10,
       OF comma_semantic_concrete_boundary_occurrence_bridge rank_check])
    show "comma_boundary_valid (Comma_N,2,10)" by (rule source_valid)
    show "5 \<le> 10" by simp
    show "10 mod 924 = snd (snd (Comma_N,2,10))" by (rule phase_match)
    show "comma_semantic_concrete_future_rank (Comma_N,2,10) = None"
      by (rule comma_semantic_concrete_source20_unranked)
  qed
qed

theorem comma_semantic_concrete_source20_infinite_path:
  "\<exists>stream. comma_semantic_infinite_path comma_boundary_value
    (Comma_N,2,10) 10 stream"
  by (rule comma_semantic_concrete_source20_infinite_path_if_provider_checked
      [OF comma_semantic_future_candidate_provider_check_checked])

theorem comma_semantic_concrete_future_paths_agree:
  "\<forall>q p left right. comma_boundary_valid q \<longrightarrow>
    5 \<le> p \<longrightarrow> p mod 924 = snd (snd q) \<longrightarrow>
    comma_semantic_infinite_path comma_boundary_value q p left \<longrightarrow>
    comma_semantic_infinite_path comma_boundary_value q p right \<longrightarrow>
    (\<forall>n. left n = right n)"
  by (rule comma_semantic_concrete_future_paths_agree_if_provider_checked
      [OF comma_semantic_future_candidate_provider_check_checked])

lemma comma_semantic_concrete_source20_path_has_unique_unranked_child_if_provider_checked:
  assumes provider_check: "comma_semantic_future_candidate_provider_check"
    and path: "comma_semantic_infinite_path comma_boundary_value
      (Comma_N,2,10) 10 stream"
  obtains control endpoint weight child tail where
    "comma_semantic_boundary_control_step comma_semantic_decade_summary
      (Comma_N,2,10) = Some control"
    "comma_literal_path weight
      (comma_boundary_value (Comma_N,2,10) 10) endpoint"
    "child \<in> set (comma_semantic_boundary_children comma_semantic_decade_summary
      (Comma_N,2,10) control)"
    "stream (Suc weight) =
      comma_boundary_value child
        (10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
          (Comma_N,2,10) control)"
    "comma_boundary_valid child"
    "5 \<le> 10 + comma_semantic_boundary_exponent_delta
      comma_semantic_decade_summary (Comma_N,2,10) control"
    "(10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
      (Comma_N,2,10) control) mod 924 = snd (snd child)"
    "comma_semantic_infinite_path comma_boundary_value child
      (10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
        (Comma_N,2,10) control) tail"
    "comma_semantic_concrete_future_rank (Comma_N,2,10) = None"
    "comma_semantic_concrete_future_rank child = None"
    "\<forall>other\<in>set (comma_semantic_boundary_children comma_semantic_decade_summary
      (Comma_N,2,10) control).
        other \<noteq> child \<longrightarrow>
        comma_semantic_concrete_future_rank other \<noteq> None"
proof -
  have rank_check:
    "comma_semantic_rank_check comma_boundary_valid
      comma_semantic_concrete_future_rank
      (comma_semantic_boundary_children comma_semantic_decade_summary)
      (comma_semantic_boundary_control_step comma_semantic_decade_summary)"
    by (rule comma_semantic_future_provider_check_lifts_rank[OF provider_check])
  have source_valid: "comma_boundary_valid (Comma_N,2,10)"
    by (simp add: comma_boundary_valid_def)
  have phase_match: "10 mod 924 = snd (snd (Comma_N,2,10))"
    by simp
  show thesis
    by (rule comma_semantic_infinite_path_forces_unique_unranked_child
      [where q="(Comma_N,2,10)" and p=10,
       OF comma_semantic_concrete_boundary_occurrence_bridge rank_check
         source_valid])
      (use path phase_match in simp_all;
       simp_all add: comma_semantic_concrete_source20_unranked)
qed

theorem comma_semantic_concrete_source20_path_has_unique_unranked_child:
  assumes path: "comma_semantic_infinite_path comma_boundary_value
      (Comma_N,2,10) 10 stream"
  obtains control endpoint weight child tail where
    "comma_semantic_boundary_control_step comma_semantic_decade_summary
      (Comma_N,2,10) = Some control"
    "comma_literal_path weight
      (comma_boundary_value (Comma_N,2,10) 10) endpoint"
    "child \<in> set (comma_semantic_boundary_children comma_semantic_decade_summary
      (Comma_N,2,10) control)"
    "stream (Suc weight) =
      comma_boundary_value child
        (10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
          (Comma_N,2,10) control)"
    "comma_boundary_valid child"
    "5 \<le> 10 + comma_semantic_boundary_exponent_delta
      comma_semantic_decade_summary (Comma_N,2,10) control"
    "(10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
      (Comma_N,2,10) control) mod 924 = snd (snd child)"
    "comma_semantic_infinite_path comma_boundary_value child
      (10 + comma_semantic_boundary_exponent_delta comma_semantic_decade_summary
        (Comma_N,2,10) control) tail"
    "comma_semantic_concrete_future_rank (Comma_N,2,10) = None"
    "comma_semantic_concrete_future_rank child = None"
    "\<forall>other\<in>set (comma_semantic_boundary_children comma_semantic_decade_summary
      (Comma_N,2,10) control).
        other \<noteq> child \<longrightarrow>
        comma_semantic_concrete_future_rank other \<noteq> None"
  using comma_semantic_concrete_source20_path_has_unique_unranked_child_if_provider_checked
    [OF comma_semantic_future_candidate_provider_check_checked path] .

theorem comma_semantic_concrete_source20_z_no_infinite_path:
  "\<not> comma_semantic_infinite_path comma_boundary_value
    (Comma_Z,2,10) 10 stream"
proof -
  have state_valid: "comma_boundary_valid (Comma_Z,2,10)"
    by (simp add: comma_boundary_valid_def)
  have exponent: "5 \<le> 10" by simp
  have phase_match: "10 mod 924 = snd (snd (Comma_Z,2,10))" by simp
  obtain k where ranked:
      "comma_semantic_concrete_future_rank (Comma_Z,2,10) = Some k"
    using comma_semantic_concrete_source20_z_ranked by blast
  show ?thesis
    by (rule comma_semantic_ranked_state_no_infinite_path
      [OF comma_semantic_concrete_boundary_occurrence_bridge
        comma_semantic_concrete_future_rank_check state_valid exponent
        phase_match ranked])
qed

ML \<open>
  val checked = @{thms
    comma_semantic_future_candidate_class_table_checked
    comma_semantic_future_candidate_provider_check_checked
    comma_semantic_future_candidate_class_rank_check
    comma_semantic_future_provider_check_lifts_rank
    comma_semantic_concrete_future_rank_check
    comma_semantic_concrete_source20_unranked
    comma_semantic_concrete_source20_z_ranked_exact
    comma_semantic_concrete_future_paths_agree_if_provider_checked
    comma_semantic_concrete_source20_infinite_path_if_provider_checked
    comma_semantic_concrete_source20_path_has_unique_unranked_child_if_provider_checked
    comma_semantic_concrete_future_paths_agree
    comma_semantic_concrete_source20_infinite_path
    comma_semantic_concrete_source20_path_has_unique_unranked_child
    comma_semantic_concrete_source20_z_no_infinite_path
    comma_semantic_boundary_step_decisive_round};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "semantic FutureCID candidate checker and path lift" checked;
\<close>

end
