theory Comma_Semantic_Global_Safety
  imports Comma_Semantic_Global_Root_Bridge
    Comma_Semantic_Future_Path_Results
    Comma_Source_Uniqueness.Comma_Source_Unique
begin

text \<open>
The global source-20 facts are reconstructed from the semantic boundary
provider.  The arithmetic-only unique prefix reaches the first fork; the
checked semantic N/Z states decide which child can have an infinite tail.
All later tail positions use the provider-neutral all-index agreement proof.
\<close>

lemma comma_rtrancl_child_has_literal_path:
  assumes reach: "rtranclp comma_child source target"
  shows "\<exists>n. comma_literal_path n source target"
  using reach
proof (induction rule: rtranclp_induct)
  case base
  then show ?case
    by (intro exI[of _ 0]) (simp add: comma_literal_path.zero)
next
  case (step middle target)
  then show ?case
    by (metis comma_literal_path_snoc)
qed

lemma comma_positive_source_has_literal_root_path:
  assumes positive: "0 < source"
  obtains root weight where "root \<in> comma_decimal_roots"
    "comma_literal_path weight root source"
proof -
  obtain root where root: "root \<in> comma_decimal_roots"
    and reach: "rtranclp comma_child root source"
    using comma_every_positive_has_decimal_root[OF positive] by blast
  obtain weight where path: "comma_literal_path weight root source"
    using comma_rtrancl_child_has_literal_path[OF reach] by blast
  show thesis by (rule that[OF root path])
qed

lemma comma_literal_path_endpoint_ge:
  assumes path: "comma_literal_path weight source endpoint"
  shows "source \<le> endpoint"
  using path
proof (induction rule: comma_literal_path.induct)
  case zero
  then show ?case by simp
next
  case (step source next weight endpoint)
  have growth: "source < next"
    by (rule comma_child_strict_growth[OF step.hyps(1)])
  show ?case using growth step.IH by arith
qed

lemma comma_semantic_source20_near_boundary_unbounded:
  "comma_literal_unbounded 19999999999"
proof -
  obtain stream where stream_path:
      "comma_semantic_infinite_path comma_boundary_value
        (Comma_N,2,10) 10 stream"
    using comma_semantic_concrete_source20_infinite_path by blast
  have boundary_value:
    "comma_boundary_value (Comma_N,2,10) 10 = 19999999999"
    by (simp add: comma_boundary_value_def comma_near_boundary_def)
  have stream_start: "stream 0 = 19999999999"
    using stream_path boundary_value
    by (simp add: comma_semantic_infinite_path_def)
  have stream_edges: "comma_child (stream j) (stream (Suc j))" for j
    using stream_path by (simp add: comma_semantic_infinite_path_def)
  show ?thesis
    by (rule comma_literal_infinite_path_unbounded[OF stream_start stream_edges])
qed

theorem comma_semantic_source20_global_infinite_literal_path:
  "\<exists>path :: nat \<Rightarrow> nat. path 0=20 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have near_edge: "comma_child 19999999918 19999999999"
    using comma_source20_first_fork_children by simp
  have prefix:
    "comma_literal_path 412987859 20 19999999999"
    by (rule comma_literal_path_snoc
      [OF comma_unique_literal_path_literal[OF comma_source20_to_fork_unique]
        near_edge])
  have source_unbounded: "comma_literal_unbounded 20"
    by (rule comma_literal_unbounded_prefix
      [OF prefix comma_semantic_source20_near_boundary_unbounded])
  show ?thesis
    by (rule comma_literal_unbounded_infinite_path[OF source_unbounded])
qed

lemma comma_semantic_source20_zero_child_no_infinite_literal_path:
  "\<not>(\<exists>path :: nat \<Rightarrow> nat. path 0=20000000000 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
proof
  assume exists_path:
    "\<exists>path :: nat \<Rightarrow> nat. path 0=20000000000 \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
  then obtain path where initial: "path 0=20000000000"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
    by blast
  have boundary_value:
    "comma_boundary_value (Comma_Z,2,10) 10 = 20000000000"
    by (simp add: comma_boundary_value_def comma_zero_boundary_def)
  have semantic_path:
    "comma_semantic_infinite_path comma_boundary_value
      (Comma_Z,2,10) 10 path"
    using initial edges boundary_value
    by (simp add: comma_semantic_infinite_path_def)
  show False
    using comma_semantic_concrete_source20_z_no_infinite_path semantic_path
    by blast
qed

theorem comma_semantic_source20_global_first_choice_unique:
  fixes path :: "nat \<Rightarrow> nat"
  assumes initial: "path 0=20"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "path 412987859=19999999999"
proof -
  have prefix: "comma_literal_path 412987858 20 (path 412987858)"
    using comma_infinite_literal_prefix
      [where path=path and n=412987858, OF edges] initial by simp
  have fork_value: "path 412987858=19999999918"
    by (rule comma_unique_literal_path_endpoint
      [OF comma_source20_to_fork_unique prefix])
  have alternatives:
    "path 412987859=19999999999 \<or> path 412987859=20000000000"
    using edges[of 412987858] fork_value comma_source20_first_fork_children
    by blast
  show ?thesis
  proof (rule ccontr)
    assume not_near: "path 412987859 \<noteq> 19999999999"
    have zero: "path 412987859=20000000000"
      using alternatives not_near by blast
    let ?tail = "\<lambda>j. path (412987859+j)"
    have tail_start: "?tail 0=20000000000"
      using zero by simp
    have tail_edges: "comma_child (?tail j) (?tail (Suc j))" for j
      using edges[of "412987859+j"] by simp
    have zero_infinite:
      "\<exists>tail :: nat \<Rightarrow> nat. tail 0=20000000000 \<and>
        (\<forall>j. comma_child (tail j) (tail (Suc j)))"
      by (rule exI[of _ "?tail"]) (use tail_start tail_edges in simp)
    show False
      using zero_infinite
        comma_semantic_source20_zero_child_no_infinite_literal_path
      by blast
  qed
qed

theorem comma_semantic_source20_global_infinite_paths_agree:
  fixes left right :: "nat \<Rightarrow> nat"
  assumes left_initial: "left 0=20"
    and left_edges: "\<And>j. comma_child (left j) (left (Suc j))"
    and right_initial: "right 0=20"
    and right_edges: "\<And>j. comma_child (right j) (right (Suc j))"
  shows "\<forall>n. left n=right n"
proof -
  have left_fork: "left 412987859=19999999999"
    by (rule comma_semantic_source20_global_first_choice_unique
      [OF left_initial left_edges])
  have right_fork: "right 412987859=19999999999"
    by (rule comma_semantic_source20_global_first_choice_unique
      [OF right_initial right_edges])
  have boundary_value:
    "comma_boundary_value (Comma_N,2,10) 10 = 19999999999"
    by (simp add: comma_boundary_value_def comma_near_boundary_def)
  have boundary_valid: "comma_boundary_valid (Comma_N,2,10)"
    by (simp add: comma_boundary_valid_def)
  have boundary_exponent: "5 \<le> (10::nat)" by simp
  have boundary_phase: "10 mod 924=snd (snd (Comma_N,2,10))" by simp
  let ?left_tail = "\<lambda>j. left (412987859+j)"
  let ?right_tail = "\<lambda>j. right (412987859+j)"
  have left_tail_start: "?left_tail 0=19999999999"
    using left_fork by simp
  have right_tail_start: "?right_tail 0=19999999999"
    using right_fork by simp
  have left_tail_edges:
    "comma_child (?left_tail j) (?left_tail (Suc j))" for j
    using left_edges[of "412987859+j"] by simp
  have right_tail_edges:
    "comma_child (?right_tail j) (?right_tail (Suc j))" for j
    using right_edges[of "412987859+j"] by simp
  have left_tail_path:
    "comma_semantic_infinite_path comma_boundary_value
      (Comma_N,2,10) 10 ?left_tail"
    using left_tail_start left_tail_edges boundary_value
    by (simp add: comma_semantic_infinite_path_def)
  have right_tail_path:
    "comma_semantic_infinite_path comma_boundary_value
      (Comma_N,2,10) 10 ?right_tail"
    using right_tail_start right_tail_edges boundary_value
    by (simp add: comma_semantic_infinite_path_def)
  have tails_agree: "\<forall>j. ?left_tail j=?right_tail j"
    using comma_semantic_concrete_future_paths_agree boundary_valid
      boundary_exponent boundary_phase left_tail_path right_tail_path
    by blast
  show ?thesis
  proof (intro allI)
    fix n
    show "left n=right n"
    proof (cases "n < 412987859")
      case True
      have n_bound: "n \<le> 412987858" using True by arith
      obtain middle where unique_prefix:
          "comma_unique_literal_path n 20 middle"
        using comma_unique_literal_path_prefix
          [OF comma_source20_to_fork_unique n_bound] by blast
      have left_prefix: "comma_literal_path n 20 (left n)"
        using comma_infinite_literal_prefix[where path=left and n=n,
          OF left_edges] left_initial by simp
      have right_prefix: "comma_literal_path n 20 (right n)"
        using comma_infinite_literal_prefix[where path=right and n=n,
          OF right_edges] right_initial by simp
      have left_eq: "left n=middle"
        by (rule comma_unique_literal_path_endpoint[OF unique_prefix left_prefix])
      have right_eq: "right n=middle"
        by (rule comma_unique_literal_path_endpoint[OF unique_prefix right_prefix])
      show ?thesis using left_eq right_eq by simp
    next
      case False
      have after_fork: "412987859 \<le> n" using False by simp
      let ?j = "n - 412987859"
      have split: "n=412987859+?j" using after_fork by arith
      have tail_eq: "?left_tail ?j=?right_tail ?j"
        using tails_agree by blast
      show ?thesis using tail_eq split by simp
    qed
  qed
qed

theorem comma_semantic_positive_infinite_start_at_least20:
  fixes source :: nat
  assumes positive: "0 < source"
    and infinite: "\<exists>path :: nat \<Rightarrow> nat. path 0=source \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
  shows "20 \<le> source"
proof -
  obtain path where initial: "path 0=source"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
    using infinite by blast
  obtain root weight where root: "root \<in> comma_decimal_roots"
    and root_prefix: "comma_literal_path weight root source"
    using comma_positive_source_has_literal_root_path[OF positive] by blast
  have source_unbounded: "comma_literal_unbounded source"
    by (rule comma_literal_infinite_path_unbounded[OF initial edges])
  have root_unbounded: "comma_literal_unbounded root"
    by (rule comma_literal_unbounded_prefix[OF root_prefix source_unbounded])
  have root_infinite:
    "\<exists>root_path :: nat \<Rightarrow> nat. root_path 0=root \<and>
      (\<forall>j. comma_child (root_path j) (root_path (Suc j)))"
    by (rule comma_literal_unbounded_infinite_path[OF root_unbounded])
  have root_is20: "root=20"
    by (rule comma_semantic_unique_infinite_decimal_root[OF root root_infinite])
  have root_le_source: "root \<le> source"
    by (rule comma_literal_path_endpoint_ge[OF root_prefix])
  show ?thesis using root_is20 root_le_source by simp
qed

theorem comma_semantic_decimal_root_infinite_iff_20:
  assumes root: "root \<in> comma_decimal_roots"
  shows "(\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))) \<longleftrightarrow> root=20"
proof
  assume infinite:
    "\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
  show "root=20"
    by (rule comma_semantic_unique_infinite_decimal_root[OF root infinite])
next
  assume "root=20"
  then show "\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
    using comma_semantic_source20_global_infinite_literal_path by simp
qed

theorem comma_semantic_global_release_safety:
  "(\<forall>root\<in>comma_decimal_roots.
      ((\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
        (\<forall>j. comma_child (path j) (path (Suc j)))) \<longleftrightarrow> root=20)) \<and>
   (\<forall>path :: nat \<Rightarrow> nat. path 0=20 \<longrightarrow>
      (\<forall>j. comma_child (path j) (path (Suc j))) \<longrightarrow>
      path 412987859=19999999999) \<and>
   (\<forall>left right :: nat \<Rightarrow> nat. left 0=20 \<longrightarrow>
      (\<forall>j. comma_child (left j) (left (Suc j))) \<longrightarrow>
      right 0=20 \<longrightarrow>
      (\<forall>j. comma_child (right j) (right (Suc j))) \<longrightarrow>
      (\<forall>n. left n=right n)) \<and>
   (\<forall>source. 0<source \<longrightarrow>
      (\<exists>path :: nat \<Rightarrow> nat. path 0=source \<and>
        (\<forall>j. comma_child (path j) (path (Suc j)))) \<longrightarrow>
      20 \<le> source)"
proof (intro conjI)
  show "\<forall>root\<in>comma_decimal_roots.
      ((\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
        (\<forall>j. comma_child (path j) (path (Suc j)))) \<longleftrightarrow> root=20)"
    using comma_semantic_decimal_root_infinite_iff_20 by blast
  show "\<forall>path :: nat \<Rightarrow> nat. path 0=20 \<longrightarrow>
      (\<forall>j. comma_child (path j) (path (Suc j))) \<longrightarrow>
      path 412987859=19999999999"
    using comma_semantic_source20_global_first_choice_unique by blast
  show "\<forall>left right :: nat \<Rightarrow> nat. left 0=20 \<longrightarrow>
      (\<forall>j. comma_child (left j) (left (Suc j))) \<longrightarrow>
      right 0=20 \<longrightarrow>
      (\<forall>j. comma_child (right j) (right (Suc j))) \<longrightarrow>
      (\<forall>n. left n=right n)"
    using comma_semantic_source20_global_infinite_paths_agree by blast
  show "\<forall>source. 0<source \<longrightarrow>
      (\<exists>path :: nat \<Rightarrow> nat. path 0=source \<and>
        (\<forall>j. comma_child (path j) (path (Suc j)))) \<longrightarrow>
      20 \<le> source"
    using comma_semantic_positive_infinite_start_at_least20 by blast
qed

ML \<open>
  val endpoints = @{thms comma_semantic_global_release_safety
    comma_semantic_source20_global_infinite_literal_path
    comma_semantic_source20_global_first_choice_unique
    comma_semantic_source20_global_infinite_paths_agree}
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "semantic global comma release endpoints"
    ["comma_semantic_future_candidate_provider_check_checked",
     "comma_semantic_concrete_future_rank_check",
     "comma_semantic_concrete_boundary_strong_occurrence_bridge",
     "comma_semantic_graph_valid_checked",
     "comma_semantic_graph_root_binding_exact",
     "comma_semantic_graph_root_binding_exists",
     "comma_semantic_graph_root_action_exact",
     "comma_semantic_graph_action_power_refines",
     "comma_semantic_b1_action_power_refines_orbit",
     "comma_semantic_phase_continue24_image_certificate_native",
     "comma_semantic_phase_continue24_image_checked",
     "comma_semantic_phase_class_B32_exact_output_checked",
     "comma_semantic_phase_class_B32_exact_output",
     "comma_crt_rank_relations_sound",
     "comma_semantic_graph_stop242_from_stop_within",
     "comma_semantic_graph_stop_within_exact_action",
     "comma_semantic_graph_stop_within_summary",
     "comma_semantic_graph_root_control_transport",
     "comma_semantic_graph_stop_from_exact_summary",
     "comma_semantic_b1_action_power_b32_stop242",
     "comma_semantic_graph_weighted_power_exact",
     "comma_semantic_decade_summary_provider_exact",
     "comma_semantic_graph_b32_stop242_checked",
     "comma_semantic_p5_entry_future_open_checked",
     "comma_semantic_p5_entry_infinite_imp_open",
     "comma_semantic_unique_infinite_decimal_root",
     "comma_semantic_concrete_source20_infinite_path",
     "comma_semantic_concrete_source20_z_no_infinite_path",
     "comma_semantic_concrete_future_paths_agree",
     "comma_every_positive_has_decimal_root",
     "comma_source20_to_fork_unique"] endpoints
\<close>

end
