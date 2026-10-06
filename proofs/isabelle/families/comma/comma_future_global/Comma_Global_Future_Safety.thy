theory Comma_Global_Future_Safety
  imports Comma_Native_Future_Instance.Comma_Native_Future_Instance
    Comma_Native_Boundary.Comma_Native_Path_Uniqueness
begin

text \<open>The public source-20 result is now derived from the checked native
B32 transition and its executable rank-measure admission. The rank rows are
untrusted numerical witnesses; branch outcomes and complete child sets come
only from the native action. The source prelude is the independently checked
literal unique prefix to the first fork.\<close>

lemma comma_future_global_ranked_boundary_no_infinite_literal_path:
  assumes valid: "comma_boundary_valid q"
    and ranked: "comma_native_rank_measure q=Some n"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat.
    path 0=comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))) )"
proof
  assume exists_path: "\<exists>path :: nat \<Rightarrow> nat.
    path 0=comma_boundary_value q p \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  then obtain path where initial: "path 0=comma_boundary_value q p"
    and edges: "\<forall>j. comma_child (path j) (path (Suc j))" by blast
  have native_path: "comma_native_infinite_literal_path
      (comma_boundary_value q p) path"
    using initial edges by (simp add: comma_native_infinite_literal_path_def)
  show False using comma_native_ranked_boundary_no_infinite_path
      [OF valid exponent phase ranked] native_path by contradiction
qed

corollary comma_future_global_infinite_path_follows_unique_unranked_child:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5\<le>p"
    and phase: "p mod 924=snd (snd q)"
    and path: "\<exists>stream :: nat \<Rightarrow> nat.
      stream 0=comma_boundary_value q p \<and>
      (\<forall>j. comma_child (stream j) (stream (Suc j)))"
  obtains source_stream a d endpoint weight child tail where
    "source_stream 0=comma_boundary_value q p"
    "\<forall>j. comma_child (source_stream j) (source_stream (Suc j))"
    "comma_native_B32_boundary_step q=Some (Comma_Fork_At a d)"
    "comma_unique_literal_path weight (comma_boundary_value q p) endpoint"
    "child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
    "source_stream (Suc weight)=comma_boundary_value child (p+d)"
    "comma_boundary_valid child"
    "5\<le>p+d"
    "(p+d) mod 924=snd (snd child)"
    "comma_native_infinite_literal_path (comma_boundary_value child (p+d)) tail"
    "comma_native_rank_measure q=None"
    "comma_native_rank_measure child=None"
    "\<forall>other\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
      other\<noteq>child \<longrightarrow> comma_native_rank_measure other\<noteq>None"
proof -
  obtain source_stream :: "nat \<Rightarrow> nat" where initial:
      "source_stream 0=comma_boundary_value q p"
    and edges: "\<forall>j. comma_child (source_stream j) (source_stream (Suc j))"
    using path by blast
  have native_path: "comma_native_infinite_literal_path
      (comma_boundary_value q p) source_stream"
    using initial edges by (simp add: comma_native_infinite_literal_path_def)
  obtain a d endpoint weight child tail where step:
      "comma_native_B32_boundary_step q=Some (Comma_Fork_At a d)"
    and occurrence:
      "comma_unique_literal_path weight (comma_boundary_value q p) endpoint"
    and member:
      "child\<in>set (comma_native_boundary_children q (Comma_Fork_At a d))"
    and next_value: "source_stream (Suc weight)=comma_boundary_value child (p+d)"
    and child_valid: "comma_boundary_valid child"
    and exponent_next: "5\<le>p+d"
    and phase_next: "(p+d) mod 924=snd (snd child)"
    and tail_path: "comma_native_infinite_literal_path
      (comma_boundary_value child (p+d)) tail"
    and source_unranked: "comma_native_rank_measure q=None"
    and child_unranked: "comma_native_rank_measure child=None"
    and siblings_ranked:
      "\<forall>other\<in>set (comma_native_boundary_children q (Comma_Fork_At a d)).
        other\<noteq>child \<longrightarrow> comma_native_rank_measure other\<noteq>None"
    using comma_native_B32_infinite_path_forces_unique_unranked_child
      [OF valid exponent phase native_path] .
  show thesis by (rule that[OF initial edges step occurrence member next_value
    child_valid exponent_next phase_next tail_path source_unranked child_unranked
    siblings_ranked])
qed

lemma comma_source20_zero_child_has_no_infinite_literal_path:
  "\<not>(\<exists>path :: nat \<Rightarrow> nat.
    path 0=20000000000 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
proof
  assume exists_path: "\<exists>path :: nat \<Rightarrow> nat.
    path 0=20000000000 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  then obtain path where initial: "path 0=20000000000"
    and edges: "\<forall>j. comma_child (path j) (path (Suc j))" by blast
  let ?q = "(Comma_Z,2,10)"
  have value: "comma_boundary_value ?q 10=20000000000"
    by (simp add: comma_boundary_value_def comma_zero_boundary_def)
  have valid: "comma_boundary_valid ?q" by (simp add: comma_boundary_valid_def)
  have native_path: "comma_native_infinite_literal_path
      (comma_boundary_value ?q 10) path"
    using initial edges value by (simp add: comma_native_infinite_literal_path_def)
  have ranked: "comma_native_rank_measure ?q=Some 7"
    by (rule comma_native_zero_child_ranked)
  show False using comma_native_ranked_boundary_no_infinite_path
      [OF valid, where p=10 and k=7] ranked native_path by simp
qed

lemma comma_source20_near_child_has_infinite_literal_path:
  "\<exists>path :: nat \<Rightarrow> nat.
    path 0=19999999999 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  have unbounded:
    "comma_literal_unbounded (comma_boundary_value (Comma_N,2,10) 10)"
    by (rule comma_native_near_child_unbounded)
  have value: "comma_boundary_value (Comma_N,2,10) 10=19999999999"
    by (simp add: comma_boundary_value_def comma_near_boundary_def)
  show ?thesis
    using comma_literal_unbounded_infinite_path[OF unbounded] value by simp
qed

lemmas comma_source20_run_cycle_entry = comma_native_run_entry_checked
lemmas comma_source20_periodic_run_selector = comma_native_run_cycle_checked

theorem comma_source20_global_infinite_literal_path:
  "\<exists>path :: nat \<Rightarrow> nat. path 0=20 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  by (rule comma_native_source20_infinite_path)

theorem comma_source20_global_first_choice_unique:
  assumes initial: "path 0=20"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "path 412987859=19999999999"
proof -
  have prefix: "comma_literal_path 412987858 20 (path 412987858)"
    using comma_infinite_literal_prefix[where path=path and n=412987858, OF edges]
      initial by simp
  have endpoint: "path 412987858=19999999918"
    by (rule comma_unique_literal_path_endpoint
      [OF comma_source20_to_fork_unique prefix])
  have alternatives:
    "path 412987859=19999999999 \<or> path 412987859=20000000000"
    using edges[of 412987858] endpoint comma_source20_first_fork_children by blast
  show ?thesis
  proof (rule ccontr)
    assume not_near: "path 412987859\<noteq>19999999999"
    have zero: "path 412987859=20000000000"
      using alternatives not_near by blast
    let ?tail = "\<lambda>j. path (412987859+j)"
    have tail_start: "?tail 0=20000000000" using zero by simp
    have tail_edges: "comma_child (?tail j) (?tail (Suc j))" for j
      using edges[of "412987859+j"] by (simp add: add.assoc)
    have native_tail:
      "comma_native_infinite_literal_path
        (comma_boundary_value (Comma_Z,2,10) 10) ?tail"
    proof -
      have target: "comma_boundary_value (Comma_Z,2,10) 10=20000000000"
        by (simp add: comma_boundary_value_def comma_zero_boundary_def)
      show ?thesis using tail_start tail_edges target
        by (simp add: comma_native_infinite_literal_path_def)
    qed
    have valid: "comma_boundary_valid (Comma_Z,2,10)"
      by (simp add: comma_boundary_valid_def)
    have ranked: "comma_native_rank_measure (Comma_Z,2,10)=Some 7"
      by (rule comma_native_zero_child_ranked)
    have "\<not>comma_native_infinite_literal_path
        (comma_boundary_value (Comma_Z,2,10) 10) ?tail"
      by (rule comma_native_ranked_boundary_no_infinite_path
        [OF valid, where p=10 and k=7]) (simp_all add: ranked)
    then show False using native_tail by contradiction
  qed
qed

text \<open>The checked first fork fixes the common finite prefix. After that
fork, every infinite path is a native infinite path from the near boundary;
the checked native quotient proves all such tails agree at every index. This
is an all-index statement, not only agreement at the first fork or on the
checked periodic witness.\<close>

theorem comma_source20_global_infinite_paths_agree:
  assumes left_initial: "left 0=20"
    and left_edges: "\<And>j. comma_child (left j) (left (Suc j))"
    and right_initial: "right 0=20"
    and right_edges: "\<And>j. comma_child (right j) (right (Suc j))"
  shows "\<forall>n. left n=right n"
proof -
  have left_fork: "left 412987859=19999999999"
    by (rule comma_source20_global_first_choice_unique[OF left_initial left_edges])
  have right_fork: "right 412987859=19999999999"
    by (rule comma_source20_global_first_choice_unique[OF right_initial right_edges])
  let ?q = "(Comma_N,2,10)"
  let ?left_tail = "\<lambda>j. left (412987859+j)"
  let ?right_tail = "\<lambda>j. right (412987859+j)"
  have boundary_value: "comma_boundary_value ?q 10=19999999999"
    by (simp add: comma_boundary_value_def comma_near_boundary_def)
  have boundary_valid: "comma_boundary_valid ?q"
    by (simp add: comma_boundary_valid_def)
  have boundary_exponent: "5\<le>(10::nat)" by simp
  have boundary_phase: "10 mod 924=snd (snd ?q)" by simp
  have left_tail_edges: "comma_child (?left_tail j) (?left_tail (Suc j))" for j
    using left_edges[of "412987859+j"] by simp
  have right_tail_edges: "comma_child (?right_tail j) (?right_tail (Suc j))" for j
    using right_edges[of "412987859+j"] by simp
  have left_tail_path:
    "comma_native_infinite_literal_path (comma_boundary_value ?q 10) ?left_tail"
    unfolding comma_native_infinite_literal_path_def
    using left_fork boundary_value left_tail_edges by auto
  have right_tail_path:
    "comma_native_infinite_literal_path (comma_boundary_value ?q 10) ?right_tail"
    unfolding comma_native_infinite_literal_path_def
    using right_fork boundary_value right_tail_edges by auto
  have powers: "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (comma_checked_sparse_B32_rows i)"
    by (rule comma_native_B32_refines_all)
  have stops: "\<forall>i<46. \<forall>out bits.
      (out,bits)\<in>set (comma_checked_sparse_B32_rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    by (rule comma_native_B32_stop26_all)
  have checked_b32: "comma_native_rank_check comma_native_rank_measure
      comma_native_B32_boundary_step"
    by (rule comma_native_rank_check_checked)
  have checked: "comma_native_rank_check comma_native_rank_measure
      (comma_native_boundary_step comma_checked_sparse_B32_rows)"
    using checked_b32 by (simp only: comma_native_B32_boundary_step_def)
  have all_paths_agree:
    "\<forall>q p left right. comma_boundary_valid q \<longrightarrow>
      5\<le>p \<longrightarrow> p mod 924=snd (snd q) \<longrightarrow>
      comma_native_infinite_literal_path (comma_boundary_value q p) left \<longrightarrow>
      comma_native_infinite_literal_path (comma_boundary_value q p) right \<longrightarrow>
      (\<forall>n. left n=right n)"
  proof (rule comma_native_infinite_paths_agree
      [where rows=comma_checked_sparse_B32_rows
        and rank=comma_native_rank_measure])
    show "\<forall>i<46. comma_sparse_refines
        (\<lambda>r. comma_orbit_word 5 r i) (comma_checked_sparse_B32_rows i)"
      by (rule powers)
    show "\<forall>i<46. \<forall>out bits.
        (out,bits)\<in>set (comma_checked_sparse_B32_rows i) \<longrightarrow>
        (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
      by (rule stops)
    show "comma_native_rank_check comma_native_rank_measure
        (comma_native_boundary_step comma_checked_sparse_B32_rows)"
      by (rule checked)
  qed
  have tails_agree: "\<forall>j. ?left_tail j=?right_tail j"
    using all_paths_agree boundary_valid boundary_exponent boundary_phase
      left_tail_path right_tail_path by blast
  show ?thesis
  proof (intro allI)
    fix n
    show "left n=right n"
    proof (cases "n<412987859")
      case True
      have bound: "n\<le>412987858" using True by arith
      obtain middle where unique_prefix:
          "comma_unique_literal_path n 20 middle"
        using comma_unique_literal_path_prefix
          [OF comma_source20_to_fork_unique bound] by blast
      have left_prefix: "comma_literal_path n 20 (left n)"
        using comma_infinite_literal_prefix[where path=left and n=n,
          OF left_edges] left_initial by simp
      have right_prefix: "comma_literal_path n 20 (right n)"
        using comma_infinite_literal_prefix[where path=right and n=n,
          OF right_edges] right_initial by simp
      have left_endpoint:
          "left n=middle"
        by (rule comma_unique_literal_path_endpoint[OF unique_prefix left_prefix])
      have right_endpoint:
          "right n=middle"
        by (rule comma_unique_literal_path_endpoint[OF unique_prefix right_prefix])
      show ?thesis using left_endpoint right_endpoint by simp
    next
      case False
      have after_fork: "412987859\<le>n" using False by simp
      have split: "n=412987859+(n-412987859)" using after_fork by arith
      have tail_equal:
          "?left_tail (n-412987859)=?right_tail (n-412987859)"
        using tails_agree by blast
      show ?thesis using tail_equal split by simp
    qed
  qed
qed

corollary comma_source20_global_unique_infinite_literal_path:
  "\<exists>!path :: nat \<Rightarrow> nat. path 0=20 \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
proof -
  obtain witness :: "nat \<Rightarrow> nat" where witness_initial: "witness 0=20"
    and witness_edges: "\<And>j. comma_child (witness j) (witness (Suc j))"
    using comma_source20_global_infinite_literal_path by blast
  show ?thesis
  proof (rule ex1I[of _ witness])
    show "witness 0=20 \<and>
        (\<forall>j. comma_child (witness j) (witness (Suc j)))"
      using witness_initial witness_edges by blast
    fix path :: "nat \<Rightarrow> nat"
    assume path: "path 0=20 \<and>
        (\<forall>j. comma_child (path j) (path (Suc j)))"
    have path_initial: "path 0=20" using path by blast
    have edges: "comma_child (path j) (path (Suc j))" for j
      using path by blast
    have pointwise: "\<forall>n. path n=witness n"
    proof (rule comma_source20_global_infinite_paths_agree)
      show "path 0=20" by (rule path_initial)
      show "comma_child (path j) (path (Suc j))" for j by (rule edges)
      show "witness 0=20" by (rule witness_initial)
      show "comma_child (witness j) (witness (Suc j))" for j
        by (rule witness_edges)
    qed
    show "path=witness"
      using pointwise by (rule ext) simp
  qed
qed

theorem comma_source20_global_future_safety:
  "(\<exists>path :: nat \<Rightarrow> nat. path 0=20 \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))) \<and>
   (\<forall>path :: nat \<Rightarrow> nat.
      path 0=20 \<longrightarrow>
      (\<forall>j. comma_child (path j) (path (Suc j))) \<longrightarrow>
      path 412987859=19999999999)"
proof
  show "\<exists>path :: nat \<Rightarrow> nat. path 0=20 \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
    by (rule comma_source20_global_infinite_literal_path)
  show "\<forall>path :: nat \<Rightarrow> nat.
      path 0=20 \<longrightarrow>
      (\<forall>j. comma_child (path j) (path (Suc j))) \<longrightarrow>
      path 412987859=19999999999"
  proof (intro allI impI)
    fix path :: "nat \<Rightarrow> nat"
    assume initial: "path 0=20"
      and edges: "\<forall>j. comma_child (path j) (path (Suc j))"
    show "path 412987859=19999999999"
      by (rule comma_source20_global_first_choice_unique[OF initial])
        (use edges in blast)
  qed
qed

ML \<open>
  val release_endpoints = @{thms comma_source20_global_future_safety
    comma_source20_global_infinite_paths_agree
    comma_source20_global_unique_infinite_literal_path}
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "Global comma future-safety release endpoints"
    ["comma_source20_global_infinite_literal_path",
     "comma_source20_global_first_choice_unique",
     "comma_source20_global_infinite_paths_agree"] release_endpoints
\<close>

end
