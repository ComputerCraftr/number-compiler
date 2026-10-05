theory Comma_Global_Root_Safety
  imports Comma_Global_Future_Safety
    Comma_Native_Summary_Instance.Comma_Native_Summary_Instance
    Comma_Source_Entry.Comma_Global_Root_Arithmetic
begin

text \<open>
The old runtime forest had one logically separate obligation after source-20
future safety: prove that no other decimal root can start an infinite literal
path.  We do not reproduce the 49 trees here.

Every literal edge has a unique decimal parent.  Any infinite path from a
listed decimal root must eventually cross 10^5; its first crossing is
100000+x with x <= 90.  The native sparse B32 summary supplies a checked
total/exact result for all 91 entry states.  Its unique occurrence lift then
shows that an infinite continuation must select an unranked child at its
terminal fork.  The current finite classification leaves x in {3,34,75};
all three values lie in the root-20 tree. The finite ranks are candidate
descent measures only: a kernel-checked native transition audit verifies
every valid boundary row and its complete child set before any rank is used.
This is a 91-entry theorem, not a production forest traversal.
\<close>

fun comma_p5_entry_native_stopped :: "nat \<Rightarrow> bool" where
  "comma_p5_entry_native_stopped x =
    (case comma_native_decade_summary (Comma_Decade 5 x) of
       Some (h,terminal) \<Rightarrow> h\<le>26
     | None \<Rightarrow> False)"

definition comma_p5_entry_future_open :: "nat \<Rightarrow> bool" where
  "comma_p5_entry_future_open x =
    (case comma_native_decade_summary (Comma_Decade 5 x) of
       Some (h,Comma_Terminal_Fork a) \<Rightarrow>
         (comma_boundary_valid (Comma_N,a,(5+h) mod 924) \<and>
          comma_boundary_valid (Comma_Z,a,(5+h) mod 924) \<and>
          (comma_native_rank_measure (Comma_N,a,(5+h) mod 924) = None \<or>
           comma_native_rank_measure (Comma_Z,a,(5+h) mod 924) = None))
     | _ \<Rightarrow> False)"

lemma comma_p5_entry_native_total_checked:
  "list_all comma_p5_entry_native_stopped [0..<91]"
proof -
  have every: "x<91 \<Longrightarrow> comma_p5_entry_native_stopped x" for x
  proof -
    assume x: "x<91"
    have x_bound: "x\<le>90" using x by simp
    obtain h terminal where result:
      "comma_native_decade_summary (Comma_Decade 5 x)=Some (h,terminal)"
      "h\<le>26"
      "comma_decade_exact_summary (Comma_Decade 5 x) h terminal"
      using comma_native_decade_summary_total_exact[of "Comma_Decade 5 x"] x_bound
      by auto
    show "comma_p5_entry_native_stopped x"
      using result(1,2) by (simp add: comma_p5_entry_native_stopped.simps)
  qed
  show ?thesis using every by (simp add: list_all_iff)
qed

lemma comma_p5_entry_future_open_checked:
  "filter comma_p5_entry_future_open [0..<91] = [3,34,75]"
  unfolding comma_p5_entry_future_open_def
  by code_simp

lemma comma_p5_entry_native_stop:
  assumes "x \<le> 90"
  obtains h terminal where
    "comma_native_decade_summary (Comma_Decade 5 x)=Some (h,terminal)"
    "h\<le>26"
    "comma_decade_exact_summary (Comma_Decade 5 x) h terminal"
proof -
  obtain h terminal where result:
    "comma_native_decade_summary (Comma_Decade 5 x)=Some (h,terminal)"
    "h\<le>26"
    "comma_decade_exact_summary (Comma_Decade 5 x) h terminal"
    using comma_native_decade_summary_total_exact[of "Comma_Decade 5 x"] assms by auto
  show thesis by (rule that[OF result(1) result(2) result(3)])
qed

lemma comma_finite_fork_boundary_valid:
  assumes fork: "comma_finite_step residue terminal = Comma_Fork a d"
  shows "comma_boundary_valid (kind,a,r mod 924)"
  using fork
  by (cases terminal)
    (auto simp: comma_finite_step_def comma_weighted_step_def
      comma_boundary_valid_def Let_def
      split: if_splits)

lemma comma_infinite_boundary_is_unranked:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
    and infinite: "\<exists>path :: nat \<Rightarrow> nat.
      path 0 = comma_boundary_value q p \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
  shows "comma_native_rank_measure q = None"
proof (cases "comma_native_rank_measure q")
  case None
  then show ?thesis .
next
  case (Some n)
  have impossible: "\<not>(\<exists>path :: nat \<Rightarrow> nat.
      path 0 = comma_boundary_value q p \<and>
      (\<forall>j. comma_child (path j) (path (Suc j))))"
    by (rule comma_future_global_ranked_boundary_no_infinite_literal_path
      [OF valid Some exponent phase])
  show ?thesis using impossible infinite Some by contradiction
qed

lemma comma_p5_entry_infinite_imp_open:
  assumes offset: "x \<le> 90"
    and infinite: "\<exists>path :: nat \<Rightarrow> nat.
      path 0 = 100000+x \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
  shows "comma_p5_entry_future_open x"
proof -
  have start: "comma_chart_value 5 (Comma_Entry 1 0 x)=100000+x"
    by (simp add: comma_chart_value_def)
  obtain path :: "nat \<Rightarrow> nat" where initial: "path 0=100000+x"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
    using infinite by blast
  have path_spec:
    "path 0=comma_chart_value 5 (Comma_Entry 1 0 x) \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
    using initial edges start by blast
  obtain h terminal weight t child where summary:
    "comma_native_decade_summary (Comma_Decade (5 mod 924) x)=Some (h,terminal)"
    and height: "h\<le>26"
    and member: "child\<in>set (comma_summary_ordered_children terminal (5+h))"
    and next_value: "path (Suc weight)=child"
    and path_tail: "comma_native_infinite_literal_path child
      (\<lambda>j. path (weight+Suc j))"
    using comma_native_B32_entry_infinite_path_projects
      [OF offset, where p=5 and path=path] path_spec by simp
  have native: "comma_native_decade_summary (Comma_Decade 5 x)=Some (h,terminal)"
    using summary by (simp add: comma_native_decade_summary_def)
  have stopped: "comma_p5_entry_native_stopped x"
    using native height by simp
  have powers:
    "\<forall>i<46. comma_sparse_refines
      (\<lambda>r. comma_orbit_word 5 r i) (comma_checked_sparse_B32_rows i)"
    by (rule comma_native_B32_refines_all)
  have stops:
    "\<forall>i<46. \<forall>out bits.
      (out,bits)\<in>set (comma_checked_sparse_B32_rows i) \<longrightarrow>
      (\<exists>h terminal. out=Comma_Word_Stop h terminal \<and> h\<le>26)"
    by (rule comma_native_B32_stop26_all)
  have admitted: "comma_decade_admitted (Comma_Decade (5 mod 924) x)"
    using offset by simp
  have sparse_summary:
    "comma_sparse_decade_summary comma_checked_sparse_B32_rows
      (Comma_Decade (5 mod 924) x)=Some (h,terminal)"
    using summary by (simp only: comma_native_decade_summary_def)
  have terminal_bounds:
    "(case terminal of Comma_Terminal_Fork a \<Rightarrow> 2\<le>a \<and> a\<le>9
      | Comma_Terminal_Landmine \<Rightarrow> True)"
    by (rule comma_native_sparse_summary_fork_bounds
      [OF powers stops admitted sparse_summary])
  show ?thesis
  proof (cases terminal)
    case Comma_Terminal_Landmine
    have no_member: "child\<notin>set (comma_summary_ordered_children terminal (5+h))"
      using Comma_Terminal_Landmine by (simp add: comma_summary_ordered_children.simps)
    show ?thesis using member no_member by contradiction
  next
    case (Comma_Terminal_Fork a)
    have a_bounds: "2\<le>a" "a\<le>9"
      using terminal_bounds Comma_Terminal_Fork by auto
    have near_valid: "comma_boundary_valid (Comma_N,a,(5+h) mod 924)"
      using a_bounds by (simp add: comma_boundary_valid_def)
    have zero_valid: "comma_boundary_valid (Comma_Z,a,(5+h) mod 924)"
      using a_bounds by (simp add: comma_boundary_valid_def)
    have alternatives:
      "child=comma_near_boundary a (5+h) \<or>
       child=comma_zero_boundary a (5+h)"
      using member Comma_Terminal_Fork
      by (auto simp: comma_summary_ordered_children.simps)
    have selected_unranked:
      "child=comma_boundary_value (kind,a,(5+h) mod 924) (5+h) \<Longrightarrow>
       comma_native_rank_measure (kind,a,(5+h) mod 924)=None" for kind
    proof -
      assume selected: "child=comma_boundary_value (kind,a,(5+h) mod 924) (5+h)"
      have valid: "comma_boundary_valid (kind,a,(5+h) mod 924)"
        using a_bounds by (simp add: comma_boundary_valid_def)
      have tail_exists: "\<exists>tail :: nat \<Rightarrow> nat.
          tail 0=comma_boundary_value (kind,a,(5+h) mod 924) (5+h) \<and>
          (\<forall>j. comma_child (tail j) (tail (Suc j)))"
        using path_tail selected
        unfolding comma_native_infinite_literal_path_def by blast
      show ?thesis
        by (rule comma_infinite_boundary_is_unranked[OF valid, where p="5+h"])
          (use tail_exists in simp_all)
    qed
    have near_unranked:
      "child=comma_near_boundary a (5+h) \<Longrightarrow>
       comma_native_rank_measure (Comma_N,a,(5+h) mod 924)=None"
      using selected_unranked[of Comma_N]
      by (simp add: comma_boundary_value_def comma_near_boundary_def)
    have zero_unranked:
      "child=comma_zero_boundary a (5+h) \<Longrightarrow>
       comma_native_rank_measure (Comma_Z,a,(5+h) mod 924)=None"
      using selected_unranked[of Comma_Z]
      by (simp add: comma_boundary_value_def comma_zero_boundary_def)
    have open_rank:
      "comma_native_rank_measure (Comma_N,a,(5+h) mod 924)=None \<or>
       comma_native_rank_measure (Comma_Z,a,(5+h) mod 924)=None"
      using alternatives near_unranked zero_unranked by blast
    show ?thesis using native near_valid zero_valid open_rank Comma_Terminal_Fork
      by (simp add: comma_p5_entry_future_open_def)
  qed
qed

theorem comma_unique_infinite_decimal_root:
  assumes root: "root \<in> comma_decimal_roots"
    and infinite: "\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
  shows "root = 20"
proof -
  obtain path :: "nat \<Rightarrow> nat" where initial: "path 0=root"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
    using infinite by blast
  obtain m x where x: "x \<le> 90" and entry: "path m = 100000+x"
    and prefix: "comma_literal_path m root (path m)"
    using comma_infinite_root_first_p5_entry[OF root initial edges] by blast
  have tail_infinite: "\<exists>tail :: nat \<Rightarrow> nat. tail 0=100000+x \<and>
      (\<forall>j. comma_child (tail j) (tail (Suc j)))"
    by (rule exI[of _ "\<lambda>j. path (m+j)"])
      (use entry edges in simp)
  have open: "comma_p5_entry_future_open x"
    by (rule comma_p5_entry_infinite_imp_open[OF x tail_infinite])
  have member: "x \<in> set (filter comma_p5_entry_future_open [0..<91])"
    using x open by simp
  have cases: "x=3 \<or> x=34 \<or> x=75"
    using member comma_p5_entry_future_open_checked by simp
  have target_root: "comma_decimal_root_of (path m) = root"
  proof -
    have source_root: "comma_decimal_root_of root = root"
      by (rule comma_decimal_root_of_root)
        (use comma_decimal_root_properties[OF root] in auto)
    have preserve: "comma_decimal_root_of (path m) = comma_decimal_root_of root"
      by (rule comma_decimal_root_of_literal_path[OF prefix])
        (use comma_decimal_root_properties[OF root] in auto)
    show ?thesis using preserve source_root by simp
  qed
  have target20: "comma_decimal_root_of (path m) = 20"
    using comma_p5_open_entries_have_root20[OF cases] entry by simp
  show ?thesis using target_root target20 by simp
qed

corollary comma_other_decimal_roots_have_no_infinite_literal_path:
  assumes root: "root \<in> comma_decimal_roots" and other: "root \<noteq> 20"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
  using comma_unique_infinite_decimal_root[OF root] other by blast

corollary comma_decimal_root_infinite_iff_20:
  assumes root: "root \<in> comma_decimal_roots"
  shows "(\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))) \<longleftrightarrow> root=20"
proof
  assume infinite: "\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
  show "root=20" by (rule comma_unique_infinite_decimal_root[OF assms infinite])
next
  assume "root=20"
  then show "\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
    (\<forall>j. comma_child (path j) (path (Suc j)))"
    using comma_source20_global_infinite_literal_path by simp
qed

theorem comma_global_release_safety:
  "(\<forall>root\<in>comma_decimal_roots.
      ((\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
        (\<forall>j. comma_child (path j) (path (Suc j)))) \<longleftrightarrow> root=20)) \<and>
   (\<forall>path :: nat \<Rightarrow> nat.
      path 0=20 \<longrightarrow>
      (\<forall>j. comma_child (path j) (path (Suc j))) \<longrightarrow>
      path 412987859 = 19999999999)"
proof
  show "\<forall>root\<in>comma_decimal_roots.
      ((\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
        (\<forall>j. comma_child (path j) (path (Suc j)))) \<longleftrightarrow> root=20)"
    using comma_decimal_root_infinite_iff_20 by blast
  show "\<forall>path :: nat \<Rightarrow> nat.
      path 0=20 \<longrightarrow>
      (\<forall>j. comma_child (path j) (path (Suc j))) \<longrightarrow>
      path 412987859 = 19999999999"
    using comma_source20_global_future_safety by blast
qed

ML \<open>
  val release_endpoints = @{thms comma_global_release_safety}
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "Global comma root-safety release endpoint"
    ["comma_decimal_root_infinite_iff_20",
     "comma_source20_global_future_safety"] release_endpoints
\<close>

end
