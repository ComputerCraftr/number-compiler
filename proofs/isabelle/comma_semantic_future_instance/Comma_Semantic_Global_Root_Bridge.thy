theory Comma_Semantic_Global_Root_Bridge
  imports Comma_Semantic_Entry_Open
    Comma_Source_Entry.Comma_Global_Root_Arithmetic
begin

text \<open>
The semantic global rebase combines the checked 91-entry future-open filter
with canonical literal arithmetic shared with the legacy root proof.  No
native or forest authority is imported.
\<close>

theorem comma_semantic_unique_infinite_decimal_root:
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
  obtain tail where tail_start: "tail 0=100000+x"
    and tail_edges: "\<And>j. comma_child (tail j) (tail (Suc j))"
    using tail_infinite by blast
  have open_entry: "comma_semantic_p5_entry_future_open x"
  proof (rule comma_semantic_p5_entry_infinite_imp_open[OF x tail_start])
    fix j
    show "comma_child (tail j) (tail (Suc j))"
      by (rule tail_edges)
  qed
  have member:
    "x \<in> set (filter comma_semantic_p5_entry_future_open [0..<91])"
    using x open_entry by simp
  have cases: "x=3 \<or> x=34 \<or> x=75"
    using member comma_semantic_p5_entry_future_open_checked by simp
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

corollary comma_semantic_other_decimal_roots_have_no_infinite_literal_path:
  assumes root: "root \<in> comma_decimal_roots" and other: "root \<noteq> 20"
  shows "\<not>(\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
    (\<forall>j. comma_child (path j) (path (Suc j))))"
  using comma_semantic_unique_infinite_decimal_root[OF root] other by blast

end
