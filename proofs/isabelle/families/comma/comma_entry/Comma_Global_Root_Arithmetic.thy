theory Comma_Global_Root_Arithmetic
  imports Comma_Source_Entry
    Comma_Arithmetic.Comma_Decimal_Parent
    Comma_Arithmetic.Comma_Child_Classification
begin

ML_file "../comma_entry_arithmetic/proof_profile.ML"

ML \<open>
  structure Comma_Global_Root_Arithmetic_Profile =
  struct
    val checkpoint = Comma_Proof_Profile.timer "Comma_Global_Root_Arithmetic"
    fun consolidate_checkpoint name theorems =
      (Thm.consolidate theorems; checkpoint name)
  end
\<close>

text \<open>
Canonical literal arithmetic shared by the legacy global safety theorem and
its semantic-provider rebase.  These lemmas connect child edges to the unique
decimal parent, locate the first exponent-five entry on an infinite path, and
reuse the checked finite source-20 prefix to identify the three open entries.
No future rank map or forest authority is imported here.
\<close>

lemma comma_child_strict_growth:
  assumes child: "comma_child k target"
  shows "k < target"
proof -
  obtain e p where sector: "comma_sector e p target"
    and child_value: "target = k + 10 * (k mod 10) + e"
    and e: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF child] by blast
  show ?thesis using child_value e by linarith
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "child-strict-growth" [@{thm comma_child_strict_growth}]\<close>

lemma comma_child_increment_bound:
  assumes child: "comma_child k target"
  shows "target \<le> k + 99"
proof -
  obtain e p where child_value: "target = k + 10 * (k mod 10) + e"
    and e: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF child] by blast
  have digit: "k mod 10 \<le> 9" by simp
  show ?thesis using child_value e digit by linarith
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "child-increment-bound" [@{thm comma_child_increment_bound}]\<close>

lemma comma_child_parent:
  assumes child: "comma_child k target"
  shows "comma_parent target = k"
proof -
  obtain e p where sector: "comma_sector e p target"
    and child_value: "target = k + 10 * (k mod 10) + e"
    and e: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF child] by blast
  have positive: "target > 0"
    using comma_child_strict_growth[OF child] by simp
  obtain q where leading_sector:
      "comma_sector (comma_leading_digit target) q target"
    using comma_leading_sector[OF positive] by blast
  have exponent: "q = p"
    by (rule comma_sector_exponent_unique[OF leading_sector sector])
  have same_sector: "comma_sector (comma_leading_digit target) p target"
    using leading_sector exponent by simp
  have leading: "comma_leading_digit target = e"
    by (rule comma_sector_leading_unique[OF same_sector sector])
  have diff: "target - e = k + 10 * (k mod 10)"
    using child_value by arith
  have residue: "(target - e) mod 10 = k mod 10"
    using diff by simp
  have parent_formula:
    "comma_parent target = target - (10 * ((target - e) mod 10) + e)"
    by (simp only: comma_parent_def Let_def leading)
  also have "... = target - (10 * (k mod 10) + e)"
    by (simp only: residue)
  also have "... = k"
    using child_value by arith
  finally show ?thesis .
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "child-parent" [@{thm comma_child_parent}]\<close>

function comma_decimal_root_of :: "nat \<Rightarrow> nat" where
  "comma_decimal_root_of n =
    (if n=0 then 0
     else if comma_parent n=0 then n
     else comma_decimal_root_of (comma_parent n))"
  by pat_completeness auto
termination
  by (relation "measure id")
    (auto intro: comma_parent_smaller)
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "decimal-root-recursion" [@{thm comma_decimal_root_of.simps}]\<close>

declare comma_decimal_root_of.simps[simp del]

lemma comma_decimal_root_of_root:
  assumes positive: "0 < root" and parent: "comma_parent root = 0"
  shows "comma_decimal_root_of root = root"
  by (subst comma_decimal_root_of.simps) (simp add: positive parent)
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "root-fixed" [@{thm comma_decimal_root_of_root}]\<close>

lemma comma_decimal_root_of_child:
  assumes positive: "0 < k" and child: "comma_child k target"
  shows "comma_decimal_root_of target = comma_decimal_root_of k"
proof -
  have parent: "comma_parent target = k" by (rule comma_child_parent[OF child])
  have target_positive: "0 < target"
    using positive comma_child_strict_growth[OF child] by linarith
  have target_nonzero: "target \<noteq> 0"
    using target_positive by simp
  have k_nonzero: "k \<noteq> 0"
    using positive by simp
  show ?thesis
    by (subst comma_decimal_root_of.simps)
      (simp only: target_nonzero parent k_nonzero if_False)
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "root-child-invariance" [@{thm comma_decimal_root_of_child}]\<close>

lemma comma_decimal_root_of_literal_path:
  assumes path: "comma_literal_path n source target" and positive: "0 < source"
  shows "comma_decimal_root_of target = comma_decimal_root_of source"
  using path positive
proof (induction rule: comma_literal_path.induct)
  case (zero k)
  then show ?case by simp
next
  case (step k k' n target)
  have next_positive: "0 < k'"
    using step.prems comma_child_strict_growth[OF step.hyps(1)] by linarith
  have head: "comma_decimal_root_of k' = comma_decimal_root_of k"
    by (rule comma_decimal_root_of_child[OF step.prems step.hyps(1)])
  have tail: "comma_decimal_root_of target = comma_decimal_root_of k'"
    by (rule step.IH[OF next_positive])
  show ?case using head tail by simp
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "literal-path-invariance" [@{thm comma_decimal_root_of_literal_path}]\<close>

lemma comma_decimal_root_properties:
  assumes "root \<in> comma_decimal_roots"
  shows "0 < root" "root < 100" "comma_parent root = 0"
proof -
  have member: "root \<in> {n. 1 \<le> n \<and> n < 100 \<and> comma_parent n = 0}"
    using assms comma_small_root_classification by simp
  show "0 < root" "root < 100" "comma_parent root = 0"
    using member by auto
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "root-properties" @{thms comma_decimal_root_properties}\<close>

lemma comma_infinite_path_linear_growth:
  assumes edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "path 0 + n \<le> path n"
proof (induction n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have grow: "path n < path (Suc n)"
    by (rule comma_child_strict_growth[OF edges])
  show ?case using Suc.IH grow by arith
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "infinite-growth" [@{thm comma_infinite_path_linear_growth}]\<close>

lemma comma_infinite_root_first_p5_entry:
  assumes root: "root \<in> comma_decimal_roots"
    and initial: "path 0 = root"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
  shows "\<exists>m x. x \<le> 90 \<and> path m = 100000 + x \<and>
    comma_literal_path m root (path m)"
proof -
  have root_lt: "root < 100" and root_pos: "0 < root"
    using comma_decimal_root_properties[OF root] by auto
  have eventual: "100000 \<le> path 100000"
  proof -
    have "path 0 + 100000 \<le> path 100000"
      by (rule comma_infinite_path_linear_growth
        [where path=path and n=100000, OF edges])
    then show ?thesis using initial root_pos by arith
  qed
  let ?m = "LEAST j. 100000 \<le> path j"
  have at_m: "100000 \<le> path ?m"
    by (rule LeastI[of _ 100000]) (rule eventual)
  have nonzero: "?m \<noteq> 0"
  proof
    assume m_zero: "?m = 0"
    have "100000 \<le> root" using at_m initial m_zero by simp
    with root_lt show False by arith
  qed
  obtain j where m: "?m = Suc j" using nonzero by (cases ?m) auto
  have before: "path j < 100000"
  proof -
    have jlt: "j < ?m" using m by simp
    have "\<not> 100000 \<le> path j"
      by (rule not_less_Least[OF jlt])
    then show ?thesis by simp
  qed
  have edge: "comma_child (path j) (path ?m)" using edges[of j] m by simp
  obtain e p where sector: "comma_sector e p (path ?m)"
    and entry_value: "path ?m = path j + 10 * (path j mod 10) + e"
    and ebounds: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF edge] by blast
  have digit: "path j mod 10 \<le> 9" by simp
  have rough_upper: "path ?m < 200000"
    using before entry_value ebounds digit by linarith
  have sector_one: "comma_sector 1 5 (path ?m)"
    using at_m rough_upper by (simp add: comma_sector_def)
  have exponent: "p = 5"
    by (rule comma_sector_exponent_unique[OF sector sector_one])
  have sector5: "comma_sector e 5 (path ?m)"
    using sector exponent by simp
  have leading: "e = 1"
    by (rule comma_sector_leading_unique[OF sector5 sector_one])
  have tight_upper: "path ?m \<le> 100090"
    using before entry_value digit leading by linarith
  let ?x = "path ?m - 100000"
  have x: "?x \<le> 90" using at_m tight_upper by arith
  have endpoint: "path ?m = 100000 + ?x" using at_m by arith
  have prefix: "comma_literal_path ?m root (path ?m)"
    using comma_infinite_literal_prefix[where path=path and n="?m", OF edges] initial by simp
  show ?thesis using x endpoint prefix by blast
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "first-p5-entry" [@{thm comma_infinite_root_first_p5_entry}]\<close>

lemma comma_source20_entry_children:
  "comma_child 100003 100034" "comma_child 100034 100075"
proof -
  show "comma_child 100003 100034"
    unfolding comma_child_def
    by (rule exI[where x=1], rule exI[where x=5], simp add: comma_sector_def)
  show "comma_child 100034 100075"
    unfolding comma_child_def
    by (rule exI[where x=1], rule exI[where x=5], simp add: comma_sector_def)
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "source20-entry-children" @{thms comma_source20_entry_children}\<close>

lemma comma_p5_open_entries_have_root20:
  assumes "x = 3 \<or> x = 34 \<or> x = 75"
  shows "comma_decimal_root_of (100000+x) = 20"
proof -
  have root20_member: "20 \<in> comma_decimal_roots"
    by (simp add: comma_decimal_roots_def)
  have root20_positive: "0 < (20::nat)"
    by simp
  have root20: "comma_decimal_root_of 20 = 20"
    by (rule comma_decimal_root_of_root)
      (use comma_decimal_root_properties[OF root20_member] in auto)
  have p3: "comma_literal_path 1939 20 100003" by (rule comma_source20_to_p5)
  have p34: "comma_literal_path 1940 20 100034"
    using comma_literal_path_snoc[OF p3 comma_source20_entry_children(1)] by simp
  have p75: "comma_literal_path 1941 20 100075"
    using comma_literal_path_snoc[OF p34 comma_source20_entry_children(2)] by simp
  have r3: "comma_decimal_root_of 100003 = 20"
    using comma_decimal_root_of_literal_path[OF p3 root20_positive] root20 by simp
  have r34: "comma_decimal_root_of 100034 = 20"
    using comma_decimal_root_of_literal_path[OF p34 root20_positive] root20 by simp
  have r75: "comma_decimal_root_of 100075 = 20"
    using comma_decimal_root_of_literal_path[OF p75 root20_positive] root20 by simp
  show ?thesis using assms r3 r34 r75 by auto
qed
ML \<open>Comma_Global_Root_Arithmetic_Profile.consolidate_checkpoint
  "open-entry-root20" [@{thm comma_p5_open_entries_have_root20}]\<close>



ML \<open>
val _ =
  if null (Thm_Deps.all_oracles @{thms
    comma_child_strict_growth
    comma_child_increment_bound
    comma_child_parent
    comma_decimal_root_of_root
    comma_decimal_root_of_child
    comma_decimal_root_of_literal_path
    comma_decimal_root_properties
    comma_infinite_path_linear_growth
    comma_infinite_root_first_p5_entry
    comma_source20_entry_children
    comma_p5_open_entries_have_root20
  }) then ()
  else error "Comma_Global_Root_Arithmetic local oracle audit failed"
\<close>
end
