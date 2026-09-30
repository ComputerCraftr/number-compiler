theory Comma_Global_Root_Safety
  imports Comma_Global_Future_Safety
    Comma_Arithmetic.Comma_Decimal_Parent
    Comma_Arithmetic.Comma_Child_Classification
    Comma_Decade_Summary_Transport.Comma_Decade_Summary_Transport
begin

text \<open>
The old runtime forest had one logically separate obligation after source-20
future safety: prove that no other decimal root can start an infinite literal
path.  We do not reproduce the 49 trees here.

Every literal edge has a unique decimal parent.  Any infinite path from a
listed decimal root must eventually cross 10^5; its first crossing is
100000+x with x <= 90.  A complete B32 evaluation of just those 91 entry
states, followed by the already checked future rank, leaves x in {3,34,75}.
All three values lie in the root-20 tree.  Thus an infinite decimal-root path
has root 20.  This is a 91-entry admission theorem, not a forest certificate.
\<close>

lemma comma_child_strict_growth:
  assumes child: "comma_child k target"
  shows "k < target"
proof -
  obtain e p where sector: "comma_sector e p target"
    and value: "target = k + 10 * (k mod 10) + e"
    and e: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF child] by blast
  show ?thesis using value e by linarith
qed

lemma comma_child_increment_bound:
  assumes child: "comma_child k target"
  shows "target \<le> k + 99"
proof -
  obtain e p where value: "target = k + 10 * (k mod 10) + e"
    and e: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF child] by blast
  have digit: "k mod 10 \<le> 9" by simp
  show ?thesis using value e digit by linarith
qed

lemma comma_child_parent:
  assumes child: "comma_child k target"
  shows "comma_parent target = k"
proof -
  obtain e p where sector: "comma_sector e p target"
    and value: "target = k + 10 * (k mod 10) + e"
    and e: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF child] by blast
  have positive: "target > 0" using sector by (auto simp: comma_sector_def)
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
    using value by arith
  have residue: "(target - e) mod 10 = k mod 10"
    using diff by simp
  show ?thesis
    using value residue
    by (simp add: comma_parent_def Let_def leading)
qed

function comma_decimal_root_of :: "nat \<Rightarrow> nat" where
  "comma_decimal_root_of n =
    (if n=0 then 0
     else if comma_parent n=0 then n
     else comma_decimal_root_of (comma_parent n))"
  by pat_completeness auto
termination
  by (relation "measure id")
    (auto intro: comma_parent_smaller)

lemma comma_decimal_root_of_root:
  assumes positive: "0 < root" and parent: "comma_parent root = 0"
  shows "comma_decimal_root_of root = root"
  by (subst comma_decimal_root_of.simps) (simp add: positive parent)

lemma comma_decimal_root_of_child:
  assumes positive: "0 < k" and child: "comma_child k target"
  shows "comma_decimal_root_of target = comma_decimal_root_of k"
proof -
  have parent: "comma_parent target = k" by (rule comma_child_parent[OF child])
  have target_positive: "0 < target"
    using positive comma_child_strict_growth[OF child] by linarith
  show ?thesis
    by (subst comma_decimal_root_of.simps)
      (simp add: target_positive parent positive)
qed

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

lemma comma_decimal_root_properties:
  assumes "root \<in> comma_decimal_roots"
  shows "0 < root" "root < 100" "comma_parent root = 0"
proof -
  have member: "root \<in> {n. 1 \<le> n \<and> n < 100 \<and> comma_parent n = 0}"
    using assms comma_small_root_classification by simp
  show "0 < root" "root < 100" "comma_parent root = 0"
    using member by auto
qed

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
      by (rule comma_infinite_path_linear_growth[OF edges])
    then show ?thesis using initial root_pos by arith
  qed
  let ?m = "LEAST j. 100000 \<le> path j"
  have at_m: "100000 \<le> path ?m"
    by (rule LeastI[of _ 100000]) (rule eventual)
  have nonzero: "?m \<noteq> 0" using at_m initial root_lt by auto
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
    and value: "path ?m = path j + 10 * (path j mod 10) + e"
    and ebounds: "1 \<le> e" "e \<le> 9"
    using comma_child_witness[OF edge] by blast
  have digit: "path j mod 10 \<le> 9" by simp
  have rough_upper: "path ?m < 200000"
    using before value ebounds digit by linarith
  have sector_one: "comma_sector 1 5 (path ?m)"
    using at_m rough_upper by (simp add: comma_sector_def)
  have exponent: "p = 5"
    by (rule comma_sector_exponent_unique[OF sector sector_one])
  have sector5: "comma_sector e 5 (path ?m)"
    using sector exponent by simp
  have leading: "e = 1"
    by (rule comma_sector_leading_unique[OF sector5 sector_one])
  have tight_upper: "path ?m \<le> 100090"
    using before value digit leading by linarith
  let ?x = "path ?m - 100000"
  have x: "?x \<le> 90" using at_m tight_upper by arith
  have endpoint: "path ?m = 100000 + ?x" using at_m by arith
  have prefix: "comma_literal_path ?m root (path ?m)"
    using comma_infinite_literal_prefix[where path=path and n=?m, OF edges] initial by simp
  show ?thesis using x endpoint prefix by blast
qed

fun comma_p5_entry_B32_stopped :: "nat \<Rightarrow> bool" where
  "comma_p5_entry_B32_stopped x =
    (case comma_decade_block_power 5 (Comma_Decade 5 x) of
       Comma_Block_Stop h terminal \<Rightarrow> True
     | _ \<Rightarrow> False)"

definition comma_p5_entry_future_open :: "nat \<Rightarrow> bool" where
  "comma_p5_entry_future_open x =
    (case comma_decade_block_power 5 (Comma_Decade 5 x) of
       Comma_Block_Stop h (Comma_Terminal_Fork a) \<Rightarrow>
         (comma_rank_candidate (Comma_N,a,(5+h) mod 924) = None \<or>
          comma_rank_candidate (Comma_Z,a,(5+h) mod 924) = None)
     | _ \<Rightarrow> False)"

lemma comma_p5_entry_B32_complete_checked:
  "list_all comma_p5_entry_B32_stopped [0..<91]"
  by code_simp

lemma comma_p5_entry_future_open_checked:
  "filter comma_p5_entry_future_open [0..<91] = [3,34,75]"
  unfolding comma_p5_entry_future_open_def
  by code_simp

lemma comma_p5_entry_B32_stop:
  assumes "x \<le> 90"
  obtains h terminal where
    "comma_decade_block_power 5 (Comma_Decade 5 x) = Comma_Block_Stop h terminal"
proof -
  have member: "x \<in> set [0..<91]" using assms by simp
  have stopped: "comma_p5_entry_B32_stopped x"
    using comma_p5_entry_B32_complete_checked member
    by (simp add: list_all_iff)
  show thesis using stopped that
    by (cases "comma_decade_block_power 5 (Comma_Decade 5 x)") auto
qed

lemma comma_weighted_fork_boundary_valid:
  assumes fork: "comma_weighted_step residue terminal = Comma_WFork terminal a d"
  shows "comma_boundary_valid (kind,a,r mod 924)"
  using fork
  by (cases terminal)
    (auto simp: comma_weighted_step_def comma_boundary_valid_def Let_def
      split: if_splits)

lemma comma_infinite_boundary_is_unranked:
  assumes valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and phase: "p mod 924 = snd (snd q)"
    and infinite: "\<exists>path :: nat \<Rightarrow> nat.
      path 0 = comma_boundary_value q p \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
  shows "comma_rank_candidate q = None"
proof (cases "comma_rank_candidate q")
  case None
  then show ?thesis .
next
  case (Some n)
  have impossible: "\<not>(\<exists>path :: nat \<Rightarrow> nat.
      path 0 = comma_boundary_value q p \<and>
      (\<forall>j. comma_child (path j) (path (Suc j))))"
    by (rule comma_future_global_ranked_boundary_no_infinite_literal_path
      [OF valid Some exponent phase])
  show ?thesis using impossible infinite by contradiction
qed

lemma comma_p5_entry_infinite_imp_open:
  assumes offset: "x \<le> 90"
    and infinite: "\<exists>path :: nat \<Rightarrow> nat.
      path 0 = 100000+x \<and>
      (\<forall>j. comma_child (path j) (path (Suc j)))"
  shows "comma_p5_entry_future_open x"
proof -
  obtain h terminal where stop:
    "comma_decade_block_power 5 (Comma_Decade 5 x) = Comma_Block_Stop h terminal"
    using comma_p5_entry_B32_stop[OF offset] by blast
  have summary: "comma_decade_exact_summary (Comma_Decade 5 x) h terminal"
    by (rule comma_decade_block_power_stop(2)[OF stop])
  have admitted: "comma_decade_admitted (Comma_Decade 5 x)" using offset by simp
  obtain fuel where run:
    "comma_finite_run fuel 5 (Comma_Entry 1 0 x) =
      Some (comma_summary_outcome h terminal)"
    using comma_decade_exact_summary_run[OF summary admitted] by simp
  have erased:
    "map_option fst (comma_finite_weighted_run fuel 5 (Comma_Entry 1 0 x)) =
      Some (comma_summary_outcome h terminal)"
    using comma_finite_weighted_erasure[of fuel 5 "Comma_Entry 1 0 x"] run by simp
  obtain weight terminal_position where weighted:
    "comma_finite_weighted_run fuel 5 (Comma_Entry 1 0 x) =
      Some (comma_summary_outcome h terminal,weight,terminal_position)"
    using erased
    by (cases "comma_finite_weighted_run fuel 5 (Comma_Entry 1 0 x)")
      (auto split: prod.splits)
  obtain rows where trace:
      "comma_indexed_trace 5 (Comma_Entry 1 0 x) rows
        (comma_summary_outcome h terminal) terminal_position"
    and weight: "sum_list (map fst rows) = weight"
    using comma_weighted_run_indexed_trace[OF weighted] by blast
  have exponent5: "5 \<le> (5::nat)" by simp
  have unique: "comma_unique_literal_path weight (100000+x)
      (comma_chart_value 5 terminal_position)"
    using comma_source_indexed_unique_path[OF trace exponent5] weight
    by (simp add: comma_chart_value_def)
  obtain path :: "nat \<Rightarrow> nat" where initial: "path 0 = 100000+x"
    and edges: "\<And>j. comma_child (path j) (path (Suc j))"
    using infinite by blast
  have actual: "comma_literal_path weight (100000+x) (path weight)"
    using comma_infinite_literal_prefix[where path=path and n=weight, OF edges] initial by simp
  have endpoint: "path weight = comma_chart_value 5 terminal_position"
    by (rule comma_unique_literal_path_endpoint[OF unique actual])
  show ?thesis
  proof (cases terminal)
    case Comma_Terminal_Landmine
    have terminal_trace:
      "comma_indexed_trace 5 (Comma_Entry 1 0 x) rows
        (Comma_Landmine_At h) terminal_position"
      using trace by (simp add: Comma_Terminal_Landmine)
    have no_child: "\<nexists>v. comma_child (comma_chart_value 5 terminal_position) v"
      by (rule comma_weighted_landmine_no_literal_child[OF _
        comma_indexed_trace_terminal_landmine[OF terminal_trace]]) simp
    show ?thesis using no_child edges[of weight] endpoint by simp
  next
    case (Comma_Terminal_Fork a)
    have terminal_trace:
      "comma_indexed_trace 5 (Comma_Entry 1 0 x) rows
        (Comma_Fork_At a h) terminal_position"
      using trace by (simp add: Comma_Terminal_Fork)
    have fork:
      "comma_weighted_step (5 mod 924) terminal_position =
        Comma_WFork terminal_position a h"
      by (rule comma_indexed_trace_terminal_fork[OF terminal_trace])
    have children: "comma_child (comma_chart_value 5 terminal_position) v \<longleftrightarrow>
        v = comma_near_boundary a (5+h) \<or> v = comma_zero_boundary a (5+h)" for v
      by (rule comma_weighted_fork_literal_children[OF _ fork]) simp
    have actual_child: "comma_child (comma_chart_value 5 terminal_position)
        (path (Suc weight))"
      using edges[of weight] endpoint by simp
    have alternatives: "path (Suc weight) = comma_near_boundary a (5+h) \<or>
        path (Suc weight) = comma_zero_boundary a (5+h)"
      using iffD1[OF children actual_child] .
    have kind_valid: "comma_boundary_valid (kind,a,(5+h) mod 924)" for kind
      using comma_weighted_fork_boundary_valid[OF fork, where kind=kind and r="5+h"] by simp
    have near_unranked:
      "path (Suc weight) = comma_near_boundary a (5+h) \<Longrightarrow>
       comma_rank_candidate (Comma_N,a,(5+h) mod 924) = None"
    proof -
      assume chosen: "path (Suc weight) = comma_near_boundary a (5+h)"
      have initial_tail: "path (Suc weight) =
          comma_boundary_value (Comma_N,a,(5+h) mod 924) (5+h)"
        using chosen by (simp add: comma_boundary_value_def comma_near_boundary_def)
      have tail: "\<exists>tail :: nat \<Rightarrow> nat.
          tail 0 = comma_boundary_value (Comma_N,a,(5+h) mod 924) (5+h) \<and>
          (\<forall>j. comma_child (tail j) (tail (Suc j)))"
        by (rule exI[of _ "\<lambda>j. path (Suc weight+j)"])
          (use initial_tail edges in simp)
      show ?thesis
        by (rule comma_infinite_boundary_is_unranked[OF kind_valid])
          (use tail in simp_all)
    qed
    have zero_unranked:
      "path (Suc weight) = comma_zero_boundary a (5+h) \<Longrightarrow>
       comma_rank_candidate (Comma_Z,a,(5+h) mod 924) = None"
    proof -
      assume chosen: "path (Suc weight) = comma_zero_boundary a (5+h)"
      have initial_tail: "path (Suc weight) =
          comma_boundary_value (Comma_Z,a,(5+h) mod 924) (5+h)"
        using chosen by (simp add: comma_boundary_value_def comma_zero_boundary_def)
      have tail: "\<exists>tail :: nat \<Rightarrow> nat.
          tail 0 = comma_boundary_value (Comma_Z,a,(5+h) mod 924) (5+h) \<and>
          (\<forall>j. comma_child (tail j) (tail (Suc j)))"
        by (rule exI[of _ "\<lambda>j. path (Suc weight+j)"])
          (use initial_tail edges in simp)
      show ?thesis
        by (rule comma_infinite_boundary_is_unranked[OF kind_valid])
          (use tail in simp_all)
    qed
    have open_rank:
      "comma_rank_candidate (Comma_N,a,(5+h) mod 924) = None \<or>
       comma_rank_candidate (Comma_Z,a,(5+h) mod 924) = None"
      using alternatives near_unranked zero_unranked by blast
    show ?thesis using stop open_rank
      by (simp add: comma_p5_entry_future_open_def Comma_Terminal_Fork)
  qed
qed

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
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_child_strict_growth comma_child_increment_bound comma_child_parent
      comma_decimal_root_of_root comma_decimal_root_of_child
      comma_decimal_root_of_literal_path comma_decimal_root_properties
      comma_infinite_path_linear_growth comma_infinite_root_first_p5_entry
      comma_p5_entry_B32_complete_checked comma_p5_entry_future_open_checked
      comma_p5_entry_B32_stop comma_weighted_fork_boundary_valid
      comma_infinite_boundary_is_unranked comma_p5_entry_infinite_imp_open
      comma_source20_entry_children comma_p5_open_entries_have_root20
      comma_unique_infinite_decimal_root
      comma_other_decimal_roots_have_no_infinite_literal_path
      comma_decimal_root_infinite_iff_20 comma_global_release_safety})
    then () else error "Global comma root-safety theorem depends on an oracle";
\<close>

end
