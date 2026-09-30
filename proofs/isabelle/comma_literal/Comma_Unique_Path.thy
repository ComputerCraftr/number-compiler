theory Comma_Unique_Path
  imports Comma_Macro_Selection
begin

text \<open>A unique path records all children at each preceding point, while
leaving the terminal point unrestricted. This distinguishes arrival at a fork
from choosing either of its children.\<close>

inductive comma_unique_literal_path ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  zero: "comma_unique_literal_path 0 k k"
| step: "(\<And>v. comma_child k v \<longleftrightarrow> v = next) \<Longrightarrow>
    comma_unique_literal_path n next target \<Longrightarrow>
    comma_unique_literal_path (Suc n) k target"

lemma comma_unique_literal_path_append:
  assumes "comma_unique_literal_path n source middle"
    "comma_unique_literal_path m middle target"
  shows "comma_unique_literal_path (n + m) source target"
  using assms
  by (induction arbitrary: m target rule: comma_unique_literal_path.induct)
    (auto intro: comma_unique_literal_path.intros)

lemma comma_unique_literal_path_literal:
  assumes "comma_unique_literal_path n source target"
  shows "comma_literal_path n source target"
  using assms by (induction rule: comma_unique_literal_path.induct)
    (auto intro: comma_literal_path.intros)

lemma comma_unique_literal_path_endpoint:
  assumes "comma_unique_literal_path n source target"
    "comma_literal_path n source other"
  shows "other = target"
  using assms
proof (induction arbitrary: other rule: comma_unique_literal_path.induct)
  case (zero k)
  then show ?case by (cases rule: comma_literal_path.cases) auto
next
  case (step k successor n target)
  from step.prems obtain first where first:
    "comma_child k first" "comma_literal_path n first other"
    by (cases rule: comma_literal_path.cases) auto
  have "first = successor" using step.hyps(1) first(1) by blast
  then show ?case using step.IH first(2) by simp
qed

lemma comma_unique_literal_path_from_points:
  assumes edges: "\<And>j v. j < n \<Longrightarrow>
    (comma_child (point j) v \<longleftrightarrow> v = point (Suc j))"
  shows "comma_unique_literal_path n (point 0) (point n)"
  using edges
proof (induction n arbitrary: point)
  case 0
  then show ?case by (simp add: comma_unique_literal_path.zero)
next
  case (Suc n)
  have suffix_edges: "comma_child (point (Suc j)) v \<longleftrightarrow>
      v = point (Suc (Suc j))" if "j < n" for j v
    using Suc.prems[of "Suc j" v] that by simp
  have suffix: "comma_unique_literal_path n (point 1) (point (Suc n))"
    using Suc.IH[where point="\<lambda>j. point (Suc j)", OF suffix_edges] by (simp add: One_nat_def)
  have first: "comma_child (point 0) v \<longleftrightarrow> v = point 1" for v
    using Suc.prems[of 0 v] by (simp add: One_nat_def)
  show ?case using comma_unique_literal_path.step[OF first suffix] .
qed

lemma comma_source_chart_step_unique:
  assumes exponent: "5 \<le> p"
    and step: "comma_weighted_step (p mod 924) source =
      Comma_WNext next weight"
    and index: "j < comma_chart_weight_value p weight"
  shows "comma_child (comma_chart_fragment_point p source next j) v
    \<longleftrightarrow>
    v = comma_chart_fragment_point p source next (Suc j)"
proof (cases source)
  case (Comma_Entry f delta offset)
  have valid: "1 \<le> f" "f \<le> 9" "offset \<le> 98"
    using step by (auto simp: Comma_Entry comma_weighted_step_def
      Let_def split: if_splits)
  let ?h = "comma_finite_headroom f (p mod 924) delta offset"
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?L = "comma_cycle_length f"
  let ?c = "(10 ^ (p + delta) - offset - ?h) div ?P"
  have chart_step: "comma_weighted_step (p mod 924)
      (Comma_Entry f delta offset) = Comma_WNext next weight"
    using step by (simp only: Comma_Entry)
  have emitted: "comma_finite_next_weight p (Comma_Entry f delta offset) =
      comma_chart_weight_value p weight"
    by (simp only: comma_finite_next_weight_def chart_step comma_weighted_move.case)
  have period_weight: "comma_finite_next_weight p
      (Comma_Entry f delta offset) = ?c * ?L"
    using comma_entry_chart_exact_literal_path(2)
      [where delta=delta, OF valid(1,2) exponent valid(3)] .
  have amount: "comma_chart_weight_value p weight = ?c * ?L"
    using emitted[symmetric] period_weight by (rule trans)
  show ?thesis
    using comma_entry_chart_exact_literal_path(5)
      [where delta=delta, OF valid(1,2) exponent valid(3)] index amount
    by (auto simp: Comma_Entry)
next
  case (Comma_Near f delta H)
  have chart_step: "comma_weighted_step (p mod 924)
      (Comma_Near f delta H) = Comma_WNext next weight"
    using step by (simp only: Comma_Near)
  have finite: "comma_finite_step (p mod 924)
      (Comma_Near f delta H) = Comma_Next next"
    by (simp only: comma_finite_step_def chart_step comma_erase_weight.simps)
  have valid: "1 \<le> f" "f \<le> 9" "1 \<le> H" "H \<le> 540"
    using comma_near_success_admissible[of "p mod 924" f delta H]
      finite by auto
  have sector: "comma_sector f (p + delta)
      (comma_chart_value p (Comma_Near f delta H))"
    using comma_near_chart_checked_sector[OF valid(1,2) exponent valid(3,4)] .
  have large: "2 \<le> p + delta" using exponent by simp
  have children: "comma_child (comma_chart_value p (Comma_Near f delta H)) v
      \<longleftrightarrow> v = comma_chart_value p next"
    using comma_large_children_complete[OF sector large, of v]
      comma_near_chart_next_literal(3)
        [OF valid(1,2) exponent valid(3,4) finite] by simp
  have emitted: "comma_finite_next_weight p (Comma_Near f delta H) =
      comma_chart_weight_value p weight"
    by (simp only: comma_finite_next_weight_def chart_step comma_weighted_move.case)
  have unit: "comma_finite_next_weight p (Comma_Near f delta H) = 1"
    using comma_near_chart_next_literal(2)
      [OF valid(1,2) exponent valid(3,4) finite] .
  have amount: "comma_chart_weight_value p weight = 1"
    using emitted[symmetric] unit by (rule trans)
  have zero: "j = 0" using index amount by simp
  show ?thesis using children by (simp add: Comma_Near zero)
qed

lemma comma_source_chart_unique_path:
  assumes exponent: "5 \<le> p"
    and step: "comma_weighted_step (p mod 924) source =
      Comma_WNext next weight"
  shows "comma_unique_literal_path (comma_chart_weight_value p weight)
    (comma_chart_value p source) (comma_chart_value p next)"
proof -
  have points: "comma_unique_literal_path (comma_chart_weight_value p weight)
      (comma_chart_fragment_point p source next 0)
      (comma_chart_fragment_point p source next (comma_chart_weight_value p weight))"
    by (rule comma_unique_literal_path_from_points;
        rule comma_source_chart_step_unique[OF exponent step]; assumption)
  have refined: "comma_chart_step_refined p source next weight"
    using comma_admitted_weighted_step_refined[OF exponent step] .
  show ?thesis using points refined
    by (simp add: comma_chart_step_refined_def Let_def)
qed

lemma comma_source_indexed_unique_path:
  assumes trace: "comma_indexed_trace p source rows outcome terminal"
    and exponent: "5 \<le> p"
  shows "comma_unique_literal_path (sum_list (map fst rows))
    (comma_chart_value p source) (comma_chart_value p terminal)"
  using trace exponent
proof (induction rule: comma_indexed_trace.induct)
  case (fork p position a delta)
  then show ?case by (simp add: comma_unique_literal_path.zero)
next
  case (landmine p position delta)
  then show ?case by (simp add: comma_unique_literal_path.zero)
next
  case (advance p position successor weight rows outcome terminal)
  have local: "comma_unique_literal_path (comma_chart_weight_value p weight)
      (comma_chart_value p position) (comma_chart_value p successor)"
    using comma_source_chart_unique_path[OF advance.prems advance.hyps(1)] .
  show ?case
    using comma_unique_literal_path_append[OF local advance.IH[OF advance.prems]]
    by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_unique_literal_path_append comma_unique_literal_path_literal
      comma_unique_literal_path_endpoint comma_unique_literal_path_from_points
      comma_source_chart_step_unique comma_source_chart_unique_path
      comma_source_indexed_unique_path})
    then () else error "Comma generic unique path depends on an oracle";
\<close>
end
