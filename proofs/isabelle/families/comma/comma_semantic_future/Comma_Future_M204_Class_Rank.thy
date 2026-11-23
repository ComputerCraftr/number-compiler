theory Comma_Future_M204_Class_Rank
  imports Comma_Semantic_Future
begin

text \<open>Rows are proposed semantic classes, not source occurrences.  Their
  properties require kernel checking and a separate source-to-class refinement.\<close>

type_synonym comma_future_m204_row = "nat option \<times> nat list \<times> nat option"

definition comma_future_m204_valid :: "comma_future_m204_row list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_future_m204_valid rows c \<longleftrightarrow> c < length rows"

definition comma_future_m204_rank :: "comma_future_m204_row list \<Rightarrow> nat \<Rightarrow> nat option" where
  "comma_future_m204_rank rows c = (if c < length rows then snd (snd (rows ! c)) else None)"

definition comma_future_m204_step :: "comma_future_m204_row list \<Rightarrow> nat \<Rightarrow> comma_future_control option" where
  "comma_future_m204_step rows c =
    (if c < length rows then
       Some (case fst (rows ! c) of None \<Rightarrow> Comma_Future_Landmine
         | Some digit \<Rightarrow> Comma_Future_Fork digit)
     else None)"

definition comma_future_m204_children :: "comma_future_m204_row list \<Rightarrow> nat \<Rightarrow> comma_future_control \<Rightarrow> nat list" where
  "comma_future_m204_children rows c control =
    (if comma_future_m204_step rows c = Some control
     then fst (snd (rows ! c)) else [])"

definition comma_future_m204_row_checked :: "comma_future_m204_row list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_future_m204_row_checked rows c \<longleftrightarrow>
    c < length rows \<and>
    (case rows ! c of (control, children, rank) \<Rightarrow>
      list_all (\<lambda>child. child < length rows) children \<and>
      (case control of None \<Rightarrow> children = []
       | Some digit \<Rightarrow> 2 \<le> digit \<and> digit \<le> 9 \<and> length children = 2)) \<and>
    comma_semantic_rank_row_checked (comma_future_m204_rank rows)
      (comma_future_m204_children rows) (comma_future_m204_step rows) c"

definition comma_future_m204_branch_rank ::
  "nat option \<Rightarrow> nat option \<Rightarrow> nat option \<Rightarrow> bool" where
  "comma_future_m204_branch_rank rank north south \<longleftrightarrow>
    (case rank of None \<Rightarrow> (north=None) \<noteq> (south=None)
     | Some k \<Rightarrow> (case north of None \<Rightarrow> False | Some n \<Rightarrow> n<k) \<and>
        (case south of None \<Rightarrow> False | Some z \<Rightarrow> z<k))"

lemma comma_future_m204_rank_at:
  assumes "c < length rows" "rows ! c = (control,children,k)"
  shows "comma_future_m204_rank rows c = k"
  using assms by (simp add: comma_future_m204_rank_def)

lemma comma_future_m204_checked_landmine_row:
  assumes "c < length rows" "rows ! c = (None,[],Some k)"
  shows "comma_future_m204_row_checked rows c"
  using assms by (simp add: comma_future_m204_row_checked_def
    comma_future_m204_step_def comma_future_m204_rank_def
    comma_future_m204_children_def comma_semantic_rank_row_checked_def)

lemma comma_future_m204_checked_fork_row:
  assumes bound: "c < length rows" "n < length rows" "z < length rows"
    and digit: "2 \<le> d" "d \<le> 9"
    and selected: "rows ! c = (Some d,[n,z],k)"
    and children: "comma_future_m204_rank rows n = north"
      "comma_future_m204_rank rows z = south"
    and rank: "comma_future_m204_branch_rank k north south"
  shows "comma_future_m204_row_checked rows c"
proof -
  have rank_here: "comma_future_m204_rank rows c = k"
    by (rule comma_future_m204_rank_at[OF bound(1) selected])
  show ?thesis using rank bound digit
    by (cases k; cases north; cases south;
        simp add: comma_future_m204_branch_rank_def comma_future_m204_row_checked_def
          comma_future_m204_step_def comma_future_m204_children_def
          comma_semantic_rank_row_checked_def selected children rank_here)
qed

lemma comma_future_m204_checked_interval_join:
  assumes "a \<le> b" "b \<le> c"
    "list_all P [a..<b]" "list_all P [b..<c]"
  shows "list_all P [a..<c]"
proof -
  have "[a..<c] = [a..<b] @ [b..<c]"
    using assms(1,2) upt_add_eq_append[of a b "c-b"] by simp
  then show ?thesis using assms(3,4) by (simp add: list_all_append)
qed

lemma comma_future_m204_checked_rank:
  assumes checked: "list_all (comma_future_m204_row_checked rows) [0..<length rows]"
  shows "comma_semantic_rank_check (comma_future_m204_valid rows)
    (comma_future_m204_rank rows) (comma_future_m204_children rows)
    (comma_future_m204_step rows)"
  using checked
  by (auto simp: comma_semantic_rank_check_def comma_future_m204_valid_def
      comma_future_m204_row_checked_def list_all_iff)

text \<open>The terminating part of an ordered quotient graph is defined by
its reachable actions.  The optional natural rank is a derived witness for
the same inductive property.\<close>

inductive comma_future_m204_finite :: "comma_future_m204_row list \<Rightarrow> nat \<Rightarrow> bool"
  for rows where
  landmine: "comma_future_m204_valid rows q \<Longrightarrow>
    comma_future_m204_step rows q = Some Comma_Future_Landmine \<Longrightarrow>
    comma_future_m204_finite rows q"
| fork: "comma_future_m204_valid rows q \<Longrightarrow>
    comma_future_m204_step rows q = Some (Comma_Future_Fork digit) \<Longrightarrow>
    (\<And>child. child \<in> set (comma_future_m204_children rows q (Comma_Future_Fork digit))
      \<Longrightarrow> comma_future_m204_finite rows child) \<Longrightarrow>
    comma_future_m204_finite rows q"

lemma comma_future_m204_checked_children_valid:
  assumes row: "comma_future_m204_row_checked rows q"
    and step: "comma_future_m204_step rows q = Some control"
    and child: "child \<in> set (comma_future_m204_children rows q control)"
  shows "comma_future_m204_valid rows child"
  using row step child
  by (auto simp: comma_future_m204_row_checked_def comma_future_m204_valid_def
      comma_future_m204_children_def list_all_iff split: prod.splits option.splits)

theorem comma_future_m204_finite_from_rank:
  assumes checked: "list_all (comma_future_m204_row_checked rows) [0..<length rows]"
    and valid: "comma_future_m204_valid rows q"
    and rank: "comma_future_m204_rank rows q = Some k"
  shows "comma_future_m204_finite rows q"
proof -
  have rank_check: "comma_semantic_rank_check (comma_future_m204_valid rows)
    (comma_future_m204_rank rows) (comma_future_m204_children rows)
    (comma_future_m204_step rows)"
    by (rule comma_future_m204_checked_rank[OF checked])
  have ranked: "\<And>n q. comma_future_m204_valid rows q \<Longrightarrow>
      comma_future_m204_rank rows q = Some n \<Longrightarrow>
      comma_future_m204_finite rows q"
  proof -
    fix n
    show "\<And>q. comma_future_m204_valid rows q \<Longrightarrow>
      comma_future_m204_rank rows q = Some n \<Longrightarrow>
      comma_future_m204_finite rows q"
    proof (induction n rule: less_induct)
      case (less n)
      fix q
      assume q_valid: "comma_future_m204_valid rows q"
        and q_rank: "comma_future_m204_rank rows q = Some n"
      have row: "comma_future_m204_row_checked rows q"
        using checked q_valid by (simp add: comma_future_m204_valid_def list_all_iff)
      obtain control where step: "comma_future_m204_step rows q = Some control"
        using comma_semantic_rank_check_row[OF rank_check q_valid]
        by (cases "comma_future_m204_step rows q")
           (auto simp: comma_semantic_rank_row_checked_def)
      show "comma_future_m204_finite rows q"
      proof (cases control)
        case Comma_Future_Landmine
        show ?thesis by (rule comma_future_m204_finite.landmine[OF q_valid])
          (use step Comma_Future_Landmine in simp)
      next
        case (Comma_Future_Fork digit)
        have fork_step: "comma_future_m204_step rows q = Some (Comma_Future_Fork digit)"
          using step Comma_Future_Fork by simp
        have lower: "\<forall>child\<in>set (comma_future_m204_children rows q (Comma_Future_Fork digit)).
          \<exists>j<n. comma_future_m204_rank rows child = Some j"
          by (rule comma_semantic_rank_check_fork_decreases[OF rank_check q_valid q_rank fork_step])
        show ?thesis
        proof (rule comma_future_m204_finite.fork[OF q_valid fork_step])
          fix child
          assume member: "child \<in> set (comma_future_m204_children rows q (Comma_Future_Fork digit))"
          obtain j where j: "j<n" "comma_future_m204_rank rows child = Some j"
            using lower member by blast
          have child_valid: "comma_future_m204_valid rows child"
            by (rule comma_future_m204_checked_children_valid[OF row fork_step member])
          show "comma_future_m204_finite rows child"
            by (rule less.IH[OF j(1) child_valid j(2)])
        qed
      qed
    qed
  qed
  show ?thesis by (rule ranked[OF valid rank])
qed

theorem comma_future_m204_rank_from_finite:
  assumes checked: "list_all (comma_future_m204_row_checked rows) [0..<length rows]"
    and finite: "comma_future_m204_finite rows q"
  shows "comma_future_m204_rank rows q \<noteq> None"
  using finite
proof (induction rule: comma_future_m204_finite.induct)
  case (landmine q)
  have row: "comma_future_m204_row_checked rows q"
    using checked landmine.hyps(1) by (simp add: comma_future_m204_valid_def list_all_iff)
  show ?case using row landmine.hyps(2)
    by (auto simp: comma_future_m204_row_checked_def comma_semantic_rank_row_checked_def)
next
  case (fork q digit)
  have row: "comma_future_m204_row_checked rows q"
    using checked fork.hyps(1) by (simp add: comma_future_m204_valid_def list_all_iff)
  have none: "filter (\<lambda>child. comma_future_m204_rank rows child = None)
      (comma_future_m204_children rows q (Comma_Future_Fork digit)) = []"
    using fork.IH by (auto simp: filter_empty_conv)
  show ?case using row fork.hyps(2) none
    by (cases "comma_future_m204_rank rows q")
       (auto simp: comma_future_m204_row_checked_def comma_semantic_rank_row_checked_def)
qed

corollary comma_future_m204_finite_iff_ranked:
  assumes checked: "list_all (comma_future_m204_row_checked rows) [0..<length rows]"
    and valid: "comma_future_m204_valid rows q"
  shows "comma_future_m204_finite rows q \<longleftrightarrow> comma_future_m204_rank rows q \<noteq> None"
proof
  assume finite: "comma_future_m204_finite rows q"
  show "comma_future_m204_rank rows q \<noteq> None"
    by (rule comma_future_m204_rank_from_finite[OF checked finite])
next
  assume ranked: "comma_future_m204_rank rows q \<noteq> None"
  obtain k where rank: "comma_future_m204_rank rows q = Some k"
    using ranked by (cases "comma_future_m204_rank rows q") auto
  show "comma_future_m204_finite rows q"
    by (rule comma_future_m204_finite_from_rank[OF checked valid rank])
qed

end
