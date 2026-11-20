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

end
