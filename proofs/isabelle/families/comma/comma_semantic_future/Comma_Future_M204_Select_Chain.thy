theory Comma_Future_M204_Select_Chain
  imports Comma_Future_M204_Select_Map
begin

type_synonym comma_future_m204_select_step = "nat \<times> nat \<times> nat \<times> nat"

fun comma_future_m204_select_chain ::
  "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_future_m204_select_step list \<Rightarrow> bool" where
  "comma_future_m204_select_chain evaluate code initial [] = True"
| "comma_future_m204_select_chain evaluate code initial ((label,yes,no,out)#steps) =
    (no=initial \<and> evaluate out = (if code=label then evaluate yes else evaluate no) \<and>
      comma_future_m204_select_chain evaluate code out steps)"

lemma comma_future_m204_select_chain_exact:
  assumes checked: "comma_future_m204_select_chain evaluate code initial steps"
  shows "evaluate (fold (\<lambda>(label,yes,no,out) _. out) steps initial) =
    fold (\<lambda>(label,yes,no,out) tail. if code=label then evaluate yes else tail)
      steps (evaluate initial)"
  using checked
  by (induction steps arbitrary: initial)
     (auto simp: fold_Cons split: prod.splits if_splits)

lemma comma_future_m204_select_chain_map:
  assumes checked: "comma_future_m204_select_chain evaluate code initial steps"
  shows "evaluate (fold (\<lambda>(label,yes,no,out) _. out) steps initial) =
    (case map_of (rev (map (\<lambda>(label,yes,no,out). (label,yes)) steps)) code of
      None \<Rightarrow> evaluate initial | Some root \<Rightarrow> evaluate root)"
proof -
  have selection: "fold (\<lambda>(label,yes,no,out) tail.
      if code=label then evaluate yes else tail) steps (evaluate initial) =
    fold (\<lambda>(label,yes) tail. if code=label then evaluate yes else tail)
      (map (\<lambda>(label,yes,no,out). (label,yes)) steps) (evaluate initial)"
    by (induction steps arbitrary: initial)
       (auto simp: fold_Cons split: prod.splits)
  show ?thesis using comma_future_m204_select_chain_exact[OF checked] selection
    comma_future_m204_select_pairs[of code evaluate
      "map (\<lambda>(label,yes,no,out). (label,yes)) steps" "evaluate initial"]
    by simp
qed

end
