theory Comma_Future_M204_Select_Map
  imports Comma_Future_M204_Select_Step
begin

lemma comma_future_m204_select_pairs:
  "fold (\<lambda>(label,root) tail. if code=label then evaluate root else tail)
      entries initial =
    (case map_of (rev entries) code of None \<Rightarrow> initial | Some root \<Rightarrow> evaluate root)"
  by (induction entries arbitrary: initial)
     (auto simp: fold_Cons map_of_append split: option.splits prod.splits if_splits)

end
