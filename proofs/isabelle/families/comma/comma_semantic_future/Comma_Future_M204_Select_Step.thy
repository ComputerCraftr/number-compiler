theory Comma_Future_M204_Select_Step
  imports Comma_Future_M204_Select_Fold
begin

lemma comma_future_m204_select_step:
  fixes evaluate :: "nat \<Rightarrow> nat option"
  assumes source: "evaluate source = Some code"
    and zero: "evaluate false_root = Some 0"
    and one: "evaluate true_root = Some 1"
    and mask: "evaluate guard =
      (case evaluate source of None \<Rightarrow> evaluate false_root
       | Some payload \<Rightarrow> evaluate
           (comma_crt_mdd_bind_target false_root [(label,true_root)] payload))"
    and selection: "evaluate output =
      (case evaluate guard of None \<Rightarrow> evaluate no_root
       | Some payload \<Rightarrow> evaluate
           (comma_crt_mdd_bind_target no_root [(0,no_root),(1,yes_root)] payload))"
  shows "evaluate output = (if code=label then evaluate yes_root else evaluate no_root)"
  using source zero one mask selection
  by (cases "code=label")
     (simp_all add: comma_crt_mdd_bind_target_def)

end
