theory Comma_Future_M204_Select_Fold
  imports Comma_Future_M204_Source_Join
begin

lemma comma_future_m204_select_fold:
  "fold (\<lambda>label tail. if code=label then value label else tail) labels initial =
    (if code \<in> set labels then value code else initial)"
  by (induction labels arbitrary: initial)
     (auto simp: fold_Cons split: if_splits)

lemma comma_future_m204_select_fold_covered:
  assumes covered: "code=0 \<or> code \<in> set labels"
    and positive: "0 \<notin> set labels"
  shows "fold (\<lambda>label tail. if code=label then value label else tail) labels 0 =
    (if code=0 then 0 else value code)"
  using covered positive by (auto simp: comma_future_m204_select_fold)

lemma comma_future_m204_eval_phase_covered:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and root: "root < length nodes"
    and cover: "comma_crt_mdd_payload_cover nodes root labels"
    and evaluation: "comma_crt_mdd_eval_phase radices nodes phase root = Some value"
  shows "value \<in> set labels"
proof -
  have raw: "comma_crt_mdd_eval_raw radices nodes (\<lambda>_. phase) root = Some value"
    using evaluation wf by (simp only: comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def if_True)
  show ?thesis by (rule comma_crt_mdd_eval_raw_payload_covered[OF wf root cover raw])
qed

end
