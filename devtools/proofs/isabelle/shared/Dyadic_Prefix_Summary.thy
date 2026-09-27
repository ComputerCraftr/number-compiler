theory Dyadic_Prefix_Summary
  imports Dyadic_Source_Lift "Prefix_Effect_Core.Prefix_Effect"
begin

lemma (in dyadic_source_action) dyadic_source_prefix_summary_append:
  "prefix_summary weight (dyadic_source_word step label source (first + second)) =
    (let left = prefix_summary weight
         (dyadic_source_word step label source first);
         right = prefix_summary weight
         (dyadic_source_word step label
           (dyadic_source_orbit step source first) second)
     in (fst left + fst right, min (snd left) (fst left + snd right)))"
  by (simp add: dyadic_source_word_append prefix_summary_append Let_def)

lemma (in dyadic_source_action) dyadic_source_prefix_summary_high_fiber:
  "prefix_summary weight
      (dyadic_source_word step label (source + 2^n * lift_amount) n) =
    prefix_summary weight (dyadic_source_word step label source n)"
  using exact_precision_source_lift[of source n lift_amount] by simp

lemma (in dyadic_source_action) dyadic_source_prefix_summary_low_cylinder:
  "prefix_summary weight (dyadic_source_word step label source n) =
    prefix_summary weight
      (dyadic_source_word step label (source mod 2^n) n)"
  using source_residue_lift[of source n] by simp

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms dyadic_source_action.dyadic_source_prefix_summary_append
      dyadic_source_action.dyadic_source_prefix_summary_high_fiber
      dyadic_source_action.dyadic_source_prefix_summary_low_cylinder})
    then () else error "Dyadic prefix summary depends on an oracle";
\<close>

end
