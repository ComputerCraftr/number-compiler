theory Comma_Phase_134_Continue_Barrier
  imports Comma_Continue_Image_Bridge
begin

text \<open>A single checked phase barrier for qualitative Continue termination.
The proposed rows carry no authority until the shared class-step store has
checked each complete action. This theorem does not establish B32's bound.\<close>

lemma comma_phase_134_intro:
  assumes "list_all
    (\<lambda>cid. comma_phase_class_continue_power comma_semantic_phase_program_class_step
      k (b,cid) = None) [0..<46]"
  shows "\<forall>cid<46. comma_phase_class_continue_power
    comma_semantic_phase_program_class_step k (b,cid) = None"
  using assms by (simp add: list_all_iff)

lemma comma_phase_134_list_nil: "list_all P []" by simp
lemma comma_phase_134_list_cons:
  assumes "P x" "list_all P xs"
  shows "list_all P (x#xs)" using assms by simp

ML_file "semantic_phase_134_actions.ML"
ML_file "semantic_phase_134_certificate.ML"
local_setup \<open>Comma_Phase_134_Certificate.run\<close>

ML \<open>
  val checked = @{thms comma_continue_phase_134_checked};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Continue phase barrier depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked then
    error "Continue phase barrier contains skipped proofs" else ();
\<close>

end
