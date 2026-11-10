theory Comma_Semantic_Phase_Class_Action
  imports Comma_Phase_Class_Rank
begin

text \<open>
The phase-free action label is shared by the symbolic class constructor and
the existing packed-mask consumers. The phase remains in the occurrence environment;
only a Continue action advances it.
\<close>

datatype comma_phase_rank_mask_action =
    Comma_Phase_Rank_Mask_Invalid
  | Comma_Phase_Rank_Mask_Fork nat nat
  | Comma_Phase_Rank_Mask_Landmine nat
  | Comma_Phase_Rank_Mask_Continue nat

fun comma_phase_rank_mask_lift ::
    "nat \<Rightarrow> comma_phase_rank_mask_action \<Rightarrow>
      nat comma_phase_class_action"
where
  "comma_phase_rank_mask_lift phase Comma_Phase_Rank_Mask_Invalid =
    Comma_Phase_Class_Invalid"
| "comma_phase_rank_mask_lift phase (Comma_Phase_Rank_Mask_Fork a d) =
    Comma_Phase_Class_Fork a d"
| "comma_phase_rank_mask_lift phase (Comma_Phase_Rank_Mask_Landmine d) =
    Comma_Phase_Class_Landmine d"
| "comma_phase_rank_mask_lift phase (Comma_Phase_Rank_Mask_Continue c) =
    Comma_Phase_Class_Continue ((phase+1) mod 924) c"

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Phase-free action label transport" @{thms comma_phase_rank_mask_lift.simps};
\<close>

end
