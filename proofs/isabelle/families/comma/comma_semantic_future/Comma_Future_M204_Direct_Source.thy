theory Comma_Future_M204_Direct_Source
  imports Comma_Future_M204_Source_Bridge
    Comma_Semantic_B1.Comma_Direct_Action_Constructors
begin

text \<open>The two checked action refinements and the independently admitted
source determine the physical first round.  Neither the expression binding
nor the MDD evaluation is supplied by a candidate table alone.\<close>

lemma comma_future_m204_direct_physical_round:
  assumes evaluated: "comma_crt_mdd_eval_phase radices nodes phase root =
      Some (comma_parametric_typed_mask_code
        (comma_direct_action_interpret expression phase 0))"
    and program_action: "comma_direct_action_interpret expression phase 0 =
      comma_semantic_phase_program_fold comma_phase_program_full_action_output phase program 0"
    and canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source = comma_source_continuation_base source"
    and binding: "comma_semantic_port_program_of_source source = Some program"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (comma_parametric_typed_mask_code
      (comma_phase_program_full_action_output phase
        (comma_decisive_endpoint_round phase source)))"
proof -
  have physical: "comma_semantic_phase_program_round phase program 0 =
      comma_decisive_endpoint_round phase source"
    using comma_semantic_phase_program_round_exact
      [where phase=phase and shift=0, OF canonical admitted normalized binding]
    by (cases source) simp_all
  show ?thesis using evaluated program_action physical
    comma_phase_program_full_action_fold_fusion by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Direct M204 physical source transport" @{thms comma_future_m204_direct_physical_round};
\<close>

end
