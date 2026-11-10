theory Comma_Semantic_Phase_Action_Program_Certificate
  imports Comma_Semantic_Phase_Class_Compiler
begin

text \<open>
The compiler certificate follows the final named CRT action pointwise.  This
cofactor cover lemma is the finite branching step used by that proof: the
selected external clock character chooses exactly one checked cofactor.
It does not identify trees structurally or trust a normalization result.
\<close>

lemma comma_crt_payload_cofactor_cover:
  fixes tree :: "'a comma_semantic_weighted_crt_dag"
    and expected :: "'a option"
  assumes axis: "axis<4"
    and shape: "comma_weighted_crt_shape 0 tree"
    and branches:
      "\<forall>slot<comma_crt_axis_radix axis.
        phase mod comma_crt_axis_radix axis=slot \<longrightarrow>
        comma_crt_payload
          (snd (comma_weighted_crt_cofactor_all_raw axis slot tree)) phase =
          expected"
  shows "comma_crt_payload tree phase=expected"
proof -
  let ?slot = "phase mod comma_crt_axis_radix axis"
  have slot_bound: "?slot<comma_crt_axis_radix axis"
    using comma_crt_axis_cases[OF axis]
    by (auto simp: comma_crt_axis_radix_def)
  have selected: "?slot=phase mod comma_crt_axis_radix axis" by simp
  have branch_value:
    "comma_crt_payload
        (snd (comma_weighted_crt_cofactor_all_raw axis ?slot tree)) phase =
      expected"
    using branches slot_bound selected by blast
  have payload_rebase:
    "comma_crt_payload
        (snd (comma_weighted_crt_cofactor_all_raw axis ?slot tree)) phase =
      comma_crt_payload tree phase"
    by (rule comma_crt_payload_cofactor_selected[OF axis selected shape])
  show ?thesis using branch_value payload_rebase by simp
qed

text \<open>
A local action period observes only the gcd residue of each assigned CRT
coordinate.  The inactive factor of the CRT weight annihilates the remaining
coordinate quotient modulo the local period.
\<close>
lemma comma_crt_weighted_gcd_residue_transport:
  fixes source radix gcd_residue period weight :: nat
  assumes gcd_divides_radix: "gcd_residue dvd radix"
    and period_divides_weighted_gcd: "period dvd weight*gcd_residue"
  shows "(weight*(source mod radix)) mod period =
    (weight*(source mod gcd_residue)) mod period"
proof -
  let ?coordinate = "source mod radix"
  have coordinate_decomposition:
      "?coordinate=(?coordinate div gcd_residue)*gcd_residue+
        ?coordinate mod gcd_residue"
    by (rule sym[OF div_mult_mod_eq])
  have weighted_decomposition:
      "weight*?coordinate=
        (?coordinate div gcd_residue)*(weight*gcd_residue)+
          weight*(?coordinate mod gcd_residue)"
  proof -
    have "weight*?coordinate =
        weight*((?coordinate div gcd_residue)*gcd_residue+
          ?coordinate mod gcd_residue)"
      by (rule arg_cong[OF coordinate_decomposition])
    also have "... = (?coordinate div gcd_residue)*(weight*gcd_residue)+
        weight*(?coordinate mod gcd_residue)"
      by (simp only: algebra_simps)
    finally show ?thesis .
  qed
  obtain quotient where weighted_period:
      "weight*gcd_residue=period*quotient"
    using period_divides_weighted_gcd unfolding dvd_def by blast
  have first_multiple:
      "period dvd ((?coordinate div gcd_residue)*
        (weight*gcd_residue))"
    unfolding weighted_period dvd_def
    by (rule exI[of _ "(?coordinate div gcd_residue)*quotient"])
      (simp add: algebra_simps)
  have first_zero:
      "((?coordinate div gcd_residue)*(weight*gcd_residue)) mod period=0"
    using first_multiple by (simp add: dvd_eq_mod_eq_0)
  have weighted_mod:
      "(weight*?coordinate) mod period =
        (weight*(?coordinate mod gcd_residue)) mod period"
  proof -
    have split_mod:
        "(weight*?coordinate) mod period =
          ((?coordinate div gcd_residue)*(weight*gcd_residue)+
            weight*(?coordinate mod gcd_residue)) mod period"
      by (rule arg_cong[OF weighted_decomposition])
    also have "...=(weight*(?coordinate mod gcd_residue)) mod period"
    proof -
      have "((?coordinate div gcd_residue)*(weight*gcd_residue)+
          weight*(?coordinate mod gcd_residue)) mod period =
        (((?coordinate div gcd_residue)*(weight*gcd_residue)) mod period+
          weight*(?coordinate mod gcd_residue)) mod period"
        by (rule mod_add_left_eq[symmetric])
      also have "...=(weight*(?coordinate mod gcd_residue)) mod period"
        using first_zero by simp
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
  have coordinate_mod:
      "?coordinate mod gcd_residue=source mod gcd_residue"
    by (rule mod_mod_cancel[OF gcd_divides_radix])
  show ?thesis using weighted_mod coordinate_mod by simp
qed

lemma comma_crt_slot_gcd_residue_transport:
  fixes phase radix gcd_residue slot :: nat
  assumes gcd_divides_radix: "gcd_residue dvd radix"
    and selected: "phase mod radix=slot"
  shows "phase mod gcd_residue=slot mod gcd_residue"
proof -
  have "(phase mod radix) mod gcd_residue =
      phase mod gcd_residue"
    by (rule mod_mod_cancel[OF gcd_divides_radix])
  then show ?thesis using selected by simp
qed

lemma comma_phase_program_action_at_source_sampled:
  fixes phase period :: nat
    and actions :: "comma_source_continuation_action list"
  assumes canonical: "comma_canonical_position_admitted source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and binding:
      "comma_semantic_port_program_of_source source=Some program"
    and positive: "0<period"
    and extent: "length actions=period"
    and selector_phase:
      "comma_phase_program_selector_phase program phase=phase mod period"
    and samples:
      "\<forall>slot<period.
        comma_phase_program_operator_nf program slot =
        actions!slot"
  shows "comma_phase_program_action_at_source phase source =
    Some (actions!(phase mod period))"
proof -
  have specialized:
    "comma_phase_program_action_at_source phase source =
      Some (comma_phase_program_operator_nf program (comma_phase_program_selector_phase program phase))"
    by (rule comma_phase_program_action_at_source_selector_operator_nf
      [OF canonical admitted normalized binding])
  have slot_bound: "phase mod period<length actions"
    using positive extent by simp
  have selected:
    "comma_phase_program_operator_nf program (phase mod period) = actions!(phase mod period)"
    using samples slot_bound extent by blast
  show ?thesis using specialized selector_phase selected by simp
qed

ML \<open>
  val source_certificate_rules =
    @{thms comma_crt_payload_cofactor_selected
      comma_crt_weighted_gcd_residue_transport
      comma_crt_slot_gcd_residue_transport
      comma_phase_program_action_at_source_sampled
      comma_phase_program_action_at_source_exact
      comma_weighted_crt_selector_bind_apply
      comma_phase_program_action_at_source_round_output
      comma_semantic_b1_port_round_output
      comma_phase_entry_program_same_key_congruence
      comma_phase_near_program_same_key_congruence};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Comma source-action pointwise certificate" source_certificate_rules;
\<close>

end
