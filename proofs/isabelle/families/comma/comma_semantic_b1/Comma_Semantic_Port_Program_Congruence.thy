theory Comma_Semantic_Port_Program_Congruence
  imports Comma_Semantic_Phase_Program_Source_Specialization
begin

text \<open>
These congruence theorems justify reuse by the normalized typed program key.
They identify only the local selected port action and its exact B1 result.
Physical occurrence shifts, elapsed weights, and source-bound writer
authority remain outside the key and are transported by their own contracts.
\<close>

lemma comma_phase_entry_program_same_key_congruence:
  fixes f f' x x' phase :: nat
  assumes canonical_left:
      "comma_canonical_position_admitted (Comma_Entry f 0 x)"
    and admitted_left: "comma_round_admitted (Comma_Entry f 0 x)"
    and normalized_left:
      "Comma_Entry f 0 x =
        comma_source_continuation_base (Comma_Entry f 0 x)"
    and canonical_right:
      "comma_canonical_position_admitted (Comma_Entry f' 0 x')"
    and admitted_right: "comma_round_admitted (Comma_Entry f' 0 x')"
    and normalized_right:
      "Comma_Entry f' 0 x' =
        comma_source_continuation_base (Comma_Entry f' 0 x')"
    and same_program:
      "comma_semantic_port_program_of_source (Comma_Entry f 0 x) =
        comma_semantic_port_program_of_source (Comma_Entry f' 0 x')"
  shows
    "comma_semantic_b1_source_port_action (Comma_Entry f 0 x) phase =
      comma_semantic_b1_source_port_action (Comma_Entry f' 0 x') phase"
    and
    "comma_semantic_b1_round_output phase (Comma_Entry f 0 x) =
      comma_semantic_b1_round_output phase (Comma_Entry f' 0 x')"
proof -
  have left_bound: "comma_sector_entry_bound f x"
    using canonical_left by simp
  have right_bound: "comma_sector_entry_bound f' x'"
    using canonical_right by simp
  have control_program:
    "comma_entry_control_program f x =
      comma_entry_control_program f' x'"
    using same_program canonical_left canonical_right
    by (simp add: comma_semantic_port_program_of_source_def)
  have selected:
    "comma_phase_program_apply_entry f x (phase mod 924) =
      comma_phase_program_apply_entry f' x' (phase mod 924)"
    by (rule comma_phase_program_apply_entry_same_control
      [OF left_bound right_bound control_program])
  have applied:
    "comma_phase_program_action_at_source phase (Comma_Entry f 0 x) =
      comma_phase_program_action_at_source phase (Comma_Entry f' 0 x')"
    using selected
    by (simp add: comma_phase_program_action_at_source_def)
  have left_exact:
    "comma_phase_program_action_at_source phase (Comma_Entry f 0 x) =
      Some (comma_semantic_b1_source_port_action (Comma_Entry f 0 x) phase)"
    by (rule comma_phase_program_action_at_source_port_exact
      [OF canonical_left admitted_left normalized_left])
  have right_exact:
    "comma_phase_program_action_at_source phase (Comma_Entry f' 0 x') =
      Some (comma_semantic_b1_source_port_action (Comma_Entry f' 0 x') phase)"
    by (rule comma_phase_program_action_at_source_port_exact
      [OF canonical_right admitted_right normalized_right])
  have ports:
    "comma_semantic_b1_source_port_action (Comma_Entry f 0 x) phase =
      comma_semantic_b1_source_port_action (Comma_Entry f' 0 x') phase"
    using applied left_exact right_exact by auto
  have left_output:
    "comma_semantic_b1_source_slot_output phase
        (comma_semantic_b1_source_port_action (Comma_Entry f 0 x) phase) =
      comma_semantic_b1_round_output phase (Comma_Entry f 0 x)"
    by (rule comma_semantic_b1_port_round_output
      [OF admitted_left normalized_left])
  have right_output:
    "comma_semantic_b1_source_slot_output phase
        (comma_semantic_b1_source_port_action (Comma_Entry f' 0 x') phase) =
      comma_semantic_b1_round_output phase (Comma_Entry f' 0 x')"
    by (rule comma_semantic_b1_port_round_output
      [OF admitted_right normalized_right])
  show
    "comma_semantic_b1_source_port_action (Comma_Entry f 0 x) phase =
      comma_semantic_b1_source_port_action (Comma_Entry f' 0 x') phase"
    by (rule ports)
  show
    "comma_semantic_b1_round_output phase (Comma_Entry f 0 x) =
      comma_semantic_b1_round_output phase (Comma_Entry f' 0 x')"
    using left_output right_output ports by simp
qed

lemma comma_phase_near_program_same_key_congruence:
  fixes f f' H H' phase :: nat
  assumes canonical_left:
      "comma_canonical_position_admitted (Comma_Near f 0 H)"
    and admitted_left: "comma_round_admitted (Comma_Near f 0 H)"
    and normalized_left:
      "Comma_Near f 0 H =
        comma_source_continuation_base (Comma_Near f 0 H)"
    and canonical_right:
      "comma_canonical_position_admitted (Comma_Near f' 0 H')"
    and admitted_right: "comma_round_admitted (Comma_Near f' 0 H')"
    and normalized_right:
      "Comma_Near f' 0 H' =
        comma_source_continuation_base (Comma_Near f' 0 H')"
    and same_program:
      "comma_semantic_port_program_of_source (Comma_Near f 0 H) =
        comma_semantic_port_program_of_source (Comma_Near f' 0 H')"
  shows
    "comma_semantic_b1_source_port_action (Comma_Near f 0 H) phase =
      comma_semantic_b1_source_port_action (Comma_Near f' 0 H') phase"
    and
    "comma_semantic_b1_round_output phase (Comma_Near f 0 H) =
      comma_semantic_b1_round_output phase (Comma_Near f' 0 H')"
proof -
  have control_program:
    "comma_near_control_program f H =
      comma_near_control_program f' H'"
    using same_program canonical_left canonical_right
    by (simp add: comma_semantic_port_program_of_source_def)
  have left_exact:
    "comma_phase_program_action_at_source phase (Comma_Near f 0 H) =
      Some (comma_semantic_b1_source_port_action (Comma_Near f 0 H) phase)"
    by (rule comma_phase_program_action_at_source_port_exact
      [OF canonical_left admitted_left normalized_left])
  have right_exact:
    "comma_phase_program_action_at_source phase (Comma_Near f' 0 H') =
      Some (comma_semantic_b1_source_port_action (Comma_Near f' 0 H') phase)"
    by (rule comma_phase_program_action_at_source_port_exact
      [OF canonical_right admitted_right normalized_right])
  have left_eval:
    "comma_phase_program_at_near (comma_near_control_program f H) H phase =
      Some (comma_semantic_b1_source_port_action (Comma_Near f 0 H) phase)"
  proof -
    have clock_eval:
      "comma_phase_program_at_near (comma_near_control_program f H) H
          (phase mod 924) =
        Some (comma_semantic_b1_source_port_action (Comma_Near f 0 H) phase)"
      using left_exact
      by (simp add: comma_phase_program_action_at_source_def)
    have phase_independent:
      "comma_phase_program_at_near (comma_near_control_program f H) H
          (phase mod 924) =
        comma_phase_program_at_near (comma_near_control_program f H) H phase"
      by (rule comma_phase_program_at_near_phase_independent)
    show ?thesis using clock_eval phase_independent by simp
  qed
  have right_eval:
    "comma_phase_program_at_near (comma_near_control_program f' H') H' phase =
      Some (comma_semantic_b1_source_port_action (Comma_Near f' 0 H') phase)"
  proof -
    have clock_eval:
      "comma_phase_program_at_near (comma_near_control_program f' H') H'
          (phase mod 924) =
        Some (comma_semantic_b1_source_port_action (Comma_Near f' 0 H') phase)"
      using right_exact
      by (simp add: comma_phase_program_action_at_source_def)
    have phase_independent:
      "comma_phase_program_at_near (comma_near_control_program f' H') H'
          (phase mod 924) =
        comma_phase_program_at_near (comma_near_control_program f' H') H' phase"
      by (rule comma_phase_program_at_near_phase_independent)
    show ?thesis using clock_eval phase_independent by simp
  qed
  have right_common:
    "comma_phase_program_at_near (comma_near_control_program f H) H' phase =
      Some (comma_semantic_b1_source_port_action (Comma_Near f' 0 H') phase)"
    using right_eval control_program[symmetric] by simp
  have ports:
    "comma_semantic_b1_source_port_action (Comma_Near f 0 H) phase =
      comma_semantic_b1_source_port_action (Comma_Near f' 0 H') phase"
    by (rule comma_phase_program_at_near_output_unique
      [OF left_eval right_common])
  have left_output:
    "comma_semantic_b1_source_slot_output phase
        (comma_semantic_b1_source_port_action (Comma_Near f 0 H) phase) =
      comma_semantic_b1_round_output phase (Comma_Near f 0 H)"
    by (rule comma_semantic_b1_port_round_output
      [OF admitted_left normalized_left])
  have right_output:
    "comma_semantic_b1_source_slot_output phase
        (comma_semantic_b1_source_port_action (Comma_Near f' 0 H') phase) =
      comma_semantic_b1_round_output phase (Comma_Near f' 0 H')"
    by (rule comma_semantic_b1_port_round_output
      [OF admitted_right normalized_right])
  show
    "comma_semantic_b1_source_port_action (Comma_Near f 0 H) phase =
      comma_semantic_b1_source_port_action (Comma_Near f' 0 H') phase"
    by (rule ports)
  show
    "comma_semantic_b1_round_output phase (Comma_Near f 0 H) =
      comma_semantic_b1_round_output phase (Comma_Near f' 0 H')"
    using left_output right_output ports by simp
qed

lemma comma_phase_program_same_key_round_output:
  fixes left right :: comma_finite_position
    and program :: comma_semantic_port_program
  assumes canonical_left: "comma_canonical_position_admitted left"
    and admitted_left: "comma_round_admitted left"
    and normalized_left: "left=comma_source_continuation_base left"
    and left_binding:
      "comma_semantic_port_program_of_source left = Some program"
    and canonical_right: "comma_canonical_position_admitted right"
    and admitted_right: "comma_round_admitted right"
    and normalized_right: "right=comma_source_continuation_base right"
    and right_binding:
      "comma_semantic_port_program_of_source right = Some program"
  shows "\<forall>phase. comma_semantic_b1_round_output phase left =
    comma_semantic_b1_round_output phase right"
proof (rule allI)
  fix phase :: nat
  let ?action = "comma_phase_program_operator_nf program phase"
  have left_selected:
    "comma_phase_program_action_at_source phase left = Some ?action"
    by (rule comma_phase_program_action_at_source_operator_nf
      [OF canonical_left admitted_left normalized_left left_binding])
  have right_selected:
    "comma_phase_program_action_at_source phase right = Some ?action"
    by (rule comma_phase_program_action_at_source_operator_nf
      [OF canonical_right admitted_right normalized_right right_binding])
  have left_output:
    "comma_semantic_b1_source_slot_output phase ?action =
      comma_semantic_b1_round_output phase left"
    by (rule comma_phase_program_action_at_source_selected_round_output
      [OF canonical_left admitted_left normalized_left left_selected])
  have right_output:
    "comma_semantic_b1_source_slot_output phase ?action =
      comma_semantic_b1_round_output phase right"
    by (rule comma_phase_program_action_at_source_selected_round_output
      [OF canonical_right admitted_right normalized_right right_selected])
  show "comma_semantic_b1_round_output phase left =
    comma_semantic_b1_round_output phase right"
    by (rule trans[OF left_output[symmetric] right_output])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Normalized program-key control and output congruence"
    @{thms comma_phase_program_same_key_round_output
      comma_phase_entry_program_same_key_congruence
      comma_phase_near_program_same_key_congruence};
\<close>

end
