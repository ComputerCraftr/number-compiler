theory Comma_Guarded_Source_Mask_Evaluator
  imports Comma_Guarded_Source_Right_Transport Comma_Symbolic_Phase_Masks
begin

text \<open>
The result mask is generated from the source's local, typed port actions.
The selector phase remains external: each slot contributes its CRT guard,
and a Goto intersects that guard with the already-computed child result
mask. Terminal payloads are kept as their exact B1 result.  The recursion is
strictly down the sector measure; it is independent of graph CIDs, graph
validity, and any precomputed source/output equality.
\<close>

function comma_guarded_source_output_mask ::
    "comma_finite_position \<Rightarrow> comma_semantic_b1_result \<Rightarrow> nat"
where
  "comma_guarded_source_output_mask source result =
    (if comma_round_admitted source \<and>
        source=comma_source_continuation_base source then
      (let period=comma_decisive_sector_period source in
       comma_indexed_phase_union
         (\<lambda>slot phase. phase mod period=slot)
         (map (\<lambda>slot.
           (case comma_semantic_b1_source_port_action source slot of
              Comma_Continuation_Goto child shift \<Rightarrow>
                (if shift=0 \<and> comma_round_admitted child \<and>
                    child=comma_source_continuation_base child
                 then comma_guarded_source_output_mask child result else 0)
            | action \<Rightarrow>
                (case comma_semantic_b1_terminal_action_result action of
                   Some terminal \<Rightarrow>
                     (if terminal=result then mask 924 else 0)
                 | None \<Rightarrow> 0)))
           [0..<period]))
     else 0)"
  by pat_completeness auto

lemma comma_guarded_source_mask_goto_decreases:
  assumes admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and slot: "slot<comma_decisive_sector_period source"
    and action:
      "comma_semantic_b1_source_port_action source slot =
        Comma_Continuation_Goto child shift"
  shows "shift=0"
    and "child=comma_source_continuation_base child"
    and "9-comma_sector_number child < 9-comma_sector_number source"
    and "comma_round_admitted child"
proof -
  have source_packet:
    "comma_semantic_b1_source_port_action source slot =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet slot source)"
    using comma_semantic_b1_source_port_action_packet[OF admitted, of slot]
      normalized by simp
  have packet_goto:
    "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet slot source) =
      Comma_Continuation_Goto child shift"
    using source_packet action by simp
  have slot_shape:
    "comma_semantic_b1_local_action_shape
      (comma_semantic_b1_source_slot_action source slot)"
    by (rule comma_semantic_b1_source_slot_action_shape[OF admitted normalized])
  have port_shape:
    "comma_semantic_b1_local_action_shape
      (comma_semantic_b1_source_port_action source slot)"
    using slot_shape
      comma_guarded_source_action_at_port[OF admitted normalized, of slot]
      comma_semantic_b1_source_slot_action_refines[OF admitted, of slot]
    by simp
  have shift_zero: "shift=0"
    using packet_goto action port_shape
    by (simp add: comma_semantic_b1_local_action_shape.simps)
  have child_facts:
    "comma_round_admitted child \<and>
      9-comma_sector_number child < 9-comma_sector_number source"
    by (rule comma_source_continuation_goto_decreases[OF admitted packet_goto])
  have child_base: "child=comma_source_continuation_base child"
  proof -
    obtain target move where endpoint:
      "comma_decisive_endpoint_packet slot source=(target,move)"
      by (cases "comma_decisive_endpoint_packet slot source") auto
    have packet_result:
      "comma_source_continuation_action_of_packet (target,move) =
        Comma_Continuation_Goto child shift"
      using packet_goto endpoint by simp
    show ?thesis
    proof (cases move)
      case (Comma_Next successor)
      have next_result:
        "comma_source_continuation_action_of_packet
            (target,Comma_Next successor) =
          Comma_Continuation_Goto child shift"
        using packet_result Comma_Next by simp
      show ?thesis using next_result
        by (auto simp: comma_source_continuation_action_of_packet.simps
            split: if_splits)
    next
      case (Comma_Fork a delta)
      then show ?thesis using packet_result by simp
    next
      case (Comma_Landmine delta)
      then show ?thesis using packet_result by simp
    next
      case Comma_Invalid
      then show ?thesis using packet_result by simp
    qed
  qed
  show "shift=0" by (rule shift_zero)
  show "child=comma_source_continuation_base child" by fact
  show "9-comma_sector_number child < 9-comma_sector_number source"
    using child_facts by simp
  show "comma_round_admitted child" using child_facts by simp
qed

termination
  by (relation
      "measure (\<lambda>(source,result). 9-comma_sector_number source)")
    (auto simp: Let_def set_upt
      split: if_splits comma_source_continuation_action.splits
        option.splits
      intro: comma_guarded_source_mask_goto_decreases)

declare comma_guarded_source_output_mask.simps[simp del]

lemma comma_guarded_source_terminal_mask_member:
  assumes phase: "phase<924"
  shows "comma_phase_member
      (if output=result then mask 924 else 0) phase = (output=result)"
  using phase by (cases "output=result")
    (auto simp: comma_phase_member_def bit_simps)

lemma comma_guarded_source_output_mask_bounded:
  "take_bit 924 (comma_guarded_source_output_mask source result) =
    comma_guarded_source_output_mask source result"
proof (cases "comma_round_admitted source \<and>
    source=comma_source_continuation_base source")
  case True
  have output_eq:
    "comma_guarded_source_output_mask source result =
      comma_indexed_phase_union
        (\<lambda>slot phase. phase mod comma_decisive_sector_period source=slot)
        (map (\<lambda>slot.
          case comma_semantic_b1_source_port_action source slot of
            Comma_Continuation_Goto child shift \<Rightarrow>
              (if shift=0 \<and> comma_round_admitted child \<and>
                  child=comma_source_continuation_base child
               then comma_guarded_source_output_mask child result else 0)
          | action \<Rightarrow>
              (case comma_semantic_b1_terminal_action_result action of
                Some terminal \<Rightarrow>
                  (if terminal=result then mask 924 else 0)
              | None \<Rightarrow> 0))
          [0..<comma_decisive_sector_period source])"
    using comma_guarded_source_output_mask.simps[of source result] True
    by (simp only: if_P Let_def)
  show ?thesis
    unfolding output_eq
    by (rule comma_indexed_phase_union_bounded)
next
  case False
  have gate_false:
    "(comma_round_admitted source \<and>
      source=comma_source_continuation_base source)=False"
    using False by blast
  show ?thesis
  proof -
    have zero:
      "comma_guarded_source_output_mask source result=0"
      using comma_guarded_source_output_mask.simps[of source result] gate_false
      by (simp only: if_False)
    show ?thesis using zero by simp
  qed
qed

lemma comma_guarded_source_output_mask_member_exact:
  assumes admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and phase: "phase<924"
  shows "comma_phase_member
      (comma_guarded_source_output_mask source result) phase =
    (comma_semantic_b1_round_output phase source=result)"
  using admitted normalized phase
proof (induction "9-comma_sector_number source"
    arbitrary: source result phase rule: less_induct)
  case less
  note source_admitted = less.prems(1)
  note source_normalized = less.prems(2)
  note phase_bound = less.prems(3)
  note sector_induction = less.hyps
  let ?period = "comma_decisive_sector_period source"
  let ?slot = "phase mod ?period"
  have period_pair:
    "0<?period \<and> ?period dvd 924"
    by (rule comma_decisive_sector_period_admitted_pair[OF source_admitted])
  have positive: "0<?period" and divides: "?period dvd 924"
    using period_pair by auto
  have slot_bound: "?slot<?period" using positive by simp
  have period_slot: "phase mod ?period=?slot" by simp
  let ?rows =
    "map (\<lambda>slot.
       case comma_semantic_b1_source_port_action source slot of
         Comma_Continuation_Goto child shift \<Rightarrow>
           (if shift=0 \<and> comma_round_admitted child \<and>
               child=comma_source_continuation_base child
            then comma_guarded_source_output_mask child result else 0)
       | action \<Rightarrow>
           (case comma_semantic_b1_terminal_action_result action of
              Some terminal \<Rightarrow>
                (if terminal=result then mask 924 else 0)
            | None \<Rightarrow> 0)) [0..<?period]"
  have rows_length: "length ?rows=?period" by simp
  have selected:
    "comma_phase_member
      (comma_indexed_phase_union (\<lambda>slot phase. phase mod ?period=slot)
        ?rows) phase =
      comma_phase_member (?rows!?slot) phase"
    by (rule comma_indexed_phase_union_select[OF positive rows_length])
  have selected_row:
    "?rows!?slot =
      (case comma_semantic_b1_source_port_action source ?slot of
         Comma_Continuation_Goto child shift \<Rightarrow>
           (if shift=0 \<and> comma_round_admitted child \<and>
               child=comma_source_continuation_base child
            then comma_guarded_source_output_mask child result else 0)
       | action \<Rightarrow>
           (case comma_semantic_b1_terminal_action_result action of
              Some terminal \<Rightarrow>
                (if terminal=result then mask 924 else 0)
            | None \<Rightarrow> 0))"
    using slot_bound by simp
  have mask_equation:
    "comma_guarded_source_output_mask source result =
      comma_indexed_phase_union
        (\<lambda>slot phase. phase mod ?period=slot) ?rows"
    using comma_guarded_source_output_mask.simps[of source result]
      source_admitted source_normalized
    by (simp only: if_P Let_def)
  have source_slot:
    "comma_semantic_b1_source_slot_action source ?slot =
      comma_semantic_b1_source_port_action source ?slot"
  proof -
    have port:
      "comma_source_continuation_action_at source ?slot =
        comma_semantic_b1_source_port_action source ?slot"
      by (rule comma_guarded_source_action_at_port
        [OF source_admitted source_normalized])
    have action:
      "comma_semantic_b1_source_slot_action source ?slot =
        comma_source_continuation_action_at source ?slot"
      by (rule comma_semantic_b1_source_slot_action_refines[OF source_admitted])
    show ?thesis using action port by simp
  qed
  have source_round:
    "comma_semantic_b1_source_slot_output phase
        (comma_semantic_b1_source_slot_action source ?slot) =
      comma_semantic_b1_round_output phase source"
    by (rule comma_semantic_b1_source_slot_round_output
      [OF source_normalized source_admitted slot_bound period_slot])
  have slot_output:
    "comma_semantic_b1_source_slot_output phase
        (comma_semantic_b1_source_port_action source ?slot) =
      comma_semantic_b1_round_output phase source"
    using source_round source_slot by simp
  show ?case
  proof (cases "\<exists>child shift. comma_semantic_b1_source_port_action
      source ?slot = Comma_Continuation_Goto child shift")
    case True
    then obtain child shift where action_eq:
      "comma_semantic_b1_source_port_action source ?slot =
        Comma_Continuation_Goto child shift"
      by blast
    have shift_zero: "shift=0"
      and child_normalized:
        "child=comma_source_continuation_base child"
      and child_decrease:
        "9-comma_sector_number child < 9-comma_sector_number source"
      and child_admitted: "comma_round_admitted child"
      by (rule comma_guarded_source_mask_goto_decreases
        [OF source_admitted source_normalized slot_bound action_eq])+
    have child_exact:
      "comma_phase_member
          (comma_guarded_source_output_mask child result) phase =
        (comma_semantic_b1_round_output phase child=result)"
      by (rule sector_induction[OF child_decrease child_admitted child_normalized
        phase_bound])
    have row:
      "?rows!?slot=comma_guarded_source_output_mask child result"
      using selected_row action_eq shift_zero child_admitted child_normalized
      by simp
    have source_child:
      "comma_semantic_b1_round_output phase source=
        comma_semantic_b1_round_output phase child"
      using slot_output action_eq
      by (simp add: comma_semantic_b1_source_slot_output_def)
    have row_exact:
      "comma_phase_member (?rows!?slot) phase =
        (comma_semantic_b1_round_output phase source=result)"
      using child_exact row source_child by simp
    show ?thesis using selected mask_equation row_exact by simp
  next
    case False
    let ?action="comma_semantic_b1_source_port_action source ?slot"
    have non_goto:
      "\<not>(\<exists>child shift. ?action=Comma_Continuation_Goto child shift)"
      using False by blast
    obtain terminal where terminal:
      "comma_semantic_b1_terminal_action_result ?action=Some terminal"
      using comma_semantic_b1_terminal_action_result_present[OF non_goto]
      by blast
    have terminal_slot:
      "comma_semantic_b1_source_slot_output phase ?action=terminal"
      by (rule comma_semantic_b1_terminal_action_output[OF terminal])
    have terminal_output:
      "terminal=comma_semantic_b1_round_output phase source"
      using terminal_slot slot_output by simp
    have row:
      "?rows!?slot=(if terminal=result then mask 924 else 0)"
      using selected_row terminal non_goto by (cases ?action) auto
    have row_exact:
      "comma_phase_member (?rows!?slot) phase =
        (comma_semantic_b1_round_output phase source=result)"
      using row terminal_output phase_bound
      by (simp add: comma_guarded_source_terminal_mask_member)
    show ?thesis using selected mask_equation row_exact by simp
  qed
qed

lemma comma_guarded_source_class_rel_output_mask_member:
  assumes rel: "comma_guarded_source_class_rel left right"
    and phase: "phase<924"
  shows "comma_phase_member
      (comma_guarded_source_output_mask left result) phase =
    comma_phase_member
      (comma_guarded_source_output_mask right result) phase"
proof -
  have left_admitted: "comma_round_admitted left"
    and right_admitted: "comma_round_admitted right"
    using rel by (auto simp: comma_guarded_source_class_rel_def)
  have left_normalized:
    "left=comma_source_continuation_base left"
    and right_normalized:
    "right=comma_source_continuation_base right"
    using comma_guarded_source_class_rel_normalized[OF rel] by simp_all
  have left_exact:
    "comma_phase_member
        (comma_guarded_source_output_mask left result) phase =
      (comma_semantic_b1_round_output phase left=result)"
    by (rule comma_guarded_source_output_mask_member_exact
      [OF left_admitted left_normalized phase])
  have right_exact:
    "comma_phase_member
        (comma_guarded_source_output_mask right result) phase =
      (comma_semantic_b1_round_output phase right=result)"
    by (rule comma_guarded_source_output_mask_member_exact
      [OF right_admitted right_normalized phase])
  have outputs_equal:
    "comma_semantic_b1_round_output phase left =
      comma_semantic_b1_round_output phase right"
    by (rule comma_guarded_source_class_rel_complete_observation[OF rel])
  show ?thesis using left_exact right_exact outputs_equal by simp
qed

lemma comma_guarded_source_class_rel_output_mask:
  assumes rel: "comma_guarded_source_class_rel left right"
  shows "comma_guarded_source_output_mask left result =
    comma_guarded_source_output_mask right result"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_guarded_source_output_mask left result) phase =
    bit (comma_guarded_source_output_mask right result) phase"
  proof (cases "phase<924")
    case True
    have members:
      "comma_phase_member
          (comma_guarded_source_output_mask left result) phase =
        comma_phase_member
          (comma_guarded_source_output_mask right result) phase"
      by (rule comma_guarded_source_class_rel_output_mask_member[OF rel True])
    show ?thesis using members True
      by (simp add: comma_phase_member_def)
  next
    case False
    have left_bounded:
      "take_bit 924 (comma_guarded_source_output_mask left result) =
        comma_guarded_source_output_mask left result"
      by (rule comma_guarded_source_output_mask_bounded)
    have right_bounded:
      "take_bit 924 (comma_guarded_source_output_mask right result) =
        comma_guarded_source_output_mask right result"
      by (rule comma_guarded_source_output_mask_bounded)
    have left_zero:
      "bit (comma_guarded_source_output_mask left result) phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF left_bounded])
        (use False in arith)
    have right_zero:
      "bit (comma_guarded_source_output_mask right result) phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF right_bounded])
        (use False in arith)
    show ?thesis using left_zero right_zero by simp
  qed
qed

ML \<open>
  val checked = @{thms comma_guarded_source_output_mask_bounded
    comma_guarded_source_output_mask_member_exact
    comma_guarded_source_class_rel_output_mask};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Source-only guarded mask evaluation" checked;
\<close>

end
