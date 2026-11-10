theory Comma_Semantic_Phase_Class_Endpoint
  imports Comma_Semantic_B1_Entry_Near_Ports Comma_Semantic_Action_Power
    Comma_Semantic_Phase_Class_Action Comma_Semantic_Phase_Class
begin

text \<open>
This is the source-to-class-action boundary for the CRT cofactor compiler.
It reuses the existing static phase-class action alphabet and the admitted
Entry/Near endpoint constructor.  The theorem is independent of candidate
rows, masks, or graph validity: it relates the selected semantic result
directly to the exact decade control.
\<close>

fun comma_rank_mask_action_of_b1_result ::
    "comma_semantic_b1_result \<Rightarrow> comma_phase_rank_mask_action" where
  "comma_rank_mask_action_of_b1_result (Comma_Semantic_B1_Live root) =
    Comma_Phase_Rank_Mask_Continue root"
| "comma_rank_mask_action_of_b1_result (Comma_Semantic_B1_Stop digit) =
    (if digit<8 then Comma_Phase_Rank_Mask_Fork (digit+2) 0
     else if digit=8 then Comma_Phase_Rank_Mask_Landmine 0
     else Comma_Phase_Rank_Mask_Invalid)"
| "comma_rank_mask_action_of_b1_result Comma_Semantic_B1_Invalid =
    Comma_Phase_Rank_Mask_Invalid"

lemma comma_decisive_endpoint_round_decade_control:
  assumes offset: "offset\<le>90"
  shows "comma_decade_control (Comma_Decade phase offset) =
    comma_decade_decode phase
      (comma_decisive_endpoint_round phase (Comma_Entry 1 0 offset))"
proof -
  let ?source = "Comma_Entry 1 0 offset"
  have source_admitted: "comma_round_admitted ?source"
    using offset by simp
  obtain steps terminal event where close:
      "comma_round_close phase ?source=(steps,terminal,event)"
    by (cases "comma_round_close phase ?source") auto
  have endpoint_event:
      "comma_decisive_endpoint_round phase ?source=event"
    using comma_decisive_endpoint_round_refines_close[OF source_admitted] close
    by simp
  show ?thesis using close endpoint_event
    by (simp add: comma_decade_control.simps)
qed

lemma comma_rank_source_result_control_exact:
  assumes phase: "phase<924" and offset: "offset\<le>90"
  shows "comma_phase_rank_mask_lift phase
      (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase (Comma_Entry 1 0 offset))) =
    comma_phase_classify_decade_control comma_offset_orbit
      (comma_decade_control (Comma_Decade phase offset))"
proof -
  let ?source = "Comma_Entry 1 0 offset"
  let ?state = "Comma_Decade phase offset"
  let ?endpoint = "comma_decisive_endpoint_round phase ?source"
  have state_admitted: "comma_decade_admitted ?state"
    using phase offset by simp
  have endpoint_admitted: "comma_sector_base_admitted ?endpoint"
    by (rule comma_decisive_endpoint_result_admitted[OF offset])
  have control:
    "comma_decade_control ?state=comma_decade_decode phase ?endpoint"
    by (rule comma_decisive_endpoint_round_decade_control[OF offset])
  have output_atom:
    "comma_semantic_b1_round_output phase ?source =
      comma_semantic_b1_of_word
        (comma_word_project comma_offset_orbit (comma_decade_block_atom ?state))"
    using comma_semantic_b1_source_exact_atom[OF phase offset]
    by (simp add: comma_semantic_b1_round_output_def
      comma_semantic_b1_source_def comma_decisive_B1_source_def)
  show ?thesis
  proof (cases ?endpoint)
    case (Comma_Round_Cross target)
    then show ?thesis
    proof (cases target)
      case (Comma_Entry f delta x)
      have endpoint_facts: "comma_decade_root_admitted (Comma_Entry f delta x)"
        "delta=1"
        using endpoint_admitted Comma_Round_Cross Comma_Entry
        by (simp_all add: comma_sector_base_admitted.simps)
      have f_one: "f=1" and x_bound: "x\<le>90"
        using endpoint_facts(1) by (auto simp: comma_decade_root_admitted_def)
      have physical:
        "comma_decade_control ?state=
          Comma_Decade_Continue (Comma_Decade ((phase+1) mod 924) x)"
        using control Comma_Round_Cross Comma_Entry endpoint_facts
        by (simp only: comma_decade_decode.simps if_P)
      have target_admitted:
        "comma_decade_admitted (Comma_Decade ((phase+1) mod 924) x)"
        using phase x_bound by simp
      have atom:
        "comma_decade_block_atom ?state=
          Comma_Block_Live (Comma_Decade ((phase+1) mod 924) x)"
        using state_admitted physical target_admitted
        by (simp add: comma_decade_block_atom_def)
      show ?thesis
        using output_atom atom physical
        by (simp add: comma_phase_classify_decade_control.simps)
    next
      case (Comma_Near f delta headroom)
      then show ?thesis using endpoint_admitted Comma_Round_Cross
        by (simp add: comma_sector_base_admitted.simps)
    qed
  next
    case (Comma_Round_Fork a delta)
    have delta_zero: "delta=0"
      using endpoint_admitted Comma_Round_Fork
      by (simp add: comma_sector_base_admitted.simps)
    have physical: "comma_decade_control ?state=Comma_Decade_Fork a 0"
      using control Comma_Round_Fork delta_zero
      by (simp only: comma_decade_decode.simps)
    have atom: "comma_decade_block_atom ?state=
        Comma_Block_Stop 0 (Comma_Terminal_Fork a)"
      using state_admitted physical by (simp add: comma_decade_block_atom_def)
    have summary: "comma_decade_exact_summary ?state 0 (Comma_Terminal_Fork a)"
      by (rule comma_decade_block_atom_stop(3)[OF atom])
    have terminal_admitted:
      "comma_terminal_weight_admitted (Comma_Terminal_Fork a)"
      by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
    have a_bounds: "2\<le>a \<and> a\<le>9"
      using terminal_admitted by (simp add: comma_terminal_weight_admitted_def)
    have position_bound: "a-2<8" and position_reconstruct: "a-2+2=a"
      using a_bounds by arith+
    show ?thesis
      using output_atom atom physical position_bound position_reconstruct
      by (simp add: comma_phase_classify_decade_control.simps
        comma_terminal_weight_encode_def)
  next
    case (Comma_Round_Landmine delta)
    have delta_zero: "delta=0"
      using endpoint_admitted Comma_Round_Landmine
      by (simp add: comma_sector_base_admitted.simps)
    have physical: "comma_decade_control ?state=Comma_Decade_Landmine 0"
      using control Comma_Round_Landmine delta_zero
      by (simp only: comma_decade_decode.simps)
    have atom: "comma_decade_block_atom ?state=
        Comma_Block_Stop 0 Comma_Terminal_Landmine"
      using state_admitted physical by (simp add: comma_decade_block_atom_def)
    show ?thesis
      using output_atom atom physical
      by (simp add: comma_phase_classify_decade_control.simps
        comma_terminal_weight_encode_def)
  next
    case Comma_Round_Invalid
    then show ?thesis using endpoint_admitted
      by (simp add: comma_sector_base_admitted.simps)
  qed
qed

theorem comma_semantic_b1_round_output_phase_class_exact:
  assumes phase: "phase<924" and offset: "offset\<le>90"
  shows "comma_phase_rank_mask_lift phase
      (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase (Comma_Entry 1 0 offset))) =
    comma_semantic_phase_class_step phase (comma_offset_orbit offset)"
proof -
  have admitted: "comma_decade_admitted (Comma_Decade phase offset)"
    using phase offset by simp
  have exact_result:
    "comma_phase_rank_mask_lift phase
      (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase (Comma_Entry 1 0 offset))) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade phase offset))"
    by (rule comma_rank_source_result_control_exact[OF phase offset])
  have source_control:
    "comma_semantic_phase_class_step phase (comma_offset_orbit offset) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade phase offset))"
    by (rule comma_semantic_phase_class_source_control[OF admitted])
  show ?thesis
    by (rule trans[OF exact_result source_control[symmetric]])
qed

text \<open>
A checked class rank preserves the exact semantic Stop payload, rather than
only a termination claim. The physical writer still consumes its separately
authenticated occurrence weights. No graph or numerical mask certificate is
needed to transport this normalized output.
\<close>

theorem comma_semantic_phase_class_B32_exact_output:
  assumes checked: "comma_phase_class_rank_check
      comma_semantic_phase_class_valid rank comma_semantic_phase_class_step"
    and bounded: "\<And>phase cid. comma_semantic_phase_class_valid phase cid
      \<Longrightarrow> rank phase cid\<le>26"
    and phase: "phase<924" and cid: "cid<46"
  obtains height terminal where
    "height\<le>26"
    "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!cid)) height terminal"
    "comma_semantic_b1_action_power 5 phase cid =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    "comma_terminal_weight_encode height terminal\<le>242"
proof -
  let ?source = "Comma_Decade phase (comma_offset_representatives!cid)"
  have valid: "comma_semantic_phase_class_valid phase cid"
    using phase cid by (simp add: comma_semantic_phase_class_valid_def)
  have admitted: "comma_decade_admitted ?source"
    by (rule comma_semantic_phase_class_representative(1)[OF valid])
  obtain height terminal where height: "height\<le>26"
    and summary: "comma_decade_exact_summary ?source height terminal"
    using comma_phase_class_rank_B32
      [where class_of=comma_offset_orbit
       and valid=comma_semantic_phase_class_valid and rank=rank
       and step=comma_semantic_phase_class_step,
       OF checked comma_semantic_phase_class_source_valid
         comma_semantic_phase_class_source_control bounded admitted]
    by blast
  have exact:
    "comma_semantic_b1_action_power 5 phase cid =
        Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)
      \<and> comma_terminal_weight_encode height terminal\<le>242"
    by (rule comma_semantic_b1_action_stop_from_exact_summary
      [OF phase cid summary height])
  show thesis using that height summary exact by blast
qed

ML \<open>
  val phase_endpoint_rules =
    @{thms comma_rank_source_result_control_exact
      comma_semantic_b1_round_output_phase_class_exact
      comma_semantic_phase_class_B32_exact_output};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Comma Semantic Phase Class Endpoint" phase_endpoint_rules;
\<close>

end
