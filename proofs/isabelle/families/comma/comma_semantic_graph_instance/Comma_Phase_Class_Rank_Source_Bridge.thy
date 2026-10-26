theory Comma_Phase_Class_Rank_Source_Bridge
  imports Comma_Semantic_B1.Comma_Phase_Class_Rank_Masks
    Comma_Semantic_B1.Comma_Guarded_Source_Mask_Evaluator
    Comma_Semantic_B1.Comma_Semantic_Action_Power
begin

text \<open>
This scratch bridge keeps three contracts separate: a rank-mask witness,
the source evaluator's exact output masks, and the decade-control theorem.
The first alone is not source authority.  The per-row premise below binds
each row to an evaluator mask; exact mask membership then identifies the
actual B1 output at the selected phase.
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

definition comma_rank_source_rows_sound where
  "comma_rank_source_rows_sound rows source \<longleftrightarrow>
    (\<forall>row\<in>set rows. \<exists>result.
      snd row=comma_rank_mask_action_of_b1_result result \<and>
      fst row AND comma_guarded_source_output_mask source result=fst row)"

lemma comma_rank_source_mask_eq_from_uniform_members:
  assumes candidate_bounded: "take_bit 924 (candidate::nat)=candidate"
    and member_eq: "\<And>phase. phase<924 \<Longrightarrow>
      comma_phase_member
        (comma_guarded_source_output_mask source result) phase =
      comma_phase_member candidate phase"
  shows "comma_guarded_source_output_mask source result=candidate"
proof (rule bit_eqI)
  fix phase
  show "bit (comma_guarded_source_output_mask source result) phase=
      bit candidate phase"
  proof (cases "phase<924")
    case True
    have selected:
      "comma_phase_member
          (comma_guarded_source_output_mask source result) phase =
        comma_phase_member candidate phase"
      by (rule member_eq[OF True])
    show ?thesis using selected True
      by (simp add: comma_phase_member_def)
  next
    case False
    have source_bounded:
      "take_bit 924 (comma_guarded_source_output_mask source result) =
        comma_guarded_source_output_mask source result"
      by (rule comma_guarded_source_output_mask_bounded)
    have source_zero:
      "bit (comma_guarded_source_output_mask source result) phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF source_bounded])
        (use False in arith)
    have candidate_zero: "bit candidate phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF candidate_bounded])
        (use False in arith)
    show ?thesis using source_zero candidate_zero by simp
  qed
qed

lemma comma_rank_source_mask_subset_from_uniform_members:
  assumes candidate_bounded: "take_bit 924 (candidate::nat)=candidate"
    and member_subset: "\<And>phase. phase<924 \<Longrightarrow>
      comma_phase_member candidate phase \<Longrightarrow>
      comma_phase_member
        (comma_guarded_source_output_mask source result) phase"
  shows "candidate AND comma_guarded_source_output_mask source result=candidate"
proof (rule bit_eqI)
  fix phase
  show "bit (candidate AND comma_guarded_source_output_mask source result) phase=
      bit candidate phase"
  proof (cases "phase<924")
    case True
    have bit_subset:
      "bit candidate phase \<Longrightarrow>
        bit (comma_guarded_source_output_mask source result) phase"
      using member_subset[OF True] True by (simp add: comma_phase_member_def)
    show ?thesis using bit_subset
      by (cases "bit candidate phase") (simp_all add: bit_simps)
  next
    case False
    have candidate_zero: "bit candidate phase=False"
      by (rule comma_symbolic_phase_bit_outside[OF candidate_bounded])
        (use False in arith)
    show ?thesis using candidate_zero by (simp add: bit_simps)
  qed
qed

lemma comma_rank_source_action_at_exact:
  assumes partition: "comma_phase_mask_rows_partition rows"
    and rows_sound: "comma_rank_source_rows_sound rows source"
    and admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
    and phase: "phase<924"
  shows "comma_phase_mask_action_total [rows] phase 0 =
    comma_phase_rank_mask_lift phase
      (comma_rank_mask_action_of_b1_result
        (comma_semantic_b1_round_output phase source))"
proof -
  obtain row where row_member: "row\<in>set rows"
    and row_bit: "comma_phase_member (fst row) phase"
    and row_lookup: "comma_phase_mask_row_at rows phase=Some row"
    by (rule comma_phase_mask_row_at_some[OF partition phase])
  obtain result where row_sound:
      "snd row=comma_rank_mask_action_of_b1_result result"
      "fst row AND comma_guarded_source_output_mask source result=fst row"
    using rows_sound row_member by (auto simp: comma_rank_source_rows_sound_def)
  have row_intersection:
    "comma_phase_member
        (fst row AND comma_guarded_source_output_mask source result) phase =
      (comma_phase_member (fst row) phase \<and>
        comma_phase_member (comma_guarded_source_output_mask source result) phase)"
    by (rule comma_phase_member_and)
  have row_member_same:
    "comma_phase_member
        (fst row AND comma_guarded_source_output_mask source result) phase =
      comma_phase_member (fst row) phase"
    by (rule arg_cong[where f="\<lambda>bits. comma_phase_member bits phase",
      OF row_sound(2)])
  have result_mask_member:
    "comma_phase_member (comma_guarded_source_output_mask source result) phase"
    using row_bit row_intersection row_member_same by blast
  have selected_exact:
    "comma_phase_member
        (comma_guarded_source_output_mask source result) phase =
      (comma_semantic_b1_round_output phase source=result)"
    using comma_guarded_source_output_mask_member_exact
      [OF admitted normalized phase]
    .
  have result_eq: "result=comma_semantic_b1_round_output phase source"
    using result_mask_member selected_exact by blast
  show ?thesis
    using row_lookup row_sound(1) result_eq
    by (simp add: comma_phase_mask_action_total_def
      comma_phase_mask_action_at_option_def)
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
  have source_admitted: "comma_round_admitted ?source"
    using offset by simp
  have state_admitted: "comma_decade_admitted ?state"
    using phase offset by simp
  have endpoint_admitted: "comma_sector_base_admitted ?endpoint"
    by (rule comma_decisive_endpoint_result_admitted[OF offset])
  obtain steps terminal event where close:
    "comma_round_close phase ?source=(steps,terminal,event)"
    by (cases "comma_round_close phase ?source") auto
  have endpoint_event: "?endpoint=event"
    using comma_decisive_endpoint_round_refines_close[OF source_admitted] close
    by simp
  have control:
    "comma_decade_control ?state=comma_decade_decode phase ?endpoint"
    using close endpoint_event by (simp add: comma_decade_control.simps)
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

lemma comma_phase_mask_source_control_refines:
  fixes actions :: "(nat \<times> comma_phase_rank_mask_action) list list"
  assumes certificate: "comma_phase_mask_rank_certificate actions ranks"
    and rows_sound: "\<And>i. i<46 \<Longrightarrow>
      comma_rank_source_rows_sound (actions!i)
        (Comma_Entry 1 0 (comma_offset_representatives!i))"
    and admitted: "comma_decade_admitted (Comma_Decade phase offset)"
  shows "comma_phase_mask_action_total actions phase (comma_offset_orbit offset) =
    comma_phase_classify_decade_control comma_offset_orbit
      (comma_decade_control (Comma_Decade phase offset))"
proof -
  have phase_bound: "phase<924" and offset_bound: "offset\<le>90"
    using admitted by simp_all
  let ?class_id = "comma_offset_orbit offset"
  have class_bound: "?class_id<46"
    by (rule comma_offset_orbit_bound)
  let ?representative = "comma_offset_representatives!?class_id"
  have representative_bound: "?representative\<le>90"
    and representative_class: "comma_offset_orbit ?representative=?class_id"
    using comma_orbit_representative_index[OF class_bound] by auto
  have partition:
    "comma_phase_mask_rows_partition (actions!?class_id)"
    by (rule comma_phase_mask_rank_certificate_partition(1)
      [OF certificate class_bound])
  have representative_source_admitted:
    "comma_round_admitted (Comma_Entry 1 0 ?representative)"
    using representative_bound by simp
  have representative_source_normalized:
    "Comma_Entry 1 0 ?representative =
      comma_source_continuation_base (Comma_Entry 1 0 ?representative)"
    by simp
  have representative_action:
    "comma_phase_mask_action_total [actions!?class_id] phase 0 =
      comma_phase_rank_mask_lift phase
        (comma_rank_mask_action_of_b1_result
          (comma_semantic_b1_round_output phase
            (Comma_Entry 1 0 ?representative)))"
    by (rule comma_rank_source_action_at_exact
      [OF partition rows_sound[OF class_bound]
        representative_source_admitted representative_source_normalized phase_bound])
  have representative_control:
    "comma_phase_rank_mask_lift phase
        (comma_rank_mask_action_of_b1_result
          (comma_semantic_b1_round_output phase
            (Comma_Entry 1 0 ?representative))) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade phase ?representative))"
    by (rule comma_rank_source_result_control_exact[OF phase_bound representative_bound])
  have orbit_control:
    "comma_decade_control (Comma_Decade phase offset) =
      comma_decade_control (Comma_Decade phase ?representative)"
    using comma_decade_control_orbit_representative[OF offset_bound]
    by (simp only: comma_offset_representative_def representative_class)
  have table_lookup:
    "comma_phase_mask_action_total actions phase ?class_id =
      comma_phase_mask_action_total [actions!?class_id] phase 0"
  proof -
    have class_length: "?class_id<length actions"
      using certificate class_bound
      by (simp add: comma_phase_mask_rank_certificate_def)
    show ?thesis
      using class_length
      by (simp add: comma_phase_mask_action_total_def
        comma_phase_mask_action_at_option_def)
  qed
  show ?thesis
    using table_lookup representative_action representative_control orbit_control
    by simp
qed

lemma comma_semantic_b1_action_stop_from_exact_summary:
  assumes phase: "phase<924" and root: "root<46"
    and summary: "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!root)) h terminal"
    and height_bound: "h\<le>26"
  shows "comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h terminal)
    \<and> comma_terminal_weight_encode h terminal\<le>242"
proof -
  let ?source = "Comma_Decade phase (comma_offset_representatives!root)"
  have representative: "comma_offset_representatives!root\<le>90"
    and representative_index:
      "comma_offset_orbit (comma_offset_representatives!root)=root"
    using comma_orbit_representative_index[OF root] by auto
  have admitted: "comma_decade_admitted ?source"
    using phase representative by simp
  have block_run_stop:
    "comma_decade_block_run 32 ?source=Comma_Block_Stop h terminal"
    by (rule comma_decade_exact_summary_block_stop[OF summary admitted])
      (use height_bound in arith)
  have block_stop:
    "comma_decade_block_power 5 ?source=Comma_Block_Stop h terminal"
    using block_run_stop by (simp add: comma_decade_block_square_refines)
  have orbit_refinement:
    "comma_word_project comma_offset_orbit
        (comma_decade_block_power 5 ?source)=comma_orbit_word 5 phase root"
    using comma_orbit_word_refines[OF admitted] representative_index by simp
  have orbit_stop: "comma_orbit_word 5 phase root=Comma_Word_Stop h terminal"
    using orbit_refinement block_stop by simp
  have semantic_refinement:
    "comma_semantic_b1_action_power 5 phase root=
      comma_semantic_b1_of_word (comma_orbit_word 5 phase root)"
    by (rule comma_semantic_b1_action_power_refines_orbit[OF phase root])
  have action_equation:
    "comma_semantic_b1_action_power 5 phase root=
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h terminal)"
    using semantic_refinement orbit_stop by simp
  have terminal_admitted:
    "comma_terminal_weight_admitted terminal"
    by (rule comma_decade_exact_summary_terminal_admitted[OF summary])
  have digit_bound: "comma_terminal_weight_digit terminal<9"
    by (rule comma_terminal_weight_digit_bound[OF terminal_admitted])
  have weight_bound: "comma_terminal_weight_encode h terminal\<le>242"
    using height_bound digit_bound
    by (simp add: comma_terminal_weight_encode_def; arith)
  show ?thesis using action_equation weight_bound by blast
qed

theorem comma_phase_mask_rank_source_B32_stop242:
  fixes actions :: "(nat \<times> comma_phase_rank_mask_action) list list"
  assumes certificate: "comma_phase_mask_rank_certificate actions ranks"
    and rows_sound: "\<And>i. i<46 \<Longrightarrow>
      comma_rank_source_rows_sound (actions!i)
        (Comma_Entry 1 0 (comma_offset_representatives!i))"
  shows "\<forall>root<46. \<forall>phase<924. \<exists>D.
    comma_semantic_b1_action_power 5 phase root=
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof (intro allI impI)
  fix root phase :: nat
  assume root: "root<46" and phase: "phase<924"
  let ?state = "Comma_Decade phase (comma_offset_representatives!root)"
  have admitted: "comma_decade_admitted ?state"
    using comma_orbit_representative_index(1)[OF root] phase by simp
  have source_valid:
    "\<And>r x. comma_decade_admitted (Comma_Decade r x) \<Longrightarrow>
      r<924 \<and> comma_offset_orbit x<46"
    by (auto intro: comma_offset_orbit_bound)
  have source_control:
    "\<And>r x. comma_decade_admitted (Comma_Decade r x) \<Longrightarrow>
      comma_phase_mask_action_total actions r (comma_offset_orbit x) =
        comma_phase_classify_decade_control comma_offset_orbit
          (comma_decade_control (Comma_Decade r x))"
    by (rule comma_phase_mask_source_control_refines[OF certificate rows_sound])
  obtain h terminal where height: "h\<le>26"
    and exact_summary: "comma_decade_exact_summary ?state h terminal"
    using comma_phase_mask_rank_certificate_B32
      [where class_of=comma_offset_orbit and s="?state",
       OF certificate source_valid source_control admitted]
    by blast
  show "\<exists>D. comma_semantic_b1_action_power 5 phase root=
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
    using comma_semantic_b1_action_stop_from_exact_summary
      [OF phase root exact_summary height] by blast
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_rank_source_action_at_exact
      comma_rank_source_mask_eq_from_uniform_members
      comma_rank_source_mask_subset_from_uniform_members
      comma_rank_source_result_control_exact
      comma_phase_mask_source_control_refines
      comma_semantic_b1_action_stop_from_exact_summary
      comma_phase_mask_rank_source_B32_stop242})
    then () else error "Source-mask B32 bridge depends on an oracle";
\<close>

end
