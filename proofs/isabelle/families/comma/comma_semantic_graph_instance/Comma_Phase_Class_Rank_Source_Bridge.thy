theory Comma_Phase_Class_Rank_Source_Bridge
  imports Comma_Semantic_B1.Comma_Phase_Class_Rank_Masks
    Comma_Semantic_B1.Comma_Guarded_Source_Mask_Evaluator
    Comma_Semantic_B1.Comma_Semantic_Action_Power
    Comma_Semantic_B1.Comma_Semantic_Phase_Class_Endpoint
begin

text \<open>
This scratch bridge keeps three contracts separate: a rank-mask witness,
the source evaluator's exact output masks, and the decade-control theorem.
The first alone is not source authority.  The per-row premise below binds
each row to an evaluator mask; exact mask membership then identifies the
actual B1 output at the selected phase.
\<close>

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
