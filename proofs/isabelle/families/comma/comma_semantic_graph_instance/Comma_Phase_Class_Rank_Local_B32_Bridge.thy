theory Comma_Phase_Class_Rank_Local_B32_Bridge
  imports Comma_Phase_Class_Rank_Rotation
begin

text \<open>
This consumer uses the finite source-domain proof directly.  The 46 action
families are the families of the canonical Entry roots, so their source
binding is defined by the adapter rather than asserted as a separate
endpoint-equality premise.  Local Coverage proves each root lookup from
typed ports and the sector induction; the rank certificate then supplies
the decade descent and B32 stop result.
\<close>

definition comma_rank_local_canonical_root_actions where
  "comma_rank_local_canonical_root_actions families =
    map (\<lambda>i. families (Comma_Entry 1 0 (comma_offset_representatives!i)))
      [0..<46]"

lemma comma_rank_local_source_control_refines:
  fixes families ::
    "comma_finite_position \<Rightarrow>
      (nat \<times> comma_phase_rank_mask_action) list"
    and ranks :: "(nat \<times> nat) list list"
  assumes domain: "comma_rank_source_domain_contract sources families"
    and roots_member: "\<And>i. i<46 \<Longrightarrow>
      Comma_Entry 1 0 (comma_offset_representatives!i)\<in>set sources"
    and certificate: "comma_phase_mask_rank_certificate
      (comma_rank_local_canonical_root_actions families) ranks"
    and admitted: "comma_decade_admitted (Comma_Decade phase offset)"
  shows "comma_phase_mask_action_total
      (comma_rank_local_canonical_root_actions families) phase
      (comma_offset_orbit offset) =
    comma_phase_classify_decade_control comma_offset_orbit
      (comma_decade_control (Comma_Decade phase offset))"
proof -
  have phase_bound: "phase<924" and offset_bound: "offset\<le>90"
    using admitted by simp_all
  let ?class_id = "comma_offset_orbit offset"
  have class_bound: "?class_id<46"
    by (rule comma_offset_orbit_bound)
  let ?representative = "comma_offset_representatives!?class_id"
  let ?source = "Comma_Entry 1 0 ?representative"
  have representative_bound: "?representative\<le>90"
    and representative_class: "comma_offset_orbit ?representative=?class_id"
    using comma_orbit_representative_index[OF class_bound] by auto
  have representative_member: "?source\<in>set sources"
    by (rule roots_member[OF class_bound])
  let ?actions = "comma_rank_local_canonical_root_actions families"
  have action_row:
    "?actions!?class_id=families ?source"
    using class_bound
    by (simp add: comma_rank_local_canonical_root_actions_def nth_map)
  have representative_action:
    "comma_phase_mask_action_total [families ?source] phase 0 =
      comma_phase_rank_mask_lift phase
        (comma_rank_mask_action_of_b1_result
          (comma_semantic_b1_round_output phase ?source))"
    using comma_rank_source_domain_action_exact[OF domain]
      representative_member phase_bound by blast
  have representative_control:
    "comma_phase_rank_mask_lift phase
        (comma_rank_mask_action_of_b1_result
          (comma_semantic_b1_round_output phase ?source)) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade phase ?representative))"
    by (rule comma_rank_source_result_control_exact
      [OF phase_bound representative_bound])
  have orbit_control:
    "comma_decade_control (Comma_Decade phase offset) =
      comma_decade_control (Comma_Decade phase ?representative)"
    using comma_decade_control_orbit_representative[OF offset_bound]
    by (simp only: comma_offset_representative_def representative_class)
  have table_lookup:
    "comma_phase_mask_action_total ?actions phase ?class_id =
      comma_phase_mask_action_total [?actions!?class_id] phase 0"
  proof -
    have class_length: "?class_id<length ?actions"
      using certificate class_bound
      by (simp add: comma_phase_mask_rank_certificate_def)
    show ?thesis
      using class_length
      by (simp add: comma_phase_mask_action_total_def
        comma_phase_mask_action_at_option_def)
  qed
  have table_binding:
    "comma_phase_mask_action_total [?actions!?class_id] phase 0 =
      comma_phase_mask_action_total [families ?source] phase 0"
    using action_row by simp
  show ?thesis
    using table_lookup table_binding representative_action
      representative_control orbit_control by simp
qed

theorem comma_phase_mask_local_rank_B32_stop242:
  fixes families ::
    "comma_finite_position \<Rightarrow>
      (nat \<times> comma_phase_rank_mask_action) list"
    and ranks :: "(nat \<times> nat) list list"
  assumes domain: "comma_rank_source_domain_contract sources families"
    and roots_member: "\<And>i. i<46 \<Longrightarrow>
      Comma_Entry 1 0 (comma_offset_representatives!i)\<in>set sources"
    and certificate: "comma_phase_mask_rank_certificate
      (comma_rank_local_canonical_root_actions families) ranks"
  shows "\<forall>root<46. \<forall>phase<924. \<exists>D.
    comma_semantic_b1_action_power 5 phase root=
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof (intro allI impI)
  fix root phase :: nat
  assume root_bound: "root<46" and phase_bound: "phase<924"
  let ?state = "Comma_Decade phase (comma_offset_representatives!root)"
  have admitted: "comma_decade_admitted ?state"
    using comma_orbit_representative_index(1)[OF root_bound] phase_bound by simp
  have source_valid:
    "\<And>r x. comma_decade_admitted (Comma_Decade r x) \<Longrightarrow>
      r<924 \<and> comma_offset_orbit x<46"
    by (auto intro: comma_offset_orbit_bound)
  have source_refines:
    "\<And>r x. comma_decade_admitted (Comma_Decade r x) \<Longrightarrow>
      comma_phase_mask_action_total
        (comma_rank_local_canonical_root_actions families) r
        (comma_offset_orbit x) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade r x))"
  proof -
    fix r x
    assume decade_admitted: "comma_decade_admitted (Comma_Decade r x)"
    show "comma_phase_mask_action_total
        (comma_rank_local_canonical_root_actions families) r
        (comma_offset_orbit x) =
      comma_phase_classify_decade_control comma_offset_orbit
        (comma_decade_control (Comma_Decade r x))"
      by (rule comma_rank_local_source_control_refines
        [OF domain roots_member certificate decade_admitted])
  qed
  obtain h terminal where height: "h\<le>26"
    and exact_summary:
      "comma_decade_exact_summary ?state h terminal"
    using comma_phase_mask_rank_certificate_B32
      [where class_of=comma_offset_orbit and s="?state",
       OF certificate source_valid source_refines admitted]
    by blast
  show "\<exists>D. comma_semantic_b1_action_power 5 phase root=
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
    using comma_semantic_b1_action_stop_from_exact_summary
      [OF phase_bound root_bound exact_summary height] by blast
qed

ML \<open>
  val checked = @{thms comma_rank_local_source_control_refines
    comma_phase_mask_local_rank_B32_stop242};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Local source rank bridge depends on an oracle";
\<close>

end
