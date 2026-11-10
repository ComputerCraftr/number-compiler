theory Comma_Continue_Frontier_Certificate
  imports Comma_CRT_MDD_Frontier Comma_Targeted_Continue_Certificate
begin

text \<open>
Transport a checked semantic image into the existing public certificate.
The bad-support column remains opaque: its established semantic equivalence
supplies the contract without constructing a column or enumerating phases.
\<close>

lemma comma_map_filter_member_origin:
  assumes member: "y \<in> set (List.map_filter f xs)"
  shows "\<exists>x\<in>set xs. f x = Some y"
  using member by (induction xs) (auto split: option.splits)

theorem comma_continue24_image_implies_direct_certificate:
  assumes image:
    "\<And>phase source terminal. phase<924 \<Longrightarrow> source<46 \<Longrightarrow>
      comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 24 (phase,source) = Some terminal
      \<Longrightarrow> terminal \<in> comma_continue24_endpoints"
  shows "comma_continue24_direct_image_certificate"
  unfolding comma_continue24_direct_image_certificate_def list_all_iff
proof (intro ballI)
  fix program
  assume member: "program \<in> set comma_semantic_phase_program_catalogue"
  have raw_member:
    "program \<in> set (List.map_filter comma_semantic_phase_program_for_class [0..<46])"
    using member unfolding comma_semantic_phase_program_catalogue_def
    by (simp only: set_remdups)
  obtain source where source: "source<46"
    and binding: "comma_semantic_phase_program_for_class source = Some program"
    using comma_map_filter_member_origin[OF raw_member] by auto
  have unsupported:
    "\<not> comma_crt_supported (comma_continue24_bad_support_column program)
      \<longleftrightarrow> (\<forall>phase<924. \<not>(\<exists>terminal_phase terminal_source.
        comma_phase_class_continue_power comma_semantic_phase_program_class_step
          24 (phase,source) = Some (terminal_phase,terminal_source) \<and>
        (terminal_phase,terminal_source) \<notin> comma_continue24_endpoints))"
    by (rule comma_continue24_bad_support_column_unsupported_iff[OF source binding])
  have no_bad:
    "\<forall>phase<924. \<not>(\<exists>terminal_phase terminal_source.
      comma_phase_class_continue_power comma_semantic_phase_program_class_step
        24 (phase,source) = Some (terminal_phase,terminal_source) \<and>
      (terminal_phase,terminal_source) \<notin> comma_continue24_endpoints)"
    using image[OF _ source] by blast
  show "\<not> comma_crt_supported (comma_continue24_bad_support_column program)"
    by (rule iffD2[OF unsupported no_bad])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic frontier image transports the public opaque support contract"
    @{thms comma_map_filter_member_origin
      comma_continue24_image_implies_direct_certificate};
\<close>

end
