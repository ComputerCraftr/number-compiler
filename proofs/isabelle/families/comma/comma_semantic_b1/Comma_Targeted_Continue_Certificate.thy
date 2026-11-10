theory Comma_Targeted_Continue_Certificate
  imports Comma_Continue_Image_Bridge Comma_Semantic_Action_Power
    Comma_Targeted_Continue_Observer_Refinement
begin

text \<open>
Translate the universal 24-step image refinement into the exact B32
summary, action, and bounded Stop weight consumed by downstream clients.
\<close>

theorem comma_semantic_phase_class_B32_exact_output_if_continue24_image:
  assumes image24:
      "\<And>phase cid terminal. phase<924 \<Longrightarrow> cid<46 \<Longrightarrow>
        comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 24 (phase,cid) =
          Some terminal \<Longrightarrow> terminal\<in>comma_continue24_endpoints"
    and phase: "phase<924"
    and cid: "cid<46"
  obtains height terminal where
    "height\<le>26"
    "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!cid)) height terminal"
    "comma_semantic_b1_action_power 5 phase cid =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode height terminal)"
    "comma_terminal_weight_encode height terminal\<le>242"
proof -
  let ?source = "Comma_Decade phase (comma_offset_representatives!cid)"
  have representative: "comma_offset_representatives!cid\<le>90"
    by (rule comma_orbit_representative_index(1)[OF cid])
  have admitted: "comma_decade_admitted ?source"
    using phase representative by simp
  have stopping:
      "\<exists>h tau. h\<le>26 \<and>
        comma_decade_block_power 5 ?source=Comma_Block_Stop h tau \<and>
        comma_residual_block 32 (h,tau)=Comma_Residual_Stop h tau \<and>
        comma_decade_exact_summary ?source h tau"
  proof (rule comma_B32_if_continue24_image)
    show "\<And>p c terminal. p<924 \<Longrightarrow> c<46 \<Longrightarrow>
        comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 24 (p,c)=Some terminal \<Longrightarrow>
        terminal\<in>comma_continue24_endpoints"
      by (rule image24)
    show "comma_decade_admitted ?source" by (rule admitted)
  qed
  obtain height terminal where height: "height\<le>26"
    and exact_summary: "comma_decade_exact_summary ?source height terminal"
    and block_stop:
      "comma_decade_block_power 5 ?source=Comma_Block_Stop height terminal"
    and residual_stop:
      "comma_residual_block 32 (height,terminal)=
        Comma_Residual_Stop height terminal"
    using stopping by blast
  have action_weight:
      "comma_semantic_b1_action_power 5 phase cid =
          Comma_Semantic_B1_Stop
            (comma_terminal_weight_encode height terminal) \<and>
        comma_terminal_weight_encode height terminal\<le>242"
    by (rule comma_semantic_b1_action_stop_from_exact_summary
      [OF phase cid exact_summary height])
  have action:
      "comma_semantic_b1_action_power 5 phase cid =
        Comma_Semantic_B1_Stop
          (comma_terminal_weight_encode height terminal)"
    using action_weight by blast
  have encoded_bound: "comma_terminal_weight_encode height terminal\<le>242"
    using action_weight by blast
  show thesis
    by (rule that[OF height exact_summary action encoded_bound])
qed

lemma comma_continue24_bad_support_exact:
  assumes phase: "phase<924" and source: "source<46"
    and binding: "comma_semantic_phase_program_for_class source=Some program"
  shows "comma_crt_eval phase (comma_continue24_bad_support_column program) =
    (\<exists>terminal_phase terminal_source.
      comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 24 (phase,source) =
          Some (terminal_phase,terminal_source) \<and>
      (terminal_phase,terminal_source)\<notin>comma_continue24_endpoints)"
proof -
  have observer_admitted:
    "comma_continue_observer_admitted comma_continue_bad_endpoint_observer"
    by (rule comma_continue_bad_endpoint_observer_admitted)
  have observer_matches:
    "comma_continue_observer_matches comma_continue_bad_endpoint_observer
      comma_continue_outside_endpoints"
    by (rule comma_continue_bad_endpoint_observer_matches)
  have contract:
    "comma_continue_operator_contract comma_continue_operator_24 24"
    by (rule comma_continue_operator_24_contract)
  have exact:
    "comma_crt_eval phase
        (comma_continue_operator_24 comma_continue_bad_endpoint_observer program 0) =
      (case comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 24 (phase,source) of
          None \<Rightarrow> False
        | Some (terminal_phase,terminal_source) \<Rightarrow>
            comma_continue_outside_endpoints terminal_phase terminal_source)"
    using contract observer_admitted observer_matches phase source binding
    by (auto simp: comma_continue_operator_contract_def)
  show ?thesis
    using exact
    by (auto simp: comma_continue24_bad_support_column_def
        comma_continue_outside_endpoints_def split: option.splits prod.splits)
qed

lemma comma_continue24_bad_support_column_admitted:
  shows "comma_crt_admitted 0 (comma_continue24_bad_support_column program)"
proof -
  have observer_admitted:
    "comma_continue_observer_admitted comma_continue_bad_endpoint_observer"
    by (rule comma_continue_bad_endpoint_observer_admitted)
  have contract:
    "comma_continue_operator_contract comma_continue_operator_24 24"
    by (rule comma_continue_operator_24_contract)
  have output_admitted:
    "comma_crt_admitted 0
      (comma_continue_operator_24 comma_continue_bad_endpoint_observer program 0)"
    using contract observer_admitted
    by (auto simp: comma_continue_operator_contract_def)
  show ?thesis
    using output_admitted
    by (simp add: comma_continue24_bad_support_column_def)
qed

lemma comma_continue24_bad_support_column_unsupported_iff:
  assumes source: "source<46"
    and binding: "comma_semantic_phase_program_for_class source=Some program"
  shows "\<not> comma_crt_supported
      (comma_continue24_bad_support_column program) \<longleftrightarrow>
    (\<forall>phase<924. \<not>(\<exists>terminal_phase terminal_source.
      comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 24 (phase,source) =
          Some (terminal_phase,terminal_source) \<and>
      (terminal_phase,terminal_source)\<notin>comma_continue24_endpoints))"
proof -
  have admitted:
    "comma_crt_admitted 0 (comma_continue24_bad_support_column program)"
    by (rule comma_continue24_bad_support_column_admitted)
  have support_iff:
    "comma_crt_supported (comma_continue24_bad_support_column program) \<longleftrightarrow>
      comma_crt_set (comma_continue24_bad_support_column program)\<noteq>{}"
    using comma_crt_supported_nonempty[OF admitted] by blast
  show ?thesis
    using support_iff comma_continue24_bad_support_exact[OF _ source binding]
    by (auto simp: comma_crt_set_def)
qed

lemma comma_map_filter_member:
  assumes member: "x\<in>set xs" and selected: "f x=Some y"
  shows "y\<in>set (List.map_filter f xs)"
  using member selected
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons head tail)
  show ?case
  proof (cases "x=head")
    case True
    then show ?thesis using Cons.prems
      by (cases "f head") auto
  next
    case False
    have member_tail: "x\<in>set tail"
      using Cons.prems(1) False by simp
    have selected_tail: "f x=Some y"
      using Cons.prems(2) by simp
    have tail_member: "y\<in>set (List.map_filter f tail)"
      by (rule Cons.IH[OF member_tail selected_tail])
    show ?thesis
      using tail_member False by (cases "f head") auto
  qed
qed

lemma comma_semantic_phase_program_catalogue_contains_bound_class:
  assumes source: "source<46"
    and binding: "comma_semantic_phase_program_for_class source=Some program"
  shows "program\<in>set comma_semantic_phase_program_catalogue"
proof -
  have source_member: "source\<in>set [0..<46]"
    using source by simp
  have raw_member:
    "program\<in>set (List.map_filter comma_semantic_phase_program_for_class [0..<46])"
    by (rule comma_map_filter_member
      [where x=source and xs="[0..<46]"
        and f=comma_semantic_phase_program_for_class and y=program])
       (use source_member binding in auto)
  show ?thesis
    using raw_member
    unfolding comma_semantic_phase_program_catalogue_def
    by (simp only: set_remdups)
qed

theorem comma_continue24_direct_image_implies_image24:
  assumes certificate: "comma_continue24_direct_image_certificate"
  shows "\<And>phase source terminal. phase<924 \<Longrightarrow> source<46 \<Longrightarrow>
    comma_phase_class_continue_power
      comma_semantic_phase_program_class_step 24 (phase,source)=Some terminal
    \<Longrightarrow> terminal\<in>comma_continue24_endpoints"
proof -
  fix phase source terminal
  assume phase: "phase<924" and source: "source<46"
    and powered:
      "comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 24 (phase,source)=Some terminal"
  obtain program where binding:
      "comma_semantic_phase_program_for_class source=Some program"
    using comma_semantic_phase_program_for_class_some[OF source] by blast
  have catalogue_member:
    "program\<in>set comma_semantic_phase_program_catalogue"
    by (rule comma_semantic_phase_program_catalogue_contains_bound_class
      [OF source binding])
  have no_bad_support:
    "\<not> comma_crt_supported
      (comma_continue24_bad_support_column program)"
    using certificate catalogue_member
    by (auto simp: comma_continue24_direct_image_certificate_def list_all_iff)
  have unsupported_iff:
    "\<not> comma_crt_supported
      (comma_continue24_bad_support_column program) \<longleftrightarrow>
      (\<forall>phase<924. \<not>(\<exists>terminal_phase terminal_source.
        comma_phase_class_continue_power
          comma_semantic_phase_program_class_step 24 (phase,source) =
            Some (terminal_phase,terminal_source) \<and>
        (terminal_phase,terminal_source)\<notin>comma_continue24_endpoints))"
    by (rule comma_continue24_bad_support_column_unsupported_iff[OF source binding])
  have no_bad_path:
    "\<forall>phase<924. \<not>(\<exists>terminal_phase terminal_source.
      comma_phase_class_continue_power
        comma_semantic_phase_program_class_step 24 (phase,source) =
          Some (terminal_phase,terminal_source) \<and>
      (terminal_phase,terminal_source)\<notin>comma_continue24_endpoints)"
    by (rule iffD1[OF unsupported_iff no_bad_support])
  obtain terminal_phase terminal_source where terminal:
      "terminal=(terminal_phase,terminal_source)"
    by (cases terminal) auto
  show "terminal\<in>comma_continue24_endpoints"
    using no_bad_path[rule_format, OF phase] powered terminal by blast
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Exact B32 output from source-free Continue image"
    @{thms comma_semantic_phase_class_B32_exact_output_if_continue24_image};
\<close>

end
