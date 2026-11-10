theory Comma_Parametric_Entry_Closure
  imports Comma_Parametric_Continue_Closure
    Comma_Continue_Frontier24_Core_Guard
    Comma_Symbolic_Class_Step
begin


lemma comma_frontier24_entry_selector_cases:
  assumes shape:
      "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program:
      "cf24_programs bundle ! cf24_closure_program_ref closure =
        Comma_Entry_Core_Program f d residue core"
  shows "\<exists>selector_cases.
    cf24_selectors bundle ! cf24_closure_program_ref closure =
      Comma_Frontier24_Entry_Selector f d residue core selector_cases \<and>
    map cf24_closure_case_wanted (cf24_closure_cases closure) =
      map cf24_case_wanted selector_cases \<and>
    map cf24_closure_case_action_token (cf24_closure_cases closure) =
      map cf24_case_action_token selector_cases \<and>
    map cf24_case_wanted selector_cases = comma_core_supported_values core \<and>
    list_all (\<lambda>row. comma_frontier24_selector_case_action_matches
      f residue core row (cf24_action_tokens bundle)) selector_cases"
  using shape program
  by (cases "cf24_selectors bundle ! cf24_closure_program_ref closure")
    (auto simp: comma_frontier24_closure_shape_checked_def
      comma_frontier24_selector_recipe_matches_def
      split: comma_semantic_port_program.splits)

lemma comma_frontier24_entry_closure_shapeD:
  assumes shape:
      "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program:
      "cf24_programs bundle ! cf24_closure_program_ref closure =
        Comma_Entry_Core_Program f d residue core"
  shows
    "map cf24_closure_case_wanted (cf24_closure_cases closure) =
        comma_core_supported_values core"
    "list_all (\<lambda>row.
        comma_frontier24_case_guard_imported bundle core
          (cf24_closure_case_wanted row)
          (cf24_closure_case_guard_root row) \<and>
        comma_frontier24_closure_case_operation_shape row \<and>
        comma_frontier24_action_output_linked bundle closure_index closure
          (cf24_closure_case_action_token row)
          (cf24_closure_case_action_output_root row)
          (cf24_closure_case_child row))
      (cf24_closure_cases closure)"
    "comma_parametric_bind_chain_links
       (comma_frontier24_closure_case_bind_steps
         (cf24_closure_cases closure)) (cf24_zero_root bundle)"
    "cf24_closure_output_root closure =
      comma_parametric_bind_chain_root
        (comma_frontier24_closure_case_bind_steps
          (cf24_closure_cases closure)) (cf24_zero_root bundle)"
  using shape program comma_frontier24_entry_selector_cases[OF shape program]
  by (auto simp: comma_frontier24_closure_shape_checked_def
    comma_frontier24_selector_recipe_matches_def)

lemma comma_frontier24_entry_case_wanted_map:
  assumes shape:
    "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program:
      "cf24_programs bundle ! cf24_closure_program_ref closure =
        Comma_Entry_Core_Program f d residue core"
  shows "map cf24_closure_case_wanted (cf24_closure_cases closure) =
    comma_core_supported_values core"
proof -
  obtain selector_cases where recipe:
    "cf24_selectors bundle ! cf24_closure_program_ref closure =
       Comma_Frontier24_Entry_Selector f d residue core selector_cases"
    and rows:
    "map cf24_closure_case_wanted (cf24_closure_cases closure) =
      map cf24_case_wanted selector_cases"
    and supported:
    "map cf24_case_wanted selector_cases = comma_core_supported_values core"
    using comma_frontier24_entry_selector_cases[OF shape program] by blast
  show ?thesis using rows supported by simp
qed

lemma comma_frontier24_entry_case_action_matches:
  assumes shape:
      "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program:
      "cf24_programs bundle ! cf24_closure_program_ref closure =
        Comma_Entry_Core_Program f d residue core"
    and row: "row \<in> set (cf24_closure_cases closure)"
  shows "cf24_action_tokens bundle ! cf24_closure_case_action_token row =
    comma_phase_program_entry_core_value_action f residue core
      (cf24_closure_case_wanted row)"
proof -
  obtain selector_cases where recipe:
    "cf24_selectors bundle ! cf24_closure_program_ref closure =
      Comma_Frontier24_Entry_Selector f d residue core selector_cases"
    and wanted_map:
    "map cf24_closure_case_wanted (cf24_closure_cases closure) =
      map cf24_case_wanted selector_cases"
    and action_map:
    "map cf24_closure_case_action_token (cf24_closure_cases closure) =
      map cf24_case_action_token selector_cases"
    and supported:
    "map cf24_case_wanted selector_cases = comma_core_supported_values core"
    and selector_actions:
    "list_all (\<lambda>row. comma_frontier24_selector_case_action_matches
      f residue core row (cf24_action_tokens bundle)) selector_cases"
    using comma_frontier24_entry_selector_cases[OF shape program] by blast
  obtain i where i:
      "i < length (cf24_closure_cases closure)"
      "cf24_closure_cases closure ! i = row"
    using row by (auto simp: in_set_conv_nth)
  have wanted_length:
    "length (map cf24_closure_case_wanted
      (cf24_closure_cases closure)) =
     length (map cf24_case_wanted selector_cases)"
    by (rule arg_cong[OF wanted_map, of length])
  have selector_index: "i < length selector_cases"
    using i(1) wanted_length by simp
  have wanted_map_nth:
    "(map cf24_closure_case_wanted (cf24_closure_cases closure)) ! i =
      (map cf24_case_wanted selector_cases) ! i"
    by (rule arg_cong[OF wanted_map, of "\<lambda>xs. xs ! i"])
  have wanted_at:
    "cf24_closure_case_wanted (cf24_closure_cases closure ! i) =
      cf24_case_wanted (selector_cases ! i)"
    using wanted_map_nth i(1) selector_index by (simp only: nth_map)
  have wanted:
    "cf24_closure_case_wanted row = cf24_case_wanted (selector_cases ! i)"
    using wanted_at i(2) by simp
  have action_map_nth:
    "(map cf24_closure_case_action_token
        (cf24_closure_cases closure)) ! i =
      (map cf24_case_action_token selector_cases) ! i"
    by (rule arg_cong[OF action_map, of "\<lambda>xs. xs ! i"])
  have token_at:
    "cf24_closure_case_action_token (cf24_closure_cases closure ! i) =
      cf24_case_action_token (selector_cases ! i)"
    using action_map_nth i(1) selector_index by (simp only: nth_map)
  have token:
    "cf24_closure_case_action_token row =
      cf24_case_action_token (selector_cases ! i)"
    using token_at i(2) by simp
  have selector_action:
    "comma_frontier24_selector_case_action_matches
      f residue core (selector_cases ! i) (cf24_action_tokens bundle)"
    using selector_actions selector_index by (auto simp: list_all_iff nth_mem)
  show ?thesis
    using wanted token selector_action
    by (auto simp: comma_frontier24_selector_case_action_matches.simps)
qed

lemma comma_frontier24_entry_case_wanted_unique:
  assumes shape:
      "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program:
      "cf24_programs bundle ! cf24_closure_program_ref closure =
        Comma_Entry_Core_Program f d residue core"
    and left: "left \<in> set (cf24_closure_cases closure)"
    and right: "right \<in> set (cf24_closure_cases closure)"
    and left_active:
      "comma_crt_eval (phase+cf24_closure_full_shift closure)
        (comma_core_value_guard core (cf24_closure_case_wanted left))"
    and right_active:
      "comma_crt_eval (phase+cf24_closure_full_shift closure)
        (comma_core_value_guard core (cf24_closure_case_wanted right))"
  shows "left=right"
proof -
  have wanted_eq:
    "cf24_closure_case_wanted left = cf24_closure_case_wanted right"
    by (rule comma_core_value_guard_unique[OF left_active right_active])
  have wanted_map:
    "map cf24_closure_case_wanted (cf24_closure_cases closure) =
      comma_core_supported_values core"
    by (rule comma_frontier24_entry_case_wanted_map[OF shape program])
  have wanted_distinct:
    "distinct (map cf24_closure_case_wanted (cf24_closure_cases closure))"
    using wanted_map by (simp add: comma_core_supported_values_def)
  obtain i where i:
      "i < length (cf24_closure_cases closure)"
      "cf24_closure_cases closure ! i = left"
    using left by (auto simp: in_set_conv_nth)
  obtain j where j:
      "j < length (cf24_closure_cases closure)"
      "cf24_closure_cases closure ! j = right"
    using right by (auto simp: in_set_conv_nth)
  have same_index: "i=j"
    using wanted_distinct wanted_eq i j
    by (auto simp: distinct_conv_nth nth_map)
  then show ?thesis using i j by simp
qed


lemma comma_frontier24_entry_rows_observer_exact:
  assumes shape:
      "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program:
      "cf24_programs bundle ! cf24_closure_program_ref closure =
        Comma_Entry_Core_Program f d residue core"
    and index: "cf24_closure_full_shift closure = shift"
  shows
    "list_ex (\<lambda>row.
        comma_crt_eval (phase+shift)
          (comma_core_value_guard core (cf24_closure_case_wanted row)) \<and>
        comma_phase_continue_action_observer phase f shift
          (cf24_action_tokens bundle !
            cf24_closure_case_action_token row) target)
      (cf24_closure_cases closure) =
      comma_phase_continue_compile_job_observer phase
        (Comma_Continue_Core_Values_Job f residue core
          (comma_core_supported_values core)) shift target"
proof -
  have wanted_map:
    "map cf24_closure_case_wanted (cf24_closure_cases closure) =
      comma_core_supported_values core"
    by (rule comma_frontier24_entry_case_wanted_map[OF shape program])
  have action_matches:
    "\<And>row. row \<in> set (cf24_closure_cases closure) \<Longrightarrow>
      cf24_action_tokens bundle ! cf24_closure_case_action_token row =
        comma_phase_program_entry_core_value_action f residue core
          (cf24_closure_case_wanted row)"
    by (rule comma_frontier24_entry_case_action_matches[OF shape program])
  have row_predicate:
    "\<And>row. row \<in> set (cf24_closure_cases closure) \<Longrightarrow>
      (comma_crt_eval (phase+shift)
          (comma_core_value_guard core (cf24_closure_case_wanted row)) \<and>
        comma_phase_continue_action_observer phase f shift
          (cf24_action_tokens bundle !
            cf24_closure_case_action_token row) target) =
      (comma_crt_eval (phase+shift)
          (comma_core_value_guard core (cf24_closure_case_wanted row)) \<and>
        comma_phase_continue_action_observer phase f shift
          (comma_phase_program_entry_core_value_action f residue core
            (cf24_closure_case_wanted row)) target)"
    using action_matches by simp
  have list_map:
    "list_ex (\<lambda>row.
        comma_crt_eval (phase+shift)
          (comma_core_value_guard core (cf24_closure_case_wanted row)) \<and>
        comma_phase_continue_action_observer phase f shift
          (cf24_action_tokens bundle !
            cf24_closure_case_action_token row) target)
      (cf24_closure_cases closure) =
      list_ex (\<lambda>wanted.
        comma_crt_eval (phase+shift) (comma_core_value_guard core wanted) \<and>
        comma_phase_continue_action_observer phase f shift
          (comma_phase_program_entry_core_value_action f residue core wanted)
          target)
       (map cf24_closure_case_wanted (cf24_closure_cases closure))"
    using row_predicate by (auto simp: list_ex_iff)
  show ?thesis
    using list_map wanted_map
    by (simp only: comma_phase_continue_compile_job_observer.simps(2))
qed

lemma comma_frontier24_closure_case_step_guard_root:
  assumes shape: "comma_frontier24_closure_case_operation_shape row"
  shows "comma_parametric_guard_root
      (comma_frontier24_closure_case_bind_step row) =
    cf24_closure_case_shifted_guard_root row"
  using shape
  by (cases "cf24_closure_case_bind_key row")
    (auto simp: comma_frontier24_closure_case_operation_shape_def
      comma_frontier24_closure_case_bind_step_def)

lemma comma_frontier24_closure_case_step_action_root:
  "comma_parametric_action_root
      (comma_frontier24_closure_case_bind_step row) =
    cf24_closure_case_action_output_root row"
  by (cases "cf24_closure_case_bind_key row")
    (simp add: comma_frontier24_closure_case_bind_step_def)

lemma comma_frontier24_entry_steps_active_unique:
  assumes certified: "comma_frontier24_bundle_semantic_certified bundle"
    and closure: "closure \<in> set (cf24_closures bundle)"
    and shape:
      "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program:
      "cf24_programs bundle ! cf24_closure_program_ref closure =
        Comma_Entry_Core_Program f d residue core"
    and steps:
      "steps = comma_frontier24_closure_case_bind_steps
        (cf24_closure_cases closure)"
  shows
    "\<And>left right. left \<in> set steps \<Longrightarrow> right \<in> set steps \<Longrightarrow>
      (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (comma_parametric_guard_root left) = Some 1) \<Longrightarrow>
      (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (comma_parametric_guard_root right) = Some 1) \<Longrightarrow>
      left=right"
proof -
  have table:
    "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    using certified by (rule comma_frontier24_bundle_semantic_certifiedD(1))
  fix left right
  assume left_mem: "left \<in> set steps"
    and right_mem: "right \<in> set steps"
    and left_active:
      "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (comma_parametric_guard_root left) = Some 1"
    and right_active:
      "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (comma_parametric_guard_root right) = Some 1"
  obtain left_row where left_row:
      "left_row \<in> set (cf24_closure_cases closure)"
      "left = comma_frontier24_closure_case_bind_step left_row"
    using left_mem steps
    by (auto simp: comma_frontier24_closure_case_bind_steps_def)
  obtain right_row where right_row:
      "right_row \<in> set (cf24_closure_cases closure)"
      "right = comma_frontier24_closure_case_bind_step right_row"
    using right_mem steps
    by (auto simp: comma_frontier24_closure_case_bind_steps_def)
  have row_requirements:
    "list_all (\<lambda>row.
        comma_frontier24_case_guard_imported bundle core
          (cf24_closure_case_wanted row)
          (cf24_closure_case_guard_root row) \<and>
        comma_frontier24_closure_case_operation_shape row \<and>
        comma_frontier24_action_output_linked bundle closure_index closure
          (cf24_closure_case_action_token row)
          (cf24_closure_case_action_output_root row)
          (cf24_closure_case_child row))
      (cf24_closure_cases closure)"
    by (rule comma_frontier24_entry_closure_shapeD(2)[OF shape program])
  have left_requirements:
    "comma_frontier24_case_guard_imported bundle core
        (cf24_closure_case_wanted left_row)
        (cf24_closure_case_guard_root left_row) \<and>
     comma_frontier24_closure_case_operation_shape left_row"
    using row_requirements left_row(1) by (auto simp: list_all_iff)
  have right_requirements:
    "comma_frontier24_case_guard_imported bundle core
        (cf24_closure_case_wanted right_row)
        (cf24_closure_case_guard_root right_row) \<and>
     comma_frontier24_closure_case_operation_shape right_row"
    using row_requirements right_row(1) by (auto simp: list_all_iff)
  have left_shape:
    "comma_frontier24_closure_case_operation_shape left_row"
    using left_requirements by simp
  have right_shape:
    "comma_frontier24_closure_case_operation_shape right_row"
    using right_requirements by simp
  have left_imported:
    "comma_frontier24_case_guard_imported bundle core
      (cf24_closure_case_wanted left_row)
      (cf24_closure_case_guard_root left_row)"
    using left_requirements by blast
  have right_imported:
    "comma_frontier24_case_guard_imported bundle core
      (cf24_closure_case_wanted right_row)
      (cf24_closure_case_guard_root right_row)"
    using right_requirements by blast
  have left_root:
    "comma_parametric_guard_root
      (comma_frontier24_closure_case_bind_step left_row) =
      cf24_closure_case_shifted_guard_root left_row"
    by (rule comma_frontier24_closure_case_step_guard_root[OF left_shape])
  have right_root:
    "comma_parametric_guard_root
      (comma_frontier24_closure_case_bind_step right_row) =
      cf24_closure_case_shifted_guard_root right_row"
    by (rule comma_frontier24_closure_case_step_guard_root[OF right_shape])
  have left_value:
    "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_closure_case_shifted_guard_root left_row) =
      Some (if comma_crt_eval
        (phase+cf24_closure_full_shift closure)
        (comma_core_value_guard core
          (cf24_closure_case_wanted left_row)) then 1 else 0)"
    by (rule comma_frontier24_closure_case_guard_value
      [OF certified closure left_row(1) left_imported])
  have right_value:
    "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_closure_case_shifted_guard_root right_row) =
      Some (if comma_crt_eval
        (phase+cf24_closure_full_shift closure)
        (comma_core_value_guard core
          (cf24_closure_case_wanted right_row)) then 1 else 0)"
    by (rule comma_frontier24_closure_case_guard_value
      [OF certified closure right_row(1) right_imported])
  have left_semantic:
    "comma_crt_eval (phase+cf24_closure_full_shift closure)
      (comma_core_value_guard core
        (cf24_closure_case_wanted left_row))"
    using left_active
    by (simp only: left_row(2) left_root left_value
      comma_parametric_boolean_code_one)
  have right_semantic:
    "comma_crt_eval (phase+cf24_closure_full_shift closure)
      (comma_core_value_guard core
        (cf24_closure_case_wanted right_row))"
    using right_active
    by (simp only: right_row(2) right_root right_value
      comma_parametric_boolean_code_one)
  have rows_same:
    "left_row=right_row"
    by (rule comma_frontier24_entry_case_wanted_unique
      [OF shape program left_row(1) right_row(1) left_semantic right_semantic])
  show "left=right"
    using left_row(2) right_row(2) rows_same by simp
qed


lemma comma_frontier24_entry_closure_hit:
  assumes certified: "comma_frontier24_bundle_semantic_certified bundle"
    and closure_mem: "closure \<in> set (cf24_closures bundle)"
    and shape:
      "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program:
      "cf24_programs bundle ! cf24_closure_program_ref closure =
        Comma_Entry_Core_Program f d residue core"
    and child_hit:
      "\<And>child_index target. child_index < closure_index \<Longrightarrow>
        (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
          phase
          (cf24_closure_output_root (cf24_closures bundle ! child_index)) =
            Some (Suc target)) \<longleftrightarrow>
        comma_semantic_phase_program_continue_guard phase
          (cf24_programs bundle !
            cf24_closure_program_ref (cf24_closures bundle ! child_index))
          (cf24_closure_full_shift
            (cf24_closures bundle ! child_index)) target"
  shows
    "(comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_closure_output_root closure) = Some (Suc target)) \<longleftrightarrow>
     comma_semantic_phase_program_continue_guard phase
       (cf24_programs bundle ! cf24_closure_program_ref closure)
       (cf24_closure_full_shift closure) target"
proof -
  let ?cases = "cf24_closure_cases closure"
  let ?steps = "comma_frontier24_closure_case_bind_steps ?cases"
  let ?active = "\<lambda>step. comma_crt_mdd_eval_phase
    (cf24_radices bundle) (cf24_nodes bundle) phase
    (comma_parametric_guard_root step) = Some 1"
  let ?selected = "\<lambda>step. comma_crt_mdd_eval_phase
    (cf24_radices bundle) (cf24_nodes bundle) phase
    (comma_parametric_action_root step) = Some (Suc target)"
  have table:
    "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    using certified by (rule comma_frontier24_bundle_semantic_certifiedD(1))
  have root_index:
    "cf24_closure_program_ref closure < length (cf24_programs bundle)"
    using shape by (auto simp: comma_frontier24_closure_shape_checked_def)
  have admitted:
    "comma_phase_program_structurally_admitted
      (cf24_programs bundle ! cf24_closure_program_ref closure)"
    using certified root_index
    by (auto simp: comma_frontier24_bundle_semantic_certified_def
      comma_frontier24_bundle_semantic_structure_checked_def list_all_iff)
  have entry_shape:
    "map cf24_closure_case_wanted ?cases = comma_core_supported_values core"
    "list_all (\<lambda>row.
        comma_frontier24_case_guard_imported bundle core
          (cf24_closure_case_wanted row)
          (cf24_closure_case_guard_root row) \<and>
        comma_frontier24_closure_case_operation_shape row \<and>
        comma_frontier24_action_output_linked bundle closure_index closure
          (cf24_closure_case_action_token row)
          (cf24_closure_case_action_output_root row)
          (cf24_closure_case_child row))
      ?cases"
    "comma_parametric_bind_chain_links ?steps (cf24_zero_root bundle)"
    "cf24_closure_output_root closure =
      comma_parametric_bind_chain_root ?steps (cf24_zero_root bundle)"
    by (rule comma_frontier24_entry_closure_shapeD[OF shape program])+
  have chain_links:
    "comma_parametric_bind_chain_links ?steps (cf24_zero_root bundle)"
    using entry_shape(3) .
  have chain_output:
    "cf24_closure_output_root closure =
      comma_parametric_bind_chain_root ?steps (cf24_zero_root bundle)"
    using entry_shape(4) .
  have each_step_certificate:
    "\<And>row. row \<in> set ?cases \<Longrightarrow>
      comma_parametric_bind_step_certificate (cf24_radices bundle)
        (cf24_nodes bundle)
        (comma_frontier24_closure_case_bind_step row)"
  proof -
    fix row
    assume row: "row \<in> set ?cases"
    have requirements:
      "comma_frontier24_case_guard_imported bundle core
          (cf24_closure_case_wanted row)
          (cf24_closure_case_guard_root row) \<and>
       comma_frontier24_closure_case_operation_shape row \<and>
       comma_frontier24_action_output_linked bundle closure_index closure
          (cf24_closure_case_action_token row)
          (cf24_closure_case_action_output_root row)
          (cf24_closure_case_child row)"
      using entry_shape(2) row by (auto simp: list_all_iff)
    have bind_cert:
      "case cf24_closure_case_bind_key row of
        (source,fallback,mapping) \<Rightarrow>
          comma_crt_mdd_bind_certificate (cf24_radices bundle)
            (cf24_nodes bundle) mapping fallback source
            (cf24_closure_case_selected_root row)"
      by (rule comma_frontier24_closure_case_bind_certificate
        [OF certified closure_mem row])
    have operation:
      "comma_frontier24_closure_case_operation_shape row"
      using requirements by blast
    show "comma_parametric_bind_step_certificate (cf24_radices bundle)
        (cf24_nodes bundle)
        (comma_frontier24_closure_case_bind_step row)"
      by (rule comma_frontier24_closure_case_bind_step_certificate
        [OF operation bind_cert])
  qed
  have case_step_certificates:
    "list_all (\<lambda>row. comma_parametric_bind_step_certificate
      (cf24_radices bundle) (cf24_nodes bundle)
      (comma_frontier24_closure_case_bind_step row)) ?cases"
    using each_step_certificate by (auto simp: list_all_iff)
  have step_certificates:
    "list_all (comma_parametric_bind_step_certificate
      (cf24_radices bundle) (cf24_nodes bundle)) ?steps"
    using case_step_certificates
    by (auto simp: comma_frontier24_closure_case_bind_steps_def list_all_iff)
  have zero_eval:
    "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_zero_root bundle) = Some 0"
  proof -
    have zero:
      "cf24_nodes bundle ! cf24_zero_root bundle =
        Comma_CRT_MDD_Leaf 0"
      using certified by (auto simp: comma_frontier24_bundle_semantic_certified_def
        comma_frontier24_bundle_semantic_structure_checked_def)
    have zero_bound:
      "cf24_zero_root bundle < length (cf24_nodes bundle)"
      using certified by (auto simp: comma_frontier24_bundle_semantic_certified_def
        comma_frontier24_bundle_semantic_structure_checked_def)
    show ?thesis
      by (rule comma_crt_mdd_eval_phase_leaf[OF table zero_bound zero])
  qed
  have guard_values:
    "\<And>step. step \<in> set ?steps \<Longrightarrow>
      comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (comma_parametric_guard_root step) =
      Some (if ?active step then 1 else 0)"
  proof -
    fix step
    assume step: "step \<in> set ?steps"
    obtain row where row:
        "row \<in> set ?cases"
        "step=comma_frontier24_closure_case_bind_step row"
      using step by (auto simp:
        comma_frontier24_closure_case_bind_steps_def)
    have requirements:
      "comma_frontier24_case_guard_imported bundle core
          (cf24_closure_case_wanted row)
          (cf24_closure_case_guard_root row) \<and>
       comma_frontier24_closure_case_operation_shape row \<and>
       comma_frontier24_action_output_linked bundle closure_index closure
          (cf24_closure_case_action_token row)
          (cf24_closure_case_action_output_root row)
          (cf24_closure_case_child row)"
      using entry_shape(2) row(1) by (auto simp: list_all_iff)
    have operation:
      "comma_frontier24_closure_case_operation_shape row"
      using requirements by simp
    have guard_root:
      "comma_parametric_guard_root
        (comma_frontier24_closure_case_bind_step row) =
        cf24_closure_case_shifted_guard_root row"
      by (rule comma_frontier24_closure_case_step_guard_root[OF operation])
    have imported:
      "comma_frontier24_case_guard_imported bundle core
        (cf24_closure_case_wanted row)
        (cf24_closure_case_guard_root row)"
      using requirements by blast
    have payload:
      "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (cf24_closure_case_shifted_guard_root row) =
      Some (if comma_crt_eval
        (phase+cf24_closure_full_shift closure)
        (comma_core_value_guard core (cf24_closure_case_wanted row))
        then 1 else 0)"
      by (rule comma_frontier24_closure_case_guard_value
        [OF certified closure_mem row(1) imported])
    show "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (comma_parametric_guard_root step) =
      Some (if ?active step then 1 else 0)"
      by (simp only: row(2) guard_root payload comma_parametric_boolean_code_one)
  qed
  have action_total:
    "\<And>step. step \<in> set ?steps \<Longrightarrow>
      \<exists>payload. comma_crt_mdd_eval_phase (cf24_radices bundle)
        (cf24_nodes bundle) phase
        (comma_parametric_action_root step) = Some payload"
  proof -
    fix step
    assume step: "step \<in> set ?steps"
    obtain row where row:
        "row \<in> set ?cases"
        "step=comma_frontier24_closure_case_bind_step row"
      using step by (auto simp:
        comma_frontier24_closure_case_bind_steps_def)
    have requirements:
      "comma_frontier24_case_guard_imported bundle core
          (cf24_closure_case_wanted row)
          (cf24_closure_case_guard_root row) \<and>
       comma_frontier24_closure_case_operation_shape row \<and>
       comma_frontier24_action_output_linked bundle closure_index closure
          (cf24_closure_case_action_token row)
          (cf24_closure_case_action_output_root row)
          (cf24_closure_case_child row)"
      using entry_shape(2) row(1) by (auto simp: list_all_iff)
    have root:
      "comma_parametric_action_root
        (comma_frontier24_closure_case_bind_step row) =
        cf24_closure_case_action_output_root row"
      by (rule comma_frontier24_closure_case_step_action_root)
    have linked:
      "comma_frontier24_action_output_linked bundle closure_index closure
        (cf24_closure_case_action_token row)
        (cf24_closure_case_action_output_root row)
        (cf24_closure_case_child row)"
      using requirements by blast
    have output_bound:
      "cf24_closure_case_action_output_root row < length (cf24_nodes bundle)"
      using linked
      by (auto simp: comma_frontier24_action_output_linked_def)
    show "\<exists>payload. comma_crt_mdd_eval_phase (cf24_radices bundle)
        (cf24_nodes bundle) phase
        (comma_parametric_action_root step) = Some payload"
      using comma_crt_mdd_eval_phase_total[OF table output_bound, where phase=phase]
        row(2) root by simp
  qed
  have action_hits:
    "\<And>step. step \<in> set ?steps \<Longrightarrow>
      (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (comma_parametric_action_root step) = Some (Suc target)) \<longleftrightarrow>
      ?selected step"
    by simp
  have unique_active:
    "\<And>left right. left \<in> set ?steps \<Longrightarrow>
      right \<in> set ?steps \<Longrightarrow> ?active left \<Longrightarrow> ?active right \<Longrightarrow>
      left=right"
  proof -
    fix left right
    assume left: "left \<in> set ?steps"
      and right: "right \<in> set ?steps"
      and left_active: "?active left"
      and right_active: "?active right"
    show "left=right"
      by (rule comma_frontier24_entry_steps_active_unique
        [OF certified closure_mem shape program refl
          left right left_active right_active])
  qed
  have fallback:
    "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_zero_root bundle) = Some 0"
    by (rule zero_eval)
  have selected_cases:
    "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (cf24_closure_output_root closure) = Some (Suc target) \<longleftrightarrow>
      list_ex (\<lambda>row.
        comma_crt_eval (phase+cf24_closure_full_shift closure)
          (comma_core_value_guard core (cf24_closure_case_wanted row)) \<and>
        comma_phase_continue_action_observer phase f
          (cf24_closure_full_shift closure)
          (cf24_action_tokens bundle !
            cf24_closure_case_action_token row) target) ?cases"
  proof -
    have chain:
      "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
          phase (comma_parametric_bind_chain_root ?steps
            (cf24_zero_root bundle)) = Some (Suc target) \<longleftrightarrow>
        list_ex (\<lambda>step. ?active step \<and> ?selected step) ?steps"
      by (rule comma_parametric_bind_chain_hit
        [OF table step_certificates chain_links guard_values action_total
          action_hits fallback unique_active])
    have cases:
      "list_ex (\<lambda>step. ?active step \<and> ?selected step) ?steps =
        list_ex (\<lambda>row.
          comma_crt_eval (phase+cf24_closure_full_shift closure)
            (comma_core_value_guard core (cf24_closure_case_wanted row)) \<and>
          comma_phase_continue_action_observer phase f
            (cf24_closure_full_shift closure)
            (cf24_action_tokens bundle !
              cf24_closure_case_action_token row) target) ?cases"
    proof -
      have active_row:
        "\<And>row. row \<in> set ?cases \<Longrightarrow>
          ?active (comma_frontier24_closure_case_bind_step row) =
          comma_crt_eval (phase+cf24_closure_full_shift closure)
            (comma_core_value_guard core
              (cf24_closure_case_wanted row))"
      proof -
        fix row assume row: "row \<in> set ?cases"
        have operation:
          "comma_frontier24_closure_case_operation_shape row"
          using entry_shape(2) row by (auto simp: list_all_iff)
        have guard_root:
          "comma_parametric_guard_root
            (comma_frontier24_closure_case_bind_step row) =
            cf24_closure_case_shifted_guard_root row"
          by (rule comma_frontier24_closure_case_step_guard_root[OF operation])
        have imported:
          "comma_frontier24_case_guard_imported bundle core
            (cf24_closure_case_wanted row)
            (cf24_closure_case_guard_root row)"
          using entry_shape(2) row by (auto simp: list_all_iff)
        have payload:
          "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
            phase (cf24_closure_case_shifted_guard_root row) =
          Some (if comma_crt_eval
            (phase+cf24_closure_full_shift closure)
            (comma_core_value_guard core (cf24_closure_case_wanted row))
            then 1 else 0)"
          by (rule comma_frontier24_closure_case_guard_value
            [OF certified closure_mem row imported])
        show "?active (comma_frontier24_closure_case_bind_step row) =
          comma_crt_eval (phase+cf24_closure_full_shift closure)
            (comma_core_value_guard core
              (cf24_closure_case_wanted row))"
          by (simp only: guard_root payload comma_parametric_boolean_code_one)
      qed
      have action_row:
        "\<And>row. row \<in> set ?cases \<Longrightarrow>
          ?selected (comma_frontier24_closure_case_bind_step row) =
          comma_phase_continue_action_observer phase f
            (cf24_closure_full_shift closure)
            (cf24_action_tokens bundle !
              cf24_closure_case_action_token row) target"
      proof -
        fix row assume row: "row \<in> set ?cases"
        have action_root:
          "comma_parametric_action_root
            (comma_frontier24_closure_case_bind_step row) =
            cf24_closure_case_action_output_root row"
          by (rule comma_frontier24_closure_case_step_action_root)
        have requirements:
          "comma_frontier24_case_guard_imported bundle core
              (cf24_closure_case_wanted row)
              (cf24_closure_case_guard_root row) \<and>
           comma_frontier24_closure_case_operation_shape row \<and>
           comma_frontier24_action_output_linked bundle closure_index closure
              (cf24_closure_case_action_token row)
              (cf24_closure_case_action_output_root row)
              (cf24_closure_case_child row)"
          using entry_shape(2) row by (auto simp: list_all_iff)
        have linked:
          "comma_frontier24_action_output_linked bundle closure_index closure
            (cf24_closure_case_action_token row)
            (cf24_closure_case_action_output_root row)
            (cf24_closure_case_child row)"
          using requirements by blast
        have hit:
          "(comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
            phase (cf24_closure_case_action_output_root row) =
              Some (Suc target)) \<longleftrightarrow>
            comma_phase_continue_action_observer phase f
              (cf24_closure_full_shift closure)
              (cf24_action_tokens bundle !
                cf24_closure_case_action_token row) target"
          using comma_frontier24_action_output_linked_hit
            [where phase=phase and target=target, OF table linked child_hit]
            program action_root
          by (simp add: comma_phase_program_sector.simps)
        show "?selected (comma_frontier24_closure_case_bind_step row) =
          comma_phase_continue_action_observer phase f
            (cf24_closure_full_shift closure)
            (cf24_action_tokens bundle !
              cf24_closure_case_action_token row) target"
          using action_root hit by simp
      qed
      show ?thesis
        using active_row action_row
        by (auto simp: comma_frontier24_closure_case_bind_steps_def
          list_ex_iff)
    qed
    show ?thesis using chain cases chain_output by simp
  qed
  have rows_observer:
    "list_ex (\<lambda>row.
        comma_crt_eval (phase+cf24_closure_full_shift closure)
          (comma_core_value_guard core (cf24_closure_case_wanted row)) \<and>
        comma_phase_continue_action_observer phase f
          (cf24_closure_full_shift closure)
          (cf24_action_tokens bundle !
            cf24_closure_case_action_token row) target) ?cases =
      comma_phase_continue_compile_job_observer phase
        (Comma_Continue_Core_Values_Job f residue core
          (comma_core_supported_values core))
        (cf24_closure_full_shift closure) target"
    by (rule comma_frontier24_entry_rows_observer_exact
      [OF shape program refl])
  have entry_exact:
    "comma_phase_continue_compile_job_observer phase
        (Comma_Continue_Core_Values_Job f residue core
          (comma_core_supported_values core))
        (cf24_closure_full_shift closure) target =
      comma_semantic_phase_program_continue_guard phase
        (cf24_programs bundle ! cf24_closure_program_ref closure)
        (cf24_closure_full_shift closure) target"
  proof -
    have supported:
      "comma_phase_continue_compile_job_observer phase
        (Comma_Continue_Core_Values_Job f residue core
          (comma_core_supported_values core))
        (cf24_closure_full_shift closure) target =
      comma_phase_continue_compile_job_observer phase
        (Comma_Continue_Core_Values_Job f residue core
          [0..<comma_phase_core_modulus core])
        (cf24_closure_full_shift closure) target"
      by (rule sym; rule comma_phase_continue_core_supported_values_observer)
    have admitted_entry:
      "comma_phase_program_structurally_admitted
        (Comma_Entry_Core_Program f d residue core)"
      using admitted program by simp
    have entry_step:
      "comma_phase_continue_compile_job_observer phase
        (Comma_Continue_Core_Values_Job f residue core
          [0..<comma_phase_core_modulus core])
        (cf24_closure_full_shift closure) target =
      comma_phase_continue_step_observer phase target
        (comma_phase_program_step_at
          (cf24_programs bundle ! cf24_closure_program_ref closure)
          phase (cf24_closure_full_shift closure))"
      using comma_phase_continue_entry_core_values_observer_exact[
        where f=f and d=d and residue=residue and core=core and phase=phase
          and shift="cf24_closure_full_shift closure" and target=target,
        OF admitted_entry]
        program by simp
    show ?thesis
      using supported entry_step comma_semantic_phase_program_continue_guard_step
        program by simp
  qed
  show ?thesis
    using selected_cases rows_observer entry_exact by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Parametric Continue Entry closure refinement"
    @{thms comma_frontier24_entry_closure_hit};
\<close>

end
