theory Comma_Parametric_Entry_Closure
  imports Comma_Parametric_Typed_Output
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
        comma_frontier24_action_output_linked bundle closure_index closure
          (cf24_closure_case_action_token row)
          (cf24_closure_case_action_output_root row)
          (cf24_closure_case_child row))
      (cf24_closure_cases closure)"
    "cf24_closure_near_token closure = None"
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

lemma comma_frontier24_entry_rows_typed_fold:
  assumes shape:
      "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program:
      "cf24_programs bundle ! cf24_closure_program_ref closure =
        Comma_Entry_Core_Program f d residue core"
  shows "foldr (\<lambda>row tail.
      if comma_crt_eval (phase + cf24_closure_full_shift closure)
          (comma_core_value_guard core (cf24_closure_case_wanted row))
      then comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
        (cf24_action_tokens bundle ! cf24_closure_case_action_token row) child_code
      else tail) (cf24_closure_cases closure) 0 =
    foldr (\<lambda>wanted tail.
      if comma_crt_eval (phase + cf24_closure_full_shift closure)
          (comma_core_value_guard core wanted)
      then comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
        (comma_phase_program_entry_core_value_action f residue core wanted) child_code
      else tail) (comma_core_supported_values core) 0"
proof -
  have wanted: "map cf24_closure_case_wanted (cf24_closure_cases closure) =
      comma_core_supported_values core"
    by (rule comma_frontier24_entry_case_wanted_map[OF shape program])
  have actions: "\<And>row. row \<in> set (cf24_closure_cases closure) \<Longrightarrow>
      cf24_action_tokens bundle ! cf24_closure_case_action_token row =
        comma_phase_program_entry_core_value_action f residue core
          (cf24_closure_case_wanted row)"
    by (rule comma_frontier24_entry_case_action_matches[OF shape program])
  have fold_map:
    "\<And>rows::comma_frontier24_closure_case list. (\<And>row. row \<in> set rows \<Longrightarrow>
        cf24_action_tokens bundle ! cf24_closure_case_action_token row =
          comma_phase_program_entry_core_value_action f residue core
            (cf24_closure_case_wanted row)) \<Longrightarrow>
      foldr (\<lambda>row tail.
        if comma_crt_eval (phase + cf24_closure_full_shift closure)
            (comma_core_value_guard core (cf24_closure_case_wanted row))
        then comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
          (cf24_action_tokens bundle ! cf24_closure_case_action_token row) child_code
        else tail) rows 0 =
      foldr (\<lambda>wanted tail.
        if comma_crt_eval (phase + cf24_closure_full_shift closure)
            (comma_core_value_guard core wanted)
        then comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
          (comma_phase_program_entry_core_value_action f residue core wanted) child_code
        else tail) (map cf24_closure_case_wanted rows) 0"
  proof -
    fix rows :: "comma_frontier24_closure_case list"
    assume matches: "\<And>row. row \<in> set rows \<Longrightarrow>
      cf24_action_tokens bundle ! cf24_closure_case_action_token row =
        comma_phase_program_entry_core_value_action f residue core
          (cf24_closure_case_wanted row)"
    show "foldr (\<lambda>row tail.
        if comma_crt_eval (phase + cf24_closure_full_shift closure)
            (comma_core_value_guard core (cf24_closure_case_wanted row))
        then comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
          (cf24_action_tokens bundle ! cf24_closure_case_action_token row) child_code
        else tail) rows 0 =
      foldr (\<lambda>wanted tail.
        if comma_crt_eval (phase + cf24_closure_full_shift closure)
            (comma_core_value_guard core wanted)
        then comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
          (comma_phase_program_entry_core_value_action f residue core wanted) child_code
        else tail) (map cf24_closure_case_wanted rows) 0"
      using matches by (induction rows) auto
  qed
  show ?thesis using fold_map[OF actions] wanted by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Parametric Continue Entry closure refinement"
    @{thms comma_frontier24_entry_rows_typed_fold};
\<close>

end
