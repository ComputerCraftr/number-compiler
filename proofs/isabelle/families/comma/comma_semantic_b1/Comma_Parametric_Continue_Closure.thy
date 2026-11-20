theory Comma_Parametric_Continue_Closure
  imports "HOL-Library.Code_Target_Nat"
    Comma_Semantic_Phase_Action_Program
    Comma_Parametric_Continue_Action
    Comma_Continue_Frontier24_Core_Guard
    Comma_CRT_MDD_Multiway
    Comma_CRT_MDD_Shift
    Comma_CRT_MDD_Transport
begin

lemma comma_parametric_boolean_code_one:
  "(Some (if active then (1::nat) else 0) = Some 1) \<longleftrightarrow> active"
  by (cases active) simp_all

text \<open>
Compile the source-independent control vocabulary once into ML for the
untrusted Frontier24 data producer.  The reflected evaluator provides only
candidate data; all resulting program, action, guard, shift, and multiway claims
must still be discharged by the kernel replay theorems.
\<close>

code_reflect Comma_Frontier24_Data
  datatypes comma_phase_core_id = _
    and comma_semantic_port_program = _
    and comma_finite_position = _
    and comma_source_continuation_action = _
    and comma_crt_mdd_node = _
    and comma_phase_class_action = _
  functions "integer_of_nat" "nat_of_integer"
    "comma_semantic_phase_program_for_class"
    "comma_semantic_phase_program_class_step"
    "comma_semantic_port_program_of_source"
    "comma_core_supported_values"
    "comma_phase_core_modulus"
    "comma_recursive_core_residue"
    "comma_phase_program_entry_core_value_action"
    "comma_entry_core_action_key"
    "comma_entry_row_action"
    "comma_entry_port_row"
    "comma_decisive_entry_clock_key_from_core_residue"
    "comma_phase_program_operator_nf"
    "comma_phase_program_structurally_admitted"
    "comma_frontier24_core_guard_nodes"
    "comma_frontier24_core_guard_root"
    "comma_offset_orbit"
    "comma_parametric_exit_continue_code"
    "comma_phase_continue_exit_target"

record comma_frontier24_selector_case =
  cf24_case_wanted :: nat
  cf24_case_guard_root :: nat
  cf24_case_action_token :: nat

datatype comma_frontier24_selector_recipe =
    Comma_Frontier24_Near_Selector nat
  | Comma_Frontier24_Entry_Selector nat nat nat comma_phase_core_id
      "comma_frontier24_selector_case list"

record comma_frontier24_closure_case =
  cf24_closure_case_wanted :: nat
  cf24_closure_case_guard_root :: nat
  cf24_closure_case_shifted_guard_root :: nat
  cf24_closure_case_action_token :: nat
  cf24_closure_case_action_output_root :: nat
  cf24_closure_case_child :: "nat option"

record comma_frontier24_closure =
  cf24_closure_program_ref :: nat
  cf24_closure_full_shift :: nat
  cf24_closure_cases :: "comma_frontier24_closure_case list"
  cf24_closure_near_token :: "nat option"
  cf24_closure_near_action_output_root :: "nat option"
  cf24_closure_near_child :: "nat option"
  cf24_closure_output_root :: nat

record comma_frontier24_guard_entry =
  cf24_guard_core :: comma_phase_core_id
  cf24_guard_wanted :: nat
  cf24_guard_root :: nat

record comma_frontier24_parametric_bundle =
  cf24_programs :: "comma_semantic_port_program list"
  cf24_selectors :: "comma_frontier24_selector_recipe list"
  cf24_action_tokens :: "comma_source_continuation_action list"
  cf24_guard_entries :: "comma_frontier24_guard_entry list"
  cf24_closures :: "comma_frontier24_closure list"
  cf24_class_program_refs :: "nat list"
  cf24_class_roots :: "nat list"
  cf24_radices :: "nat list"
  cf24_nodes :: "nat comma_crt_mdd_node list"
  cf24_zero_root :: nat

fun comma_frontier24_selector_case_action_matches ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_phase_core_id \<Rightarrow>
      comma_frontier24_selector_case \<Rightarrow>
      comma_source_continuation_action list \<Rightarrow> bool" where
  "comma_frontier24_selector_case_action_matches f residue core row actions =
    (cf24_case_action_token row < length actions \<and>
      actions ! cf24_case_action_token row =
        comma_phase_program_entry_core_value_action f residue core
          (cf24_case_wanted row))"

definition comma_frontier24_selector_recipe_matches ::
    "comma_semantic_port_program \<Rightarrow>
      comma_frontier24_selector_recipe \<Rightarrow>
      comma_source_continuation_action list \<Rightarrow> bool" where
  "comma_frontier24_selector_recipe_matches program recipe actions \<longleftrightarrow>
    (case (program,recipe) of
       (Comma_Entry_Core_Program f d residue core,
        Comma_Frontier24_Entry_Selector f' d' residue' core' rows) \<Rightarrow>
          f=f' \<and> d=d' \<and> residue=residue' \<and> core=core' \<and>
          map cf24_case_wanted rows = comma_core_supported_values core \<and>
          list_all (\<lambda>row. comma_frontier24_selector_case_action_matches
            f residue core row actions) rows
     | (Comma_Near_Residual_Program f d residual,
        Comma_Frontier24_Near_Selector token) \<Rightarrow>
          token < length actions \<and>
          actions ! token = comma_phase_program_operator_nf program 0
     | (Comma_Near_Boundary_Program f,
        Comma_Frontier24_Near_Selector token) \<Rightarrow>
          token < length actions \<and>
          actions ! token = comma_phase_program_operator_nf program 0
     | _ \<Rightarrow> False)"

definition comma_frontier24_selector_rows_checked ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_selector_rows_checked bundle \<longleftrightarrow>
    length (cf24_programs bundle) = length (cf24_selectors bundle) \<and>
    list_all2 (\<lambda>program selector.
      comma_frontier24_selector_recipe_matches program selector
        (cf24_action_tokens bundle))
      (cf24_programs bundle) (cf24_selectors bundle)"

lemma comma_frontier24_selector_rows_checked_code [code]:
  "comma_frontier24_selector_rows_checked bundle =
    list_all2 (\<lambda>program selector.
      comma_frontier24_selector_recipe_matches program selector
        (cf24_action_tokens bundle))
      (cf24_programs bundle) (cf24_selectors bundle)"
  by (auto simp: comma_frontier24_selector_rows_checked_def
      dest: list_all2_lengthD)

lemma comma_frontier24_selector_rows_checkedD:
  assumes checked: "comma_frontier24_selector_rows_checked bundle"
    and index: "i < length (cf24_programs bundle)"
  shows "comma_frontier24_selector_recipe_matches
      (cf24_programs bundle ! i) (cf24_selectors bundle ! i)
      (cf24_action_tokens bundle)"
  using checked index
  by (auto simp: comma_frontier24_selector_rows_checked_def
      list_all2_conv_all_nth)

lemma comma_frontier24_selector_rows_indexed_intro:
  assumes extent: "length (cf24_programs bundle) = length (cf24_selectors bundle)"
    and rows: "list_all (\<lambda>i. comma_frontier24_selector_recipe_matches
      (cf24_programs bundle ! i) (cf24_selectors bundle ! i)
      (cf24_action_tokens bundle)) [0..<length (cf24_programs bundle)]"
  shows "comma_frontier24_selector_rows_checked bundle"
  using extent rows
  by (auto simp: comma_frontier24_selector_rows_checked_def
      list_all2_conv_all_nth list_all_iff)

text \<open>These introduction rules assemble already authenticated full-action
bindings in source order. They do not evaluate Entry or Near arithmetic.\<close>

lemma comma_frontier24_selector_case_intro:
  assumes bound: "cf24_case_action_token row < length tokens"
    and action: "tokens ! cf24_case_action_token row =
      comma_phase_program_entry_core_value_action f residue core (cf24_case_wanted row)"
  shows "comma_frontier24_selector_case_action_matches f residue core row tokens"
  using bound action by simp

lemma comma_frontier24_selector_cases_nil:
  "list_all (\<lambda>row. comma_frontier24_selector_case_action_matches
    f residue core row tokens) []"
  by simp

lemma comma_frontier24_selector_cases_cons:
  assumes head: "comma_frontier24_selector_case_action_matches f residue core row tokens"
    and tail: "list_all (\<lambda>r. comma_frontier24_selector_case_action_matches
      f residue core r tokens) rows"
  shows "list_all (\<lambda>r. comma_frontier24_selector_case_action_matches
    f residue core r tokens) (row # rows)"
  using head tail by simp

lemma comma_frontier24_selector_entry_intro:
  assumes wanted: "map cf24_case_wanted rows = comma_core_supported_values core"
    and actions: "list_all (\<lambda>row. comma_frontier24_selector_case_action_matches
      f residue core row tokens) rows"
  shows "comma_frontier24_selector_recipe_matches
    (Comma_Entry_Core_Program f d residue core)
    (Comma_Frontier24_Entry_Selector f d residue core rows) tokens"
  using wanted actions by (simp only: comma_frontier24_selector_recipe_matches_def
      prod.case comma_semantic_port_program.simps comma_frontier24_selector_recipe.simps)

lemma comma_frontier24_selector_near_residual_intro:
  assumes bound: "token < length tokens"
    and action: "tokens ! token = comma_phase_program_operator_nf
      (Comma_Near_Residual_Program f d residual) 0"
  shows "comma_frontier24_selector_recipe_matches
    (Comma_Near_Residual_Program f d residual)
    (Comma_Frontier24_Near_Selector token) tokens"
  using bound action by (simp only: comma_frontier24_selector_recipe_matches_def
      prod.case comma_semantic_port_program.simps comma_frontier24_selector_recipe.simps)

lemma comma_frontier24_selector_near_boundary_intro:
  assumes bound: "token < length tokens"
    and action: "tokens ! token = comma_phase_program_operator_nf
      (Comma_Near_Boundary_Program f) 0"
  shows "comma_frontier24_selector_recipe_matches
    (Comma_Near_Boundary_Program f)
    (Comma_Frontier24_Near_Selector token) tokens"
  using bound action by (simp only: comma_frontier24_selector_recipe_matches_def
      prod.case comma_semantic_port_program.simps comma_frontier24_selector_recipe.simps)

lemma comma_frontier24_selector_rows_nil:
  "list_all2 (\<lambda>program selector.
    comma_frontier24_selector_recipe_matches program selector actions) [] []"
  by simp

lemma comma_frontier24_selector_rows_cons:
  assumes head: "comma_frontier24_selector_recipe_matches program selector actions"
    and tail: "list_all2 (\<lambda>p s. comma_frontier24_selector_recipe_matches p s actions)
      programs selectors"
  shows "list_all2 (\<lambda>p s. comma_frontier24_selector_recipe_matches p s actions)
    (program # programs) (selector # selectors)"
  using head tail by simp

lemma comma_frontier24_selector_rows_intro:
  assumes paired: "list_all2 (\<lambda>p s. comma_frontier24_selector_recipe_matches p s
      (cf24_action_tokens bundle)) (cf24_programs bundle) (cf24_selectors bundle)"
  shows "comma_frontier24_selector_rows_checked bundle"
  using paired list_all2_lengthD
  by (auto simp: comma_frontier24_selector_rows_checked_def)

text \<open>Do not simplify a selector body before its list arguments supply
the program and row. The predicate remains unchanged by these congruences;
each concrete application is still evaluated and checked.\<close>

lemma comma_frontier24_list_all2_weak_cong:
  "xs=xs' \<Longrightarrow> ys=ys' \<Longrightarrow>
    list_all2 P xs ys = list_all2 P xs' ys'"
  by simp

lemma comma_frontier24_list_all_weak_cong:
  "xs=xs' \<Longrightarrow> list_all P xs = list_all P xs'"
  by simp

lemma comma_frontier24_selector_recipe_weak_cong:
  "program=program' \<Longrightarrow> recipe=recipe' \<Longrightarrow>
    comma_frontier24_selector_recipe_matches program recipe actions =
    comma_frontier24_selector_recipe_matches program' recipe' actions"
  by simp

lemma comma_frontier24_selector_case_action_weak_cong:
  "f=f' \<Longrightarrow> residue=residue' \<Longrightarrow>
    core=core' \<Longrightarrow> row=row' \<Longrightarrow>
    comma_frontier24_selector_case_action_matches f residue core row actions =
    comma_frontier24_selector_case_action_matches f' residue' core' row' actions"
  by simp

definition comma_frontier24_case_guard_imported ::
    "comma_frontier24_parametric_bundle \<Rightarrow>
      comma_phase_core_id \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_frontier24_case_guard_imported bundle core wanted root \<longleftrightarrow>
    (\<exists>entry\<in>set (cf24_guard_entries bundle).
      cf24_guard_core entry=core \<and>
      cf24_guard_wanted entry=wanted \<and>
      cf24_guard_root entry=root)"

definition comma_frontier24_action_output_linked_scalar ::
    "comma_frontier24_parametric_bundle \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> bool" where
  "comma_frontier24_action_output_linked_scalar bundle closure_index program_ref full_shift
      token output_root child_ref \<longleftrightarrow>
    token < length (cf24_action_tokens bundle) \<and>
    program_ref < length (cf24_programs bundle) \<and>
    output_root < length (cf24_nodes bundle) \<and>
    (case cf24_action_tokens bundle ! token of
       Comma_Continuation_Goto source delta \<Rightarrow>
         (case (comma_semantic_port_program_of_source source,
             child_ref) of
            (Some child_program, Some child_index) \<Rightarrow>
              child_index < closure_index \<and>
              child_index < length (cf24_closures bundle) \<and>
              (let parent_program = cf24_programs bundle !
                     program_ref;
                   child = cf24_closures bundle ! child_index
               in cf24_closure_program_ref child < length (cf24_programs bundle) \<and>
                 cf24_programs bundle ! cf24_closure_program_ref child =
                   child_program \<and>
                 cf24_closure_full_shift child=
                   full_shift+delta \<and>
                 comma_phase_program_sector parent_program <
                   comma_phase_program_sector child_program \<and>
                 comma_phase_program_sector child_program \<le> 9 \<and>
                 output_root=cf24_closure_output_root child)
          | (None,None) \<Rightarrow>
              output_root=cf24_zero_root bundle \<and>
              cf24_nodes bundle ! output_root=Comma_CRT_MDD_Leaf 0
          | (Some child_program,None) \<Rightarrow>
              (let parent_program=cf24_programs bundle !
                    program_ref
               in \<not> (comma_phase_program_sector parent_program <
                    comma_phase_program_sector child_program \<and>
                    comma_phase_program_sector child_program \<le> 9)) \<and>
                output_root=cf24_zero_root bundle \<and>
                cf24_nodes bundle ! output_root=Comma_CRT_MDD_Leaf 0
          | _ \<Rightarrow> False)
     | Comma_Continuation_Exit source delta \<Rightarrow>
         child_ref=None \<and>
         cf24_nodes bundle ! output_root = Comma_CRT_MDD_Leaf
           (comma_parametric_exit_continue_code source
             (full_shift+delta))
     | Comma_Continuation_Fork digit delta \<Rightarrow>
         child_ref=None \<and> cf24_nodes bundle ! output_root = Comma_CRT_MDD_Leaf
           (if 2 \<le> digit \<and> digit \<le> 9 \<and>
                 full_shift + delta = 0
            then 45 + digit else 0)
     | Comma_Continuation_Landmine delta \<Rightarrow>
         child_ref=None \<and> cf24_nodes bundle ! output_root = Comma_CRT_MDD_Leaf
           (if full_shift + delta = 0 then 55 else 0)
     | Comma_Continuation_Invalid \<Rightarrow>
         child_ref=None \<and> output_root=cf24_zero_root bundle \<and>
         cf24_nodes bundle ! output_root=Comma_CRT_MDD_Leaf 0)"

definition comma_frontier24_action_output_linked ::
    "comma_frontier24_parametric_bundle \<Rightarrow>
      nat \<Rightarrow> comma_frontier24_closure \<Rightarrow>
      nat \<Rightarrow> nat \<Rightarrow> nat option \<Rightarrow> bool" where
  "comma_frontier24_action_output_linked bundle closure_index closure token output_root child_ref \<longleftrightarrow>
    comma_frontier24_action_output_linked_scalar bundle closure_index
      (cf24_closure_program_ref closure) (cf24_closure_full_shift closure)
      token output_root child_ref"

definition comma_frontier24_closure_shape_checked ::
    "comma_frontier24_parametric_bundle \<Rightarrow> nat \<times>
      comma_frontier24_closure \<Rightarrow> bool" where
  "comma_frontier24_closure_shape_checked bundle indexed_closure \<longleftrightarrow>
    (case indexed_closure of (closure_index,closure) \<Rightarrow>
    cf24_closure_program_ref closure < length (cf24_programs bundle) \<and>
    cf24_closure_output_root closure < length (cf24_nodes bundle) \<and>
    (let program = cf24_programs bundle ! cf24_closure_program_ref closure;
         recipe = cf24_selectors bundle ! cf24_closure_program_ref closure
     in comma_frontier24_selector_recipe_matches program recipe
          (cf24_action_tokens bundle) \<and>
        (case (program,recipe) of
          (Comma_Entry_Core_Program f d residue core,
           Comma_Frontier24_Entry_Selector f' d' residue' core' selector_cases) \<Rightarrow>
             f=f' \<and> d=d' \<and> residue=residue' \<and> core=core' \<and>
             cf24_closure_near_token closure=None \<and>
             cf24_closure_near_action_output_root closure=None \<and>
             cf24_closure_near_child closure=None \<and>
             map cf24_closure_case_wanted (cf24_closure_cases closure) =
               map cf24_case_wanted selector_cases \<and>
             map cf24_closure_case_guard_root (cf24_closure_cases closure) =
               map cf24_case_guard_root selector_cases \<and>
             map cf24_closure_case_action_token (cf24_closure_cases closure) =
               map cf24_case_action_token selector_cases \<and>
             list_all (\<lambda>row.
               comma_frontier24_case_guard_imported bundle core
                 (cf24_closure_case_wanted row)
                 (cf24_closure_case_guard_root row) \<and>
               comma_frontier24_action_output_linked bundle closure_index closure
                 (cf24_closure_case_action_token row)
                 (cf24_closure_case_action_output_root row)
                 (cf24_closure_case_child row))
               (cf24_closure_cases closure)
        | (_,Comma_Frontier24_Near_Selector token) \<Rightarrow>
             cf24_closure_cases closure=[] \<and>
             cf24_closure_near_token closure=Some token \<and>
             (case (cf24_closure_near_action_output_root closure,
                 cf24_closure_near_child closure) of
               (Some action_root,child_ref) \<Rightarrow>
                 comma_frontier24_action_output_linked bundle closure_index closure
                   token action_root child_ref \<and>
                 cf24_closure_output_root closure=action_root
             | _ \<Rightarrow> False)
        | _ \<Rightarrow> False)))"

definition comma_frontier24_class_roots_checked ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_class_roots_checked bundle \<longleftrightarrow>
    length (cf24_class_program_refs bundle)=46 \<and>
    length (cf24_class_roots bundle)=46 \<and>
    list_all (\<lambda>cid.
      (case comma_semantic_phase_program_for_class cid of
         None \<Rightarrow> False
       | Some program \<Rightarrow>
           cf24_class_program_refs bundle ! cid < length (cf24_programs bundle) \<and>
           cf24_programs bundle ! (cf24_class_program_refs bundle ! cid)=program \<and>
           (\<exists>closure\<in>set (cf24_closures bundle).
             cf24_closure_program_ref closure=cf24_class_program_refs bundle ! cid \<and>
             cf24_closure_full_shift closure=0 \<and>
             cf24_closure_output_root closure=cf24_class_roots bundle ! cid)))
      [0..<46]"

definition comma_frontier24_closure_structure_checked ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_closure_structure_checked bundle \<longleftrightarrow>
    comma_frontier24_selector_rows_checked bundle \<and>
    list_all comma_phase_program_structurally_admitted (cf24_programs bundle) \<and>
    cf24_zero_root bundle < length (cf24_nodes bundle) \<and>
    cf24_nodes bundle ! cf24_zero_root bundle=Comma_CRT_MDD_Leaf 0 \<and>
    list_all (comma_frontier24_closure_shape_checked bundle)
      (zip [0..<length (cf24_closures bundle)] (cf24_closures bundle))"

definition comma_frontier24_bundle_semantic_structure_checked ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_bundle_semantic_structure_checked bundle \<longleftrightarrow>
    comma_frontier24_selector_rows_checked bundle \<and>
    list_all comma_phase_program_structurally_admitted
      (cf24_programs bundle) \<and>
    cf24_zero_root bundle < length (cf24_nodes bundle) \<and>
    cf24_nodes bundle ! cf24_zero_root bundle=Comma_CRT_MDD_Leaf 0 \<and>
    list_all (comma_frontier24_closure_shape_checked bundle)
      (zip [0..<length (cf24_closures bundle)] (cf24_closures bundle)) \<and>
    comma_frontier24_class_roots_checked bundle"

lemma comma_frontier24_structure_iff_closures_and_classes:
  "comma_frontier24_bundle_semantic_structure_checked bundle \<longleftrightarrow>
    comma_frontier24_closure_structure_checked bundle \<and>
      comma_frontier24_class_roots_checked bundle"
  by (simp only: comma_frontier24_bundle_semantic_structure_checked_def
      comma_frontier24_closure_structure_checked_def conj_assoc)

lemma comma_frontier24_closure_at_checked_from_closures:
  assumes structural: "comma_frontier24_closure_structure_checked bundle"
    and index: "i < length (cf24_closures bundle)"
  shows "comma_frontier24_closure_shape_checked bundle
      (i,cf24_closures bundle ! i)"
proof -
  let ?rows = "zip [0..<length (cf24_closures bundle)] (cf24_closures bundle)"
  have checked: "list_all (comma_frontier24_closure_shape_checked bundle) ?rows"
    using structural unfolding comma_frontier24_closure_structure_checked_def by blast
  have row_bound: "i < length ?rows" using index by simp
  have member: "?rows ! i \<in> set ?rows" by (rule nth_mem[OF row_bound])
  have selected: "?rows ! i = (i,cf24_closures bundle ! i)"
    using index by (simp add: nth_zip)
  show ?thesis using checked member selected by (auto simp: list_all_iff)
qed

lemma comma_frontier24_closure_at_checked:
  assumes structural: "comma_frontier24_bundle_semantic_structure_checked bundle"
    and index: "i < length (cf24_closures bundle)"
  shows "comma_frontier24_closure_shape_checked bundle
      (i,cf24_closures bundle ! i)"
proof -
  have closures: "comma_frontier24_closure_structure_checked bundle"
    using structural by (simp only: comma_frontier24_structure_iff_closures_and_classes; blast)
  show ?thesis by (rule comma_frontier24_closure_at_checked_from_closures[OF closures index])
qed

text \<open>
The arena certifier replays each distinct structural operation once.  These
request lists are derived from the source-bound closure applications; their
references are proof-local construction coordinates, not semantic IDs.  The
proof consumes the corresponding inductive certificates in a generic list
theorem rather than issuing one semantic proof per class or phase.
\<close>

definition comma_frontier24_shift_requests ::
    "comma_frontier24_parametric_bundle \<Rightarrow> (nat \<times> nat \<times> nat) list" where
  "comma_frontier24_shift_requests bundle = remdups (concat
    (map (\<lambda>closure. map (\<lambda>row.
      (cf24_closure_full_shift closure,
       cf24_closure_case_guard_root row,
       cf24_closure_case_shifted_guard_root row))
      (cf24_closure_cases closure)) (cf24_closures bundle)))"

definition comma_frontier24_multiway_requests ::
    "comma_frontier24_parametric_bundle \<Rightarrow>
      ((nat \<times> nat) list \<times> nat \<times> nat) list" where
  "comma_frontier24_multiway_requests bundle = remdups
    (map (\<lambda>closure.
      (map (\<lambda>row. (cf24_closure_case_shifted_guard_root row,
          cf24_closure_case_action_output_root row)) (cf24_closure_cases closure),
       cf24_zero_root bundle,cf24_closure_output_root closure))
      (filter (\<lambda>closure. cf24_closure_near_token closure=None) (cf24_closures bundle)))"

definition comma_frontier24_shifts_certified ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_shifts_certified bundle \<longleftrightarrow>
    list_all (\<lambda>(amount,source,target).
      comma_crt_mdd_root_shift_certificate (cf24_radices bundle)
        (cf24_nodes bundle) amount source target)
      (comma_frontier24_shift_requests bundle)"

lemma comma_frontier24_shift_requests_from_indexed:
  assumes checked: "list_all (\<lambda>i. list_all P
    (map (\<lambda>row. (cf24_closure_full_shift (cf24_closures bundle ! i),
      cf24_closure_case_guard_root row, cf24_closure_case_shifted_guard_root row))
      (cf24_closure_cases (cf24_closures bundle ! i))))
    [0..<length (cf24_closures bundle)]"
  shows "list_all P (comma_frontier24_shift_requests bundle)"
proof -
  have "list_all (\<lambda>closure. list_all P
    (map (\<lambda>row. (cf24_closure_full_shift closure,
      cf24_closure_case_guard_root row, cf24_closure_case_shifted_guard_root row))
      (cf24_closure_cases closure))) (cf24_closures bundle)"
    using checked by (simp add: list_all_length)
  then show ?thesis
    by (auto simp: comma_frontier24_shift_requests_def list_all_iff)
qed

lemma comma_frontier24_multiway_requests_from_indexed:
  assumes checked: "list_all (\<lambda>i.
    cf24_closure_near_token (cf24_closures bundle ! i) = None \<longrightarrow>
    P (map (\<lambda>row. (cf24_closure_case_shifted_guard_root row,
        cf24_closure_case_action_output_root row))
        (cf24_closure_cases (cf24_closures bundle ! i)),
      cf24_zero_root bundle, cf24_closure_output_root (cf24_closures bundle ! i)))
    [0..<length (cf24_closures bundle)]"
  shows "list_all P (comma_frontier24_multiway_requests bundle)"
proof -
  have "list_all (\<lambda>closure. cf24_closure_near_token closure = None \<longrightarrow>
    P (map (\<lambda>row. (cf24_closure_case_shifted_guard_root row,
      cf24_closure_case_action_output_root row)) (cf24_closure_cases closure),
      cf24_zero_root bundle, cf24_closure_output_root closure)) (cf24_closures bundle)"
    using checked by (simp add: list_all_length)
  then show ?thesis
    by (auto simp: comma_frontier24_multiway_requests_def list_all_iff)
qed

definition comma_frontier24_multiways_certified ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_multiways_certified bundle \<longleftrightarrow>
    list_all (\<lambda>(cases,fallback,result).
      comma_crt_mdd_multiway_certificate (cf24_radices bundle)
        (cf24_nodes bundle) cases fallback result)
      (comma_frontier24_multiway_requests bundle)"

lemma comma_frontier24_shift_request_certified:
  assumes checked: "comma_frontier24_shifts_certified bundle"
    and request:
      "(amount,source,target) \<in> set (comma_frontier24_shift_requests bundle)"
  shows "comma_crt_mdd_root_shift_certificate
      (cf24_radices bundle) (cf24_nodes bundle) amount source target"
  using checked request
  by (auto simp: comma_frontier24_shifts_certified_def list_all_iff)

lemma comma_frontier24_multiway_request_certified:
  assumes checked: "comma_frontier24_multiways_certified bundle"
    and request:
      "(cases,fallback,result) \<in>
        set (comma_frontier24_multiway_requests bundle)"
  shows "comma_crt_mdd_multiway_certificate (cf24_radices bundle)
      (cf24_nodes bundle) cases fallback result"
  using checked request
  by (auto simp: comma_frontier24_multiways_certified_def list_all_iff)

definition comma_frontier24_guard_imports_exact ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_guard_imports_exact bundle \<longleftrightarrow>
    cf24_radices bundle = [3,4,7,11] \<and>
    (\<forall>entry\<in>set (cf24_guard_entries bundle).
      comma_crt_mdd_root_map_certificate [3,4,7,11]
        (comma_frontier24_core_guard_nodes (cf24_guard_core entry)
          (cf24_guard_wanted entry))
        (cf24_nodes bundle) (\<lambda>payload. if payload then 1 else 0)
        (comma_frontier24_core_guard_root (cf24_guard_core entry))
        (cf24_guard_root entry))"

lemma comma_frontier24_guard_import_eval:
  assumes imported_guards: "comma_frontier24_guard_imports_exact bundle"
    and table: "comma_crt_mdd_table_wellformed
      (cf24_radices bundle) (cf24_nodes bundle)"
    and member: "entry \<in> set (cf24_guard_entries bundle)"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_guard_root entry) =
    Some (if comma_crt_eval phase
      (comma_core_value_guard (cf24_guard_core entry)
        (cf24_guard_wanted entry)) then 1 else 0)"
proof -
  have radices: "cf24_radices bundle = [3,4,7,11]"
    using imported_guards by (simp add: comma_frontier24_guard_imports_exact_def)
  have source_wf:
    "comma_crt_mdd_table_wellformed [3,4,7,11]
      (comma_frontier24_core_guard_nodes (cf24_guard_core entry)
        (cf24_guard_wanted entry))"
    by (rule comma_frontier24_core_guard_nodes_wellformed)
  have target_wf:
    "comma_crt_mdd_table_wellformed [3,4,7,11] (cf24_nodes bundle)"
    using table radices by simp
  have root_map:
    "comma_crt_mdd_root_map_certificate [3,4,7,11]
      (comma_frontier24_core_guard_nodes (cf24_guard_core entry)
        (cf24_guard_wanted entry))
      (cf24_nodes bundle) (\<lambda>payload. if payload then 1 else 0)
      (comma_frontier24_core_guard_root (cf24_guard_core entry))
      (cf24_guard_root entry)"
    using imported_guards member
    by (auto simp: comma_frontier24_guard_imports_exact_def)
  have imported:
    "comma_crt_mdd_eval_phase [3,4,7,11] (cf24_nodes bundle) phase
        (cf24_guard_root entry) =
      map_option (\<lambda>payload. if payload then 1 else 0)
        (comma_crt_mdd_eval_phase [3,4,7,11]
          (comma_frontier24_core_guard_nodes (cf24_guard_core entry)
            (cf24_guard_wanted entry)) phase
          (comma_frontier24_core_guard_root (cf24_guard_core entry)))"
    by (rule comma_crt_mdd_root_map_certificate_eval_phase
      [OF source_wf target_wf root_map])
  have source_eval:
    "comma_crt_mdd_eval_phase [3,4,7,11]
        (comma_frontier24_core_guard_nodes (cf24_guard_core entry)
          (cf24_guard_wanted entry)) phase
        (comma_frontier24_core_guard_root (cf24_guard_core entry)) =
      Some (comma_crt_eval phase
        (comma_core_value_guard (cf24_guard_core entry)
          (cf24_guard_wanted entry)))"
    by (rule comma_frontier24_core_guard_phase_eval)
  show ?thesis using imported source_eval radices by simp
qed

definition comma_frontier24_closure_certified ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_closure_certified bundle \<longleftrightarrow>
    comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle) \<and>
    comma_frontier24_closure_structure_checked bundle \<and>
    comma_frontier24_guard_imports_exact bundle \<and>
    comma_frontier24_shifts_certified bundle \<and>
    comma_frontier24_multiways_certified bundle"

definition comma_frontier24_bundle_semantic_certified ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_bundle_semantic_certified bundle \<longleftrightarrow>
    comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle) \<and>
    comma_frontier24_bundle_semantic_structure_checked bundle \<and>
    comma_frontier24_guard_imports_exact bundle \<and>
    comma_frontier24_shifts_certified bundle \<and>
    comma_frontier24_multiways_certified bundle"

lemma comma_frontier24_full_iff_closures_and_classes:
  "comma_frontier24_bundle_semantic_certified bundle \<longleftrightarrow>
    comma_frontier24_closure_certified bundle \<and>
      comma_frontier24_class_roots_checked bundle"
  by (simp only: comma_frontier24_bundle_semantic_certified_def
      comma_frontier24_closure_certified_def
      comma_frontier24_structure_iff_closures_and_classes; blast)

lemma comma_frontier24_closure_certifiedD:
  assumes "comma_frontier24_closure_certified bundle"
  shows "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    and "comma_frontier24_closure_structure_checked bundle"
    and "comma_frontier24_guard_imports_exact bundle"
    and "comma_frontier24_shifts_certified bundle"
    and "comma_frontier24_multiways_certified bundle"
  using assms by (auto simp: comma_frontier24_closure_certified_def)

lemma comma_frontier24_bundle_semantic_certifiedD:
  assumes certified: "comma_frontier24_bundle_semantic_certified bundle"
  shows table:
      "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    and structural: "comma_frontier24_bundle_semantic_structure_checked bundle"
    and guards: "comma_frontier24_guard_imports_exact bundle"
    and shifts: "comma_frontier24_shifts_certified bundle"
    and multiways: "comma_frontier24_multiways_certified bundle"
  using certified
  by (auto simp: comma_frontier24_bundle_semantic_certified_def)

lemma comma_frontier24_closure_case_shift_certificate:
  assumes certified: "comma_frontier24_closure_certified bundle"
    and closure: "closure \<in> set (cf24_closures bundle)"
    and row: "row \<in> set (cf24_closure_cases closure)"
  shows "comma_crt_mdd_root_shift_certificate (cf24_radices bundle)
      (cf24_nodes bundle) (cf24_closure_full_shift closure)
      (cf24_closure_case_guard_root row)
      (cf24_closure_case_shifted_guard_root row)"
proof -
  have shifts: "comma_frontier24_shifts_certified bundle"
    using certified by (rule comma_frontier24_closure_certifiedD(4))
  have request:
    "(cf24_closure_full_shift closure,
       cf24_closure_case_guard_root row,
       cf24_closure_case_shifted_guard_root row) \<in>
      set (comma_frontier24_shift_requests bundle)"
    using closure row
    by (auto simp: comma_frontier24_shift_requests_def)
  show ?thesis
    by (rule comma_frontier24_shift_request_certified[OF shifts request])
qed

lemma comma_frontier24_closure_multiway_certificate:
  assumes certified: "comma_frontier24_closure_certified bundle"
    and closure: "closure \<in> set (cf24_closures bundle)"
    and entry: "cf24_closure_near_token closure = None"
  shows "comma_crt_mdd_multiway_certificate (cf24_radices bundle)
      (cf24_nodes bundle)
      (map (\<lambda>row. (cf24_closure_case_shifted_guard_root row,
         cf24_closure_case_action_output_root row)) (cf24_closure_cases closure))
      (cf24_zero_root bundle) (cf24_closure_output_root closure)"
proof -
  have checked: "comma_frontier24_multiways_certified bundle"
    using certified by (rule comma_frontier24_closure_certifiedD(5))
  have request:
    "(map (\<lambda>row. (cf24_closure_case_shifted_guard_root row,
         cf24_closure_case_action_output_root row)) (cf24_closure_cases closure),
      cf24_zero_root bundle,cf24_closure_output_root closure) \<in>
      set (comma_frontier24_multiway_requests bundle)"
    using closure entry by (auto simp: comma_frontier24_multiway_requests_def)
  show ?thesis by (rule comma_frontier24_multiway_request_certified[OF checked request])
qed

lemma comma_frontier24_closure_case_guard_value:
  assumes certified: "comma_frontier24_closure_certified bundle"
    and closure: "closure \<in> set (cf24_closures bundle)"
    and row: "row \<in> set (cf24_closure_cases closure)"
    and imported: "comma_frontier24_case_guard_imported bundle core
      (cf24_closure_case_wanted row) (cf24_closure_case_guard_root row)"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_closure_case_shifted_guard_root row) =
    Some (if comma_crt_eval (phase+cf24_closure_full_shift closure)
      (comma_core_value_guard core (cf24_closure_case_wanted row))
      then 1 else 0)"
proof -
  have table:
    "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    using certified by (rule comma_frontier24_closure_certifiedD(1))
  have guard_imports: "comma_frontier24_guard_imports_exact bundle"
    using certified by (rule comma_frontier24_closure_certifiedD(3))
  have guard_entry:
    "\<exists>entry\<in>set (cf24_guard_entries bundle).
      cf24_guard_core entry=core \<and>
      cf24_guard_wanted entry=cf24_closure_case_wanted row \<and>
      cf24_guard_root entry=cf24_closure_case_guard_root row"
    using imported by (simp add: comma_frontier24_case_guard_imported_def)
  then obtain entry where entry:
    "entry\<in>set (cf24_guard_entries bundle)"
    "cf24_guard_core entry=core"
    "cf24_guard_wanted entry=cf24_closure_case_wanted row"
    "cf24_guard_root entry=cf24_closure_case_guard_root row"
    by blast
  have base:
    "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      (phase+cf24_closure_full_shift closure)
      (cf24_closure_case_guard_root row) =
     Some (if comma_crt_eval (phase+cf24_closure_full_shift closure)
       (comma_core_value_guard core (cf24_closure_case_wanted row))
       then 1 else 0)"
    using comma_frontier24_guard_import_eval[OF guard_imports table entry(1),
      of "phase+cf24_closure_full_shift closure"] entry(2,3,4) by simp
  have shift_cert: "comma_crt_mdd_root_shift_certificate
      (cf24_radices bundle) (cf24_nodes bundle)
      (cf24_closure_full_shift closure)
      (cf24_closure_case_guard_root row)
      (cf24_closure_case_shifted_guard_root row)"
    by (rule comma_frontier24_closure_case_shift_certificate
      [OF certified closure row])
  show ?thesis
    using comma_crt_mdd_root_shift_certificate_eval_phase[OF table shift_cert,
        of phase] base by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Parametric Continue closure operation transport"
    @{thms comma_frontier24_selector_case_intro comma_frontier24_selector_cases_nil
      comma_frontier24_selector_cases_cons
      comma_frontier24_selector_entry_intro comma_frontier24_selector_near_residual_intro
      comma_frontier24_selector_near_boundary_intro comma_frontier24_selector_rows_nil
      comma_frontier24_selector_rows_cons comma_frontier24_selector_rows_intro
      comma_frontier24_selector_rows_indexed_intro
      comma_frontier24_guard_import_eval comma_frontier24_closure_multiway_certificate
      comma_frontier24_closure_case_guard_value};
\<close>

end
