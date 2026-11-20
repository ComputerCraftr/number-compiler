theory Comma_Parametric_Continue_Constructors
  imports Comma_Parametric_Continue_Closure
begin

text \<open>Constructors assemble checked closure data without evaluating the
source-specific selector arithmetic. The action-output and guard premises are
still independently authenticated against the exact frozen store.\<close>

lemma comma_frontier24_closure_structure_intro:
  assumes selector: "comma_frontier24_selector_rows_checked bundle"
    and programs: "list_all comma_phase_program_structurally_admitted (cf24_programs bundle)"
    and zero_bound: "cf24_zero_root bundle < length (cf24_nodes bundle)"
    and zero_leaf: "cf24_nodes bundle ! cf24_zero_root bundle = Comma_CRT_MDD_Leaf 0"
    and closures: "list_all (comma_frontier24_closure_shape_checked bundle)
      (zip [0..<length (cf24_closures bundle)] (cf24_closures bundle))"
  shows "comma_frontier24_closure_structure_checked bundle"
  using assms by (simp only: comma_frontier24_closure_structure_checked_def)

lemma comma_frontier24_structure_intro:
  assumes selector: "comma_frontier24_selector_rows_checked bundle"
    and programs: "list_all comma_phase_program_structurally_admitted (cf24_programs bundle)"
    and zero_bound: "cf24_zero_root bundle < length (cf24_nodes bundle)"
    and zero_leaf: "cf24_nodes bundle ! cf24_zero_root bundle = Comma_CRT_MDD_Leaf 0"
    and closures: "list_all (comma_frontier24_closure_shape_checked bundle)
      (zip [0..<length (cf24_closures bundle)] (cf24_closures bundle))"
    and roots: "comma_frontier24_class_roots_checked bundle"
  shows "comma_frontier24_bundle_semantic_structure_checked bundle"
  using assms by (simp only: comma_frontier24_bundle_semantic_structure_checked_def)

fun comma_frontier24_indexed_closure_rows ::
    "comma_frontier24_parametric_bundle \<Rightarrow> nat \<Rightarrow>
      comma_frontier24_closure list \<Rightarrow> bool" where
  "comma_frontier24_indexed_closure_rows bundle start [] = True"
| "comma_frontier24_indexed_closure_rows bundle start (closure # closures) =
    (comma_frontier24_closure_shape_checked bundle (start,closure) \<and>
      comma_frontier24_indexed_closure_rows bundle (Suc start) closures)"

lemma comma_frontier24_indexed_closures_nil:
  "comma_frontier24_indexed_closure_rows bundle start []"
  by simp

lemma comma_frontier24_indexed_closures_cons:
  assumes head: "comma_frontier24_closure_shape_checked bundle (start,closure)"
    and tail: "comma_frontier24_indexed_closure_rows bundle (Suc start) closures"
  shows "comma_frontier24_indexed_closure_rows bundle start (closure # closures)"
  using head tail by simp

lemma comma_frontier24_indexed_closures_to_zip:
  assumes "comma_frontier24_indexed_closure_rows bundle start closures"
  shows "list_all (comma_frontier24_closure_shape_checked bundle)
    (zip [start..<start + length closures] closures)"
  using assms
proof (induction closures arbitrary: start)
  case Nil
  then show ?case by simp
next
  case (Cons closure closures)
  have head: "comma_frontier24_closure_shape_checked bundle (start,closure)"
    and tail: "comma_frontier24_indexed_closure_rows bundle (Suc start) closures"
    using Cons.prems by simp_all
  have range: "[start..<start + Suc (length closures)] =
      start # [Suc start..<Suc start + length closures]"
    by (subst upt_conv_Cons) simp_all
  show ?case using head Cons.IH[OF tail]
    by (simp only: length_Cons range zip_Cons_Cons list_all_Cons_iff)
qed

lemma comma_frontier24_indexed_closures_zero:
  assumes "comma_frontier24_indexed_closure_rows bundle 0 closures"
  shows "list_all (comma_frontier24_closure_shape_checked bundle)
    (zip [0..<length closures] closures)"
  using comma_frontier24_indexed_closures_to_zip[OF assms] by simp

lemma comma_frontier24_indexed_closures_nth:
  assumes checked: "list_all (\<lambda>i. comma_frontier24_closure_shape_checked bundle
      (i,closures ! i)) [0..<length closures]"
  shows "list_all (comma_frontier24_closure_shape_checked bundle)
    (zip [0..<length closures] closures)"
  using checked by (auto simp: list_all_iff in_set_conv_nth)

definition comma_frontier24_indexed_closure_shape ::
    "comma_frontier24_parametric_bundle \<Rightarrow>
      comma_frontier24_closure list \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_frontier24_indexed_closure_shape bundle closures i \<longleftrightarrow>
    comma_frontier24_closure_shape_checked bundle (i,closures ! i)"

lemma comma_frontier24_indexed_closure_shape_intro:
  assumes selected: "closures ! i = closure"
    and checked: "comma_frontier24_closure_shape_checked bundle (i,closure)"
  shows "comma_frontier24_indexed_closure_shape bundle closures i"
  using selected checked by (simp only: comma_frontier24_indexed_closure_shape_def)

lemma comma_frontier24_indexed_closure_shapes_to_zip:
  assumes "list_all (comma_frontier24_indexed_closure_shape bundle closures)
    [0..<length closures]"
  shows "list_all (comma_frontier24_closure_shape_checked bundle)
    (zip [0..<length closures] closures)"
  apply (rule comma_frontier24_indexed_closures_nth)
  using assms by (auto simp: list_all_iff comma_frontier24_indexed_closure_shape_def)

lemma comma_frontier24_closure_entry_intro:
  assumes program_bound: "cf24_closure_program_ref closure < length (cf24_programs bundle)"
    and root_bound: "cf24_closure_output_root closure < length (cf24_nodes bundle)"
    and program: "cf24_programs bundle ! cf24_closure_program_ref closure =
      Comma_Entry_Core_Program f d residue core"
    and selector: "cf24_selectors bundle ! cf24_closure_program_ref closure =
      Comma_Frontier24_Entry_Selector f d residue core selector_cases"
    and match: "comma_frontier24_selector_recipe_matches
      (Comma_Entry_Core_Program f d residue core)
      (Comma_Frontier24_Entry_Selector f d residue core selector_cases)
      (cf24_action_tokens bundle)"
    and near_token: "cf24_closure_near_token closure = None"
    and near_root: "cf24_closure_near_action_output_root closure = None"
    and near_child: "cf24_closure_near_child closure = None"
    and wanted: "map cf24_closure_case_wanted (cf24_closure_cases closure) =
      map cf24_case_wanted selector_cases"
    and guards: "map cf24_closure_case_guard_root (cf24_closure_cases closure) =
      map cf24_case_guard_root selector_cases"
    and tokens: "map cf24_closure_case_action_token (cf24_closure_cases closure) =
      map cf24_case_action_token selector_cases"
    and rows: "list_all (\<lambda>row.
      comma_frontier24_case_guard_imported bundle core (cf24_closure_case_wanted row)
        (cf24_closure_case_guard_root row) \<and>
      comma_frontier24_action_output_linked bundle closure_index closure
        (cf24_closure_case_action_token row) (cf24_closure_case_action_output_root row)
        (cf24_closure_case_child row)) (cf24_closure_cases closure)"
  shows "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
  using assms by (simp only: comma_frontier24_closure_shape_checked_def prod.case Let_def
    comma_semantic_port_program.simps comma_frontier24_selector_recipe.simps)

lemma comma_frontier24_closure_entry_scalar_intro:
  assumes program_bound: "cf24_closure_program_ref closure < length (cf24_programs bundle)"
    and root_bound: "cf24_closure_output_root closure < length (cf24_nodes bundle)"
    and program: "cf24_programs bundle ! cf24_closure_program_ref closure =
      Comma_Entry_Core_Program f d residue core"
    and selector: "cf24_selectors bundle ! cf24_closure_program_ref closure =
      Comma_Frontier24_Entry_Selector f d residue core selector_cases"
    and match: "comma_frontier24_selector_recipe_matches
      (Comma_Entry_Core_Program f d residue core)
      (Comma_Frontier24_Entry_Selector f d residue core selector_cases)
      (cf24_action_tokens bundle)"
    and near_token: "cf24_closure_near_token closure = None"
    and near_root: "cf24_closure_near_action_output_root closure = None"
    and near_child: "cf24_closure_near_child closure = None"
    and wanted: "map cf24_closure_case_wanted (cf24_closure_cases closure) =
      map cf24_case_wanted selector_cases"
    and guards: "map cf24_closure_case_guard_root (cf24_closure_cases closure) =
      map cf24_case_guard_root selector_cases"
    and tokens: "map cf24_closure_case_action_token (cf24_closure_cases closure) =
      map cf24_case_action_token selector_cases"
    and rows: "list_all (\<lambda>row.
      comma_frontier24_case_guard_imported bundle core (cf24_closure_case_wanted row)
        (cf24_closure_case_guard_root row) \<and>
      comma_frontier24_action_output_linked_scalar bundle closure_index
        (cf24_closure_program_ref closure) (cf24_closure_full_shift closure)
        (cf24_closure_case_action_token row) (cf24_closure_case_action_output_root row)
        (cf24_closure_case_child row)) (cf24_closure_cases closure)"
  shows "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
proof -
  have linked_rows: "list_all (\<lambda>row.
      comma_frontier24_case_guard_imported bundle core (cf24_closure_case_wanted row)
        (cf24_closure_case_guard_root row) \<and>
      comma_frontier24_action_output_linked bundle closure_index closure
        (cf24_closure_case_action_token row) (cf24_closure_case_action_output_root row)
        (cf24_closure_case_child row)) (cf24_closure_cases closure)"
    using rows by (simp only: comma_frontier24_action_output_linked_def)
  show ?thesis by (rule comma_frontier24_closure_entry_intro
    [OF program_bound root_bound program selector match near_token near_root near_child wanted guards tokens linked_rows])
qed

lemma comma_frontier24_closure_near_intro:
  assumes program_bound: "cf24_closure_program_ref closure < length (cf24_programs bundle)"
    and root_bound: "cf24_closure_output_root closure < length (cf24_nodes bundle)"
    and selector: "cf24_selectors bundle ! cf24_closure_program_ref closure =
      Comma_Frontier24_Near_Selector token"
    and match: "comma_frontier24_selector_recipe_matches
      (cf24_programs bundle ! cf24_closure_program_ref closure)
      (Comma_Frontier24_Near_Selector token) (cf24_action_tokens bundle)"
    and cases_empty: "cf24_closure_cases closure = []"
    and near_token: "cf24_closure_near_token closure = Some token"
    and near_root: "cf24_closure_near_action_output_root closure = Some action_root"
    and linked: "comma_frontier24_action_output_linked bundle closure_index closure
      token action_root (cf24_closure_near_child closure)"
    and root: "cf24_closure_output_root closure = action_root"
  shows "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
  using assms by (cases "cf24_programs bundle ! cf24_closure_program_ref closure")
    (simp_all only: comma_frontier24_closure_shape_checked_def prod.case Let_def
      comma_semantic_port_program.simps comma_frontier24_selector_recipe.simps option.case)

lemma comma_frontier24_class_root_witness:
  assumes index: "index < length (cf24_closures bundle)"
    and program: "cf24_closure_program_ref (cf24_closures bundle ! index) = program_ref"
    and shift: "cf24_closure_full_shift (cf24_closures bundle ! index) = 0"
    and root: "cf24_closure_output_root (cf24_closures bundle ! index) = root_id"
  shows "\<exists>closure\<in>set (cf24_closures bundle).
    cf24_closure_program_ref closure = program_ref \<and>
    cf24_closure_full_shift closure = 0 \<and>
    cf24_closure_output_root closure = root_id"
  using assms nth_mem by blast

lemma comma_frontier24_case_guard_imported_witness:
  assumes index: "index < length (cf24_guard_entries bundle)"
    and core: "cf24_guard_core (cf24_guard_entries bundle ! index) = guard_core"
    and wanted: "cf24_guard_wanted (cf24_guard_entries bundle ! index) = guard_wanted"
    and root: "cf24_guard_root (cf24_guard_entries bundle ! index) = guard_root"
  shows "comma_frontier24_case_guard_imported bundle guard_core guard_wanted guard_root"
  using assms nth_mem by (auto simp: comma_frontier24_case_guard_imported_def)

lemma comma_frontier24_class_roots_intro:
  assumes refs: "length (cf24_class_program_refs bundle) = 46"
    and roots: "length (cf24_class_roots bundle) = 46"
    and class_binding: "\<And>cid. cid < 46 \<Longrightarrow>
      (case comma_semantic_phase_program_for_class cid of None \<Rightarrow> False
       | Some program \<Rightarrow>
           cf24_class_program_refs bundle ! cid < length (cf24_programs bundle) \<and>
           cf24_programs bundle ! (cf24_class_program_refs bundle ! cid) = program \<and>
           (\<exists>closure\<in>set (cf24_closures bundle).
             cf24_closure_program_ref closure = cf24_class_program_refs bundle ! cid \<and>
             cf24_closure_full_shift closure = 0 \<and>
             cf24_closure_output_root closure = cf24_class_roots bundle ! cid))"
  shows "comma_frontier24_class_roots_checked bundle"
  using refs roots class_binding by (auto simp: comma_frontier24_class_roots_checked_def list_all_iff)

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "parametric Continue constructor rules"
    @{thms comma_frontier24_closure_structure_intro comma_frontier24_structure_intro comma_frontier24_indexed_closures_nil
      comma_frontier24_indexed_closures_cons comma_frontier24_indexed_closures_to_zip
      comma_frontier24_indexed_closures_zero
      comma_frontier24_indexed_closures_nth
      comma_frontier24_indexed_closure_shape_intro
      comma_frontier24_indexed_closure_shapes_to_zip
      comma_frontier24_closure_entry_intro comma_frontier24_closure_near_intro
      comma_frontier24_class_root_witness comma_frontier24_case_guard_imported_witness
      comma_frontier24_class_roots_intro};
\<close>

end
