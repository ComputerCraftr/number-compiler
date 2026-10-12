theory Comma_Semantic_B1_CRT_Mass_Annotation_Regression
  imports Comma_Semantic_B1_CRT_Mass_Annotations
begin

text \<open>
These fixtures exercise the executable annotation checker, independently of
the ML candidate generator.  In particular, a missing annotation must not be
accepted through the total mass lookup's default value.
\<close>

abbreviation comma_mass_test_dag where
  "comma_mass_test_dag children \<equiv>
    Comma_B1_CRT_Column_DAG_Block 2 1
      (Comma_B1_CRT_Column_Block_Node 2 0 children
        Comma_B1_CRT_Column_Block_Empty Comma_B1_CRT_Column_Block_Empty)"

abbreviation comma_mass_test_tree where
  "comma_mass_test_tree mass \<equiv>
    Comma_B1_CRT_Mass_Tree_Node 2 0 mass
      Comma_B1_CRT_Mass_Tree_Empty Comma_B1_CRT_Mass_Tree_Empty"

lemmas comma_mass_test_simps =
  comma_semantic_b1_crt_column_mass_annotation_tree_valid_def
  comma_semantic_b1_crt_mass_tree_row_valid_def
  comma_semantic_b1_crt_mass_tree_child_valid_def
  comma_crt_period_def

lemma comma_mass_annotation_checks_repeated_children:
  "comma_semantic_b1_crt_column_mass_annotation_tree_valid
    (comma_mass_test_dag [1,1,0,0]) 3 (comma_mass_test_tree 462)"
  by (simp add: comma_mass_test_simps)

lemma comma_mass_annotation_rejects_deduplicated_mass:
  "\<not> comma_semantic_b1_crt_column_mass_annotation_tree_valid
    (comma_mass_test_dag [1,1,0,0]) 3 (comma_mass_test_tree 231)"
  by (simp add: comma_mass_test_simps)

lemma comma_mass_annotation_rejects_forward_child:
  "\<not> comma_semantic_b1_crt_column_mass_annotation_tree_valid
    (comma_mass_test_dag [2,0,0,0]) 3 (comma_mass_test_tree 0)"
  by (simp add: comma_mass_test_simps)

lemma comma_mass_annotation_rejects_wrong_radix:
  "\<not> comma_semantic_b1_crt_column_mass_annotation_tree_valid
    (comma_mass_test_dag [1]) 3 (comma_mass_test_tree 231)"
  by (simp add: comma_mass_test_simps)

lemma comma_mass_annotation_rejects_foreign_extent:
  "\<not> comma_semantic_b1_crt_column_mass_annotation_tree_valid
    (comma_mass_test_dag [1,1,0,0]) 2 (comma_mass_test_tree 462)"
  by (simp add: comma_mass_test_simps)

lemma comma_mass_annotation_rejects_missing_nonterminal:
  "\<not> comma_semantic_b1_crt_column_mass_annotation_tree_valid
    (Comma_B1_CRT_Column_DAG_Block 2 2
      (Comma_B1_CRT_Column_Block_Node 3 0 [2,0,0,0]
        (Comma_B1_CRT_Column_Block_Node 2 1 [1,1,1]
          Comma_B1_CRT_Column_Block_Empty Comma_B1_CRT_Column_Block_Empty)
        Comma_B1_CRT_Column_Block_Empty)) 4
    (Comma_B1_CRT_Mass_Tree_Node 3 0 0
      Comma_B1_CRT_Mass_Tree_Empty Comma_B1_CRT_Mass_Tree_Empty)"
  by (simp add: comma_mass_test_simps)

ML \<open>
  val checked = @{thms comma_mass_annotation_checks_repeated_children
    comma_mass_annotation_rejects_deduplicated_mass
    comma_mass_annotation_rejects_forward_child
    comma_mass_annotation_rejects_wrong_radix
    comma_mass_annotation_rejects_foreign_extent
    comma_mass_annotation_rejects_missing_nonterminal}
  val _ = Thm.consolidate checked
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Mass annotation regression uses an oracle"
\<close>

end
