theory Comma_Semantic_B1_Occurrence_Arithmetic
  imports Comma_Semantic_B1.Comma_Semantic_B1_CRT_Local_Cover
begin

text \<open>
Publish the discovered source graph with geometry stored once per template.
Each source keeps compact slot references into shared lift descriptors, while
its occurrence retains the clock rebase and exact output binding.  The finite
source list resolves occurrences.  The structural certificate below checks
the published values against checked packet-slot arithmetic before any root
or power consumes them.
\<close>

definition comma_semantic_b1_crt_local_cover_fixture_parent ::
    comma_semantic_b1_crt_occurrence where
  "comma_semantic_b1_crt_local_cover_fixture_parent =
    \<lparr>comma_semantic_b1_crt_occurrence_columns =
       [comma_crt_source_axis_column 0 2 0,
        comma_crt_source_axis_column 0 2 1],
     comma_semantic_b1_crt_occurrence_rebase = 0,
     comma_semantic_b1_crt_occurrence_beta =
       [Comma_Semantic_B1_Stop 8, Comma_Semantic_B1_Stop 0]\<rparr>"

definition comma_semantic_b1_crt_local_cover_fixture_rebased_parent ::
    comma_semantic_b1_crt_occurrence where
  "comma_semantic_b1_crt_local_cover_fixture_rebased_parent =
    \<lparr>comma_semantic_b1_crt_occurrence_columns =
       [comma_crt_source_axis_column 0 2 0,
        comma_crt_source_axis_column 0 2 1],
     comma_semantic_b1_crt_occurrence_rebase = 1,
     comma_semantic_b1_crt_occurrence_beta =
       [Comma_Semantic_B1_Stop 8, Comma_Semantic_B1_Stop 0]\<rparr>"

lemma comma_semantic_b1_crt_local_cover_fixtures:
  "comma_semantic_b1_crt_occurrence_beta
      comma_semantic_b1_crt_local_cover_fixture_parent ! 0 =
        Comma_Semantic_B1_Stop 8 \<and>
  comma_semantic_b1_crt_local_piece_covered
      comma_semantic_b1_crt_local_cover_fixture_parent
      (comma_crt_source_axis_column 0 2 0) (Comma_Semantic_B1_Stop 8) \<and>
  \<not> comma_semantic_b1_crt_local_piece_covered
      comma_semantic_b1_crt_local_cover_fixture_parent
      (Comma_CRT_Bool True) (Comma_Semantic_B1_Stop 8) \<and>
  \<not> comma_semantic_b1_crt_local_piece_covered
      comma_semantic_b1_crt_local_cover_fixture_parent
      (comma_crt_source_axis_column 0 2 1) (Comma_Semantic_B1_Stop 8) \<and>
  comma_semantic_b1_crt_local_piece_covered
      comma_semantic_b1_crt_local_cover_fixture_parent
      (Comma_CRT_Bool False) (Comma_Semantic_B1_Live 77) \<and>
  \<not> comma_semantic_b1_crt_local_piece_covered
      comma_semantic_b1_crt_local_cover_fixture_parent
      (Comma_CRT_Bool True) (Comma_Semantic_B1_Live 77) \<and>
  comma_semantic_b1_crt_local_piece_covered
      comma_semantic_b1_crt_local_cover_fixture_rebased_parent
      (comma_crt_source_axis_column 0 2 1) (Comma_Semantic_B1_Stop 8) \<and>
  \<not> comma_semantic_b1_crt_local_piece_covered
      comma_semantic_b1_crt_local_cover_fixture_rebased_parent
      (comma_crt_source_axis_column 0 2 0) (Comma_Semantic_B1_Stop 8)"
  by code_simp

ML \<open>Thm.consolidate @{thms comma_semantic_b1_crt_local_cover_fixtures}\<close>

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_indexed_all_zero comma_indexed_all_Suc
      comma_selected_length_nil comma_selected_length_cons
      comma_semantic_b1_crt_local_cover_fixtures})
    then () else error "Occurrence arithmetic helper depends on an oracle";
\<close>

end
