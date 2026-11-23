theory Comma_Future_M204_Certificate_Smoke
  imports Comma_Frontier24_Certificate_Smoke
    Comma_Semantic_Future.Comma_Future_M204_Class_Decoder
    Comma_Semantic_Future.Comma_Future_M204_Select_Step
    Comma_Semantic_Future.Comma_Future_M204_Select_Chain
    Comma_Semantic_Future.Comma_Future_M204_Periodic
    Comma_Semantic_Future.Comma_Future_M204_Class_Rank_Lift
    Comma_Semantic_Future.Comma_Future_M204_Direct_Source
begin

text \<open>The same production replay modules are compiled against the generic
refinement laws here. Loading them does not issue a concrete source morphism or
grant release authority.\<close>

ML_file "../comma_semantic_future_instance/semantic_future_m204_candidate_data.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_graph_data.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_graph_reachability.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_class_rank.ML"
ML_file "semantic_future_m204_class_rank_fixture.ML"
local_setup \<open>Comma_Future_M204_Class_Rank_Fixture.run\<close>
ML_file "../comma_semantic_future_instance/semantic_future_m204_source_bindings.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_join_replay.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_graph_replay.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_graph_pointwise.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_select_steps.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_select_folds.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_weight_evals.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_shifted_weights.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_shifted_classes.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_source_transport.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_child_transport.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_source_pointwise.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_child_pointwise.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_graph_family_pointwise.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_source20.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_final_publication.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_compact_class_transport.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_compact_rank_publication.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_direct_source_bindings.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_direct_physical_issuer.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_component_loader.ML"

end
