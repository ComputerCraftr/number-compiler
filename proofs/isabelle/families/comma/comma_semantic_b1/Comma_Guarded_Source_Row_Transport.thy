theory Comma_Guarded_Source_Row_Transport
  imports Comma_Guarded_Source_Right_Transport
    Comma_Semantic_Graph_Pointwise_Binding_Row
begin

text \<open>
The producer supplies a scalar guarded-source relation before discovering
ports.  The existing row contract follows by one generic transport; no
materialized continuation identifier is a producer premise.
\<close>

lemma comma_guarded_source_class_rel_continuation_id:
  assumes rel: "comma_guarded_source_class_rel source representative"
  shows "comma_source_continuation_id source =
    comma_source_continuation_id representative"
proof -
  have admitted_source: "comma_round_admitted source"
    and admitted_representative: "comma_round_admitted representative"
    using rel by (auto simp: comma_guarded_source_class_rel_def)
  have normalized_source: "source=comma_source_continuation_base source"
    and normalized_representative:
      "representative=comma_source_continuation_base representative"
    by (rule comma_guarded_source_class_rel_normalized[OF rel])+
  have period: "comma_decisive_sector_period source =
      comma_decisive_sector_period representative"
    by (rule comma_guarded_source_class_rel_period[OF rel])
  have ports: "comma_semantic_b1_source_port_actions source =
      comma_semantic_b1_source_port_actions representative"
    unfolding comma_semantic_b1_source_port_actions_def
    using normalized_source normalized_representative period
      comma_guarded_source_class_rel_port_action[OF rel]
    by simp
  show ?thesis
    using comma_semantic_b1_source_id_ports[OF admitted_source]
      comma_semantic_b1_source_id_ports[OF admitted_representative]
      normalized_source normalized_representative period ports
    by simp
qed

lemma comma_semantic_b1_binding_row_valid_pair_guarded_rebase:
  assumes representative_row:
      "comma_semantic_b1_binding_row_valid bindings nodes
        (comma_semantic_b1_binding_from_pair (representative,cid))"
    and class_rel: "comma_guarded_source_class_rel source representative"
  shows "comma_semantic_b1_binding_row_valid bindings nodes
    (comma_semantic_b1_binding_from_pair (source,cid))"
proof -
  have admitted: "comma_round_admitted source"
    using class_rel by (simp add: comma_guarded_source_class_rel_def)
  have normalized: "source=comma_source_continuation_base source"
    by (rule comma_guarded_source_class_rel_normalized(1)[OF class_rel])
  have same_id: "comma_source_continuation_id source =
      comma_source_continuation_id representative"
    by (rule comma_guarded_source_class_rel_continuation_id[OF class_rel])
  show ?thesis
    by (rule comma_semantic_b1_binding_row_valid_pair_id_rebase
      [OF representative_row same_id admitted normalized])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_guarded_source_class_rel_continuation_id
      comma_semantic_b1_binding_row_valid_pair_guarded_rebase})
    then () else error "Guarded source-row transport depends on an oracle";
\<close>

end
