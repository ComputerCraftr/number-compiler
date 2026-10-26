theory Comma_Semantic_Graph_Pointwise_Binding_Row
  imports Comma_Semantic_Graph_Congruence
begin

text \<open>
This generic bridge turns pointwise source-to-port and representative-row
facts into the existing binding-row contract.  Its premises do not assume
graph validity and do not carry a materialized source action list or a family
of per-phase theorem objects.  A caller may discharge the quantified port
facts from one source-independent transport law and exact child bindings.
\<close>

lemma comma_semantic_b1_binding_row_valid_from_pointwise_port:
  fixes port_action :: "nat \<Rightarrow> comma_source_continuation_action"
  assumes admitted: "comma_round_admitted source"
    and normalized: "source = comma_source_continuation_base source"
    and source_binding:
      "comma_semantic_b1_binding_source binding = source"
    and node_lookup:
      "comma_semantic_b1_node_of nodes
        (comma_semantic_b1_binding_cid binding) = Some node"
    and node_positive: "0 < comma_semantic_b1_node_period node"
    and node_divides:
      "comma_semantic_b1_node_period node dvd
        comma_decisive_sector_period source"
    and node_length:
      "length (comma_semantic_b1_node_actions node) =
        comma_semantic_b1_node_period node"
    and source_to_port:
      "\<forall>phase < comma_decisive_sector_period source.
        comma_source_continuation_action_at source phase = port_action phase"
    and port_row:
      "\<forall>phase < comma_decisive_sector_period source.
        comma_semantic_b1_local_action_shape (port_action phase) \<and>
        comma_semantic_b1_edge_of_continuation bindings (port_action phase) =
          Some (comma_semantic_b1_node_actions node !
            (phase mod comma_semantic_b1_node_period node))"
  shows "comma_semantic_b1_binding_row_valid bindings nodes binding"
proof -
  let ?P = "comma_decisive_sector_period source"
  let ?d = "comma_semantic_b1_node_period node"
  let ?actions = "map (\<lambda>phase.
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet phase source)) [0..<?P]"
  have source_period_positive: "0 < ?P"
    by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
  have source_period_divides: "?P dvd 924"
    by (rule comma_decisive_sector_period_admitted(2)[OF admitted])
  have node_divides_924: "?d dvd 924"
    by (rule dvd_trans[OF node_divides source_period_divides])
  have node_at_most_924: "?d \<le> 924"
    by (rule dvd_imp_le[OF node_divides_924]) simp
  have source_id:
    "comma_source_continuation_id source = (?P, ?actions)"
    using normalized
    by (simp add: comma_source_continuation_id_def Let_def)
  have source_action_nth:
    "comma_source_continuation_action_at source phase = ?actions ! phase"
    if phase_bound: "phase < ?P" for phase
    using phase_bound source_period_positive source_id
    by (simp add: comma_source_continuation_action_at_def)
  have row_all:
    "list_all (\<lambda>phase.
      comma_semantic_b1_local_action_shape (?actions ! phase) \<and>
      comma_semantic_b1_edge_of_continuation bindings (?actions ! phase) =
        Some (comma_semantic_b1_node_actions node ! (phase mod ?d)))
      [0..<?P]"
    using source_to_port port_row source_action_nth
    by (auto simp: list_all_iff)
  show ?thesis
    unfolding comma_semantic_b1_binding_row_valid_def
    using admitted normalized source_binding node_lookup node_positive
      node_at_most_924 node_divides_924 node_divides node_length row_all
      source_id
    by (simp add: Let_def)
qed

text \<open>
Binding-row authority depends on the complete continuation identifier, not
the source's spelling.  Since the identifier contains both the selector
period and the ordered packet-action row, equal identifiers transport every
local edge obligation while retaining admission, normalization and the
published CID check.
\<close>

lemma comma_semantic_b1_binding_row_valid_id_rebase:
  assumes representative_row:
      "comma_semantic_b1_binding_row_valid bindings nodes representative"
    and same_cid:
      "comma_semantic_b1_binding_cid binding =
        comma_semantic_b1_binding_cid representative"
    and same_id:
      "comma_source_continuation_id (comma_semantic_b1_binding_source binding) =
        comma_source_continuation_id
          (comma_semantic_b1_binding_source representative)"
    and admitted:
      "comma_round_admitted (comma_semantic_b1_binding_source binding)"
    and normalized:
      "comma_semantic_b1_binding_source binding =
        comma_source_continuation_base
          (comma_semantic_b1_binding_source binding)"
  shows "comma_semantic_b1_binding_row_valid bindings nodes binding"
proof -
  let ?source = "comma_semantic_b1_binding_source binding"
  let ?representative = "comma_semantic_b1_binding_source representative"
  have period_equal:
    "fst (comma_source_continuation_id ?source) =
      fst (comma_source_continuation_id ?representative)"
    using same_id by (metis prod.inject)
  have actions_equal:
    "snd (comma_source_continuation_id ?source) =
      snd (comma_source_continuation_id ?representative)"
    using same_id by (metis prod.inject)
  have representative_normalized:
    "?representative = comma_source_continuation_base ?representative"
    using representative_row
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def)
  have sector_periods_equal:
    "comma_decisive_sector_period ?source =
      comma_decisive_sector_period ?representative"
    using period_equal normalized representative_normalized
    by (simp add: comma_source_continuation_id_def Let_def)
  show ?thesis
    using representative_row same_cid same_id sector_periods_equal
      actions_equal admitted normalized
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
        split: option.splits)
qed

lemma comma_semantic_b1_binding_row_valid_pair_id_rebase:
  fixes bindings :: "comma_semantic_b1_binding list"
    and nodes :: "comma_semantic_b1_node list"
    and source representative :: comma_finite_position
    and cid :: nat
  assumes representative_row:
      "comma_semantic_b1_binding_row_valid bindings nodes
        (comma_semantic_b1_binding_from_pair (representative,cid))"
    and same_id:
      "comma_source_continuation_id source =
        comma_source_continuation_id representative"
    and admitted: "comma_round_admitted source"
    and normalized:
      "source = comma_source_continuation_base source"
  shows "comma_semantic_b1_binding_row_valid bindings nodes
    (comma_semantic_b1_binding_from_pair (source,cid))"
proof -
  have same_cid:
      "comma_semantic_b1_binding_cid
          (comma_semantic_b1_binding_from_pair (source,cid)) =
        comma_semantic_b1_binding_cid
          (comma_semantic_b1_binding_from_pair (representative,cid))"
    by (simp add: comma_semantic_b1_binding_from_pair_def)
  have same_id_selectors:
      "comma_source_continuation_id
          (comma_semantic_b1_binding_source
            (comma_semantic_b1_binding_from_pair (source,cid))) =
        comma_source_continuation_id
          (comma_semantic_b1_binding_source
            (comma_semantic_b1_binding_from_pair (representative,cid)))"
    using same_id by (simp add: comma_semantic_b1_binding_from_pair_def)
  have admitted_selector:
      "comma_round_admitted
        (comma_semantic_b1_binding_source
          (comma_semantic_b1_binding_from_pair (source,cid)))"
    using admitted by (simp add: comma_semantic_b1_binding_from_pair_def)
  have normalized_selector:
      "comma_semantic_b1_binding_source
          (comma_semantic_b1_binding_from_pair (source,cid)) =
        comma_source_continuation_base
          (comma_semantic_b1_binding_source
            (comma_semantic_b1_binding_from_pair (source,cid)))"
    using normalized by (simp add: comma_semantic_b1_binding_from_pair_def)
  show ?thesis
    by (rule comma_semantic_b1_binding_row_valid_id_rebase
      [OF representative_row same_cid same_id_selectors admitted_selector
        normalized_selector])
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms comma_semantic_b1_binding_row_valid_from_pointwise_port
        comma_semantic_b1_binding_row_valid_id_rebase
        comma_semantic_b1_binding_row_valid_pair_id_rebase}) then ()
    else error "Pointwise source-port row bridge depends on an oracle";
\<close>

end
