theory Comma_Semantic_Graph
  imports Comma_Semantic_B1
begin

text \<open>
The checked continuation graph stores reusable edges separately from exact
source bindings. Its evaluator follows only strictly smaller CIDs; the endpoint
refinement theorem connects graph application to the exact B1 round semantics.
\<close>

text \<open>
The continuation graph separates reusable behavior from its source binding.
Node rows contain only quotient edges.  Exact source positions and the
phase-dependent endpoint packets remain in the proof-only binding relation;
in particular, shifts and absolute terminal weights never enter a CID.
\<close>

datatype comma_semantic_b1_edge =
    Comma_Semantic_B1_Goto nat
  | Comma_Semantic_B1_Live_Edge nat
  | Comma_Semantic_B1_Stop_Edge nat
  | Comma_Semantic_B1_Invalid_Edge

record comma_semantic_b1_node =
  comma_semantic_b1_node_cid :: nat
  comma_semantic_b1_node_period :: nat
  comma_semantic_b1_node_actions :: "comma_semantic_b1_edge list"

record comma_semantic_b1_binding =
  comma_semantic_b1_binding_source :: comma_finite_position
  comma_semantic_b1_binding_cid :: nat

definition comma_semantic_b1_binding_ids ::
    "comma_semantic_b1_binding list \<Rightarrow>
      (comma_finite_position \<times> nat) list" where
  "comma_semantic_b1_binding_ids bindings =
    map (\<lambda>b. (comma_semantic_b1_binding_source b,
      comma_semantic_b1_binding_cid b)) bindings"

definition comma_semantic_b1_binding_cid_of ::
    "comma_semantic_b1_binding list \<Rightarrow>
      comma_finite_position \<Rightarrow> nat option" where
  "comma_semantic_b1_binding_cid_of bindings source =
    map_of (comma_semantic_b1_binding_ids bindings) source"

definition comma_semantic_b1_nodes_by_cid ::
    "comma_semantic_b1_node list \<Rightarrow>
      (nat \<times> comma_semantic_b1_node) list" where
  "comma_semantic_b1_nodes_by_cid nodes =
    map (\<lambda>node. (comma_semantic_b1_node_cid node,node)) nodes"

definition comma_semantic_b1_node_of ::
    "comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_node option" where
  "comma_semantic_b1_node_of nodes cid =
    map_of (comma_semantic_b1_nodes_by_cid nodes) cid"

fun comma_semantic_b1_edge_of_continuation ::
    "comma_semantic_b1_binding list \<Rightarrow>
      comma_source_continuation_action \<Rightarrow>
      comma_semantic_b1_edge option" where
  "comma_semantic_b1_edge_of_continuation bindings
      (Comma_Continuation_Goto source shift) =
    map_option Comma_Semantic_B1_Goto
      (comma_semantic_b1_binding_cid_of bindings source)"
| "comma_semantic_b1_edge_of_continuation bindings
      (Comma_Continuation_Exit source shift) =
    (case source of
       Comma_Entry f delta x \<Rightarrow>
         if f=1 \<and> delta=0 \<and> x\<le>90
         then Some (Comma_Semantic_B1_Live_Edge (comma_offset_orbit x))
         else None
     | Comma_Near f delta h \<Rightarrow> None)"
| "comma_semantic_b1_edge_of_continuation bindings
      (Comma_Continuation_Fork a shift) =
    (if 2 \<le> a \<and> a \<le> 9
     then Some (Comma_Semantic_B1_Stop_Edge (a - 2)) else None)"
| "comma_semantic_b1_edge_of_continuation bindings
      (Comma_Continuation_Landmine shift) =
    Some (Comma_Semantic_B1_Stop_Edge 8)"
| "comma_semantic_b1_edge_of_continuation bindings
      Comma_Continuation_Invalid = Some Comma_Semantic_B1_Invalid_Edge"

fun comma_semantic_b1_local_action_shape ::
    "comma_source_continuation_action \<Rightarrow> bool" where
  "comma_semantic_b1_local_action_shape (Comma_Continuation_Goto source shift) =
    (shift=0)"
| "comma_semantic_b1_local_action_shape (Comma_Continuation_Exit source shift) =
    (shift=1)"
| "comma_semantic_b1_local_action_shape (Comma_Continuation_Fork a shift) =
    (shift=0)"
| "comma_semantic_b1_local_action_shape (Comma_Continuation_Landmine shift) =
    (shift=0)"
| "comma_semantic_b1_local_action_shape Comma_Continuation_Invalid = True"

definition comma_semantic_b1_binding_row_valid ::
    "comma_semantic_b1_binding list \<Rightarrow> comma_semantic_b1_node list \<Rightarrow>
      comma_semantic_b1_binding \<Rightarrow> bool" where
  "comma_semantic_b1_binding_row_valid bindings nodes binding =
    (let source=comma_semantic_b1_binding_source binding;
         cid=comma_semantic_b1_binding_cid binding;
         (source_period,source_actions)=comma_source_continuation_id source
     in comma_round_admitted source
       \<and> source=comma_source_continuation_base source
       \<and> source_period=comma_decisive_sector_period source
       \<and> length source_actions=source_period
       \<and> (case comma_semantic_b1_node_of nodes cid of
          None \<Rightarrow> False
        | Some node \<Rightarrow>
            let period=comma_semantic_b1_node_period node;
                actions=comma_semantic_b1_node_actions node
            in 0<period
              \<and> period \<le> 924
              \<and> period dvd 924
              \<and> period dvd source_period
              \<and> length actions=period
              \<and> list_all (\<lambda>phase.
                comma_semantic_b1_local_action_shape (source_actions ! phase)
                \<and> comma_semantic_b1_edge_of_continuation bindings
                  (source_actions ! phase) = Some (actions ! (phase mod period)))
                [0..<source_period]))"

definition comma_semantic_b1_edge_refs_valid ::
    "comma_semantic_b1_node list \<Rightarrow> comma_semantic_b1_node \<Rightarrow> bool" where
  "comma_semantic_b1_edge_refs_valid nodes node =
    (\<forall>edge\<in>set (comma_semantic_b1_node_actions node).
      (case edge of
         Comma_Semantic_B1_Goto child \<Rightarrow>
           child < comma_semantic_b1_node_cid node
             \<and> comma_semantic_b1_node_of nodes child \<noteq> None
       | Comma_Semantic_B1_Live_Edge root \<Rightarrow> root < 46
       | Comma_Semantic_B1_Stop_Edge j \<Rightarrow> j \<le> 8
       | Comma_Semantic_B1_Invalid_Edge \<Rightarrow> True))"

definition comma_semantic_b1_graph_apply ::
    "comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_edge option" where
  "comma_semantic_b1_graph_apply nodes cid clock =
    (case comma_semantic_b1_node_of nodes cid of
       None \<Rightarrow> None
     | Some node \<Rightarrow>
         let period=comma_semantic_b1_node_period node;
             actions=comma_semantic_b1_node_actions node
         in if period=0 \<or> length actions\<noteq>period
            then None
            else Some (actions ! (clock mod period)))"

function comma_semantic_b1_graph_eval ::
    "comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_semantic_b1_result option" where
  "comma_semantic_b1_graph_eval nodes cid clock =
    (case comma_semantic_b1_graph_apply nodes cid clock of
       None \<Rightarrow> None
     | Some edge \<Rightarrow>
         case edge of
           Comma_Semantic_B1_Goto child \<Rightarrow>
             if child<cid then comma_semantic_b1_graph_eval nodes child clock else None
         | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
             if root<46 then Some (Comma_Semantic_B1_Live root) else None
         | Comma_Semantic_B1_Stop_Edge j \<Rightarrow>
             if j\<le>8 then Some (Comma_Semantic_B1_Stop j) else None
         | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
             Some Comma_Semantic_B1_Invalid)"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>(nodes,cid,clock). cid)") auto

definition comma_semantic_b1_round_output ::
    "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_b1_round_output clock source =
    comma_semantic_b1_of_word
      (comma_sector_base_project (comma_decisive_endpoint_round clock source))"

definition comma_semantic_b1_graph_valid ::
    "comma_semantic_b1_binding list \<Rightarrow> comma_semantic_b1_node list \<Rightarrow> bool" where
  "comma_semantic_b1_graph_valid bindings nodes =
    (distinct (map comma_semantic_b1_binding_source bindings)
      \<and> distinct (map comma_semantic_b1_node_cid nodes)
      \<and> list_all (comma_semantic_b1_binding_row_valid bindings nodes) bindings
      \<and> (\<forall>node\<in>set nodes.
        (\<exists>binding\<in>set bindings.
          comma_semantic_b1_binding_cid binding=comma_semantic_b1_node_cid node)
        \<and> comma_semantic_b1_edge_refs_valid nodes node)
      \<and> (\<forall>root<46. \<exists>binding\<in>set bindings.
        comma_semantic_b1_binding_source binding =
          Comma_Entry 1 0 (comma_offset_representatives!root)))"

lemma comma_semantic_b1_graph_binding_row:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding \<in> set bindings"
  shows "comma_semantic_b1_binding_row_valid bindings nodes binding"
proof -
  have rows: "list_all (comma_semantic_b1_binding_row_valid bindings nodes) bindings"
    using graph by (simp add: comma_semantic_b1_graph_valid_def)
  show ?thesis using rows binding by (simp add: list_all_iff)
qed

lemma comma_semantic_b1_binding_cid_of_sound:
  assumes found: "comma_semantic_b1_binding_cid_of bindings source=Some cid"
  shows "\<exists>binding\<in>set bindings.
    comma_semantic_b1_binding_source binding=source \<and>
    comma_semantic_b1_binding_cid binding=cid"
proof -
  have pair: "(source,cid) \<in>set (comma_semantic_b1_binding_ids bindings)"
    using found by (auto simp: comma_semantic_b1_binding_cid_of_def
      dest: map_of_SomeD)
  show ?thesis using pair
    by (auto simp: comma_semantic_b1_binding_ids_def)
qed

lemma comma_semantic_b1_node_lookup_member:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding \<in> set bindings"
    and cid: "comma_semantic_b1_binding_cid binding=cid"
  shows "comma_semantic_b1_node_of nodes cid \<noteq> None"
proof -
  have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
    by (rule comma_semantic_b1_graph_binding_row[OF graph binding])
  show ?thesis using row cid
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
qed

lemma comma_semantic_b1_binding_row_exact:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding \<in> set bindings"
    and cid: "comma_semantic_b1_binding_cid binding=cid"
    and phase: "phase < comma_decisive_sector_period
      (comma_semantic_b1_binding_source binding)"
  obtains node where
    "comma_semantic_b1_node_of nodes cid=Some node"
    "comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source binding) phase)"
    "comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source binding) phase) =
      Some (comma_semantic_b1_node_actions node !
        (phase mod comma_semantic_b1_node_period node))"
proof -
  have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
    by (rule comma_semantic_b1_graph_binding_row[OF graph binding])
  have lookup: "comma_semantic_b1_node_of nodes cid \<noteq> None"
    by (rule comma_semantic_b1_node_lookup_member[OF graph binding cid])
  obtain node where node: "comma_semantic_b1_node_of nodes cid=Some node"
    using lookup by (cases "comma_semantic_b1_node_of nodes cid") auto
  have period_divides: "comma_semantic_b1_node_period node dvd
      comma_decisive_sector_period (comma_semantic_b1_binding_source binding)"
    using row node cid
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have period_positive: "0<comma_semantic_b1_node_period node"
    using row node cid
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have row_facts:
    "comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source binding) phase) =
         Some (comma_semantic_b1_node_actions node !
           (phase mod comma_semantic_b1_node_period node))
      \<and> comma_semantic_b1_local_action_shape
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source binding) phase)"
  proof -
    obtain source_period source_actions where source_id:
      "comma_source_continuation_id
         (comma_semantic_b1_binding_source binding) =
       (source_period,source_actions)"
      by (cases "comma_source_continuation_id
        (comma_semantic_b1_binding_source binding)") auto
    have source_period: "source_period=comma_decisive_sector_period
        (comma_semantic_b1_binding_source binding)"
      and source_length: "length source_actions=source_period"
      and source_row: "list_all (\<lambda>j.
          comma_semantic_b1_local_action_shape (source_actions!j)
          \<and> comma_semantic_b1_edge_of_continuation bindings (source_actions!j) =
            Some (comma_semantic_b1_node_actions node !
              (j mod comma_semantic_b1_node_period node)))
          [0..<source_period]"
      using row node cid source_id
      by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
        split: option.splits)
    have source_base:
      "comma_semantic_b1_binding_source binding =
        comma_source_continuation_base
          (comma_semantic_b1_binding_source binding)"
      using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
    have listed: "phase < source_period"
      using phase source_period by simp
    have edge:
      "comma_semantic_b1_edge_of_continuation bindings (source_actions!phase) =
        Some (comma_semantic_b1_node_actions node !
          (phase mod comma_semantic_b1_node_period node))"
      using source_row listed by (auto simp: list_all_iff)
    have action_shape:
      "comma_semantic_b1_local_action_shape (source_actions!phase)"
      using source_row listed by (auto simp: list_all_iff)
    have at:
      "comma_source_continuation_action_at
          (comma_semantic_b1_binding_source binding) phase = source_actions!phase"
      using source_id phase source_period source_base
      by (simp add: comma_source_continuation_action_at_def
        comma_source_continuation_id_def Let_def)
    show ?thesis using edge action_shape at by simp
  qed
  have row_edge:
    "comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_at
        (comma_semantic_b1_binding_source binding) phase) =
       Some (comma_semantic_b1_node_actions node !
         (phase mod comma_semantic_b1_node_period node))"
    by (rule conjunct1[OF row_facts])
  have shape:
    "comma_semantic_b1_local_action_shape
      (comma_source_continuation_action_at
        (comma_semantic_b1_binding_source binding) phase)"
    by (rule conjunct2[OF row_facts])
  show thesis
    by (rule that[OF node shape])
      (use row_edge in simp)
qed

lemma comma_semantic_b1_graph_edges_are_well_formed:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and node: "node \<in> set nodes"
    and edge: "edge \<in> set (comma_semantic_b1_node_actions node)"
  shows "case edge of
      Comma_Semantic_B1_Goto child \<Rightarrow>
        child < comma_semantic_b1_node_cid node \<and>
          comma_semantic_b1_node_of nodes child \<noteq> None
    | Comma_Semantic_B1_Live_Edge root \<Rightarrow> root < 46
    | Comma_Semantic_B1_Stop_Edge j \<Rightarrow> j \<le> 8
    | Comma_Semantic_B1_Invalid_Edge \<Rightarrow> True"
  using graph node edge
  by (auto simp: comma_semantic_b1_graph_valid_def
    comma_semantic_b1_edge_refs_valid_def)

lemma comma_semantic_b1_node_of_member:
  assumes node: "comma_semantic_b1_node_of nodes cid=Some value"
  shows "value \<in> set nodes"
  using node
  by (auto simp: comma_semantic_b1_node_of_def
    comma_semantic_b1_nodes_by_cid_def dest: map_of_SomeD)

lemma comma_semantic_b1_node_of_key:
  assumes node: "comma_semantic_b1_node_of nodes cid=Some value"
  shows "comma_semantic_b1_node_cid value=cid"
  using node
  by (auto simp: comma_semantic_b1_node_of_def
    comma_semantic_b1_nodes_by_cid_def dest: map_of_SomeD)

lemma comma_semantic_b1_graph_apply_goto_decreases:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding \<in> set bindings"
    and cid: "comma_semantic_b1_binding_cid binding=parent"
    and applied: "comma_semantic_b1_graph_apply nodes parent clock=
      Some (Comma_Semantic_B1_Goto child)"
  shows "child<parent"
proof -
  obtain node where node: "comma_semantic_b1_node_of nodes parent=Some node"
    using comma_semantic_b1_node_lookup_member[OF graph binding cid]
    by (cases "comma_semantic_b1_node_of nodes parent") auto
  have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
    by (rule comma_semantic_b1_graph_binding_row[OF graph binding])
  have period_positive: "0<comma_semantic_b1_node_period node"
    and action_length: "length (comma_semantic_b1_node_actions node)=
      comma_semantic_b1_node_period node"
    using row node cid
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have index:
    "clock mod comma_semantic_b1_node_period node <
      length (comma_semantic_b1_node_actions node)"
    using period_positive action_length by simp
  have selected:
    "comma_semantic_b1_node_actions node !
      (clock mod comma_semantic_b1_node_period node)=
       Comma_Semantic_B1_Goto child"
    using applied node period_positive action_length
    by (simp add: comma_semantic_b1_graph_apply_def
      comma_semantic_b1_node_of_def comma_semantic_b1_nodes_by_cid_def)
  have member: "Comma_Semantic_B1_Goto child \<in>
      set (comma_semantic_b1_node_actions node)"
  proof -
    have selected_member:
      "comma_semantic_b1_node_actions node !
        (clock mod comma_semantic_b1_node_period node) \<in>
        set (comma_semantic_b1_node_actions node)"
      by (rule nth_mem[OF index])
    show ?thesis using selected selected_member by simp
  qed
  have node_member: "node\<in>set nodes"
    by (rule comma_semantic_b1_node_of_member[OF node])
  have all_node_checks:
    "\<forall>candidate\<in>set nodes.
      (\<exists>binding\<in>set bindings.
        comma_semantic_b1_binding_cid binding=comma_semantic_b1_node_cid candidate)
      \<and> comma_semantic_b1_edge_refs_valid nodes candidate"
    using graph by (simp add: comma_semantic_b1_graph_valid_def)
  have refs:
    "comma_semantic_b1_edge_refs_valid nodes node"
    using all_node_checks node_member by blast
  have valid_edge:
    "case Comma_Semantic_B1_Goto child of
       Comma_Semantic_B1_Goto target \<Rightarrow>
         target < comma_semantic_b1_node_cid node \<and>
           comma_semantic_b1_node_of nodes target \<noteq> None
     | Comma_Semantic_B1_Live_Edge root \<Rightarrow> root < 46
     | Comma_Semantic_B1_Stop_Edge j \<Rightarrow> j \<le> 8
     | Comma_Semantic_B1_Invalid_Edge \<Rightarrow> True"
    by (rule comma_semantic_b1_graph_edges_are_well_formed[OF graph node_member member])
  have node_key: "comma_semantic_b1_node_cid node=parent"
    by (rule comma_semantic_b1_node_of_key[OF node])
  show ?thesis using valid_edge node_key by simp
qed

lemma comma_semantic_b1_graph_apply_exact_local:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding \<in> set bindings"
    and cid: "comma_semantic_b1_binding_cid binding=target"
  shows "comma_semantic_b1_graph_apply nodes target clock =
    comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_at
        (comma_semantic_b1_binding_source binding) clock)"
proof -
  let ?source = "comma_semantic_b1_binding_source binding"
  let ?period = "comma_decisive_sector_period ?source"
  have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
    by (rule comma_semantic_b1_graph_binding_row[OF graph binding])
  have source_base: "?source=comma_source_continuation_base ?source"
    using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
  obtain node where node:
      "comma_semantic_b1_node_of nodes target=Some node"
    using comma_semantic_b1_node_lookup_member[OF graph binding cid]
    by (cases "comma_semantic_b1_node_of nodes target") auto
  have node_period_positive: "0<comma_semantic_b1_node_period node"
    and period_divides:
      "comma_semantic_b1_node_period node dvd ?period"
    and node_length:
      "length (comma_semantic_b1_node_actions node)=
        comma_semantic_b1_node_period node"
    using row cid node
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have source_period_positive: "0<?period"
  proof -
    have admitted: "comma_round_admitted ?source"
      using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
    show ?thesis by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
  qed
  have in_range: "clock mod ?period<?period"
    using source_period_positive by simp
  obtain row_node where row_node:
      "comma_semantic_b1_node_of nodes target=Some row_node"
    and phase_row:
      "comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at ?source (clock mod ?period)) =
       Some (comma_semantic_b1_node_actions row_node !
         ((clock mod ?period) mod comma_semantic_b1_node_period row_node))"
    by (rule comma_semantic_b1_binding_row_exact[OF graph binding cid in_range])
  have row_node_eq: "row_node=node"
    using row_node node by simp
  have row_period_divides:
    "comma_semantic_b1_node_period row_node dvd ?period"
    using period_divides row_node_eq by simp
  have mod_phase:
    "(clock mod ?period) mod comma_semantic_b1_node_period row_node =
       clock mod comma_semantic_b1_node_period row_node"
    by (rule mod_mod_cancel[OF row_period_divides])
  have action_phase:
    "comma_source_continuation_action_at ?source (clock mod ?period) =
      comma_source_continuation_action_at ?source clock"
    using source_base by (simp add: comma_source_continuation_action_at_def
      comma_source_continuation_id_def Let_def)
  show ?thesis
    using row_node phase_row mod_phase action_phase node_period_positive node_length
      row_node_eq
    by (simp add: comma_semantic_b1_graph_apply_def
      comma_semantic_b1_node_of_def comma_semantic_b1_nodes_by_cid_def)
qed

lemma comma_semantic_b1_graph_eval_apply_goto:
  assumes applied: "comma_semantic_b1_graph_apply nodes cid clock=
      Some (Comma_Semantic_B1_Goto child)"
    and decreasing: "child<cid"
  shows "comma_semantic_b1_graph_eval nodes cid clock=
    comma_semantic_b1_graph_eval nodes child clock"
  using applied decreasing
  by (subst (1) comma_semantic_b1_graph_eval.simps)
    (simp add: applied decreasing del: comma_semantic_b1_graph_eval.simps)

lemma comma_semantic_b1_graph_eval_apply_live:
  assumes applied: "comma_semantic_b1_graph_apply nodes cid clock=
      Some (Comma_Semantic_B1_Live_Edge root)"
    and root: "root<46"
  shows "comma_semantic_b1_graph_eval nodes cid clock=
    Some (Comma_Semantic_B1_Live root)"
  using applied root
  by (subst (1) comma_semantic_b1_graph_eval.simps)
    (simp add: applied root del: comma_semantic_b1_graph_eval.simps)

lemma comma_semantic_b1_graph_eval_apply_stop:
  assumes applied: "comma_semantic_b1_graph_apply nodes cid clock=
      Some (Comma_Semantic_B1_Stop_Edge j)"
    and bound: "j\<le>8"
  shows "comma_semantic_b1_graph_eval nodes cid clock=
    Some (Comma_Semantic_B1_Stop j)"
  using applied bound
  by (subst (1) comma_semantic_b1_graph_eval.simps)
    (simp add: applied bound del: comma_semantic_b1_graph_eval.simps)

lemma comma_semantic_b1_graph_eval_apply_invalid:
  assumes applied: "comma_semantic_b1_graph_apply nodes cid clock=
      Some Comma_Semantic_B1_Invalid_Edge"
  shows "comma_semantic_b1_graph_eval nodes cid clock=
    Some Comma_Semantic_B1_Invalid"
  using applied
  by (subst (1) comma_semantic_b1_graph_eval.simps)
    (simp add: applied del: comma_semantic_b1_graph_eval.simps)

lemma comma_semantic_b1_base_packet_target_shift_zero:
  assumes base: "source=comma_source_continuation_base source"
  shows "comma_source_continuation_shift
      (fst (comma_decisive_endpoint_packet clock source))=0"
  using base
  by (cases source)
    (simp_all add: comma_decisive_endpoint_packet_def Let_def
      comma_decisive_sector_target.simps split: option.splits prod.splits)

lemma comma_semantic_b1_edge_transport_invariant:
  "comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_transport shift action) =
    comma_semantic_b1_edge_of_continuation bindings action"
  by (cases action) (simp_all split: comma_finite_position.splits)

lemma comma_semantic_b1_edge_apply_exact_packet:
  assumes admitted: "comma_round_admitted source"
  shows "comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_at
        (comma_source_continuation_base source)
        ((phase+comma_source_continuation_shift source) mod 924)) =
    comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase source))"
proof -
  have exact: "comma_source_continuation_transport
      (comma_source_continuation_shift source)
      (comma_source_continuation_action_at
        (comma_source_continuation_base source)
        ((phase+comma_source_continuation_shift source) mod 924)) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase source)"
    by (rule comma_source_continuation_apply_exact[OF admitted])
  have mapped: "comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_transport
        (comma_source_continuation_shift source)
        (comma_source_continuation_action_at
          (comma_source_continuation_base source)
          ((phase+comma_source_continuation_shift source) mod 924))) =
      comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_of_packet
          (comma_decisive_endpoint_packet phase source))"
    by (rule arg_cong[OF exact, of
      "comma_semantic_b1_edge_of_continuation bindings"])
  show ?thesis
    using mapped by (simp add: comma_semantic_b1_edge_transport_invariant)
qed

lemma comma_semantic_b1_graph_apply_exact_packet:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding \<in> set bindings"
    and base: "comma_semantic_b1_binding_source binding=
      comma_source_continuation_base source"
    and cid: "comma_semantic_b1_binding_cid binding=target"
    and admitted: "comma_round_admitted source"
  shows "comma_semantic_b1_graph_apply nodes target
      ((phase+comma_source_continuation_shift source) mod 924) =
    comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase source))"
proof -
  have base_admitted:
    "comma_round_admitted (comma_source_continuation_base source)"
    by (rule comma_source_continuation_base_admitted[OF admitted])
  have local_apply:
    "comma_semantic_b1_graph_apply nodes target
        ((phase+comma_source_continuation_shift source) mod 924) =
      comma_semantic_b1_edge_of_continuation bindings
        (comma_source_continuation_action_at
          (comma_semantic_b1_binding_source binding)
          ((phase+comma_source_continuation_shift source) mod 924))"
    by (rule comma_semantic_b1_graph_apply_exact_local[OF graph binding cid])
  have projected:
    "comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_at
        (comma_source_continuation_base source)
        ((phase+comma_source_continuation_shift source) mod 924)) =
     comma_semantic_b1_edge_of_continuation bindings
       (comma_source_continuation_action_of_packet
         (comma_decisive_endpoint_packet phase source))"
    by (rule comma_semantic_b1_edge_apply_exact_packet[OF admitted])
  show ?thesis using local_apply projected base by simp
qed

definition comma_semantic_b1_graph_correct_at ::
    "comma_semantic_b1_binding list \<Rightarrow> comma_semantic_b1_node list \<Rightarrow>
      nat \<Rightarrow> bool" where
  "comma_semantic_b1_graph_correct_at bindings nodes cid =
    (\<forall>binding\<in>set bindings.
       comma_semantic_b1_binding_cid binding=cid \<longrightarrow>
       (\<forall>clock. comma_semantic_b1_graph_eval nodes cid clock =
         Some (comma_semantic_b1_round_output clock
           (comma_semantic_b1_binding_source binding))))"

theorem comma_semantic_b1_graph_eval_refines_endpoint:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
  shows "\<forall>cid. comma_semantic_b1_graph_correct_at bindings nodes cid"
proof (rule allI)
  fix cid
  show "comma_semantic_b1_graph_correct_at bindings nodes cid"
  proof (induction cid rule: less_induct)
    case (less cid)
    show ?case
      unfolding comma_semantic_b1_graph_correct_at_def
    proof (intro ballI impI allI)
      fix binding clock
      assume binding_member: "binding\<in>set bindings"
        and binding_cid: "comma_semantic_b1_binding_cid binding=cid"
      let ?source = "comma_semantic_b1_binding_source binding"
      have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
        by (rule comma_semantic_b1_graph_binding_row[OF graph binding_member])
      have admitted: "comma_round_admitted ?source"
        using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
      have source_base: "?source=comma_source_continuation_base ?source"
        using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
      have source_period_positive: "0<comma_decisive_sector_period ?source"
        by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
      have action_slot:
        "comma_source_continuation_action_at ?source clock =
          comma_source_continuation_action_of_packet
            (comma_decisive_endpoint_packet clock ?source)"
        using comma_source_continuation_signature_slot[OF admitted, of clock]
          source_base by simp
      have current_node_exists:
        "comma_semantic_b1_node_of nodes cid\<noteq>None"
        by (rule comma_semantic_b1_node_lookup_member
          [OF graph binding_member binding_cid])
      obtain current_node where current_node:
        "comma_semantic_b1_node_of nodes cid=Some current_node"
        using current_node_exists
        by (cases "comma_semantic_b1_node_of nodes cid") auto
      have current_period:
        "0<comma_semantic_b1_node_period current_node"
        and current_actions:
        "length (comma_semantic_b1_node_actions current_node)=
          comma_semantic_b1_node_period current_node"
        using row current_node binding_cid
        by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
          split: option.splits)
      have source_shift_zero:
        "comma_source_continuation_shift ?source=0"
        using source_base by (cases ?source) simp_all
      have node_period_divides:
        "comma_semantic_b1_node_period current_node dvd 924"
        using row current_node binding_cid
        by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
          split: option.splits)
      have apply_periodic:
        "comma_semantic_b1_graph_apply nodes cid clock =
          comma_semantic_b1_graph_apply nodes cid (clock mod 924)"
        unfolding comma_semantic_b1_graph_apply_def
        using current_node current_period current_actions node_period_divides
        by (simp add: mod_mod_cancel)
      have packet_action:
        "comma_semantic_b1_graph_apply nodes cid clock =
          comma_semantic_b1_edge_of_continuation bindings
            (comma_source_continuation_action_of_packet
              (comma_decisive_endpoint_packet clock ?source))"
      proof -
        have shifted:
          "comma_semantic_b1_graph_apply nodes cid
              ((clock+comma_source_continuation_shift ?source) mod 924) =
            comma_semantic_b1_edge_of_continuation bindings
              (comma_source_continuation_action_of_packet
                (comma_decisive_endpoint_packet clock ?source))"
          by (rule comma_semantic_b1_graph_apply_exact_packet
            [OF graph binding_member source_base binding_cid admitted])
        show ?thesis using apply_periodic shifted source_shift_zero
          by simp
      qed
      have apply_present:
        "comma_semantic_b1_graph_apply nodes cid clock\<noteq>None"
        using current_node current_period current_actions
        by (simp add: comma_semantic_b1_graph_apply_def)
      obtain target move where packet:
        "comma_decisive_endpoint_packet clock ?source=(target,move)"
        by (cases "comma_decisive_endpoint_packet clock ?source") auto
      have target_admitted:
        "comma_round_admitted target"
        using comma_decisive_packet_target_admitted[OF admitted, of clock] packet
        by simp
      have packet_target:
        "comma_decisive_sector_target clock ?source=target"
        using packet by (simp add: comma_decisive_endpoint_packet_def Let_def)
      have fast_move:
        "comma_fast_step (clock mod 924) target=move"
        using packet packet_target
        by (simp add: comma_decisive_endpoint_packet_def Let_def)
      have finite_move:
        "comma_finite_step (clock mod 924) target=move"
        using fast_move by (simp only: comma_fast_step_correct)
      have target_shift_zero:
        "comma_source_continuation_shift target=0"
        using comma_semantic_b1_base_packet_target_shift_zero
            [OF source_base, of clock]
          packet by simp
      have packet_shape:
        "comma_semantic_b1_local_action_shape
          (comma_source_continuation_action_of_packet (target,move))"
      proof -
        let ?P = "comma_decisive_sector_period ?source"
        have phase: "clock mod ?P<?P"
          using source_period_positive by simp
        obtain node where node:
          "comma_semantic_b1_node_of nodes cid=Some node"
          and shape:
          "comma_semantic_b1_local_action_shape
            (comma_source_continuation_action_at ?source (clock mod ?P))"
          and edge:
          "comma_semantic_b1_edge_of_continuation bindings
            (comma_source_continuation_action_at ?source (clock mod ?P)) =
            Some (comma_semantic_b1_node_actions node !
              ((clock mod ?P) mod comma_semantic_b1_node_period node))"
          by (rule comma_semantic_b1_binding_row_exact
            [OF graph binding_member binding_cid phase])
        have periodic:
          "comma_source_continuation_action_at ?source (clock mod ?P) =
            comma_source_continuation_action_at ?source clock"
          using source_base by (simp add: comma_source_continuation_action_at_def
            comma_source_continuation_id_def Let_def)
        show ?thesis using shape periodic action_slot packet by simp
      qed
      have round_equation:
        "comma_decisive_endpoint_round clock ?source =
          (case move of
             Comma_Next successor \<Rightarrow>
               if comma_round_crossing target successor then
                 Comma_Round_Cross successor
               else comma_decisive_endpoint_round clock successor
           | Comma_Fork a delta \<Rightarrow> Comma_Round_Fork a delta
           | Comma_Landmine delta \<Rightarrow> Comma_Round_Landmine delta
           | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
        using comma_decisive_endpoint_round_packet[OF admitted]
          packet by simp
      show "comma_semantic_b1_graph_eval nodes cid clock =
        Some (comma_semantic_b1_round_output clock ?source)"
      proof (cases move)
        case (Comma_Next successor)
        show ?thesis
        proof (cases "comma_round_crossing target successor")
          case True
          have finite_next:
            "comma_finite_step (clock mod 924) target=Comma_Next successor"
            using finite_move Comma_Next by simp
          obtain delta headroom offset where target_shape:
            "target=Comma_Near 9 delta headroom"
            and successor_shape:
            "successor=Comma_Entry 1 (Suc delta) offset"
            and offset_bound: "offset\<le>90"
            using comma_round_crossing_offset_bound[OF finite_next True]
            by blast
          have target_delta: "delta=0"
            using target_shape target_shift_zero by simp
          have live_edge:
            "comma_semantic_b1_graph_apply nodes cid clock =
              Some (Comma_Semantic_B1_Live_Edge (comma_offset_orbit offset))"
            using packet_action packet Comma_Next True target_shape
              successor_shape target_delta offset_bound
            by (simp add: comma_source_continuation_action_of_packet.simps
              comma_semantic_b1_edge_of_continuation.simps)
          have eval_live:
            "comma_semantic_b1_graph_eval nodes cid clock =
              Some (Comma_Semantic_B1_Live (comma_offset_orbit offset))"
            by (rule comma_semantic_b1_graph_eval_apply_live[OF live_edge])
              (rule comma_offset_orbit_bound)
          show ?thesis
            using eval_live round_equation Comma_Next True successor_shape
              target_delta offset_bound
            by (simp add: comma_semantic_b1_round_output_def
              comma_semantic_b1_of_word.simps comma_sector_base_project.simps
              comma_decade_root_admitted_def)
        next
          case False
          have successor_shift_zero:
            "comma_source_continuation_shift successor=0"
            using packet_shape packet Comma_Next False
            by (simp add: comma_semantic_b1_local_action_shape.simps
              comma_source_continuation_action_of_packet.simps)
          have successor_base:
            "comma_source_continuation_base successor=successor"
            using successor_shift_zero
            by (cases successor) simp_all
          have edge_lookup:
            "comma_semantic_b1_graph_apply nodes cid clock =
              map_option Comma_Semantic_B1_Goto
                (comma_semantic_b1_binding_cid_of bindings successor)"
            using packet_action packet Comma_Next False successor_base
              successor_shift_zero
            by (simp add: comma_source_continuation_action_of_packet.simps
              comma_semantic_b1_edge_of_continuation.simps)
          obtain child where child_key:
            "comma_semantic_b1_binding_cid_of bindings successor=Some child"
            using edge_lookup apply_present
            by (cases "comma_semantic_b1_binding_cid_of bindings successor") auto
          have child_edge:
            "comma_semantic_b1_graph_apply nodes cid clock =
              Some (Comma_Semantic_B1_Goto child)"
            using edge_lookup child_key by simp
          have child_less: "child<cid"
            by (rule comma_semantic_b1_graph_apply_goto_decreases
              [OF graph binding_member binding_cid child_edge])
          obtain child_binding where child_member: "child_binding\<in>set bindings"
            and child_source:
              "comma_semantic_b1_binding_source child_binding=successor"
            and child_cid:
              "comma_semantic_b1_binding_cid child_binding=child"
            using comma_semantic_b1_binding_cid_of_sound[OF child_key] by blast
          have child_correct:
            "comma_semantic_b1_graph_correct_at bindings nodes child"
            by (rule less.IH[OF child_less])
          have child_eval:
            "comma_semantic_b1_graph_eval nodes child clock =
              Some (comma_semantic_b1_round_output clock successor)"
            using child_correct child_member child_source child_cid
            by (simp add: comma_semantic_b1_graph_correct_at_def)
          have eval_goto:
            "comma_semantic_b1_graph_eval nodes cid clock =
              comma_semantic_b1_graph_eval nodes child clock"
            by (rule comma_semantic_b1_graph_eval_apply_goto
              [OF child_edge child_less])
          show ?thesis using eval_goto child_eval round_equation False Comma_Next
            by (simp add: comma_semantic_b1_round_output_def)
        qed
      next
        case (Comma_Fork a delta)
        have finite_fork:
          "comma_finite_step (clock mod 924) target=Comma_Fork a delta"
          using finite_move Comma_Fork by simp
        have fork_bounds: "2\<le>a \<and> a\<le>9"
          by (rule comma_finite_fork_digit_bounds[OF finite_fork])
        have delta_zero: "delta=0"
          using packet_shape packet Comma_Fork
          by (simp add: comma_semantic_b1_local_action_shape.simps
            comma_source_continuation_action_of_packet.simps)
        have stop_edge:
          "comma_semantic_b1_graph_apply nodes cid clock =
            Some (Comma_Semantic_B1_Stop_Edge (a-2))"
          using packet_action packet Comma_Fork fork_bounds
          by (simp add: comma_source_continuation_action_of_packet.simps
            comma_semantic_b1_edge_of_continuation.simps)
        have eval_stop:
          "comma_semantic_b1_graph_eval nodes cid clock =
            Some (Comma_Semantic_B1_Stop (a-2))"
          by (rule comma_semantic_b1_graph_eval_apply_stop[OF stop_edge])
            (use fork_bounds in arith)
        show ?thesis using eval_stop round_equation Comma_Fork delta_zero fork_bounds
          by (simp add: comma_semantic_b1_round_output_def
            comma_semantic_b1_of_word.simps comma_sector_base_project.simps
            comma_terminal_weight_encode_def)
      next
        case (Comma_Landmine delta)
        have delta_zero: "delta=0"
          using packet_shape packet Comma_Landmine
          by (simp add: comma_semantic_b1_local_action_shape.simps
            comma_source_continuation_action_of_packet.simps)
        have stop_edge:
          "comma_semantic_b1_graph_apply nodes cid clock =
            Some (Comma_Semantic_B1_Stop_Edge 8)"
          using packet_action packet Comma_Landmine
          by (simp add: comma_source_continuation_action_of_packet.simps
            comma_semantic_b1_edge_of_continuation.simps)
        have eval_stop:
          "comma_semantic_b1_graph_eval nodes cid clock =
            Some (Comma_Semantic_B1_Stop 8)"
          by (rule comma_semantic_b1_graph_eval_apply_stop[OF stop_edge]) simp
        show ?thesis using eval_stop round_equation Comma_Landmine delta_zero
          by (simp add: comma_semantic_b1_round_output_def
            comma_semantic_b1_of_word.simps comma_sector_base_project.simps
            comma_terminal_weight_encode_def)
      next
        case Comma_Invalid
        have invalid_edge:
          "comma_semantic_b1_graph_apply nodes cid clock =
            Some Comma_Semantic_B1_Invalid_Edge"
          using packet_action packet Comma_Invalid
          by (simp add: comma_source_continuation_action_of_packet.simps
            comma_semantic_b1_edge_of_continuation.simps)
        have eval_invalid:
          "comma_semantic_b1_graph_eval nodes cid clock =
            Some Comma_Semantic_B1_Invalid"
          by (rule comma_semantic_b1_graph_eval_apply_invalid[OF invalid_edge])
        show ?thesis using eval_invalid round_equation Comma_Invalid
          by (simp add: comma_semantic_b1_round_output_def
            comma_semantic_b1_of_word.simps comma_sector_base_project.simps)
      qed
    qed
  qed
qed

theorem comma_semantic_b1_graph_root_exact:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and clock: "clock<924"
    and root: "root<46"
  obtains binding where
    "binding\<in>set bindings"
    "comma_semantic_b1_binding_source binding =
      Comma_Entry 1 0 (comma_offset_representatives!root)"
    "comma_semantic_b1_graph_eval nodes
      (comma_semantic_b1_binding_cid binding) clock =
        Some (comma_semantic_b1 clock root)"
proof -
  have roots:
    "\<forall>i<46. \<exists>binding\<in>set bindings.
      comma_semantic_b1_binding_source binding =
        Comma_Entry 1 0 (comma_offset_representatives!i)"
    using graph by (simp add: comma_semantic_b1_graph_valid_def)
  obtain binding where binding:
    "binding\<in>set bindings"
    and source:
    "comma_semantic_b1_binding_source binding =
      Comma_Entry 1 0 (comma_offset_representatives!root)"
    using roots root by blast
  let ?cid = "comma_semantic_b1_binding_cid binding"
  have all: "\<forall>cid. comma_semantic_b1_graph_correct_at bindings nodes cid"
    by (rule comma_semantic_b1_graph_eval_refines_endpoint[OF graph])
  have exact:
    "comma_semantic_b1_graph_eval nodes ?cid clock =
      Some (comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source binding))"
    using all binding by (simp add: comma_semantic_b1_graph_correct_at_def)
  have output_exact:
    "comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source binding) =
      comma_semantic_b1 clock root"
    using source clock root
    by (simp add: comma_semantic_b1_round_output_def
      comma_semantic_b1_source_def comma_semantic_b1_def
      comma_decisive_B1_def comma_decisive_B1_source_def)
  show thesis using that[OF binding source] exact output_exact by simp
qed


ML \<open>
  val checked = @{thms comma_semantic_b1_node_lookup_member
    comma_semantic_b1_node_of_key
    comma_semantic_b1_binding_row_exact
    comma_semantic_b1_graph_edges_are_well_formed
    comma_semantic_b1_graph_apply_exact_local
    comma_semantic_b1_graph_eval_refines_endpoint
    comma_semantic_b1_graph_root_exact
    comma_semantic_b1_edge_transport_invariant
    comma_semantic_b1_edge_apply_exact_packet
    comma_semantic_b1_graph_apply_exact_packet};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic B1 continuation graph" checked;
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Semantic graph endpoint application"
    ["comma_source_continuation_apply_exact",
      "comma_decisive_endpoint_round_packet",
      "comma_semantic_b1_graph_apply_exact_local",
      "comma_semantic_b1_graph_apply_goto_decreases"]
    @{thms comma_semantic_b1_graph_eval_refines_endpoint
      comma_semantic_b1_graph_root_exact};
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Semantic graph exact source packets"
    ["comma_source_continuation_apply_exact"]
    @{thms comma_semantic_b1_edge_apply_exact_packet
      comma_semantic_b1_graph_apply_exact_packet};
\<close>

end
