theory Comma_Semantic_Graph_Core
  imports Comma_Semantic_B1
begin
ML \<open>Comma_Proof_Profile.report "B1 graph core stage=entered"\<close>

text \<open>
The continuation graph separates reusable behavior from its source binding.
Node rows contain only quotient edges.  Exact source positions and the
phase-dependent endpoint packets remain in the proof-only binding relation;
in particular, shifts and absolute terminal weights never enter a CID.
Its evaluator follows only strictly smaller CIDs; endpoint refinement connects
graph application to exact B1 round semantics.
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

lemma comma_semantic_b1_round_output_root_exact:
  assumes clock: "clock < 924" and root: "root < 46"
  shows "comma_semantic_b1_round_output clock
      (Comma_Entry 1 0 (comma_offset_representatives ! root)) =
    comma_semantic_b1 clock root"
  using clock root
  by (simp add: comma_semantic_b1_round_output_def
      comma_semantic_b1_def comma_decisive_B1_def
      comma_decisive_B1_source_def)

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

text \<open>
The completed graph validity variant keeps one all-source lookup table but
requires an immediate action row only from a local representative.  A
nonrepresentative source may share that representative's CID only with an
admitted normalized period-one zero-shift Goto and an exact completed-output
transport at every receiving clock.  The full clock is retained across the
Goto; the source's one-slot port index is not used as a child phase.  The
all-clock endpoint transport is an explicit certificate premise.  Physical
elapsed weights remain source-bound and are not identified by this semantic
graph predicate.
\<close>

definition comma_semantic_b1_completed_binding_row_valid ::
    "comma_semantic_b1_binding list \<Rightarrow> comma_semantic_b1_node list
      \<Rightarrow> comma_semantic_b1_binding \<Rightarrow> bool" where
  "comma_semantic_b1_completed_binding_row_valid bindings nodes binding \<longleftrightarrow>
    (\<exists>representative\<in>set bindings.
      comma_semantic_b1_binding_cid representative =
        comma_semantic_b1_binding_cid binding
      \<and> comma_semantic_b1_binding_row_valid bindings nodes representative
      \<and> comma_round_admitted (comma_semantic_b1_binding_source binding)
      \<and> comma_semantic_b1_binding_source binding =
        comma_source_continuation_base
          (comma_semantic_b1_binding_source binding)
      \<and> (\<forall>clock.
        comma_semantic_b1_round_output clock
            (comma_semantic_b1_binding_source binding) =
          comma_semantic_b1_round_output clock
            (comma_semantic_b1_binding_source representative))
      \<and> (binding = representative
        \<or> (comma_decisive_sector_period
              (comma_semantic_b1_binding_source binding) = 1
          \<and> comma_source_continuation_action_at
              (comma_semantic_b1_binding_source binding) 0 =
            Comma_Continuation_Goto
              (comma_semantic_b1_binding_source representative) 0
          \<and> 9 - comma_sector_number
              (comma_semantic_b1_binding_source representative) <
            9 - comma_sector_number
              (comma_semantic_b1_binding_source binding))))"

definition comma_semantic_b1_graph_completed_valid ::
    "comma_semantic_b1_binding list \<Rightarrow> comma_semantic_b1_node list \<Rightarrow> bool" where
  "comma_semantic_b1_graph_completed_valid bindings nodes \<longleftrightarrow>
    (distinct (map comma_semantic_b1_binding_source bindings)
      \<and> distinct (map comma_semantic_b1_node_cid nodes)
      \<and> list_all
        (comma_semantic_b1_completed_binding_row_valid bindings nodes) bindings
      \<and> (\<forall>node\<in>set nodes.
        (\<exists>binding\<in>set bindings.
          comma_semantic_b1_binding_cid binding =
            comma_semantic_b1_node_cid node)
        \<and> comma_semantic_b1_edge_refs_valid nodes node)
      \<and> (\<forall>root<46. \<exists>binding\<in>set bindings.
        comma_semantic_b1_binding_source binding =
          Comma_Entry 1 0 (comma_offset_representatives!root)))"

lemma comma_semantic_b1_graph_completed_binding_row:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid bindings nodes"
    and binding: "binding \<in> set bindings"
  obtains representative where
    "representative \<in> set bindings"
    "comma_semantic_b1_binding_cid representative =
      comma_semantic_b1_binding_cid binding"
    "comma_semantic_b1_binding_row_valid bindings nodes representative"
    "comma_round_admitted (comma_semantic_b1_binding_source binding)"
    "comma_semantic_b1_binding_source binding =
      comma_source_continuation_base (comma_semantic_b1_binding_source binding)"
    "\<forall>clock. comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source binding) =
      comma_semantic_b1_round_output clock
        (comma_semantic_b1_binding_source representative)"
proof -
  have rows:
      "list_all (comma_semantic_b1_completed_binding_row_valid bindings nodes)
        bindings"
    using graph by (simp add: comma_semantic_b1_graph_completed_valid_def)
  have row:
      "comma_semantic_b1_completed_binding_row_valid bindings nodes binding"
    using rows binding by (simp add: list_all_iff)
  obtain representative where representative:
      "representative \<in> set bindings"
      "comma_semantic_b1_binding_cid representative =
        comma_semantic_b1_binding_cid binding"
      "comma_semantic_b1_binding_row_valid bindings nodes representative"
      "comma_round_admitted (comma_semantic_b1_binding_source binding)"
      "comma_semantic_b1_binding_source binding =
        comma_source_continuation_base (comma_semantic_b1_binding_source binding)"
      "(\<forall>clock. comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source binding) =
        comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source representative))"
    using row by (auto simp: comma_semantic_b1_completed_binding_row_valid_def)
  show thesis by (rule that[OF representative(1-6)])
qed

lemma comma_semantic_b1_graph_valid_implies_completed_valid:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
  shows "comma_semantic_b1_graph_completed_valid bindings nodes"
proof -
  have rows:
      "list_all (comma_semantic_b1_completed_binding_row_valid bindings nodes)
        bindings"
  proof -
    have all_rows:
        "\<forall>binding\<in>set bindings.
          comma_semantic_b1_completed_binding_row_valid bindings nodes binding"
    proof
      fix binding
      assume binding: "binding \<in> set bindings"
      have original_rows:
          "list_all (comma_semantic_b1_binding_row_valid bindings nodes) bindings"
        using graph by (simp add: comma_semantic_b1_graph_valid_def)
      have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
        using original_rows binding by (simp add: list_all_iff)
      have admitted:
          "comma_round_admitted (comma_semantic_b1_binding_source binding)"
        and normalized:
          "comma_semantic_b1_binding_source binding =
            comma_source_continuation_base (comma_semantic_b1_binding_source binding)"
        using row by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def)
      show "comma_semantic_b1_completed_binding_row_valid bindings nodes binding"
        unfolding comma_semantic_b1_completed_binding_row_valid_def
        using binding row admitted normalized by (intro bexI[of _ binding]) auto
    qed
    show ?thesis using all_rows by (simp add: list_all_iff)
  qed
  show ?thesis
    using graph rows
    by (simp add: comma_semantic_b1_graph_valid_def
      comma_semantic_b1_graph_completed_valid_def)
qed

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

lemma comma_semantic_b1_binding_row_exact_from_valid:
  assumes row:
      "comma_semantic_b1_binding_row_valid bindings nodes binding"
    and cid:
      "comma_semantic_b1_binding_cid binding=cid"
    and node:
      "comma_semantic_b1_node_of nodes cid=Some value"
    and phase:
      "phase < comma_decisive_sector_period
        (comma_semantic_b1_binding_source binding)"
  shows "comma_semantic_b1_local_action_shape
      (comma_source_continuation_action_at
        (comma_semantic_b1_binding_source binding) phase)
    \<and> comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_at
        (comma_semantic_b1_binding_source binding) phase) =
      Some (comma_semantic_b1_node_actions value !
        (phase mod comma_semantic_b1_node_period value))"
proof -
  let ?source = "comma_semantic_b1_binding_source binding"
  let ?P = "comma_decisive_sector_period ?source"
  obtain source_period source_actions where source_id:
      "comma_source_continuation_id ?source=(source_period,source_actions)"
    by (cases "comma_source_continuation_id ?source") auto
  have source_period: "source_period=?P"
    and source_length: "length source_actions=source_period"
    and row_phases:
      "list_all (\<lambda>j.
        comma_semantic_b1_local_action_shape (source_actions!j)
        \<and> comma_semantic_b1_edge_of_continuation bindings (source_actions!j) =
          Some (comma_semantic_b1_node_actions value !
            (j mod comma_semantic_b1_node_period value)))
        [0..<source_period]"
    using row node cid source_id
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have source_base: "?source=comma_source_continuation_base ?source"
    using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
  have selected: "phase<source_period"
    using phase source_period by simp
  have selected_row:
      "comma_semantic_b1_local_action_shape (source_actions!phase)
        \<and> comma_semantic_b1_edge_of_continuation bindings (source_actions!phase) =
          Some (comma_semantic_b1_node_actions value !
            (phase mod comma_semantic_b1_node_period value))"
    using row_phases selected by (auto simp: list_all_iff)
  have action_at:
      "comma_source_continuation_action_at ?source phase=source_actions!phase"
    using source_id source_period source_base phase
    by (simp add: comma_source_continuation_action_at_def
      comma_source_continuation_id_def Let_def)
  show ?thesis using selected_row action_at by simp
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
  have facts:
      "comma_semantic_b1_local_action_shape
          (comma_source_continuation_action_at
            (comma_semantic_b1_binding_source binding) phase)
        \<and> comma_semantic_b1_edge_of_continuation bindings
          (comma_source_continuation_action_at
            (comma_semantic_b1_binding_source binding) phase) =
            Some (comma_semantic_b1_node_actions node !
              (phase mod comma_semantic_b1_node_period node))"
    by (rule comma_semantic_b1_binding_row_exact_from_valid[OF row cid node phase])
  have shape: "comma_semantic_b1_local_action_shape
      (comma_source_continuation_action_at
        (comma_semantic_b1_binding_source binding) phase)"
    using facts by simp
  have edge: "comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_at
        (comma_semantic_b1_binding_source binding) phase) =
      Some (comma_semantic_b1_node_actions node !
        (phase mod comma_semantic_b1_node_period node))"
    using facts by simp
  show thesis by (rule that[OF node shape edge])
qed

lemma comma_semantic_b1_graph_completed_node_lookup:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid bindings nodes"
    and binding: "binding \<in> set bindings"
    and cid: "comma_semantic_b1_binding_cid binding=target"
  shows "comma_semantic_b1_node_of nodes target\<noteq>None"
proof -
  obtain representative where representative:
      "representative\<in>set bindings"
      "comma_semantic_b1_binding_cid representative=target"
      "comma_semantic_b1_binding_row_valid bindings nodes representative"
      "comma_round_admitted (comma_semantic_b1_binding_source binding)"
      "comma_semantic_b1_binding_source binding=
        comma_source_continuation_base (comma_semantic_b1_binding_source binding)"
      "\<forall>clock. comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source binding)=
        comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source representative)"
    using comma_semantic_b1_graph_completed_binding_row[OF graph binding] cid
    by blast
  show ?thesis using representative
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
qed

lemma comma_semantic_b1_graph_apply_exact_from_local_row:
  assumes row:
      "comma_semantic_b1_binding_row_valid bindings nodes binding"
    and cid: "comma_semantic_b1_binding_cid binding=target"
  shows "comma_semantic_b1_graph_apply nodes target clock =
    comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_at
        (comma_semantic_b1_binding_source binding) clock)"
proof -
  let ?source = "comma_semantic_b1_binding_source binding"
  let ?P = "comma_decisive_sector_period ?source"
  have source_base: "?source=comma_source_continuation_base ?source"
    using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
  have admitted: "comma_round_admitted ?source"
    using row by (simp add: comma_semantic_b1_binding_row_valid_def Let_def)
  have source_period_positive: "0<?P"
    by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
  obtain node where node:
      "comma_semantic_b1_node_of nodes target=Some node"
    using row cid
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have node_period_positive:
      "0<comma_semantic_b1_node_period node"
    and node_period_divides:
      "comma_semantic_b1_node_period node dvd ?P"
    and node_actions_length:
      "length (comma_semantic_b1_node_actions node)=
        comma_semantic_b1_node_period node"
    using row node cid
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have phase: "clock mod ?P<?P"
    using source_period_positive by simp
  have row_action:
      "comma_semantic_b1_edge_of_continuation bindings
          (comma_source_continuation_action_at ?source (clock mod ?P)) =
        Some (comma_semantic_b1_node_actions node !
          ((clock mod ?P) mod comma_semantic_b1_node_period node))"
    using comma_semantic_b1_binding_row_exact_from_valid
      [OF row cid node phase]
    by simp
  have phase_mod:
      "(clock mod ?P) mod comma_semantic_b1_node_period node =
        clock mod comma_semantic_b1_node_period node"
    by (rule mod_mod_cancel[OF node_period_divides])
  have action_periodic:
      "comma_source_continuation_action_at ?source (clock mod ?P) =
        comma_source_continuation_action_at ?source clock"
    using source_base
    by (simp add: comma_source_continuation_action_at_def
      comma_source_continuation_id_def Let_def)
  show ?thesis
    using node row_action phase_mod action_periodic
      node_period_positive node_actions_length
    by (simp add: comma_semantic_b1_graph_apply_def
      comma_semantic_b1_node_of_def comma_semantic_b1_nodes_by_cid_def)
qed

lemma comma_semantic_b1_graph_completed_node_refs:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid bindings nodes"
    and node: "node\<in>set nodes"
  shows "comma_semantic_b1_edge_refs_valid nodes node"
  using graph node
  by (auto simp: comma_semantic_b1_graph_completed_valid_def)

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

lemma comma_semantic_b1_graph_apply_goto_decreases_from_core:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid bindings nodes"
    and cid: "comma_semantic_b1_binding_cid binding=parent"
    and local_row:
      "comma_semantic_b1_binding_row_valid bindings nodes binding"
    and applied:
      "comma_semantic_b1_graph_apply nodes parent clock =
        Some (Comma_Semantic_B1_Goto child)"
  shows "child<parent"
proof -
  obtain node where node:
      "comma_semantic_b1_node_of nodes parent=Some node"
    using local_row cid
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have period_positive:
      "0<comma_semantic_b1_node_period node"
    and actions_length:
      "length (comma_semantic_b1_node_actions node)=
        comma_semantic_b1_node_period node"
    using local_row node cid
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
      split: option.splits)
  have selected:
      "comma_semantic_b1_node_actions node !
        (clock mod comma_semantic_b1_node_period node) =
          Comma_Semantic_B1_Goto child"
    using applied node period_positive actions_length
    by (simp add: comma_semantic_b1_graph_apply_def
      comma_semantic_b1_node_of_def comma_semantic_b1_nodes_by_cid_def)
  have index:
      "clock mod comma_semantic_b1_node_period node <
        length (comma_semantic_b1_node_actions node)"
    using period_positive actions_length by simp
  have edge_member:
      "Comma_Semantic_B1_Goto child\<in>set (comma_semantic_b1_node_actions node)"
    using selected nth_mem[OF index] by simp
  have node_member: "node\<in>set nodes"
    by (rule comma_semantic_b1_node_of_member[OF node])
  have refs:
      "comma_semantic_b1_edge_refs_valid nodes node"
    by (rule comma_semantic_b1_graph_completed_node_refs[OF graph node_member])
  have well_formed:
      "case Comma_Semantic_B1_Goto child of
        Comma_Semantic_B1_Goto target \<Rightarrow>
          target < comma_semantic_b1_node_cid node
            \<and> comma_semantic_b1_node_of nodes target \<noteq> None
       | Comma_Semantic_B1_Live_Edge root \<Rightarrow> root<46
       | Comma_Semantic_B1_Stop_Edge j \<Rightarrow> j\<le>8
       | Comma_Semantic_B1_Invalid_Edge \<Rightarrow> True"
    using refs edge_member
    by (auto simp: comma_semantic_b1_edge_refs_valid_def)
  have node_key: "comma_semantic_b1_node_cid node=parent"
    by (rule comma_semantic_b1_node_of_key[OF node])
  show ?thesis using well_formed node_key by simp
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

lemma comma_semantic_b1_graph_apply_goto_decreases:
  assumes graph: "comma_semantic_b1_graph_valid bindings nodes"
    and binding: "binding \<in> set bindings"
    and cid: "comma_semantic_b1_binding_cid binding=parent"
    and applied: "comma_semantic_b1_graph_apply nodes parent clock=
      Some (Comma_Semantic_B1_Goto child)"
  shows "child<parent"
proof -
  have completed:
      "comma_semantic_b1_graph_completed_valid bindings nodes"
    by (rule comma_semantic_b1_graph_valid_implies_completed_valid[OF graph])
  have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
    by (rule comma_semantic_b1_graph_binding_row[OF graph binding])
  show ?thesis
    by (rule comma_semantic_b1_graph_apply_goto_decreases_from_core
      [OF completed cid row applied])
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
  have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
    by (rule comma_semantic_b1_graph_binding_row[OF graph binding])
  show ?thesis
    by (rule comma_semantic_b1_graph_apply_exact_from_local_row[OF row cid])
qed

ML \<open>Thm.consolidate [@{thm comma_semantic_b1_graph_apply_exact_local}]; Comma_Proof_Profile.report "B1 graph claim=apply-exact-local checked"\<close>

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

lemma comma_semantic_b1_graph_completed_apply_exact_packet:
  assumes local_row:
      "comma_semantic_b1_binding_row_valid bindings nodes binding"
    and base:
      "comma_semantic_b1_binding_source binding =
        comma_source_continuation_base source"
    and cid:
      "comma_semantic_b1_binding_cid binding=target"
    and admitted: "comma_round_admitted source"
  shows "comma_semantic_b1_graph_apply nodes target
      ((phase+comma_source_continuation_shift source) mod 924) =
    comma_semantic_b1_edge_of_continuation bindings
      (comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet phase source))"
proof -
  have local_apply:
      "comma_semantic_b1_graph_apply nodes target
          ((phase+comma_source_continuation_shift source) mod 924) =
        comma_semantic_b1_edge_of_continuation bindings
          (comma_source_continuation_action_at
            (comma_semantic_b1_binding_source binding)
            ((phase+comma_source_continuation_shift source) mod 924))"
    by (rule comma_semantic_b1_graph_apply_exact_from_local_row
      [OF local_row cid])
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
  have row: "comma_semantic_b1_binding_row_valid bindings nodes binding"
    by (rule comma_semantic_b1_graph_binding_row[OF graph binding])
  show ?thesis
    by (rule comma_semantic_b1_graph_completed_apply_exact_packet
      [OF row base cid admitted])
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_graph_valid_implies_completed_valid
    comma_semantic_b1_graph_binding_row comma_semantic_b1_binding_row_exact
    comma_semantic_b1_graph_apply_goto_decreases
    comma_semantic_b1_graph_apply_exact_packet};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Semantic B1 graph core claims depend on an oracle";
\<close>

end
