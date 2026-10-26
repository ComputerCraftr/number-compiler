theory Comma_Semantic_Graph_Instance
  imports Comma_Semantic_B1.Comma_Semantic_Graph_Congruence
    Comma_Semantic_B1.Comma_Semantic_B1_Entry_Near_Ports
    Comma_Semantic_B1.Comma_Near_Symbolic_Operator
    Comma_Semantic_B1.Comma_Semantic_Graph_Pointwise_Binding_Row
    Comma_Semantic_B1.Comma_Guarded_Source_Row_Transport
    Comma_Phase_Class_Rank_Source_Bridge
    Comma_Phase_Class_Rank_Local_Coverage
    Comma_Phase_Class_Rank_Linear_WF
    Comma_Phase_Class_Rank_Rotation
    Comma_Phase_Class_Rank_Source_Family_Adapter
    Comma_Phase_Class_Rank_Local_B32_Bridge
begin

text \<open>The graph instance discovers a finite source-selected graph from checked
local endpoint actions. Source bindings remain distinct from reusable nodes.
The publisher authenticates every binding against memoized exact local action
equations and checks the graph's edge, root, and successor invariants before
exporting the data constants. This certifies graph control and terminal
positions; physical elapsed Near/Entry weights remain occurrence data.\<close>

lemma comma_semantic_graph_root_coverage_from_list_all2:
  assumes paired:
    "list_all2 (\<lambda>source cid. \<exists>binding\<in>set bindings.
      comma_semantic_b1_binding_source binding=source \<and>
      comma_semantic_b1_binding_cid binding=cid)
      (map (\<lambda>root. Comma_Entry 1 0
        (comma_offset_representatives!root)) [0..<46]) cids"
  shows "\<forall>root<46. \<exists>binding\<in>set bindings.
    comma_semantic_b1_binding_source binding=
      Comma_Entry 1 0 (comma_offset_representatives!root)"
proof (intro allI impI)
  fix root :: nat
  assume root: "root<46"
  have index: "root<length
      (map (\<lambda>root. Comma_Entry 1 0
        (comma_offset_representatives!root)) [0..<46])"
    using root by simp
  have paired_at:
    "(\<exists>binding\<in>set bindings.
      comma_semantic_b1_binding_source binding=
        (map (\<lambda>index. Comma_Entry 1 0
          (comma_offset_representatives!index)) [0..<46])!root \<and>
      comma_semantic_b1_binding_cid binding=cids!root)"
    by (rule list_all2_nthD[OF paired index])
  show "\<exists>binding\<in>set bindings.
      comma_semantic_b1_binding_source binding=
        Comma_Entry 1 0 (comma_offset_representatives!root)"
    using paired_at root by (auto simp: nth_map_upt)
qed

lemma comma_semantic_graph_Ball_set_list_all:
  "Ball (set rows) predicate = list_all predicate rows"
  by (induction rows) auto

lemma comma_semantic_graph_binding_at_index:
  assumes index: "i < length pairs"
    and pair: "pairs!i = (source,cid)"
  shows "\<exists>binding\<in>set (map comma_semantic_b1_binding_from_pair pairs).
    comma_semantic_b1_binding_source binding=source \<and>
    comma_semantic_b1_binding_cid binding=cid"
proof -
  have pair_member: "pairs!i \<in> set pairs"
    by (rule nth_mem[OF index])
  have binding_member:
    "comma_semantic_b1_binding_from_pair (pairs!i) \<in>
      set (map comma_semantic_b1_binding_from_pair pairs)"
    using pair_member by (auto simp: set_map)
  show ?thesis using binding_member pair
    by (auto simp: comma_semantic_b1_binding_from_pair_def)
qed

lemma comma_semantic_graph_binding_sources_from_pairs:
  "map comma_semantic_b1_binding_source
      (map comma_semantic_b1_binding_from_pair pairs)=map fst pairs"
proof (induction pairs)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  then show ?case
    by (cases pair) (simp add: comma_semantic_b1_binding_from_pair_def)
qed

lemma comma_semantic_graph_binding_cid_at_index:
  assumes index: "i < length pairs"
    and pair: "pairs!i = (source,cid)"
  shows "\<exists>binding\<in>set (map comma_semantic_b1_binding_from_pair pairs).
    comma_semantic_b1_binding_cid binding=cid"
  using comma_semantic_graph_binding_at_index[OF index pair] by blast

lemma comma_semantic_graph_binding_lookup_at_index:
  assumes distinct: "distinct (map fst pairs)"
    and index: "i < length pairs"
    and pair: "pairs!i = (source,cid)"
  shows "comma_semantic_b1_binding_cid_of
    (map comma_semantic_b1_binding_from_pair pairs) source=Some cid"
proof -
  have pair_member: "(source,cid) \<in> set pairs"
    using nth_mem[OF index] pair by auto
  have ids_distinct:
      "distinct (map fst (comma_semantic_b1_binding_ids
        (map comma_semantic_b1_binding_from_pair pairs)))"
    using distinct
    by (simp add: comma_semantic_b1_binding_ids_def
      comma_semantic_b1_binding_from_pair_def comp_def)
  have ids_member:
      "(source,cid) \<in> set (comma_semantic_b1_binding_ids
        (map comma_semantic_b1_binding_from_pair pairs))"
    using pair_member
    by (auto simp: comma_semantic_b1_binding_ids_def
      comma_semantic_b1_binding_from_pair_def set_map comp_def)
  have lookup:
      "map_of (comma_semantic_b1_binding_ids
        (map comma_semantic_b1_binding_from_pair pairs)) source=Some cid"
    by (rule map_of_is_SomeI[OF ids_distinct ids_member])
  show ?thesis using lookup
    by (simp add: comma_semantic_b1_binding_cid_of_def)
qed

lemma comma_semantic_graph_node_id_at_index:
  assumes dense: "map comma_semantic_b1_node_cid nodes=ids"
    and index: "i < length nodes"
    and selected: "ids!i=i"
  shows "comma_semantic_b1_node_cid (nodes!i)=i"
  using dense index selected by (metis nth_map)

lemma comma_semantic_graph_node_lookup_at_index:
  assumes distinct: "distinct (map comma_semantic_b1_node_cid nodes)"
    and index: "i < length nodes"
    and selected: "comma_semantic_b1_node_cid (nodes!i)=i"
  shows "comma_semantic_b1_node_of nodes i=Some (nodes!i)"
proof -
  have key_distinct:
    "distinct (map fst (comma_semantic_b1_nodes_by_cid nodes))"
    using distinct
    by (simp add: comma_semantic_b1_nodes_by_cid_def comp_def)
  have node_member: "nodes!i \<in> set nodes"
    by (rule nth_mem[OF index])
  have pair_member:
    "(i,nodes!i) \<in> set (comma_semantic_b1_nodes_by_cid nodes)"
  proof -
    have image_member:
        "(\<lambda>candidate. (comma_semantic_b1_node_cid candidate,candidate))
          (nodes!i) \<in>
          (\<lambda>candidate. (comma_semantic_b1_node_cid candidate,candidate)) `
            set nodes"
      by (rule imageI[OF node_member])
    show ?thesis using image_member selected
      by (simp add: comma_semantic_b1_nodes_by_cid_def)
  qed
  have "map_of (comma_semantic_b1_nodes_by_cid nodes) i=Some (nodes!i)"
    by (rule map_of_is_SomeI[OF key_distinct pair_member])
  then show ?thesis
    by (simp add: comma_semantic_b1_node_of_def)
qed

lemma comma_semantic_graph_node_ids_dense_distinct:
  assumes dense: "map comma_semantic_b1_node_cid nodes = ids"
    and ids_distinct: "distinct ids"
  shows "distinct (map comma_semantic_b1_node_cid nodes)"
  using dense ids_distinct by simp

lemma comma_semantic_graph_completed_binding_from_lookup:
  assumes found: "comma_semantic_b1_binding_cid_of bindings representative = Some cid"
    and local_row:
      "comma_semantic_b1_binding_row_valid bindings nodes
        (comma_semantic_b1_binding_from_pair (representative,cid))"
    and admitted: "comma_round_admitted source"
    and normalized: "source = comma_source_continuation_base source"
    and completed:
      "\<forall>clock. comma_semantic_b1_round_output clock source =
        comma_semantic_b1_round_output clock representative"
    and forward:
      "source = representative \<or>
        (comma_decisive_sector_period source = 1 \<and>
          comma_source_continuation_action_at source 0 =
            Comma_Continuation_Goto representative 0 \<and>
          9 - comma_sector_number representative < 9 - comma_sector_number source)"
  shows "comma_semantic_b1_completed_binding_row_valid bindings nodes
    (comma_semantic_b1_binding_from_pair (source,cid))"
proof -
  obtain binding where member: "binding \<in> set bindings"
    and source: "comma_semantic_b1_binding_source binding = representative"
    and cid: "comma_semantic_b1_binding_cid binding = cid"
    using comma_semantic_b1_binding_cid_of_sound[OF found] by blast
  have exact_binding:
      "binding = comma_semantic_b1_binding_from_pair (representative,cid)"
    using source cid
    by (cases binding) (simp add: comma_semantic_b1_binding_from_pair_def)
  have member_exact:
      "comma_semantic_b1_binding_from_pair (representative,cid) \<in> set bindings"
    using member exact_binding by simp
  show ?thesis
    unfolding comma_semantic_b1_completed_binding_row_valid_def
  proof (rule bexI[OF _ member_exact])
    show "comma_semantic_b1_binding_cid
          (comma_semantic_b1_binding_from_pair (representative,cid)) =
        comma_semantic_b1_binding_cid
          (comma_semantic_b1_binding_from_pair (source,cid))
      \<and> comma_semantic_b1_binding_row_valid bindings nodes
        (comma_semantic_b1_binding_from_pair (representative,cid))
      \<and> comma_round_admitted (comma_semantic_b1_binding_source
        (comma_semantic_b1_binding_from_pair (source,cid)))
      \<and> comma_semantic_b1_binding_source
          (comma_semantic_b1_binding_from_pair (source,cid)) =
        comma_source_continuation_base (comma_semantic_b1_binding_source
          (comma_semantic_b1_binding_from_pair (source,cid)))
      \<and> (\<forall>clock. comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source
            (comma_semantic_b1_binding_from_pair (source,cid))) =
        comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source
            (comma_semantic_b1_binding_from_pair (representative,cid))))
      \<and> (comma_semantic_b1_binding_from_pair (source,cid) =
          comma_semantic_b1_binding_from_pair (representative,cid)
        \<or> (comma_decisive_sector_period (comma_semantic_b1_binding_source
              (comma_semantic_b1_binding_from_pair (source,cid))) = 1
          \<and> comma_source_continuation_action_at (comma_semantic_b1_binding_source
              (comma_semantic_b1_binding_from_pair (source,cid))) 0 =
            Comma_Continuation_Goto (comma_semantic_b1_binding_source
              (comma_semantic_b1_binding_from_pair (representative,cid))) 0
          \<and> 9 - comma_sector_number (comma_semantic_b1_binding_source
              (comma_semantic_b1_binding_from_pair (representative,cid))) <
            9 - comma_sector_number (comma_semantic_b1_binding_source
              (comma_semantic_b1_binding_from_pair (source,cid)))))"
      using local_row admitted normalized completed forward
      by (auto simp: comma_semantic_b1_binding_from_pair_def)
  qed
qed

lemma comma_semantic_graph_source_port_action_nth:
  fixes source :: comma_finite_position and phase :: nat
  assumes phase: "phase < comma_decisive_sector_period
    (comma_source_continuation_base source)"
  shows "comma_semantic_b1_source_port_action source phase =
    comma_semantic_b1_source_port_actions source ! phase"
  using phase
  by (simp add: comma_semantic_b1_source_port_actions_def nth_map nth_upt)

lemma comma_semantic_graph_forall_less_iff_list_all:
  fixes P :: nat and F :: "nat \<Rightarrow> bool"
  shows "(\<forall>phase<P. F phase) \<longleftrightarrow> list_all F [0..<P]"
  by (auto simp: list_all_iff)

ML \<open>Thm.consolidate [@{thm comma_semantic_graph_completed_binding_from_lookup}]\<close>

ML_file "../comma_entry_arithmetic/selected_list_conversion.ML"
ML_file "semantic_source_ports.ML"
ML_file "semantic_near_operator_fixture.ML"
ML_file "semantic_graph_publication.ML"
ML_file "semantic_graph_constructor.ML"

local_setup \<open>fn lthy =>
  let
    (* Exercise Near action-class reuse in a disposable engine.  Test-only
       occurrences must not become rows or bindings in the graph that is
       subsequently published. *)
    val near_fixture_engine = Comma_Semantic_Graph_Constructor.make_audit lthy
    val near9 = @{term "Comma_Near 1 0 9"}
    val near10 = @{term "Comma_Near 1 0 10"}
    val near9_cid = #compile near_fixture_engine near9
    val near9_class = #source_class near_fixture_engine near9
    val before_near10 = #work near_fixture_engine ()
    val near10_cid = #compile near_fixture_engine near10
    val near10_class = #source_class near_fixture_engine near10
    val after_near10 = #work near_fixture_engine ()
    val _ = #validate_selection near_fixture_engine near10_class
    val _ = if near9_cid = near10_cid andalso
        Term.aconv (#action_key near9_class, #action_key near10_class) andalso
        Option.map (fn term => #2 (HOLogic.dest_number term))
          (#selected_steps near9_class) = SOME 0 andalso
        Option.map (fn term => #2 (HOLogic.dest_number term))
          (#selected_steps near10_class) = SOME 1 andalso
        #transition_evaluations before_near10 =
          #transition_evaluations after_near10 andalso
        #near_action_class_reuses after_near10 =
          #near_action_class_reuses before_near10 + 1
      then () else error
        "Equivalent Near action rebuilt a transition or lost its occurrence clock"
    val engine = Comma_Semantic_Graph_Constructor.make_audit lthy
    (* Admit the representative first. Its exact completed alias must reuse
       the CID without asking the full-word producer to run again. *)
    val representative = @{term "Comma_Entry 4 0 7"}
    val alias_source = @{term "Comma_Entry 3 0 1"}
    val representative_cid = #compile engine representative
    val before_alias = #work engine ()
    val alias_cid = #compile engine alias_source
    val after_alias = #work engine ()
    val _ = if alias_cid = representative_cid andalso
        #transition_evaluations before_alias =
          #transition_evaluations after_alias andalso
        #completed_aliases after_alias = #completed_aliases before_alias + 1
      then () else error
        "Completed source alias rediscovered a transition row or changed its representative"
    val _ = map (#root engine) (0 upto 45)
    val initial_sources = #initial_sources engine
    val initial_seed_cids = map (#compile engine) initial_sources
    val current_bindings = #bindings engine ()
    val seed_sources_published = List.all
      (fn source => List.exists
        (fn ({source=bound, ...}: Comma_Semantic_Graph_Constructor.binding) =>
          bound aconv source)
        current_bindings)
      initial_sources
    val _ = if length initial_seed_cids = 16 andalso seed_sources_published then ()
      else error "The sixteen registered initial charts were not compiled into the graph"
    val _ = Comma_Fast_Kernel.report (#stats engine ())
    val _ = if #completed_aliases (#work engine ()) > 0 then ()
      else error "The concrete source graph did not consume any completed-action transports"
    val (checked_lthy, _, _, _) = #publish engine lthy
  in checked_lthy
  end
\<close>

ML \<open>
  val checked = @{thms comma_semantic_graph_valid_checked
    comma_semantic_graph_root_binding_exact comma_semantic_graph_node_ids_dense
    comma_semantic_graph_initial_source_binding_exact};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Published semantic continuation graph" checked;
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Published graph uses the guarded source-port refinement"
    ["Comma_Semantic_B1_Guarded_Port_Action.comma_semantic_b1_source_id_ports"]
    @{thms comma_semantic_graph_valid_checked};
\<close>

end
