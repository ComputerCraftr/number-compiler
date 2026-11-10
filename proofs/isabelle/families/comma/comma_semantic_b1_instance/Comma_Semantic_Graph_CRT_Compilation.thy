theory Comma_Semantic_Graph_CRT_Compilation
  imports Comma_Semantic_Graph_Stop_Transport
    Comma_Semantic_B1.Comma_Weighted_CRT_Data
begin

text \<open>
Compile a checked continuation graph directly to the weighted CRT decision
diagram.  The diagram carries only the control result and its additive
complete-decade weight.  A single graph edge contributes no complete-decade
height: a Live edge advances to the next root, while a later Stop records the
number of complete transitions in the chronological composition.
\<close>

datatype comma_semantic_b1_crt_control =
    Comma_Semantic_B1_CRT_Continue nat
  | Comma_Semantic_B1_CRT_Stop nat
  | Comma_Semantic_B1_CRT_Invalid

type_synonym comma_semantic_b1_crt_dag =
  "comma_semantic_b1_crt_control comma_semantic_weighted_crt_dag"

definition comma_semantic_b1_crt_leaf ::
    "comma_semantic_b1_crt_control \<Rightarrow> comma_semantic_b1_crt_dag" where
  "comma_semantic_b1_crt_leaf control = Comma_Weighted_CRT_Leaf control"

definition comma_semantic_b1_crt_invalid_action ::
    "nat \<times> comma_semantic_b1_crt_dag" where
  "comma_semantic_b1_crt_invalid_action =
    (0, comma_semantic_b1_crt_leaf Comma_Semantic_B1_CRT_Invalid)"

lemma comma_semantic_b1_crt_leaf_apply:
  "comma_weighted_crt_apply
      (0,comma_semantic_b1_crt_leaf control) phase =
    Some (control,0)"
  by (simp add: comma_weighted_crt_apply_def
      comma_semantic_b1_crt_leaf_def)

primrec comma_semantic_b1_crt_compile_node_fuel ::
    "nat \<Rightarrow> (comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow>
      nat \<times> comma_semantic_b1_crt_dag)" where
  "comma_semantic_b1_crt_compile_node_fuel 0 =
    (\<lambda>nodes cid. comma_semantic_b1_crt_invalid_action)"
| "comma_semantic_b1_crt_compile_node_fuel (Suc fuel) =
    (\<lambda>nodes cid.
      case comma_semantic_b1_node_of nodes cid of
        None \<Rightarrow> comma_semantic_b1_crt_invalid_action
      | Some node \<Rightarrow>
          (let period=comma_semantic_b1_node_period node;
               actions=comma_semantic_b1_node_actions node
           in if 0<period \<and> period dvd 924 \<and> length actions=period then
                (case comma_weighted_crt_selector period actions of
                   None \<Rightarrow> comma_semantic_b1_crt_invalid_action
                 | Some selector \<Rightarrow>
                     comma_weighted_crt_bind selector
                       (\<lambda>edge.
                         case edge of
                           Comma_Semantic_B1_Goto child \<Rightarrow>
                             if child<cid then
                               comma_semantic_b1_crt_compile_node_fuel
                                 fuel nodes child
                             else comma_semantic_b1_crt_invalid_action
                         | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
                             (0, comma_semantic_b1_crt_leaf
                               (Comma_Semantic_B1_CRT_Continue root))
                         | Comma_Semantic_B1_Stop_Edge J \<Rightarrow>
                             (0, comma_semantic_b1_crt_leaf
                               (Comma_Semantic_B1_CRT_Stop J))
                         | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
                             comma_semantic_b1_crt_invalid_action))
              else comma_semantic_b1_crt_invalid_action))"

definition comma_semantic_b1_crt_compile_node ::
    "comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow>
      nat \<times> comma_semantic_b1_crt_dag" where
  "comma_semantic_b1_crt_compile_node nodes cid =
    comma_semantic_b1_crt_compile_node_fuel (Suc cid) nodes cid"

text \<open>
One postorder compiler step takes already-compiled child actions.  It does not
recursively substitute each child's full source compiler expression into the
parent.  The child callback is only observed at the selected edge for a phase.
\<close>

definition comma_semantic_b1_crt_compile_node_from_children ::
    "comma_semantic_b1_node list \<Rightarrow> nat \<Rightarrow>
      (nat \<Rightarrow> nat \<times> comma_semantic_b1_crt_dag) \<Rightarrow>
      nat \<times> comma_semantic_b1_crt_dag" where
  "comma_semantic_b1_crt_compile_node_from_children nodes cid child_action =
    (case comma_semantic_b1_node_of nodes cid of
       None \<Rightarrow> comma_semantic_b1_crt_invalid_action
     | Some node \<Rightarrow>
         (let period=comma_semantic_b1_node_period node;
              actions=comma_semantic_b1_node_actions node
          in if 0<period \<and> period dvd 924 \<and> length actions=period then
               comma_weighted_crt_bind
                 (comma_weighted_crt_selector_aux [0,1,2,3] period 0 actions)
                 (\<lambda>edge.
                   case edge of
                     Comma_Semantic_B1_Goto child \<Rightarrow>
                       if child<cid then child_action child
                       else comma_semantic_b1_crt_invalid_action
                   | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
                       (0,comma_semantic_b1_crt_leaf
                         (Comma_Semantic_B1_CRT_Continue root))
                   | Comma_Semantic_B1_Stop_Edge J \<Rightarrow>
                       (0,comma_semantic_b1_crt_leaf
                         (Comma_Semantic_B1_CRT_Stop J))
                   | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
                       comma_semantic_b1_crt_invalid_action)
             else comma_semantic_b1_crt_invalid_action))"

lemma comma_weighted_crt_bind_extensional:
  assumes callback_equal: "\<And>control. next control = next' control"
  shows "comma_weighted_crt_bind tree next =
    comma_weighted_crt_bind tree next'"
proof (induction tree)
  case (Comma_Weighted_CRT_Leaf control)
  show ?case
    by (simp only: comma_weighted_crt_bind.simps; rule callback_equal)
next
  case (Comma_Weighted_CRT_Branch axis rows)
  have child_equal:
    "\<And>weight child. (weight,child)\<in>set rows \<Longrightarrow>
      comma_weighted_crt_bind child next =
        comma_weighted_crt_bind child next'"
  proof -
    fix weight child
    assume member: "(weight,child)\<in>set rows"
    have child_member: "child\<in>Basic_BNFs.snds (weight,child)"
      by (simp add: prod_set_defs)
    show "comma_weighted_crt_bind child next =
        comma_weighted_crt_bind child next'"
      by (rule Comma_Weighted_CRT_Branch.IH[OF member child_member])
  qed
  have mapped_equal:
    "map (\<lambda>(weight,child).
        (weight+fst (comma_weighted_crt_bind child next),
          snd (comma_weighted_crt_bind child next))) rows =
     map (\<lambda>(weight,child).
        (weight+fst (comma_weighted_crt_bind child next'),
          snd (comma_weighted_crt_bind child next'))) rows"
  proof (rule map_cong)
    show "rows=rows" by simp
  next
    fix edge
    assume edge: "edge\<in>set rows"
    obtain weight child where edge_pair: "edge=(weight,child)"
      by (cases edge)
    have equal:
      "comma_weighted_crt_bind child next =
        comma_weighted_crt_bind child next'"
      using child_equal[of weight child] edge edge_pair by simp
    show "(case edge of (weight, child) \<Rightarrow>
          (weight + fst (comma_weighted_crt_bind child next),
           snd (comma_weighted_crt_bind child next))) =
        (case edge of (weight, child) \<Rightarrow>
          (weight + fst (comma_weighted_crt_bind child next'),
           snd (comma_weighted_crt_bind child next')))"
      using edge_pair equal by simp
  qed
  show ?case using mapped_equal by simp
qed

lemma comma_semantic_b1_crt_compile_fuel_canonical:
  fixes nodes :: "comma_semantic_b1_node list"
  assumes fuel: "cid<fuel_count"
  shows "comma_semantic_b1_crt_compile_node_fuel fuel_count nodes cid =
    comma_semantic_b1_crt_compile_node_fuel (Suc cid) nodes cid"
  using fuel
proof (induction cid arbitrary: fuel_count rule: less_induct)
  case (less cid)
  obtain remaining where fuel_suc: "fuel_count=Suc remaining"
    using less.prems by (cases fuel_count) auto
  have cid_below_remaining: "cid\<le>remaining"
    using less.prems fuel_suc by simp
  let ?next = "\<lambda>fuel edge. case edge of
      Comma_Semantic_B1_Goto child \<Rightarrow>
        (if child<cid then
          comma_semantic_b1_crt_compile_node_fuel fuel nodes child
         else comma_semantic_b1_crt_invalid_action)
    | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
        (0,comma_semantic_b1_crt_leaf
          (Comma_Semantic_B1_CRT_Continue root))
    | Comma_Semantic_B1_Stop_Edge J \<Rightarrow>
        (0,comma_semantic_b1_crt_leaf (Comma_Semantic_B1_CRT_Stop J))
    | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
        comma_semantic_b1_crt_invalid_action"
  have callbacks:
    "\<And>edge. ?next remaining edge = ?next cid edge"
  proof -
    fix edge
    show "?next remaining edge = ?next cid edge"
    proof (cases edge)
      case (Comma_Semantic_B1_Goto child)
      show ?thesis
      proof (cases "child<cid")
        case True
        have child_below_remaining: "child<remaining"
          using True cid_below_remaining by arith
        have left_canonical:
          "comma_semantic_b1_crt_compile_node_fuel remaining nodes child =
            comma_semantic_b1_crt_compile_node_fuel (Suc child) nodes child"
          by (rule less.IH[OF True child_below_remaining])
        have right_canonical:
          "comma_semantic_b1_crt_compile_node_fuel cid nodes child =
            comma_semantic_b1_crt_compile_node_fuel (Suc child) nodes child"
          by (rule less.IH[OF True True])
        show ?thesis using Comma_Semantic_B1_Goto True
          left_canonical right_canonical by simp
      next
        case False
        then show ?thesis using Comma_Semantic_B1_Goto by simp
      qed
    qed (simp_all)
  qed
  have callback_function_equal: "?next remaining = ?next cid"
    by (rule ext) (rule callbacks)
  show ?case
  proof (cases "comma_semantic_b1_node_of nodes cid")
    case None
    then show ?thesis
      by (simp add: fuel_suc
        comma_semantic_b1_crt_compile_node_fuel.simps)
  next
    case (Some node)
    then show ?thesis
      by (simp only: fuel_suc
        comma_semantic_b1_crt_compile_node_fuel.simps Some option.case
        Let_def callback_function_equal)
  qed
qed

lemma comma_semantic_b1_crt_compile_fuel_stable:
  fixes nodes :: "comma_semantic_b1_node list"
  assumes lower: "cid<fuel_a"
    and ordered: "fuel_a\<le>fuel_b"
  shows "comma_semantic_b1_crt_compile_node_fuel fuel_a nodes cid =
    comma_semantic_b1_crt_compile_node_fuel fuel_b nodes cid"
proof -
  have upper: "cid<fuel_b" using lower ordered by arith
  have left:
    "comma_semantic_b1_crt_compile_node_fuel fuel_a nodes cid =
      comma_semantic_b1_crt_compile_node_fuel (Suc cid) nodes cid"
    by (rule comma_semantic_b1_crt_compile_fuel_canonical[OF lower])
  have right:
    "comma_semantic_b1_crt_compile_node_fuel fuel_b nodes cid =
      comma_semantic_b1_crt_compile_node_fuel (Suc cid) nodes cid"
    by (rule comma_semantic_b1_crt_compile_fuel_canonical[OF upper])
  show ?thesis using left right by simp
qed

lemma comma_semantic_b1_crt_compile_node_step:
  fixes nodes :: "comma_semantic_b1_node list"
    and node :: comma_semantic_b1_node
  assumes lookup: "comma_semantic_b1_node_of nodes cid = Some node"
    and positive: "0 < comma_semantic_b1_node_period node"
    and divides: "comma_semantic_b1_node_period node dvd 924"
    and row_length:
      "length (comma_semantic_b1_node_actions node) =
        comma_semantic_b1_node_period node"
  shows "comma_semantic_b1_crt_compile_node nodes cid =
    comma_weighted_crt_bind
      (comma_weighted_crt_selector_aux [0,1,2,3]
        (comma_semantic_b1_node_period node) 0
        (comma_semantic_b1_node_actions node))
      (\<lambda>edge. case edge of
        Comma_Semantic_B1_Goto child \<Rightarrow>
          if child < cid then
            comma_semantic_b1_crt_compile_node nodes child
          else comma_semantic_b1_crt_invalid_action
      | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
          (0, comma_semantic_b1_crt_leaf
            (Comma_Semantic_B1_CRT_Continue root))
      | Comma_Semantic_B1_Stop_Edge J \<Rightarrow>
          (0, comma_semantic_b1_crt_leaf (Comma_Semantic_B1_CRT_Stop J))
      | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
          comma_semantic_b1_crt_invalid_action)"
proof -
  let ?period = "comma_semantic_b1_node_period node"
  let ?actions = "comma_semantic_b1_node_actions node"
  let ?selector =
    "comma_weighted_crt_selector_aux [0,1,2,3] ?period 0 ?actions"
  let ?raw_next = "\<lambda>edge. case edge of
      Comma_Semantic_B1_Goto child \<Rightarrow>
        if child < cid then
          comma_semantic_b1_crt_compile_node_fuel cid nodes child
        else comma_semantic_b1_crt_invalid_action
    | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
        (0, comma_semantic_b1_crt_leaf
          (Comma_Semantic_B1_CRT_Continue root))
    | Comma_Semantic_B1_Stop_Edge J \<Rightarrow>
        (0, comma_semantic_b1_crt_leaf (Comma_Semantic_B1_CRT_Stop J))
    | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
        comma_semantic_b1_crt_invalid_action"
  let ?next = "\<lambda>edge. case edge of
      Comma_Semantic_B1_Goto child \<Rightarrow>
        if child < cid then
          comma_semantic_b1_crt_compile_node nodes child
        else comma_semantic_b1_crt_invalid_action
    | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
        (0, comma_semantic_b1_crt_leaf
          (Comma_Semantic_B1_CRT_Continue root))
    | Comma_Semantic_B1_Stop_Edge J \<Rightarrow>
        (0, comma_semantic_b1_crt_leaf (Comma_Semantic_B1_CRT_Stop J))
    | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
        comma_semantic_b1_crt_invalid_action"
  have selector:
      "comma_weighted_crt_selector ?period ?actions = Some ?selector"
    by (rule comma_weighted_crt_selector_exact(1)[OF positive divides row_length])
  have raw:
      "comma_semantic_b1_crt_compile_node nodes cid =
        comma_weighted_crt_bind ?selector ?raw_next"
    unfolding comma_semantic_b1_crt_compile_node_def
    using lookup positive divides row_length selector
    by (simp add: comma_semantic_b1_crt_invalid_action_def
        comma_semantic_b1_crt_leaf_def Let_def)
  have callback: "\<And>edge. ?raw_next edge = ?next edge"
  proof -
    fix edge
    show "?raw_next edge = ?next edge"
    proof (cases edge)
      case (Comma_Semantic_B1_Goto child)
      show ?thesis
      proof (cases "child < cid")
        case True
        have canonical:
          "comma_semantic_b1_crt_compile_node_fuel cid nodes child =
            comma_semantic_b1_crt_compile_node_fuel (Suc child) nodes child"
          by (rule comma_semantic_b1_crt_compile_fuel_canonical[OF True])
        show ?thesis using canonical True Comma_Semantic_B1_Goto
          by (simp add: comma_semantic_b1_crt_compile_node_def)
      next
        case False
        then show ?thesis using Comma_Semantic_B1_Goto by simp
      qed
    qed (simp_all)
  qed
  have bind_equal:
    "comma_weighted_crt_bind ?selector ?raw_next =
      comma_weighted_crt_bind ?selector ?next"
    by (rule comma_weighted_crt_bind_extensional[OF callback])
  show ?thesis using raw bind_equal by simp
qed

fun comma_semantic_b1_crt_graph_result ::
    "comma_semantic_b1_result \<Rightarrow>
      comma_semantic_b1_crt_control \<times> nat" where
  "comma_semantic_b1_crt_graph_result (Comma_Semantic_B1_Live root) =
    (Comma_Semantic_B1_CRT_Continue root,0)"
| "comma_semantic_b1_crt_graph_result (Comma_Semantic_B1_Stop J) =
    (Comma_Semantic_B1_CRT_Stop J,0)"
| "comma_semantic_b1_crt_graph_result Comma_Semantic_B1_Invalid =
    (Comma_Semantic_B1_CRT_Invalid,0)"

lemma comma_semantic_b1_crt_compile_node_fuel_refines_graph_eval:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid bindings nodes"
    and lookup: "comma_semantic_b1_node_of nodes cid=Some node"
    and fuel: "cid<fuel_count"
  shows "comma_weighted_crt_apply
      (comma_semantic_b1_crt_compile_node_fuel fuel_count nodes cid) phase =
    map_option comma_semantic_b1_crt_graph_result
      (comma_semantic_b1_graph_eval nodes cid phase)"
  using fuel lookup
proof (induction fuel_count arbitrary: cid node)
  case 0
  then show ?case by simp
next
  case (Suc fuel_count)
  have cid_bound: "cid<Suc fuel_count" using Suc.prems by blast
  have node_member: "node\<in>set nodes"
    by (rule comma_semantic_b1_node_of_member[OF Suc.prems(2)])
  have node_key: "comma_semantic_b1_node_cid node=cid"
    by (rule comma_semantic_b1_node_of_key[OF Suc.prems(2)])
  have owner_exists:
      "\<exists>binding\<in>set bindings.
        comma_semantic_b1_binding_cid binding=
          comma_semantic_b1_node_cid node"
    using graph node_member
    by (auto simp: comma_semantic_b1_graph_completed_valid_def)
  then obtain binding where binding:
      "binding\<in>set bindings"
      "comma_semantic_b1_binding_cid binding=cid"
    using node_key by blast
  obtain representative where representative:
      "representative\<in>set bindings"
      "comma_semantic_b1_binding_cid representative=
        comma_semantic_b1_binding_cid binding"
      "comma_semantic_b1_binding_row_valid bindings nodes representative"
      "comma_round_admitted (comma_semantic_b1_binding_source binding)"
      "comma_semantic_b1_binding_source binding=
        comma_source_continuation_base (comma_semantic_b1_binding_source binding)"
      "\<forall>clock. comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source binding)=
        comma_semantic_b1_round_output clock
          (comma_semantic_b1_binding_source representative)"
    by (rule comma_semantic_b1_graph_completed_binding_row[OF graph binding(1)])
  have binding_row:
      "comma_semantic_b1_binding_row_valid bindings nodes representative"
    by (rule representative(3))
  have representative_cid:
      "comma_semantic_b1_binding_cid representative=cid"
    using representative(2) binding(2) by simp
  let ?source = "comma_semantic_b1_binding_source representative"
  let ?P = "comma_decisive_sector_period ?source"
  let ?period = "comma_semantic_b1_node_period node"
  let ?actions = "comma_semantic_b1_node_actions node"
  have node_lookup:
      "comma_semantic_b1_node_of nodes cid=Some node"
    using Suc.prems(2) by simp
  have source_admitted: "comma_round_admitted ?source"
    using binding_row
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def)
  have source_period: "0<?P" "?P dvd 924"
    by (rule comma_decisive_sector_period_admitted[OF source_admitted])+
  have node_facts:
      "0<?period"
      "?period dvd ?P"
      "length ?actions=?period"
    using binding_row representative_cid node_lookup
    by (auto simp: comma_semantic_b1_binding_row_valid_def Let_def
        split: option.splits)
  have period_facts:
      "0<?period" "?period dvd 924" "length ?actions=?period"
    using node_facts source_period by (auto intro: dvd_trans)
  have node_refs: "comma_semantic_b1_edge_refs_valid nodes node"
    by (rule comma_semantic_b1_graph_completed_node_refs[OF graph node_member])
  have node_key: "comma_semantic_b1_node_cid node=cid"
    by (rule comma_semantic_b1_node_of_key[OF node_lookup])
  have selector_exact:
      "comma_weighted_crt_selector ?period ?actions =
        Some (comma_weighted_crt_selector_aux [0,1,2,3] ?period 0 ?actions)"
    by (rule comma_weighted_crt_selector_exact(1)
      [OF period_facts(1,2) period_facts(3)])
  have selector_eval:
      "comma_weighted_crt_eval
        (comma_weighted_crt_selector_aux [0,1,2,3] ?period 0 ?actions) phase =
        Some (?actions!(phase mod ?period),0)"
    by (rule comma_weighted_crt_selector_exact(2)
      [OF period_facts(1,2) period_facts(3)])
  have compiled:
      "comma_semantic_b1_crt_compile_node_fuel (Suc fuel_count) nodes cid =
        comma_weighted_crt_bind
          (comma_weighted_crt_selector_aux [0,1,2,3] ?period 0 ?actions)
          (\<lambda>edge.
            case edge of
              Comma_Semantic_B1_Goto child \<Rightarrow>
                if child<cid then
                  comma_semantic_b1_crt_compile_node_fuel fuel_count nodes child
                else comma_semantic_b1_crt_invalid_action
            | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
                (0,comma_semantic_b1_crt_leaf
                  (Comma_Semantic_B1_CRT_Continue root))
            | Comma_Semantic_B1_Stop_Edge J \<Rightarrow>
                (0,comma_semantic_b1_crt_leaf
                  (Comma_Semantic_B1_CRT_Stop J))
            | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
                comma_semantic_b1_crt_invalid_action)"
    using period_facts selector_exact Suc.prems(2)
    by (simp only: comma_semantic_b1_crt_compile_node_fuel.simps
      Suc.prems(2) period_facts(1,2,3) selector_exact option.case Let_def
      if_True HOL.simp_thms)
  let ?next = "\<lambda>edge.
    case edge of
      Comma_Semantic_B1_Goto child \<Rightarrow>
        if child<cid then
          comma_semantic_b1_crt_compile_node_fuel fuel_count nodes child
        else comma_semantic_b1_crt_invalid_action
    | Comma_Semantic_B1_Live_Edge root \<Rightarrow>
        (0,comma_semantic_b1_crt_leaf
          (Comma_Semantic_B1_CRT_Continue root))
    | Comma_Semantic_B1_Stop_Edge J \<Rightarrow>
        (0,comma_semantic_b1_crt_leaf
          (Comma_Semantic_B1_CRT_Stop J))
    | Comma_Semantic_B1_Invalid_Edge \<Rightarrow>
        comma_semantic_b1_crt_invalid_action"
  have apply_selected:
      "comma_weighted_crt_apply
        (comma_semantic_b1_crt_compile_node_fuel (Suc fuel_count) nodes cid) phase =
       comma_weighted_crt_apply
        (?next (?actions!(phase mod ?period))) phase"
    using compiled selector_eval
    by (simp only: compiled comma_weighted_crt_bind_exact selector_eval
      Option.bind_lunit prod.case case_prod_Pair add_0_left option.map_id)
  have graph_apply:
      "comma_semantic_b1_graph_apply nodes cid phase =
        Some (?actions!(phase mod ?period))"
    using binding_row binding(2) node_lookup period_facts
    by (auto simp: comma_semantic_b1_graph_apply_def
        comma_semantic_b1_node_of_def comma_semantic_b1_nodes_by_cid_def
        comma_semantic_b1_binding_row_valid_def Let_def split: option.splits)
  have edge_member:
      "?actions!(phase mod ?period)\<in>set (comma_semantic_b1_node_actions node)"
    using period_facts(1,3) by (simp add: nth_mem)
  show ?case
  proof (cases "?actions!(phase mod ?period)")
    case (Comma_Semantic_B1_Goto child)
    have graph_apply_goto:
      "comma_semantic_b1_graph_apply nodes cid phase =
        Some (Comma_Semantic_B1_Goto child)"
      using graph_apply Comma_Semantic_B1_Goto by simp
    have child_less: "child<cid"
      using node_refs node_key edge_member Comma_Semantic_B1_Goto
      by (auto simp: comma_semantic_b1_edge_refs_valid_def)
    have child_lookup: "comma_semantic_b1_node_of nodes child\<noteq>None"
      using node_refs edge_member Comma_Semantic_B1_Goto
      by (auto simp: comma_semantic_b1_edge_refs_valid_def)
    obtain child_node where child_node:
        "comma_semantic_b1_node_of nodes child=Some child_node"
      using child_lookup by (cases "comma_semantic_b1_node_of nodes child") auto
    have child_bound: "child<fuel_count"
      using child_less cid_bound by arith
    have child_exact:
      "comma_weighted_crt_apply
          (comma_semantic_b1_crt_compile_node_fuel fuel_count nodes child) phase =
        map_option comma_semantic_b1_crt_graph_result
          (comma_semantic_b1_graph_eval nodes child phase)"
      by (rule Suc.IH[OF child_bound child_node])
    have graph_step:
      "comma_semantic_b1_graph_eval nodes cid phase =
        comma_semantic_b1_graph_eval nodes child phase"
      by (rule comma_semantic_b1_graph_eval_apply_goto
        [OF graph_apply_goto child_less])
    show ?thesis
      using apply_selected child_exact graph_step Comma_Semantic_B1_Goto
      by (simp only: apply_selected Comma_Semantic_B1_Goto
        comma_semantic_b1_edge.case child_less if_True child_exact graph_step)
  next
    case (Comma_Semantic_B1_Live_Edge root)
    have graph_apply_live:
      "comma_semantic_b1_graph_apply nodes cid phase =
        Some (Comma_Semantic_B1_Live_Edge root)"
      using graph_apply Comma_Semantic_B1_Live_Edge by simp
    have root_bound: "root<46"
      using node_refs edge_member Comma_Semantic_B1_Live_Edge
      by (auto simp: comma_semantic_b1_edge_refs_valid_def)
    have graph_step:
      "comma_semantic_b1_graph_eval nodes cid phase = Some (Comma_Semantic_B1_Live root)"
      by (rule comma_semantic_b1_graph_eval_apply_live[OF graph_apply_live root_bound])
    show ?thesis
      using apply_selected graph_step Comma_Semantic_B1_Live_Edge
      by (simp only: apply_selected Comma_Semantic_B1_Live_Edge
        comma_semantic_b1_edge.case comma_semantic_b1_crt_leaf_apply
        graph_step comma_semantic_b1_crt_graph_result.simps option.map)
  next
    case (Comma_Semantic_B1_Stop_Edge J)
    have graph_apply_stop:
      "comma_semantic_b1_graph_apply nodes cid phase =
        Some (Comma_Semantic_B1_Stop_Edge J)"
      using graph_apply Comma_Semantic_B1_Stop_Edge by simp
    have J_bound: "J\<le>8"
      using node_refs edge_member Comma_Semantic_B1_Stop_Edge
      by (auto simp: comma_semantic_b1_edge_refs_valid_def)
    have graph_step:
      "comma_semantic_b1_graph_eval nodes cid phase = Some (Comma_Semantic_B1_Stop J)"
      by (rule comma_semantic_b1_graph_eval_apply_stop[OF graph_apply_stop J_bound])
    show ?thesis
      using apply_selected graph_step Comma_Semantic_B1_Stop_Edge
      by (simp only: apply_selected Comma_Semantic_B1_Stop_Edge
        comma_semantic_b1_edge.case comma_semantic_b1_crt_leaf_apply
        graph_step comma_semantic_b1_crt_graph_result.simps option.map)
  next
    case Comma_Semantic_B1_Invalid_Edge
    have graph_apply_invalid:
      "comma_semantic_b1_graph_apply nodes cid phase =
        Some Comma_Semantic_B1_Invalid_Edge"
      using graph_apply Comma_Semantic_B1_Invalid_Edge by simp
    have graph_step:
      "comma_semantic_b1_graph_eval nodes cid phase = Some Comma_Semantic_B1_Invalid"
      by (rule comma_semantic_b1_graph_eval_apply_invalid
        [OF graph_apply_invalid])
    show ?thesis
      using apply_selected graph_step Comma_Semantic_B1_Invalid_Edge
      by (simp only: apply_selected Comma_Semantic_B1_Invalid_Edge
        comma_semantic_b1_edge.case comma_semantic_b1_crt_invalid_action_def
        comma_semantic_b1_crt_leaf_apply graph_step
        comma_semantic_b1_crt_graph_result.simps option.map)
  qed
qed

lemma comma_semantic_b1_crt_compile_refines_graph_eval:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid bindings nodes"
    and lookup: "comma_semantic_b1_node_of nodes cid=Some node"
  shows "comma_weighted_crt_apply
      (comma_semantic_b1_crt_compile_node nodes cid) phase =
    map_option comma_semantic_b1_crt_graph_result
      (comma_semantic_b1_graph_eval nodes cid phase)"
proof -
  have bound: "cid<Suc cid" by simp
  show ?thesis
    unfolding comma_semantic_b1_crt_compile_node_def
    by (rule comma_semantic_b1_crt_compile_node_fuel_refines_graph_eval
      [OF graph lookup bound])
qed

lemma comma_semantic_b1_crt_compile_initial_source_exact:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid
        comma_semantic_graph_bindings comma_semantic_graph_nodes"
    and index: "index<length comma_semantic_future_initial_sources"
  shows "comma_weighted_crt_apply
      (comma_semantic_b1_crt_compile_node comma_semantic_graph_nodes
        (comma_semantic_graph_initial_source_ids!index)) phase =
    map_option comma_semantic_b1_crt_graph_result
      (comma_semantic_b1_graph_eval comma_semantic_graph_nodes
        (comma_semantic_graph_initial_source_ids!index) phase)"
proof -
  have source_lookup:
      "comma_semantic_b1_binding_cid_of comma_semantic_graph_bindings
        (comma_semantic_future_initial_sources!index) =
          Some (comma_semantic_graph_initial_source_ids!index)"
    by (rule list_all2_nthD
      [OF comma_semantic_graph_initial_source_binding_exact index])
  obtain binding where binding:
      "binding\<in>set comma_semantic_graph_bindings"
      "comma_semantic_b1_binding_source binding =
        comma_semantic_future_initial_sources!index"
      "comma_semantic_b1_binding_cid binding =
        comma_semantic_graph_initial_source_ids!index"
    using comma_semantic_b1_binding_cid_of_sound[OF source_lookup] by blast
  have node_exists:
      "comma_semantic_b1_node_of comma_semantic_graph_nodes
        (comma_semantic_graph_initial_source_ids!index)\<noteq>None"
    by (rule comma_semantic_b1_graph_completed_node_lookup
      [OF graph binding(1) binding(3)])
  obtain node where node:
      "comma_semantic_b1_node_of comma_semantic_graph_nodes
        (comma_semantic_graph_initial_source_ids!index)=Some node"
    using node_exists
    by (cases "comma_semantic_b1_node_of comma_semantic_graph_nodes
      (comma_semantic_graph_initial_source_ids!index)") auto
  show ?thesis
    by (rule comma_semantic_b1_crt_compile_refines_graph_eval[OF graph node])
qed

lemma comma_semantic_b1_crt_compile_published_root_exact:
  assumes graph:
      "comma_semantic_b1_graph_completed_valid
        comma_semantic_graph_bindings comma_semantic_graph_nodes"
    and clock: "clock<924"
    and root: "root<46"
  shows "comma_weighted_crt_apply
      (comma_semantic_b1_crt_compile_node comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root)) clock =
    Some (comma_semantic_b1_crt_graph_result
      (comma_semantic_b1 clock root))"
proof -
  obtain binding where binding:
      "binding\<in>set comma_semantic_graph_bindings"
      "comma_semantic_b1_binding_source binding =
        Comma_Entry 1 0 (comma_offset_representatives!root)"
      "comma_semantic_b1_binding_cid binding=
        comma_semantic_graph_root_ids!root"
    using comma_semantic_graph_root_binding_exists[OF root] by blast
  have node_exists:
      "comma_semantic_b1_node_of comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root)\<noteq>None"
    by (rule comma_semantic_b1_graph_completed_node_lookup
      [OF graph binding(1) binding(3)])
  obtain node where node:
      "comma_semantic_b1_node_of comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root)=Some node"
    using node_exists
    by (cases "comma_semantic_b1_node_of comma_semantic_graph_nodes
      (comma_semantic_graph_root_ids!root)") auto
  have compiled:
      "comma_weighted_crt_apply
          (comma_semantic_b1_crt_compile_node comma_semantic_graph_nodes
            (comma_semantic_graph_root_ids!root)) clock =
        map_option comma_semantic_b1_crt_graph_result
          (comma_semantic_b1_graph_eval comma_semantic_graph_nodes
            (comma_semantic_graph_root_ids!root) clock)"
    by (rule comma_semantic_b1_crt_compile_refines_graph_eval[OF graph node])
  have root_action:
      "comma_semantic_graph_root_action clock root =
        comma_semantic_b1 clock root"
    by (rule comma_semantic_graph_root_action_exact[OF graph clock root])
  have root_not_invalid:
      "comma_semantic_graph_root_action clock root\<noteq>
        Comma_Semantic_B1_Invalid"
    by (rule comma_semantic_graph_root_action_not_invalid[OF clock root])
  have root_eval:
      "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root) clock =
          Some (comma_semantic_b1 clock root)"
    using root_action root_not_invalid
    by (cases "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root) clock")
      (simp_all add: comma_semantic_graph_root_action_def)
  show ?thesis using compiled root_eval by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Weighted CRT compilation refines the checked continuation graph"
    @{thms comma_weighted_crt_branch_all_offsets_congruence
      comma_weighted_crt_first_port_admissible.simps
      comma_weighted_crt_first_port_action_guarded
      comma_weighted_crt_first_port_action_guarded_offset
      comma_weighted_crt_branch_first_port_guarded
      comma_weighted_crt_branch_selected_first_port_guarded
      comma_weighted_crt_guarded_port_diagonal
      comma_weighted_crt_branch_guarded_congruence
      comma_semantic_b1_crt_compile_node_step
      comma_semantic_b1_crt_compile_node_fuel_refines_graph_eval
      comma_semantic_b1_crt_compile_refines_graph_eval
      comma_semantic_b1_crt_compile_initial_source_exact
      comma_semantic_b1_crt_compile_published_root_exact
      comma_semantic_b1_crt_compile_fuel_canonical
      comma_semantic_b1_crt_compile_fuel_stable};
\<close>

ML_file "semantic_weighted_crt_data_cache_hit_fixture.ML"
ML \<open>Comma_Weighted_CRT_Data_Cache_Hit_Fixture.run @{context}\<close>

end
