theory Comma_Semantic_Graph_Action_Power
  imports Comma_Semantic_Graph_Instance.Comma_Semantic_Graph_Instance
    Comma_Semantic_B1.Comma_Semantic_Action_Power
begin

text \<open>
The certified continuation graph supplies the base action directly.  Its
source bindings are authenticated by graph validity, and its evaluator is
related to the semantic B1 endpoint by the generic graph-refinement theorem.
This theory does not compile graph nodes into CRT columns or split MDDs.
\<close>

lemma comma_semantic_graph_root_binding_exists:
  assumes root: "root<46"
  shows "\<exists>binding\<in>set comma_semantic_graph_bindings.
      comma_semantic_b1_binding_source binding =
        Comma_Entry 1 0 (comma_offset_representatives!root)
      \<and> comma_semantic_b1_binding_cid binding = comma_semantic_graph_root_ids!root"
proof -
  have index: "root < length (map (\<lambda>index. Comma_Entry 1 0
      (comma_offset_representatives!index)) [0..<46])"
    using root by simp
  have indexed:
      "(\<exists>binding\<in>set comma_semantic_graph_bindings.
        comma_semantic_b1_binding_source binding =
          (map (\<lambda>index. Comma_Entry 1 0
            (comma_offset_representatives!index)) [0..<46])!root \<and>
        comma_semantic_b1_binding_cid binding = comma_semantic_graph_root_ids!root)"
    by (rule list_all2_nthD
      [OF comma_semantic_graph_root_binding_exact index])
  show ?thesis
    using indexed root by (auto simp: nth_map_upt)
qed

definition comma_semantic_graph_root_action ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_graph_root_action phase root =
    (case comma_semantic_b1_graph_eval comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root) phase of
       None \<Rightarrow> Comma_Semantic_B1_Invalid
     | Some result \<Rightarrow> result)"

lemma comma_semantic_graph_root_action_exact:
  assumes graph: "comma_semantic_b1_graph_completed_valid
      comma_semantic_graph_bindings comma_semantic_graph_nodes"
    and phase: "phase<924"
    and root: "root<46"
  shows "comma_semantic_graph_root_action phase root =
    comma_semantic_b1 phase root"
proof -
  obtain binding where member: "binding \<in> set comma_semantic_graph_bindings"
    and source: "comma_semantic_b1_binding_source binding =
      Comma_Entry 1 0 (comma_offset_representatives!root)"
    and cid: "comma_semantic_b1_binding_cid binding =
      comma_semantic_graph_root_ids!root"
    using comma_semantic_graph_root_binding_exists[OF root] by blast
  have correct_all:
      "\<forall>cid. comma_semantic_b1_graph_correct_at
        comma_semantic_graph_bindings comma_semantic_graph_nodes cid"
    by (rule comma_semantic_b1_graph_completed_eval_refines_endpoint[OF graph])
  have correct:
      "comma_semantic_b1_graph_correct_at comma_semantic_graph_bindings
        comma_semantic_graph_nodes (comma_semantic_graph_root_ids!root)"
    using correct_all cid member by blast
  have evaluation:
      "comma_semantic_b1_graph_eval comma_semantic_graph_nodes
        (comma_semantic_graph_root_ids!root) phase =
       Some (comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root)))"
    using correct member source cid
    by (auto simp: comma_semantic_b1_graph_correct_at_def)
  have endpoint:
      "comma_semantic_b1_round_output phase
        (Comma_Entry 1 0 (comma_offset_representatives!root)) =
       comma_semantic_b1 phase root"
    by (rule comma_semantic_b1_round_output_root_exact[OF phase root])
  show ?thesis
    using evaluation endpoint
    by (simp add: comma_semantic_graph_root_action_def)
qed

lemma comma_semantic_graph_apply_local_period:
  assumes lookup:
      "comma_semantic_b1_node_of nodes cid = Some node"
    and period:
      "comma_semantic_b1_node_period node = p"
  shows "comma_semantic_b1_graph_apply nodes cid clock =
    comma_semantic_b1_graph_apply nodes cid (clock mod p)"
  using lookup period by (simp add: comma_semantic_b1_graph_apply_def Let_def)

fun comma_semantic_graph_action_power ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_result" where
  "comma_semantic_graph_action_power 0 phase root =
    comma_semantic_graph_root_action phase root"
| "comma_semantic_graph_action_power (Suc k) phase root =
    comma_semantic_word_then (2^k)
      (comma_semantic_graph_action_power k)
      (comma_semantic_graph_action_power k) phase root"

lemma comma_semantic_graph_action_power_refines:
  assumes phase: "phase<924" and root: "root<46"
  shows "comma_semantic_graph_action_power k phase root =
    comma_semantic_b1_action_power k phase root"
  using phase root
proof (induction k arbitrary: phase root)
  case 0
  have phase_bound: "phase<924" using "0.prems" by blast
  have root_bound: "root<46" using "0.prems" by blast
  show ?case
    using comma_semantic_graph_root_action_exact
      [OF comma_semantic_graph_valid_checked phase_bound root_bound]
    by simp
next
  case (Suc k)
  have phase: "phase<924" and root: "root<46"
    using Suc.prems by auto
  have left:
      "comma_semantic_graph_action_power k phase root =
        comma_semantic_b1_action_power k phase root"
    by (rule Suc.IH[OF phase root])
  show ?case
  proof (cases "comma_semantic_b1_action_power k phase root")
    case (Comma_Semantic_B1_Live next_root)
    have action_orbit:
        "comma_semantic_b1_action_power k phase root =
          comma_semantic_b1_of_word (comma_orbit_word k phase root)"
      by (rule comma_semantic_b1_action_power_refines_orbit[OF phase root])
    have orbit_live:
        "comma_orbit_word k phase root = Comma_Word_Live next_root"
      using action_orbit Comma_Semantic_B1_Live
      by (cases "comma_orbit_word k phase root") auto
    have next_root: "next_root<46"
      by (rule comma_orbit_word_live_bound[OF orbit_live])
    have next_phase: "((phase+2^k) mod 924)<924" by simp
    have right:
        "comma_semantic_graph_action_power k
            ((phase+2^k) mod 924) next_root =
          comma_semantic_b1_action_power k
            ((phase+2^k) mod 924) next_root"
      by (rule Suc.IH[OF next_phase next_root])
    show ?thesis
      using left right Comma_Semantic_B1_Live
      by (simp add: comma_semantic_word_then_def)
  next
    case (Comma_Semantic_B1_Stop height)
    show ?thesis
      using left Comma_Semantic_B1_Stop
      by (simp add: comma_semantic_word_then_def)
  next
    case Comma_Semantic_B1_Invalid
    show ?thesis
      using left Comma_Semantic_B1_Invalid
      by (simp add: comma_semantic_word_then_def)
  qed
qed

text \<open>
An exact decade summary is the shared bridge from source termination to the
graph-powered Stop. Keeping this transport independent of how the summary
was obtained lets both a classifier and a checked rank reuse the same proof.
The summary and its height bound remain explicit premises; graph refinement
alone establishes neither.
\<close>

lemma comma_semantic_graph_stop_from_exact_summary:
  assumes phase: "phase < 924" and root: "root < 46"
    and summary: "comma_decade_exact_summary
      (Comma_Decade phase (comma_offset_representatives!root)) h terminal"
    and height_bound: "h \<le> 26"
  shows "comma_semantic_graph_action_power 5 phase root =
      Comma_Semantic_B1_Stop (comma_terminal_weight_encode h terminal)
    \<and> comma_terminal_weight_encode h terminal \<le> 242"
proof -
  have semantic:
    "comma_semantic_b1_action_power 5 phase root =
        Comma_Semantic_B1_Stop (comma_terminal_weight_encode h terminal)
      \<and> comma_terminal_weight_encode h terminal \<le> 242"
    by (rule comma_semantic_b1_action_stop_from_exact_summary
      [OF phase root summary height_bound])
  have refinement:
    "comma_semantic_graph_action_power 5 phase root =
      comma_semantic_b1_action_power 5 phase root"
    by (rule comma_semantic_graph_action_power_refines[OF phase root])
  show ?thesis using semantic refinement by simp
qed

lemma comma_semantic_graph_stop_from_residual_classifier:
  fixes C :: "comma_decade_state \<Rightarrow> comma_decade_residual"
  assumes classifier: "comma_decade_residual_classifier_ok C"
    and height_bound: "\<And>s. comma_decade_admitted s \<Longrightarrow> fst (C s) \<le> 26"
    and phase: "phase < 924" and root: "root < 46"
  shows "comma_semantic_graph_action_power 5 phase root =
      Comma_Semantic_B1_Stop
        (comma_terminal_weight_encode
          (fst (C (Comma_Decade phase (comma_offset_representatives!root))))
          (snd (C (Comma_Decade phase (comma_offset_representatives!root)))))
    \<and> comma_terminal_weight_encode
          (fst (C (Comma_Decade phase (comma_offset_representatives!root))))
          (snd (C (Comma_Decade phase (comma_offset_representatives!root)))) \<le> 242"
proof -
  let ?source = "Comma_Decade phase (comma_offset_representatives!root)"
  have representative: "comma_offset_representatives!root \<le> 90"
    using comma_orbit_representative_index[OF root] by auto
  have admitted: "comma_decade_admitted ?source"
    using phase representative by simp
  have residual: "C ?source = (fst (C ?source), snd (C ?source))"
    by (cases "C ?source") simp
  have summary: "comma_decade_exact_summary ?source (fst (C ?source)) (snd (C ?source))"
    by (rule comma_residual_classifier_sound[OF classifier admitted residual])
  have height: "fst (C ?source) \<le> 26"
    by (rule height_bound[OF admitted])
  show ?thesis
    by (rule comma_semantic_graph_stop_from_exact_summary
      [OF phase root summary height])
qed

corollary comma_semantic_graph_stop242_from_residual_classifier:
  fixes C :: "comma_decade_state \<Rightarrow> comma_decade_residual"
  assumes classifier: "comma_decade_residual_classifier_ok C"
    and height_bound: "\<And>s. comma_decade_admitted s \<Longrightarrow> fst (C s) \<le> 26"
  shows "\<forall>root<46. \<forall>phase<924. \<exists>D.
      comma_semantic_graph_action_power 5 phase root =
        Comma_Semantic_B1_Stop D \<and> D \<le> 242"
  using comma_semantic_graph_stop_from_residual_classifier
    [OF classifier height_bound] by blast

ML \<open>
  val checked = @{thms comma_semantic_graph_root_binding_exists
    comma_semantic_graph_root_action_exact comma_semantic_graph_apply_local_period
    comma_semantic_graph_action_power_refines
    comma_semantic_graph_stop_from_exact_summary
    comma_semantic_graph_stop_from_residual_classifier
    comma_semantic_graph_stop242_from_residual_classifier};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Graph-backed representation-independent B1 action power" checked;
  val _ = Comma_Proof_Dependency_Audit.require_expected_paths @{context}
    "Graph-backed B1 action power has no split-MDD dependency"
    ["comma_semantic_graph_root_binding_exact",
     "comma_semantic_b1_graph_completed_eval_refines_endpoint",
     "comma_semantic_b1_action_power_refines_orbit",
     "comma_decade_exact_summary_block_stop"]
    @{thms comma_semantic_graph_root_action_exact
      comma_semantic_graph_action_power_refines
      comma_semantic_graph_stop_from_exact_summary};
\<close>

text \<open>A period-one Goto fixes the parent's selected slot, but it does not
reduce the receiving child's clock.  This evaluator-only fixture deliberately
uses a period-two child whose outputs differ at full clocks zero and one.\<close>

definition comma_semantic_b1_receiving_clock_fixture_nodes ::
    "comma_semantic_b1_node list" where
  "comma_semantic_b1_receiving_clock_fixture_nodes =
    [\<lparr>comma_semantic_b1_node_cid=1,
      comma_semantic_b1_node_period=1,
      comma_semantic_b1_node_actions=[Comma_Semantic_B1_Goto 0]\<rparr>,
     \<lparr>comma_semantic_b1_node_cid=0,
      comma_semantic_b1_node_period=2,
      comma_semantic_b1_node_actions=[Comma_Semantic_B1_Live_Edge 5,
        Comma_Semantic_B1_Stop_Edge 3]\<rparr>]"

lemma comma_semantic_b1_graph_preserves_full_receiving_clock_fixture:
  "comma_semantic_b1_graph_apply
      comma_semantic_b1_receiving_clock_fixture_nodes 1 0 =
        Some (Comma_Semantic_B1_Goto 0)
    \<and> comma_semantic_b1_graph_apply
      comma_semantic_b1_receiving_clock_fixture_nodes 1 1 =
        Some (Comma_Semantic_B1_Goto 0)
    \<and> comma_semantic_b1_graph_eval
      comma_semantic_b1_receiving_clock_fixture_nodes 0 0 =
        Some (Comma_Semantic_B1_Live 5)
    \<and> comma_semantic_b1_graph_eval
      comma_semantic_b1_receiving_clock_fixture_nodes 0 1 =
        Some (Comma_Semantic_B1_Stop 3)
    \<and> comma_semantic_b1_graph_eval
      comma_semantic_b1_receiving_clock_fixture_nodes 1 0 =
        Some (Comma_Semantic_B1_Live 5)
    \<and> comma_semantic_b1_graph_eval
      comma_semantic_b1_receiving_clock_fixture_nodes 1 1 =
        Some (Comma_Semantic_B1_Stop 3)
    \<and> comma_semantic_b1_graph_eval
      comma_semantic_b1_receiving_clock_fixture_nodes 0 (1 mod 1) =
        Some (Comma_Semantic_B1_Live 5)
    \<and> comma_semantic_b1_graph_eval
      comma_semantic_b1_receiving_clock_fixture_nodes 1 1 \<noteq>
      comma_semantic_b1_graph_eval
        comma_semantic_b1_receiving_clock_fixture_nodes 0 (1 mod 1)"
proof -
  let ?nodes = "comma_semantic_b1_receiving_clock_fixture_nodes"
  have parent_apply_zero:
      "comma_semantic_b1_graph_apply ?nodes 1 0 =
        Some (Comma_Semantic_B1_Goto 0)"
    by (simp add: comma_semantic_b1_graph_apply_def
      comma_semantic_b1_node_of_def comma_semantic_b1_nodes_by_cid_def
      comma_semantic_b1_receiving_clock_fixture_nodes_def)
  have parent_apply_one:
      "comma_semantic_b1_graph_apply ?nodes 1 1 =
        Some (Comma_Semantic_B1_Goto 0)"
    by (simp add: comma_semantic_b1_graph_apply_def
      comma_semantic_b1_node_of_def comma_semantic_b1_nodes_by_cid_def
      comma_semantic_b1_receiving_clock_fixture_nodes_def)
  have child_apply_zero:
      "comma_semantic_b1_graph_apply ?nodes 0 0 =
        Some (Comma_Semantic_B1_Live_Edge 5)"
    by (simp add: comma_semantic_b1_graph_apply_def
      comma_semantic_b1_node_of_def comma_semantic_b1_nodes_by_cid_def
      comma_semantic_b1_receiving_clock_fixture_nodes_def)
  have child_apply_one:
      "comma_semantic_b1_graph_apply ?nodes 0 1 =
        Some (Comma_Semantic_B1_Stop_Edge 3)"
    by (simp add: comma_semantic_b1_graph_apply_def
      comma_semantic_b1_node_of_def comma_semantic_b1_nodes_by_cid_def
      comma_semantic_b1_receiving_clock_fixture_nodes_def)
  have child_eval_zero:
      "comma_semantic_b1_graph_eval ?nodes 0 0 =
        Some (Comma_Semantic_B1_Live 5)"
    by (rule comma_semantic_b1_graph_eval_apply_live[OF child_apply_zero]) simp
  have child_eval_one:
      "comma_semantic_b1_graph_eval ?nodes 0 1 =
        Some (Comma_Semantic_B1_Stop 3)"
    by (rule comma_semantic_b1_graph_eval_apply_stop[OF child_apply_one]) simp
  have parent_eval_zero:
      "comma_semantic_b1_graph_eval ?nodes 1 0 =
        Some (Comma_Semantic_B1_Live 5)"
    using comma_semantic_b1_graph_eval_apply_goto[OF parent_apply_zero] child_eval_zero
    by simp
  have parent_eval_one:
      "comma_semantic_b1_graph_eval ?nodes 1 1 =
        Some (Comma_Semantic_B1_Stop 3)"
    using comma_semantic_b1_graph_eval_apply_goto[OF parent_apply_one] child_eval_one
    by simp
  have wrong_reduction:
      "comma_semantic_b1_graph_eval ?nodes 0 (1 mod 1) =
        Some (Comma_Semantic_B1_Live 5)"
    using child_eval_zero by simp
  show ?thesis
    using parent_apply_zero parent_apply_one child_eval_zero child_eval_one
      parent_eval_zero parent_eval_one wrong_reduction
    by simp
qed

ML \<open>
  val receiving_clock_fixture =
    @{thms comma_semantic_b1_graph_preserves_full_receiving_clock_fixture};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Period-one Goto preserves the child's full receiving clock"
    receiving_clock_fixture;
  val _ = if List.all (fn theorem => Thm.nprems_of theorem = 0
      andalso null (Thm.hyps_of theorem)
      andalso null (Thm_Deps.all_oracles [theorem])) receiving_clock_fixture
    then () else error "Receiving-clock regression fixture is not closed and oracle-free";
\<close>

text \<open>Exact conversion fixtures run before the concrete rank constructor.
They check local power plumbing and request authority independently of the
universal B32 bound.\<close>

ML_file "semantic_graph_endpoint_evaluator.ML"
ML_file "semantic_graph_power_evaluator.ML"

ML \<open>
local
  val ctxt = @{context};
  val natT = @{typ nat};
  fun nat n = HOLogic.mk_number natT n;
  fun standalone theorem =
    let val prop = Thm.prop_of theorem in
      Thm.nprems_of theorem = 0 andalso null (Thm.hyps_of theorem) andalso
      null (Thm.tpairs_of theorem) andalso not (Term.is_open prop) andalso
      null (Term.add_frees prop []) andalso null (Term.add_vars prop []) andalso
      null (Thm_Deps.all_oracles [theorem])
    end;
  fun exact_equation label query result theorem =
    let val expected = HOLogic.mk_Trueprop (HOLogic.mk_eq (query, result)) in
      if standalone theorem andalso Thm.prop_of theorem aconv expected then ()
      else error (label ^ " is not the exact closed oracle-free equation")
    end;
  fun root_query phase root =
    @{term comma_semantic_graph_root_action} $ nat phase $ nat root;
  fun power_query k phase root =
    @{term comma_semantic_graph_action_power} $ nat k $ nat phase $ nat root;
  datatype result = Live of int | Stop of int | Invalid;
  fun numeral term =
    (case HOLogic.dest_number term of
      (typ, number) =>
        if typ = natT andalso number >= 0 then number
        else error "Graph fixture found a non-natural result payload");
  fun parse_result term =
    (case strip_comb term of
      (Const (name, _), []) =>
        if name = @{const_name Comma_Semantic_B1_Invalid} then Invalid
        else error "Graph fixture found an unknown nullary result"
    | (Const (name, _), [payload]) =>
        if name = @{const_name Comma_Semantic_B1_Live} then Live (numeral payload)
        else if name = @{const_name Comma_Semantic_B1_Stop} then Stop (numeral payload)
        else error "Graph fixture found an unknown unary result"
    | _ => error "Graph fixture found a malformed B1 result");
  val evaluator = Comma_Semantic_Graph_Endpoint_Evaluator.make ctxt;
  val first = #root evaluator 1 0;
  val shifted = #root evaluator 13 0;
  val _ = if #result first aconv @{term "Comma_Semantic_B1_Live 12"}
      andalso #result shifted aconv @{term "Comma_Semantic_B1_Live 23"}
    then () else error "Distinct receiving phases lost their exact B1 results";
  val _ = exact_equation "Phase-1 endpoint" (root_query 1 0)
    (#result first) (#equation first);
  val _ = exact_equation "Phase-13 endpoint" (root_query 13 0)
    (#result shifted) (#equation shifted);
  val repeated = #root evaluator 1 0;
  val _ = if Thm.prop_of (#equation first) aconv Thm.prop_of (#equation repeated)
    then () else error "Endpoint cache changed its exact source-phase equation";
  val power = Comma_Semantic_Graph_Power_Evaluator.make ctxt;
  val powered = #evaluate power 5 1 0;
  val _ = exact_equation "B32 source regression" (power_query 5 1 0)
    (#result powered) (#equation powered);
  val _ = (case parse_result (#result powered) of
      Stop _ => ()
    | _ => error "B32 source regression did not terminate");

  fun stop_absorption phase root stop_result =
    let
      val lifted = #evaluate power 1 phase root;
      val _ = if #result lifted aconv stop_result then ()
        else error "Graph power failed to absorb an actual Stop endpoint";
      val _ = exact_equation "Stop absorption power" (power_query 1 phase root)
        stop_result (#equation lifted);
    in () end;

  fun follow_live_path remaining phase root current saw_live_live =
    (case parse_result (#result current) of
      Stop _ =>
        (stop_absorption phase root (#result current);
         (saw_live_live, false, true))
    | Invalid => error "Admitted graph path reached Invalid before its Stop"
    | Live next_root =>
        if remaining = 0 then error "B32 live path exceeded its 32-action fixture bound"
        else
          let
            val next_phase = (phase + 1) mod 924;
            val next = #root evaluator next_phase next_root;
            val composed = #evaluate power 1 phase root;
            val _ = exact_equation "Successor endpoint" (root_query next_phase next_root)
              (#result next) (#equation next);
            val _ = exact_equation "One-action graph power"
              (power_query 1 phase root) (#result composed) (#equation composed);
          in
            (case parse_result (#result next) of
              Live _ =>
                let
                  val _ = if #result composed aconv #result next then ()
                    else error "Live-to-Live power changed the receiving action";
                  val _ = exact_equation "Live-to-Live power" (power_query 1 phase root)
                    (#result next) (#equation composed);
                  val (_, saw_live_stop, stopped) =
                    follow_live_path (remaining - 1) next_phase next_root next true;
                in (true, saw_live_stop, stopped) end
            | Stop height =>
                let
                  val expected = @{term Comma_Semantic_B1_Stop} $ nat (9 + height);
                  val _ = if #result composed aconv expected then ()
                    else error "Live-to-Stop power lost the chronological weight";
                  val _ = exact_equation "Live-to-Stop power" (power_query 1 phase root)
                    expected (#equation composed);
                  val _ = stop_absorption next_phase next_root (#result next);
                in (saw_live_live, true, true) end
            | Invalid => error "Admitted successor endpoint is Invalid")
          end);

  val (saw_live_live, saw_live_stop, reached_stop) =
    follow_live_path 32 1 0 first false;
  val _ = if saw_live_live andalso saw_live_stop andalso reached_stop then ()
    else error "Graph fixture did not cover both Live power branches and Stop absorption";

  val invalid_function = @{term "\<lambda>(phase::nat) (root::nat). Comma_Semantic_B1_Invalid"};
  val unused_stop_function = @{term "\<lambda>(phase::nat) (root::nat). Comma_Semantic_B1_Stop 4"};
  val invalid_query = @{term comma_semantic_word_then} $ nat 7 $
    invalid_function $ unused_stop_function $ nat 3 $ nat 8;
  val invalid_result = @{term Comma_Semantic_B1_Invalid};
  val invalid_expected = HOLogic.mk_Trueprop
    (HOLogic.mk_eq (invalid_query, invalid_result));
  val invalid_absorption = Goal.prove ctxt [] [] invalid_expected
    (fn {context, ...} =>
      resolve_tac context [@{thm comma_semantic_word_then_invalid}] 1
      THEN simp_tac context 1);
  val _ = exact_equation "Named generic Invalid absorption" invalid_query
    invalid_result invalid_absorption;

  fun rejects expected action =
    (case Exn.capture action () of
      Exn.Res _ => error ("Expected rejection with: " ^ expected)
    | Exn.Exn (ERROR message) =>
        if message = expected then ()
        else error ("Expected rejection '" ^ expected ^ "', got '" ^ message ^ "'")
    | Exn.Exn _ => error ("Expected ERROR rejection with: " ^ expected));
in
  val _ = rejects "Graph endpoint phase is outside 0..923"
    (fn () => ignore (#root evaluator 924 0));
  val _ = rejects "Graph endpoint root is outside 0..45"
    (fn () => ignore (#root evaluator 0 46));
  val _ = rejects "Graph power evaluator supports only exponents 0 through 5"
    (fn () => ignore (#evaluate power 6 0 0));
  val _ = rejects "Graph power phase is outside 0..923"
    (fn () => ignore (#evaluate power 0 924 0));
  val _ = rejects "Graph power root is outside 0..45"
    (fn () => ignore (#evaluate power 0 0 46));
  val _ = Comma_Fast_Kernel.report (#stats evaluator ());
  val _ = Comma_Fast_Kernel.report (#stats power ());
  val _ = #clear evaluator ();
  val _ = #clear power ();
end
\<close>

end
