theory Comma_Semantic_Graph_B32_Instance
  imports Comma_Semantic_Graph_Action_Power
    Comma_Semantic_B1_Instance.Comma_Semantic_B1_Instance
begin

text \<open>
The graph owner transports the independently certified B1 stop bound through
its exact graph-action refinement. This theorem remains the authority for the
graph projector and the graph-backed summary implementation.
\<close>

theorem comma_semantic_graph_b32_stop242_checked:
  "\<forall>root<46. \<forall>phase<924. \<exists>D.
    comma_semantic_graph_action_power 5 phase root =
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof (intro allI impI)
  fix root phase :: nat
  assume root: "root<46" and phase: "phase<924"
  obtain D where result:
      "comma_semantic_b1_action_power 5 phase root=Comma_Semantic_B1_Stop D"
    and bound: "D\<le>242"
    using comma_semantic_b1_action_b32_stop242_checked root phase by blast
  have refine:
      "comma_semantic_graph_action_power 5 phase root =
        comma_semantic_b1_action_power 5 phase root"
    by (rule comma_semantic_graph_action_power_refines[OF phase root])
  show "\<exists>D. comma_semantic_graph_action_power 5 phase root =
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
    using refine result bound by blast
qed

ML_file "semantic_graph_action_certificate.ML"

ML \<open>
local
  val ctxt = @{context};
  val projector = Comma_Semantic_Graph_Action_Certificate.make ctxt;
  fun nat n = HOLogic.mk_number @{typ nat} n;
  fun request k phase root =
    @{term comma_semantic_b1_action_power} $ nat k $ nat phase $ nat root;
  fun query phase root = #query projector phase root;
  val first = query 0 0;
  val repeated = query 0 0;
  val expected = #equation first RS @{thm eq_reflection};
  val _ = if Thm.prop_of (#equation first) aconv Thm.prop_of (#equation repeated)
    then () else error "B32 projection cache changed its checked equation";
  fun rejects context term =
    (case #convert projector (Thm.cterm_of context term) of
      NONE => ()
    | SOME _ => error "B32 projection accepted unsupported or foreign authority");
  val parent_context = Proof_Context.init_global
    (hd (Theory.parents_of (Proof_Context.theory_of ctxt)));
in
  val _ = (case #convert projector (Thm.cterm_of ctxt (request 5 0 0)) of
      SOME theorem =>
        if Thm.prop_of theorem aconv Thm.prop_of expected then ()
        else error "B32 projection changed the exact requested power"
    | NONE => error "B32 projection refused its checked receiving context");
  val _ = rejects ctxt (request 6 0 0);
  val _ = rejects ctxt (request 5 924 0);
  val _ = rejects ctxt (request 5 0 46);
  val _ = rejects parent_context (request 5 0 0);
  val _ = Comma_Fast_Kernel.report (#report projector ());
  val _ = #clear projector ();
end
\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths @{context}
    "Graph B32 action through exact semantic refinement"
    ["comma_semantic_b1_action_b32_stop242_checked",
     "comma_semantic_graph_action_power_refines",
     "comma_semantic_graph_root_action_exact",
     "comma_semantic_graph_valid_checked",
     "comma_semantic_b1_graph_completed_eval_refines_endpoint",
     "comma_semantic_graph_root_binding_exact"]
    @{thms comma_semantic_graph_b32_stop242_checked};
\<close>

end
