theory Comma_Semantic_B1_Instance
  imports Comma_Semantic_Predecessor_Certificate
begin

text \<open>
The concrete B32 certificate consumes the authenticated continuation graph
and representation-independent chronological powering. It does not compile
a split-MDD table or reconstruct shifted CRT applications.
\<close>

theorem comma_semantic_graph_b32_stop242_checked:
  "\<forall>root<46. \<forall>phase<924. \<exists>D.
    comma_semantic_graph_action_power 5 phase root =
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
  by (rule comma_semantic_graph_predecessor_stop242_checked)

theorem comma_semantic_b1_action_b32_stop242_checked:
  "\<forall>root<46. \<forall>phase<924. \<exists>D.
    comma_semantic_b1_action_power 5 phase root =
      Comma_Semantic_B1_Stop D \<and> D\<le>242"
proof (intro allI impI)
  fix root phase :: nat
  assume root: "root<46" and phase: "phase<924"
  obtain D where result:
      "comma_semantic_graph_action_power 5 phase root=Comma_Semantic_B1_Stop D"
    and bound: "D\<le>242"
    using comma_semantic_graph_b32_stop242_checked root phase by blast
  have refine:
      "comma_semantic_graph_action_power 5 phase root =
        comma_semantic_b1_action_power 5 phase root"
    by (rule comma_semantic_graph_action_power_refines[OF phase root])
  show "\<exists>D. comma_semantic_b1_action_power 5 phase root =
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
    "Weighted CRT B32 source action and Stop242 certificate"
    ["comma_semantic_graph_valid_checked", "comma_semantic_graph_root_binding_exact",
     "comma_semantic_graph_action_power_refines",
     "comma_semantic_graph_predecessor_stop242_checked",
     "comma_semantic_graph_b32_weighted_actions_refine",
     "comma_semantic_graph_b32_weighted_actions_wellformed",
     "comma_semantic_b1_crt_compile_published_root_exact",
     "comma_semantic_graph_weighted_power_exact",
     "comma_semantic_graph_stop242_from_weighted_crt_power_all",
     "comma_semantic_graph_b32_stop242_checked"]
    @{thms comma_semantic_b1_action_b32_stop242_checked};
\<close>

end
