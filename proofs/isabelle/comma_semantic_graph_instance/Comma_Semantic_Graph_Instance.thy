theory Comma_Semantic_Graph_Instance
  imports Comma_Decisive_Endpoint_Quotient.Comma_Source_Continuation_DAG
begin

text \<open>This audit session discovers the candidate graph from checked local endpoint
arithmetic. Its source bindings are proof data, separate from the shallow
semantic nodes. No trajectory, phase-mask word or ranked future table is an
input to this constructor. Publication requires the complete graph checker;
ML discovery alone is not an admission theorem. This physical-row audit is
not a dependency of the semantic B1 constructor.\<close>

ML_file "semantic_graph_constructor.ML"

local_setup \<open>fn lthy =>
  let
    val engine = Comma_Semantic_Graph_Constructor.make_audit lthy
    val _ = map (#root engine) (0 upto 45)
    val _ = Comma_Fast_Kernel.report (#stats engine ())
    val rows = #rows engine ()
  in
    #2 (Local_Theory.note
      ((Binding.name "comma_semantic_source_rows_checked", []), rows) lthy)
  end
\<close>

ML \<open>
  val checked = @{thms comma_semantic_source_rows_checked};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Semantic continuation source rows" checked;
\<close>

end
