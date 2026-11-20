theory Comma_Continue_Frontier24_Source_Bridge
  imports Comma_Semantic_B1.Comma_Direct_Bellman_Projection
    Comma_Semantic_B1.Comma_Direct_Action_MDD
    Comma_Semantic_B1.Comma_Direct_Action_Simulation
    Comma_Semantic_B1.Comma_Parametric_Continue_Constructors
    Comma_Semantic_B1.Comma_CRT_MDD_Certificates
    Comma_Semantic_B1.Comma_CRT_MDD_Transport
    Comma_Semantic_B1.Comma_Program_Continue_Guard_Exact
begin

text \<open>The B1 weight is issued by checked direct Bellman projection over
one seeded Store. Physical source roots are separate Future obligations.\<close>

ML_file "semantic_frontier24_parametric_compiler.ML"
ML_file "semantic_frontier24_parametric_runtime.ML"
ML_file "semantic_crt_mdd_point_eval.ML"
ML_file "semantic_direct_entry_arithmetic.ML"
ML_file "semantic_frontier24_mdd_import_certificates.ML"
ML_file "../comma_semantic_b1/crt_mdd_multiway_replay.ML"
ML_file "semantic_direct_entry_row_plan.ML"
ML_file "semantic_direct_action_proposal.ML"
ML_file "semantic_direct_mdd_proposal.ML"
ML_file "semantic_direct_terminal_proofs.ML"
ML_file "semantic_direct_row_bindings.ML"
ML_file "semantic_direct_entry_bindings.ML"
ML_file "semantic_direct_program_bindings.ML"
ML_file "semantic_direct_mdd_evaluation.ML"
ML_file "semantic_direct_class_bindings.ML"
ML_file "semantic_direct_bellman_publication.ML"
ML_file "semantic_direct_bellman_terminal_proposal.ML"
ML_file "semantic_direct_bellman_terminal_proofs.ML"
ML_file "semantic_direct_bellman_issuer.ML"
ML_file "semantic_frontier_m204_candidate_data.ML"
ML_file "semantic_direct_candidate_publication.ML"
ML_file "semantic_frontier_m204_weight_owner.ML"

ML \<open>
structure Comma_Direct_B1_Publication =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Issuer = Comma_Direct_Bellman_Issuer
  structure Owner = Comma_Frontier_M204_Weight_Owner

  fun certify (input:Issuer.publication) lthy =
    let
      val lthy1 = Issuer.certify input lthy
      val ctxt = Local_Theory.target_of lthy1
      val bellman = Proof_Context.get_thm ctxt "comma_m204_direct_concrete_bellman_native"
      val ((local_weight,(_,local_definition)),lthy2) = Local_Theory.define
        ((Binding.name "comma_frontier_m204_weight",NoSyn),
         ((Binding.name "comma_frontier_m204_weight_def",[]),#D input)) lthy1
      val morphism = Local_Theory.target_morphism lthy2
      val weight = Morphism.term morphism local_weight
      val definition = Morphism.thm morphism local_definition
      val ctxt2 = Local_Theory.target_of lthy2
      val weight_D = Utils.exact_prop ctxt2 "Direct weight alias"
        (Logic.mk_equals (weight,#D input)) definition
      val weight_named_roots = Thm.transitive weight_D (#D_definition input)
      val root_transport = Conv.arg_conv (Conv.rewr_conv (#roots_definition input))
        (Thm.rhs_of weight_named_roots)
      val weight_definition = Thm.transitive weight_named_roots root_transport
      val bellman = Simplifier.rewrite_rule (put_simpset HOL_basic_ss ctxt2)
        [Thm.symmetric weight_D] bellman
      val bellman = Utils.exact_prop ctxt2 "Direct B1 Bellman authority"
        (HOLogic.mk_Trueprop (@{term comma_frontier_m204_bellman} $ weight)) bellman
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt2
        "Direct B1 Bellman authority" [weight_definition,bellman]
      val (_,lthy3) = Local_Theory.note
        ((Binding.name "comma_frontier_m204_bellman_native",[]),[bellman]) lthy2
    in Owner.publish (#store input) (#arena input) (#roots input)
      weight weight_definition bellman lthy3 end

  fun run lthy = Comma_M204_Direct_Candidate_Publication.publish
    Comma_Direct_Bellman_Issuer.prepare certify lthy
end
\<close>

local_setup \<open>Comma_Direct_B1_Publication.run\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Direct B1 Bellman authority" @{thms comma_frontier_m204_bellman_native}
\<close>

end
