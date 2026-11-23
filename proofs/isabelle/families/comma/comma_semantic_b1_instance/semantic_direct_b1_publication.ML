(* Final direct B1 authority transport from the generated Bellman candidate. *)
structure Comma_Direct_B1_Publication =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  structure Issuer = Comma_Direct_Bellman_Issuer
  structure Owner = Comma_Frontier_M204_Weight_Owner

  fun stage name work = Comma_Proof_Profile.progress_scope
    "Comma_Semantic_B1_Instance" "b1-stage" NONE NONE name (fn _ => work ())

  fun publish_weight (input:Issuer.publication) lthy1 =
    let
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

  fun certify input lthy =
    let val checked = stage "root_bind_application" (fn () => Issuer.certify input lthy)
    in stage "publication" (fn () => publish_weight input checked) end

  fun run lthy = Comma_M204_Direct_Candidate_Publication.publish
    Issuer.prepare certify lthy
end
