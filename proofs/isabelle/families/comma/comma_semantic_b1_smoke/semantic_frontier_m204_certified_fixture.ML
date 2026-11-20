(* Tiny end-to-end structural Bellman fixture.  Its constant typed-step
   source is synthetic: it cannot authorize the real comma source program. *)
structure Comma_Frontier_M204_Certified_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Proposal = Comma_Frontier_M204_Bellman_Proposal
  structure Certificates = Comma_Frontier_M204_Bellman_Certificates
  structure Publisher = Comma_Frontier_M204_Bulk_Publisher
  structure Utils = Comma_CRT_MDD_Proof_Utils

  fun run initial_lthy =
    let
      val d_arena = Arena.create [3,4,7,11]
      val step_arena = Arena.create [3,4,7,11]
      val zero = Arena.action_none d_arena
      val nine = Arena.action_some d_arena 8
      val d_roots = nine :: replicate 45 zero
      val continue = Arena.action_some step_arena 1
      val fork2 = Arena.action_some step_arena 46
      val step_roots = continue :: replicate 45 fork2
      val (step_store,lthy1) = Store.make "m204_fixture_typed_step" step_arena initial_lthy
      val candidate = Proposal.build d_arena d_roots step_arena step_roots
      val (work_store,lthy2) = Store.make "m204_fixture_work" (#arena candidate) lthy1
      val operations = Certificates.replay step_store work_store candidate
      val ctxt = Local_Theory.target_of lthy2
      val published = Publisher.certify ctxt work_store candidate operations
      val expected = HOLogic.mk_Trueprop
        (@{term comma_frontier_m204_code_bellman} $ #D published $ #action published)
      val theorem = Utils.exact_prop ctxt "Synthetic M204 closed Bellman"
        expected (#code_bellman published)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Synthetic M204 checked Bellman" [theorem]
      val _ = if length (#step_import_evals operations)=46 then ()
        else error "Synthetic M204 did not retain every checked typed-step import"
    in lthy2 end
end
