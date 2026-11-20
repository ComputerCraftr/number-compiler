(* Universal Bellman publication from 46 checked symbolic program projections.
   There is no one-step MDD or phase-occurrence catalogue in this interface. *)
structure Comma_Direct_Bellman_Publication =
struct
  structure Utils = Comma_CRT_MDD_Proof_Utils
  type binding = {cid:int,program:term,projected:thm,bounded:thm}
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n
  fun tp p = HOLogic.mk_Trueprop p
  fun publish ctxt D (bindings:binding list) =
    let
      val _ = if Utils.closed D andalso fastype_of D = @{typ "nat => nat => nat"}
          andalso map #cid bindings = (0 upto 45) then ()
        else error "Bellman publication requires a closed value function and 46 ordered class rows"
      val class_binding = Comma_Direct_Class_Bindings.make ctxt
      val predicate = Envir.beta_norm
        (@{term "\<lambda>(D::nat \<Rightarrow> nat \<Rightarrow> nat) cid.
          \<exists>program. comma_semantic_phase_program_for_class cid = Some program \<and>
            (\<forall>phase<924. D phase cid \<le> 242 \<and> D phase cid =
              comma_direct_bellman_mask_projection D phase
                (comma_semantic_phase_program_fold comma_phase_program_full_action_output
                  phase program 0))"} $ D)
      fun one ({cid,program,projected,bounded}:binding) =
        let
          val index = nat cid
          val phase = Free ("direct_bellman_phase",natT)
          val value = D $ phase $ index
          val fold = @{term comma_semantic_phase_program_fold} $
            @{term comma_phase_program_full_action_output} $ phase $ program $ nat 0
          val rhs = @{term comma_direct_bellman_mask_projection} $ D $ phase $ fold
          val projected = Utils.exact_prop ctxt "Direct Bellman program projection"
            (Logic.all phase (tp (HOLogic.mk_eq (value,rhs)))) projected
          val bounded = Utils.exact_prop ctxt "Direct Bellman value bound"
            (Logic.all phase (tp (HOLogic.mk_binrel @{const_name less_eq} (value,nat 242)))) bounded
          val selected = class_binding cid program
          val exists_rule = Drule.infer_instantiate ctxt
            [(("x",0),Thm.cterm_of ctxt program)] @{thm exI}
          val goal = tp (Envir.beta_norm (predicate $ index))
        in Utils.prove_exact ctxt "Direct Bellman class row" goal
          (fn context =>
            resolve_tac context [exists_rule] 1 THEN
            resolve_tac context [@{thm conjI}] 1 THEN
            resolve_tac context [selected] 1 THEN
            resolve_tac context [@{thm allI}] 1 THEN
            resolve_tac context [@{thm impI}] 1 THEN
            resolve_tac context [@{thm conjI}] 1 THEN
            resolve_tac context [Thm.forall_elim_vars 0 bounded] 1 THEN
            resolve_tac context [Thm.forall_elim_vars 0 projected] 1) end
      val rows = Comma_Direct_Class_Bindings.indexed_rows ctxt predicate (map one bindings)
      val theorem = (@{thm comma_direct_bellman_from_class_rows} OF [rows])
        |> Utils.exact_prop ctxt "Direct concrete Bellman certificate"
          (tp (@{term comma_frontier_m204_bellman} $ D))
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Direct concrete Bellman certificate" [theorem]
    in theorem end
end
