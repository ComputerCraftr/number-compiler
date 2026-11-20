(* A closure-only certificate does not authenticate any class root. *)
structure Comma_Frontier24_Closure_Contract_Fixture =
struct
  fun run ctxt =
    let
      val bundle = @{term "\<lparr>
        cf24_programs = [], cf24_selectors = [], cf24_action_tokens = [],
        cf24_guard_entries = [], cf24_closures = [], cf24_class_program_refs = [],
        cf24_class_roots = [], cf24_radices = [3,4,7,11],
        cf24_nodes = [Comma_CRT_MDD_Leaf 0], cf24_zero_root = 0
      \<rparr> :: comma_frontier24_parametric_bundle"}
      val closure = HOLogic.mk_Trueprop (@{term comma_frontier24_closure_certified} $ bundle)
      val full = HOLogic.mk_Trueprop (HOLogic.mk_not
        (@{term comma_frontier24_bundle_semantic_certified} $ bundle))
      val rules = @{thms comma_frontier24_closure_certified_def
        comma_frontier24_closure_structure_checked_def
        comma_frontier24_bundle_semantic_certified_def
        comma_frontier24_structure_iff_closures_and_classes
        comma_frontier24_selector_rows_checked_def comma_frontier24_class_roots_checked_def
        comma_frontier24_guard_imports_exact_def comma_frontier24_shifts_certified_def
        comma_frontier24_multiways_certified_def comma_frontier24_shift_requests_def
        comma_frontier24_multiway_requests_def comma_crt_mdd_table_wellformed_def
        comma_crt_mdd_node_ordered_def comma_frontier24_parametric_bundle.select_convs}
      fun prove label proposition =
        Comma_CRT_MDD_Proof_Utils.prove_exact ctxt label proposition
          (fn context => auto_tac (context |> Simplifier.add_simps rules))
      val closure_theorem = prove "Empty closure certificate" closure
      val full_rejection = prove "Empty bundle has no class certificate" full
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Closure certification does not issue class roots" [closure_theorem,full_rejection]
    in () end
end
