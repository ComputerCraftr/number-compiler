(* Test-only projections for literal bundle records, without traversing fields. *)
structure Comma_Frontier24_Literal_Projections =
struct
  val bundleT = @{typ comma_frontier24_parametric_bundle}
  val fields =
    [(@{const_name cf24_programs}, @{typ "comma_semantic_port_program list"}),
     (@{const_name cf24_selectors}, @{typ "comma_frontier24_selector_recipe list"}),
     (@{const_name cf24_action_tokens}, @{typ "comma_source_continuation_action list"}),
     (@{const_name cf24_guard_entries}, @{typ "comma_frontier24_guard_entry list"}),
     (@{const_name cf24_closures}, @{typ "comma_frontier24_closure list"}),
     (@{const_name cf24_class_program_refs}, @{typ "nat list"}),
     (@{const_name cf24_class_roots}, @{typ "nat list"}),
     (@{const_name cf24_radices}, @{typ "nat list"}),
     (@{const_name cf24_nodes}, @{typ "nat comma_crt_mdd_node list"}),
     (@{const_name cf24_zero_root}, @{typ nat})]
  fun make ctxt bundle =
    map (fn (name,T) =>
      (name,Conv.rewrs_conv
        (map (fn theorem => theorem RS @{thm eq_reflection})
          @{thms comma_frontier24_parametric_bundle.select_convs})
        (Thm.cterm_of ctxt (Const (name,bundleT --> T) $ bundle)))) fields
end
