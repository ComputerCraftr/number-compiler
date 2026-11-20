(* Small independent constructor and adversarial witness fixtures. *)
local
  val ctxt = @{context}
  val entry = @{term "\<lparr>cf24_closure_program_ref=0,cf24_closure_full_shift=0,
    cf24_closure_cases=[\<lparr>cf24_closure_case_wanted=0,
      cf24_closure_case_guard_root=0,cf24_closure_case_shifted_guard_root=0,
      cf24_closure_case_action_token=0,cf24_closure_case_action_output_root=0,
      cf24_closure_case_child=None\<rparr>],cf24_closure_near_token=None,
    cf24_closure_near_action_output_root=None,cf24_closure_near_child=None,
    cf24_closure_output_root=0\<rparr>"}
  val near = @{term "\<lparr>cf24_closure_program_ref=1,cf24_closure_full_shift=0,
    cf24_closure_cases=[],cf24_closure_near_token=Some 0,
    cf24_closure_near_action_output_root=Some 0,cf24_closure_near_child=None,
    cf24_closure_output_root=0\<rparr>"}
  val closures = [entry,near]
  val bundle = Term.subst_free
    [(@{term "fixture_closures::comma_frontier24_closure list"},
      HOLogic.mk_list @{typ comma_frontier24_closure} closures)]
    @{term "\<lparr>cf24_programs=[Comma_Entry_Core_Program 0 0 0 Comma_Core_1,
          Comma_Near_Boundary_Program 0],
      cf24_selectors=[Comma_Frontier24_Entry_Selector 0 0 0 Comma_Core_1
          [\<lparr>cf24_case_wanted=0,cf24_case_guard_root=0,cf24_case_action_token=0\<rparr>],
          Comma_Frontier24_Near_Selector 0],
      cf24_action_tokens=[Comma_Continuation_Invalid],
      cf24_guard_entries=[\<lparr>cf24_guard_core=Comma_Core_1,cf24_guard_wanted=0,
          cf24_guard_root=0\<rparr>],cf24_closures=fixture_closures,
      cf24_class_program_refs=[],cf24_class_roots=[],cf24_radices=[],
      cf24_nodes=[Comma_CRT_MDD_Leaf 0],cf24_zero_root=0\<rparr>"}
  fun shape index closure = HOLogic.mk_Trueprop
    (@{term comma_frontier24_closure_shape_checked} $ bundle $
      HOLogic.mk_prod (HOLogic.mk_number @{typ nat} index,closure))
  fun prove index closure = Goal.prove ctxt [] [] (shape index closure)
    (fn _ => Code_Simp.dynamic_tac ctxt 1)
  val _ = Comma_Proof_Profile.report "Structure fixture individual shapes start"
  val facts = [prove 0 entry,prove 1 near]
  val _ = Comma_Proof_Profile.report "Structure fixture individual shapes complete"
  fun rejected label f =
    if Exn.is_exn (Exn.capture f ()) then ()
    else error ("Structure fixture accepted " ^ label)
  fun aggregation_fixture lthy =
    let
      val closureT = @{typ comma_frontier24_closure}
      val (owner,lthy1) = Comma_CRT_Balanced_Table.make
        "structure_fixture_closures" closureT closures lthy
      val (changed,lthy2) = Comma_CRT_Balanced_Table.make
        "structure_fixture_changed_closures" closureT [near,near] lthy1
      val context = Local_Theory.target_of lthy2
      fun aggregate table rows =
        Comma_Frontier24_Structure_Proofs.indexed_closures context bundle table rows
      val theorem = aggregate owner facts
      val _ = rejected "reordered facts" (fn () => aggregate owner (rev facts))
      val _ = rejected "missing fact" (fn () => aggregate owner [hd facts])
      val _ = rejected "excess fact" (fn () => aggregate owner (facts @ [hd facts]))
      val open_fact = Thm.assume (Thm.cterm_of context (shape 0 entry))
      val _ = rejected "open fact" (fn () => aggregate owner [open_fact,List.last facts])
      val _ = rejected "changed closure" (fn () => aggregate changed facts)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean context
        "Named indexed closure aggregation" [theorem]
    in lthy2 end
  val closure_plan = Comma_Frontier24_Selected_Table_Plan.make ctxt bundle
    (Comma_Frontier24_Literal_Projections.make ctxt bundle) "fixture closures"
    @{const_name cf24_closures} @{typ comma_frontier24_closure} 2 (SOME closures)
  val child_proc = (case #child_fields closure_plan of SOME proc => proc
    | NONE => error "Closure plan lacks its child-field converter")
  val child_context = put_simpset HOL_basic_ss ctxt |> Simplifier.add_proc child_proc
  val closure_table = @{term "cf24_closures :: comma_frontier24_parametric_bundle \<Rightarrow>
    comma_frontier24_closure list"} $ bundle
  fun child_request table index = @{term "cf24_closure_program_ref :: comma_frontier24_closure \<Rightarrow> nat"} $
    (Const (@{const_name nth}, @{typ "comma_frontier24_closure list \<Rightarrow> nat \<Rightarrow> comma_frontier24_closure"}) $
      table $ HOLogic.mk_number @{typ nat} index)
  val child = child_request closure_table 1
  val child_theorem = Simplifier.rewrite child_context (Thm.cterm_of ctxt child)
  val _ = if Thm.term_of (Thm.rhs_of child_theorem) aconv HOLogic.mk_number @{typ nat} 1 then ()
    else error "Selected child field returned a different projection"
  val foreign_table = @{term "[]::comma_frontier24_closure list"}
  val foreign = child_request foreign_table 0
  val foreign_result = Simplifier.rewrite child_context (Thm.cterm_of ctxt foreign)
  val _ = if Thm.term_of (Thm.rhs_of foreign_result) aconv foreign then ()
    else error "Selected child field accepted a foreign table"
  val outside = child_request closure_table 2
  val outside_result = Simplifier.rewrite child_context (Thm.cterm_of ctxt outside)
  val _ = if Thm.term_of (Thm.rhs_of outside_result) aconv outside then ()
    else error "Selected child field accepted an out-of-range index"
  val guard_plan = Comma_Frontier24_Selected_Table_Plan.make ctxt bundle (Comma_Frontier24_Literal_Projections.make ctxt bundle) "fixture guard"
    @{const_name cf24_guard_entries} @{typ comma_frontier24_guard_entry} 1 NONE
  val witness = Comma_Frontier24_Structure_Proofs.guard_witness ctxt bundle guard_plan
    0 @{term Comma_Core_1} @{term "0::nat"} @{term "0::nat"}
  val entry_program = @{term "Comma_Entry_Core_Program 0 0 0 Comma_Core_1"}
  val near_program = @{term "Comma_Near_Boundary_Program 0"}
  val entry_selector = @{term "Comma_Frontier24_Entry_Selector 0 0 0 Comma_Core_1
    [\<lparr>cf24_case_wanted=0,cf24_case_guard_root=0,cf24_case_action_token=0\<rparr>]"}
  val near_selector = @{term "Comma_Frontier24_Near_Selector 0"}
  val scalar = Comma_Entry_Arithmetic.natural_context ctxt
    |> Simplifier.add_simps @{thms comma_frontier24_parametric_bundle.select_convs
      comma_frontier24_closure.select_convs
      list.simps list.size list.map nth_Cons_0 nth_Cons_Suc nth_Cons'}
  val extraction = scalar |> Simplifier.add_simps @{thms
    comma_frontier24_closure_shape_checked_def prod.case Let_def
    comma_semantic_port_program.simps comma_frontier24_selector_recipe.simps}
  fun recipe fact program selector = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
    (@{term comma_frontier24_selector_recipe_matches} $ program $ selector $
      (@{term "cf24_action_tokens :: comma_frontier24_parametric_bundle \<Rightarrow>
        comma_source_continuation_action list"} $ bundle))) (fn {context,...} =>
        Method.insert_tac context [fact] 1 THEN auto_tac extraction)
  val _ = Comma_Proof_Profile.report "Structure fixture Entry recipe start"
  val entry_recipe = recipe (hd facts) entry_program entry_selector
  val _ = Comma_Proof_Profile.report "Structure fixture Entry recipe complete"
  val near_recipe = recipe (List.last facts) near_program near_selector
  val _ = Comma_Proof_Profile.report "Structure fixture Near recipe complete"
  val _ = Comma_Proof_Profile.report "Structure fixture Entry constructor start"
  val entry_shape = Comma_Frontier24_Structure_Proofs.closure_shape ctxt scalar
    bundle 0 entry entry_program entry_selector NONE entry_recipe [witness]
  val _ = Comma_Proof_Profile.report "Structure fixture Entry constructor complete"
  val near_shape = Comma_Frontier24_Structure_Proofs.closure_shape ctxt scalar
    bundle 1 near near_program near_selector (SOME @{term "0::nat"}) near_recipe []
  val _ = Comma_Proof_Profile.report "Structure fixture Near constructor complete"
  val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Constructed Entry closure"
    (shape 0 entry) entry_shape
  val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Constructed Near closure"
    (shape 1 near) near_shape
  val _ = rejected "changed Near output" (fn () =>
    Comma_Frontier24_Structure_Proofs.closure_shape ctxt scalar bundle 1 near
      near_program near_selector (SOME @{term "1::nat"}) near_recipe [])
  val _ = rejected "guard index" (fn () =>
    Comma_Frontier24_Structure_Proofs.guard_witness ctxt bundle guard_plan
      1 @{term Comma_Core_1} @{term "0::nat"} @{term "0::nat"})
  val _ = rejected "guard core" (fn () =>
    Comma_Frontier24_Structure_Proofs.guard_witness ctxt bundle guard_plan
      0 @{term Comma_Core_3} @{term "0::nat"} @{term "0::nat"})
  val _ = rejected "guard root" (fn () =>
    Comma_Frontier24_Structure_Proofs.guard_witness ctxt bundle guard_plan
      0 @{term Comma_Core_1} @{term "0::nat"} @{term "1::nat"})
  val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
    "Closure constructor and guard fixture"
    (witness::entry_shape::near_shape::facts)
in
  val run_frontier24_structure_aggregation_fixture = aggregation_fixture
end

(* A source-bound Near program with a represented Entry child exercises the
   same constructor and scalar premises used by the production publisher. *)
local
  val ctxt = @{context}
  val program = @{term "Comma_Near_Boundary_Program 1"}
  val selector = @{term "Comma_Frontier24_Near_Selector 0"}
  val expected_child = @{term "Comma_Entry_Core_Program 2 1 91 Comma_Core_13"}
  val parent = @{term "\<lparr>cf24_closure_program_ref=1,cf24_closure_full_shift=0,
    cf24_closure_cases=[],cf24_closure_near_token=Some 0,
    cf24_closure_near_action_output_root=Some 0,cf24_closure_near_child=Some 0,
    cf24_closure_output_root=0\<rparr>"}
  fun bundle child_program child_shift = Term.subst_free
    [(@{term "fixture_child_program::comma_semantic_port_program"},child_program),
     (@{term "fixture_child_shift::nat"},HOLogic.mk_number @{typ nat} child_shift),
     (@{term "fixture_parent::comma_frontier24_closure"},parent)]
    @{term "\<lparr>cf24_programs=[fixture_child_program,Comma_Near_Boundary_Program 1],
      cf24_selectors=[Comma_Frontier24_Near_Selector 0,Comma_Frontier24_Near_Selector 0],
      cf24_action_tokens=[Comma_Continuation_Goto (Comma_Entry 2 0 91) 0],
      cf24_guard_entries=[],cf24_closures=[
        \<lparr>cf24_closure_program_ref=0,cf24_closure_full_shift=fixture_child_shift,
          cf24_closure_cases=[],cf24_closure_near_token=None,
          cf24_closure_near_action_output_root=None,cf24_closure_near_child=None,
          cf24_closure_output_root=0\<rparr>,fixture_parent],
      cf24_class_program_refs=[],cf24_class_roots=[],cf24_radices=[],
      cf24_nodes=[Comma_CRT_MDD_Leaf 0],cf24_zero_root=0\<rparr>"}
  val scalar = Comma_Entry_Arithmetic.natural_context ctxt
    |> Simplifier.add_simps @{thms comma_frontier24_parametric_bundle.select_convs
      list.simps list.size list.map nth_Cons_0 nth_Cons_Suc nth_Cons'
      comma_phase_program_sector.simps comma_entry_core_common_rules
      comma_phase_core_of_modulus_def comma_semantic_port_program_of_source_def
      comma_source_continuation_base.simps comma_canonical_position_admitted_def
      comma_sector_entry_bound_def comma_entry_control_program_def
      comma_near_control_program_def comma_shift_position.simps}
  fun recipe source_bundle = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
    (@{term comma_frontier24_selector_recipe_matches} $ program $ selector $
      (@{term "cf24_action_tokens :: comma_frontier24_parametric_bundle \<Rightarrow>
        comma_source_continuation_action list"} $ source_bundle)))
    (fn _ => Code_Simp.dynamic_tac ctxt 1)
  fun produce source_bundle =
    Comma_Frontier24_Structure_Proofs.closure_shape ctxt scalar source_bundle
      1 parent program selector (SOME @{term "0::nat"}) (recipe source_bundle) []
  val valid_bundle = bundle expected_child 0
  val exact = produce valid_bundle
  (* Exercise the actual Goto/Some-child scalar consumer, not just a direct
     field selection: the prepared definition must expose the child fields
     before the simplifier visits the selected closure. *)
  val closure_projection = @{term "cf24_closures :: comma_frontier24_parametric_bundle \<Rightarrow>
    comma_frontier24_closure list"} $ valid_bundle
  val projection_theorem = Simplifier.rewrite
    (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps
      @{thms comma_frontier24_parametric_bundle.select_convs})
    (Thm.cterm_of ctxt closure_projection)
  val fixture_closures = HOLogic.dest_list (Thm.term_of (Thm.rhs_of projection_theorem))
  val goto_plan = Comma_Frontier24_Selected_Table_Plan.make ctxt valid_bundle
    (Comma_Frontier24_Literal_Projections.make ctxt valid_bundle) "goto fixture closures"
    @{const_name cf24_closures} @{typ comma_frontier24_closure} 2 (SOME fixture_closures)
  val goto_proc = (case #child_fields goto_plan of SOME proc => proc
    | NONE => error "Goto fixture lacks its child-field converter")
  val nonclosure_projections = Comma_Frontier24_Literal_Projections.make ctxt valid_bundle
    |> filter (fn (name,_) => name <> @{const_name cf24_closures}) |> map #2
  val closure_length = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq
      (@{term "length :: comma_frontier24_closure list \<Rightarrow> nat"} $ closure_projection,
       @{term "2::nat"}))) (fn _ => Code_Simp.dynamic_tac ctxt 1)
  val node_length = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq
      (@{term "length :: nat comma_crt_mdd_node list \<Rightarrow> nat"} $
        (@{term "cf24_nodes :: comma_frontier24_parametric_bundle \<Rightarrow> nat comma_crt_mdd_node list"} $
          valid_bundle), @{term "1::nat"}))) (fn _ => Code_Simp.dynamic_tac ctxt 1)
  val goto_scalar = scalar
    |> Simplifier.del_simps @{thms comma_frontier24_parametric_bundle.select_convs}
    |> Simplifier.add_simps nonclosure_projections
    |> Simplifier.add_simps [closure_length,node_length]
    |> Simplifier.add_proc goto_proc
    |> Simplifier.add_simp (Comma_Frontier24_Structure_Proofs.scalar_definition ctxt)
    |> Simplifier.add_simps @{thms comma_frontier24_closure.select_convs
      comma_source_continuation_action.simps comma_finite_position.simps
      option.simps prod.case Let_def}
  val goto_predicate = @{term comma_frontier24_action_output_linked_scalar} $ valid_bundle $
    @{term "1::nat"} $ @{term "1::nat"} $ @{term "0::nat"} $ @{term "0::nat"} $
    @{term "0::nat"} $ @{term "Some (0::nat)"}
  val goto_checked = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop goto_predicate)
    (fn _ => ALLGOALS (asm_full_simp_tac goto_scalar))
  val _ = if String.isSubstring "child_field_success=0" (#stats goto_plan ())
    then error "Goto scalar consumer bypassed the child-field converter" else ()
  val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
    "Goto scalar child-field consumer" [goto_checked]
  fun reject label source_bundle =
    if Exn.is_exn (Exn.capture produce source_bundle) then ()
    else error ("Goto producer accepted " ^ label)
  val _ = reject "wrong child program"
    (bundle @{term "Comma_Entry_Core_Program 2 1 90 Comma_Core_13"} 0)
  val _ = reject "wrong child shift" (bundle expected_child 1)
  fun wrong_link source_bundle =
    let val predicate = @{term comma_frontier24_action_output_linked} $ source_bundle $
      @{term "1::nat"} $ parent $ @{term "0::nat"} $ @{term "0::nat"} $
      @{term "Some (0::nat)"}
    in Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (HOLogic.mk_not predicate))
      (fn _ => Code_Simp.dynamic_tac ctxt 1) end
  val negative = [wrong_link (bundle @{term "Comma_Entry_Core_Program 2 1 90 Comma_Core_13"} 0),
    wrong_link (bundle expected_child 1)]
  val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
    "Source-bound Goto closure producer" (exact::negative)
in end

(* One real admitted source crosses into an already represented child.
   These are bounded linkage checks, not a replay of the source compiler. *)
local
  val ctxt = @{context}
  val child_program = @{term "Comma_Near_Residual_Program 2 9 9"}
  val parent = @{term "\<lparr>cf24_closure_program_ref=1,cf24_closure_full_shift=0,
    cf24_closure_cases=[],cf24_closure_near_token=Some 0,
    cf24_closure_near_action_output_root=Some 0,cf24_closure_near_child=Some 0,
    cf24_closure_output_root=0\<rparr>"}
  fun make_bundle program shift =
    Term.subst_free
      [(@{term "fixture_child_program::comma_semantic_port_program"},program),
       (@{term "fixture_child_shift::nat"},HOLogic.mk_number @{typ nat} shift),
       (@{term "fixture_parent::comma_frontier24_closure"},parent)]
      @{term "\<lparr>cf24_programs=[fixture_child_program,Comma_Near_Boundary_Program 1],
        cf24_selectors=[],cf24_action_tokens=[Comma_Continuation_Goto (Comma_Near 2 0 11) 2],
        cf24_guard_entries=[],cf24_closures=[
          \<lparr>cf24_closure_program_ref=0,cf24_closure_full_shift=fixture_child_shift,
            cf24_closure_cases=[],cf24_closure_near_token=None,
            cf24_closure_near_action_output_root=None,cf24_closure_near_child=None,
            cf24_closure_output_root=0\<rparr>,fixture_parent],
        cf24_class_program_refs=[],cf24_class_roots=[],cf24_radices=[],
        cf24_nodes=[Comma_CRT_MDD_Leaf 0],cf24_zero_root=0\<rparr>"}
  fun proposition bundle child = HOLogic.mk_Trueprop
    (@{term comma_frontier24_action_output_linked} $ bundle $
      @{term "1::nat"} $ parent $ @{term "0::nat"} $ @{term "0::nat"} $ child)
  fun prove bundle child = Goal.prove ctxt [] [] (proposition bundle child)
    (fn _ => Code_Simp.dynamic_tac ctxt 1)
  val child0 = @{term "Some (0::nat)"}
  val correct = prove (make_bundle child_program 2) child0
  fun reject label thunk =
    if Exn.is_exn (Exn.capture thunk ()) then ()
    else error ("Goto linkage fixture accepted " ^ label)
  val _ = reject "wrong child index" (fn () =>
    prove (make_bundle child_program 2) @{term "Some (1::nat)"})
  val _ = reject "wrong child source program" (fn () =>
    prove (make_bundle @{term "Comma_Near_Residual_Program 2 9 8"} 2) child0)
  val _ = reject "wrong child shift" (fn () =>
    prove (make_bundle child_program 3) child0)
  fun disprove bundle child =
    let val predicate = HOLogic.dest_Trueprop (proposition bundle child)
    in Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (HOLogic.mk_not predicate))
      (fn _ => Code_Simp.dynamic_tac ctxt 1) end
  val negative_facts =
    [disprove (make_bundle child_program 2) @{term "Some (1::nat)"},
     disprove (make_bundle @{term "Comma_Near_Residual_Program 2 9 8"} 2) child0,
     disprove (make_bundle child_program 3) child0]
  val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
    "Admitted Goto source and shifted child linkage" (correct::negative_facts)
in end
