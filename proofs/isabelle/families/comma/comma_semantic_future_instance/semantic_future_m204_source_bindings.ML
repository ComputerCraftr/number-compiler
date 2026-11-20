(* Source-bound physical-root proof producer.  Compiler bindings are only
   requests: every premise below is discharged in the receiving theory. *)
structure Comma_Future_M204_Source_Bindings =
struct
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Selected = Comma_Frontier24_Selected_Table_Plan
  structure Utils = Comma_CRT_MDD_Proof_Utils

  fun certify ctxt (candidate: Comma_Frontier24_Parametric_Runtime.candidate)
      certified (plans: Selected.plan list) =
    let
      val bundle = #bundle candidate
      val result = #result candidate
      val certified = Utils.exact_prop ctxt "Future source closure certificate"
        (HOLogic.mk_Trueprop (@{term comma_frontier24_closure_certified} $ bundle)) certified
      val bindings = Compiler.source_bindings result
      val _ = if length bindings = 16 then ()
        else error "Future source publisher requires exactly 16 source requests"
      val sources = map (fn (source,_,_,_) => source) bindings
      val expected = Comma_Frontier24_Parametric_Runtime.physical_initial_sources ()
      val _ = if ListPair.allEq (op aconv) (sources,expected) then ()
        else error "Future source requests do not match the physical family order"
      val (program_plan,closure_plan) = (case plans of
          [p,_,_,c] => (p,c)
        | _ => error "Future source publisher requires the existing selected table plans")
      val (closure_table,closure_projection) =
        Comma_Frontier24_Selector_Alignment.projection ctxt bundle (#field_projections candidate)
          @{const_name cf24_closures} @{typ comma_frontier24_closure}
      val closure_owner = #named_closures candidate
      val _ = if closure_table aconv #table closure_owner andalso
          length (#rows closure_owner) = length (Compiler.closures result)
        then () else error "Future closure table has an unexpected owner or extent"
      val closure_list = Const (@{const_name cf24_closures},
        @{typ "comma_frontier24_parametric_bundle => comma_frontier24_closure list"}) $ bundle
      val size_const = Const (@{const_name size},fastype_of closure_list --> @{typ nat})
      val extent_goal = HOLogic.mk_Trueprop (HOLogic.mk_eq
        (size_const $ closure_list,HOLogic.mk_number @{typ nat} (length (Compiler.closures result))))
      val extent = Comma_Frontier24_Selected_Table_Plan.projection_size
        ctxt "Future closure extent" closure_projection closure_owner
        |> Utils.exact_prop ctxt "Future closure extent" extent_goal
      val context = Comma_Entry_Arithmetic.natural_context ctxt
        |> fold Simplifier.add_proc
          [#procedure program_plan,#post_procedure program_plan,
           #procedure closure_plan,#post_procedure closure_plan]
        |> Simplifier.add_simps [extent]
        |> Simplifier.add_simps @{thms comma_frontier24_closure.select_convs
             comma_semantic_port_program_of_source_def
             comma_canonical_position_admitted_def comma_round_admitted.simps
             comma_source_continuation_base.simps comma_sector_entry_bound_def
             comma_entry_control_program_def comma_near_control_program_def
             comma_entry_core_common_rules comma_phase_core_of_modulus_def}
      fun publish (source,program_ref,closure_ref,_) =
        let
          val program = List.nth (Compiler.programs result,program_ref)
            handle Subscript => error "Future source program reference is outside its table"
          val phase = Free ("future_source_phase",@{typ nat})
          val rule = Drule.infer_instantiate ctxt
            [(("bundle",0),Thm.cterm_of ctxt bundle),
             (("i",0),Thm.cterm_of ctxt (HOLogic.mk_number @{typ nat} closure_ref)),
             (("source",0),Thm.cterm_of ctxt source),
             (("program",0),Thm.cterm_of ctxt program),
             (("phase",0),Thm.cterm_of ctxt phase)]
            @{thm comma_future_m204_source_closure_physical_round}
          val conclusion = Logic.strip_assums_concl (Thm.prop_of rule)
          val theorem = Goal.prove ctxt [] [] conclusion (fn {context=proof_ctxt,...} =>
            resolve_tac proof_ctxt [rule] 1 THEN
            resolve_tac proof_ctxt [certified] 1 THEN
            ALLGOALS (asm_full_simp_tac context))
          val _ = if Thm.prop_of theorem aconv conclusion then ()
            else error "Future physical source closure proves a different proposition"
          val closed = Thm.forall_intr (Thm.cterm_of ctxt phase) theorem
        in Utils.ensure_closed_context ctxt "Future physical source closure" closed end
      val theorems = map publish bindings
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Future physical source bindings" theorems
    in theorems end
end
