(* Indexed request coverage uses checked named rows and rejects missing facts. *)
structure Comma_Frontier24_Indexed_Requests_Fixture =
struct
  fun run lthy =
    let
      val entry = @{term "\<lparr>cf24_closure_program_ref=0,cf24_closure_full_shift=0,
        cf24_closure_cases=[\<lparr>cf24_closure_case_wanted=0,
          cf24_closure_case_guard_root=1,cf24_closure_case_shifted_guard_root=2,
          cf24_closure_case_action_token=0,cf24_closure_case_action_output_root=3,
          cf24_closure_case_child=None\<rparr>],cf24_closure_near_token=None,
        cf24_closure_near_action_output_root=None,cf24_closure_near_child=None,
        cf24_closure_output_root=4\<rparr>"}
      val near = @{term "\<lparr>cf24_closure_program_ref=1,cf24_closure_full_shift=0,
        cf24_closure_cases=[],cf24_closure_near_token=Some 0,
        cf24_closure_near_action_output_root=Some 0,cf24_closure_near_child=None,
        cf24_closure_output_root=0\<rparr>"}
      val (owner,lthy') = Comma_CRT_Balanced_Table.make "indexed_requests_fixture"
        @{typ comma_frontier24_closure} [entry,near] lthy
      val ctxt = Local_Theory.target_of lthy'
      val bundle = Term.subst_free
        [(@{term "fixture_closures::comma_frontier24_closure list"},#table owner)]
        @{term "\<lparr>cf24_programs=[],cf24_selectors=[],cf24_action_tokens=[],
          cf24_guard_entries=[],cf24_closures=fixture_closures,
          cf24_class_program_refs=[],cf24_class_roots=[],cf24_radices=[],
          cf24_nodes=[],cf24_zero_root=0\<rparr>"}
      val projections = Comma_Frontier24_Literal_Projections.make ctxt bundle
      val plan = Comma_Frontier24_Selected_Table_Plan.make_balanced ctxt bundle projections
        "indexed fixture closures" @{const_name cf24_closures}
        @{typ comma_frontier24_closure} 2 owner
      val shift_pred = @{term fixture_indexed_shift}
      val multi_pred = @{term fixture_indexed_multiway}
      fun fact predicate item = Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop (Envir.beta_norm (predicate $ item)))
        (fn {context,...} => simp_tac (context |> Simplifier.add_simps
          @{thms fixture_indexed_shift_def fixture_indexed_multiway_def}) 1)
      val shift_fact = fact shift_pred @{term "(0::nat,1::nat,2::nat)"}
      val multi_fact = fact multi_pred @{term "([(2::nat,3::nat)],0::nat,4::nat)"}
      fun prove label predicate facts intro =
        Comma_Frontier24_Bundle_Publisher.indexed_requests ctxt projections label predicate
          facts bundle owner plan intro
      val shift = prove "fixture shift" shift_pred [shift_fact]
        @{thm comma_frontier24_shift_requests_from_indexed}
      val multi = prove "fixture multiway" multi_pred [multi_fact]
        @{thm comma_frontier24_multiway_requests_from_indexed}
      fun missing label operation =
        (case Exn.capture operation () of Exn.Exn _ => ()
        | Exn.Res _ => error (label ^ " accepted a missing request fact"))
      val _ = missing "Shift coverage" (fn () => prove "missing shift" shift_pred []
        @{thm comma_frontier24_shift_requests_from_indexed})
      val _ = missing "Multiway coverage" (fn () => prove "missing multiway" multi_pred []
        @{thm comma_frontier24_multiway_requests_from_indexed})
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Indexed request coverage" [shift,multi]
    in lthy' end
end

structure Comma_Frontier24_Program_Admission_Fixture =
struct
  fun run lthy =
    let
      val programT = @{typ comma_semantic_port_program}
      val rows = [@{term "Comma_Near_Boundary_Program 1"},
        @{term "Comma_Near_Boundary_Program 2"}]
      val (owner,lthy1) = Comma_CRT_Balanced_Table.make "program_admission_fixture"
        programT rows lthy
      val ctxt = Local_Theory.target_of lthy1
      fun bundle table = Term.subst_free
        [(@{term "fixture_programs::comma_semantic_port_program list"},table)]
        @{term "\<lparr>cf24_programs=fixture_programs,cf24_selectors=[],cf24_action_tokens=[],
          cf24_guard_entries=[],cf24_closures=[],cf24_class_program_refs=[],
          cf24_class_roots=[],cf24_radices=[],cf24_nodes=[],cf24_zero_root=0\<rparr>"}
      val value = bundle (#table owner)
      val projections = Comma_Frontier24_Literal_Projections.make ctxt value
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
      fun prove table_owner fields = Comma_Frontier24_Structure_Proofs.program_admission
        ctxt scalar value fields table_owner
      val admitted = prove owner projections
      fun rejects label f = (case Exn.capture f () of Exn.Exn _ => ()
        | Exn.Res _ => error (label ^ " unexpectedly accepted"))
      val bad_projection = map (fn (field,theorem) =>
        if field = @{const_name cf24_programs}
        then (field,Thm.reflexive (Thm.cterm_of ctxt (#table owner)))
        else (field,theorem)) projections
      val _ = rejects "Wrong program projection" (fn () => prove owner bad_projection)
      val (invalid,lthy2) = Comma_CRT_Balanced_Table.make "program_admission_invalid"
        programT [@{term "Comma_Near_Boundary_Program 0"}] lthy1
      val ctxt2 = Local_Theory.target_of lthy2
      val bad_bundle = bundle (#table invalid)
      val bad_fields = Comma_Frontier24_Literal_Projections.make ctxt2 bad_bundle
      val _ = rejects "Inadmissible program" (fn () =>
        Comma_Frontier24_Structure_Proofs.program_admission ctxt2
          (Comma_Entry_Arithmetic.natural_context ctxt2) bad_bundle bad_fields invalid)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt2
        "Balanced program admission" [admitted]
    in lthy2 end
end

structure Comma_Frontier24_Class_Root_Fixture =
struct
  fun run lthy =
    let
      val closureT = @{typ comma_frontier24_closure}
      val first = @{term "\<lparr>cf24_closure_program_ref=3,cf24_closure_full_shift=0,
        cf24_closure_cases=[],cf24_closure_near_token=None,
        cf24_closure_near_action_output_root=None,cf24_closure_near_child=None,
        cf24_closure_output_root=5\<rparr>"}
      val second = @{term "\<lparr>cf24_closure_program_ref=4,cf24_closure_full_shift=1,
        cf24_closure_cases=[],cf24_closure_near_token=None,
        cf24_closure_near_action_output_root=None,cf24_closure_near_child=None,
        cf24_closure_output_root=6\<rparr>"}
      val (owner,lthy') = Comma_CRT_Balanced_Table.make "class_root_fixture" closureT
        [first,second] lthy
      val ctxt = Local_Theory.target_of lthy'
      val bundle = Term.subst_free
        [(@{term "fixture_closures::comma_frontier24_closure list"},#table owner)]
        @{term "\<lparr>cf24_programs=[],cf24_selectors=[],cf24_action_tokens=[],
          cf24_guard_entries=[],cf24_closures=fixture_closures,
          cf24_class_program_refs=[3],cf24_class_roots=[5],cf24_radices=[],
          cf24_nodes=[],cf24_zero_root=0\<rparr>"}
      val projections = Comma_Frontier24_Literal_Projections.make ctxt bundle
      val plan = Comma_Frontier24_Selected_Table_Plan.make_balanced ctxt bundle projections
        "class root fixture closures" @{const_name cf24_closures} closureT 2 owner
      val projection = the (AList.lookup (op =) projections @{const_name cf24_closures})
      val extent = Comma_Frontier24_Selected_Table_Plan.projection_size ctxt
        "class root fixture" projection owner
      fun class_plan label field = Comma_Frontier24_Selected_Table_Plan.make ctxt bundle
        projections label field @{typ nat} 1 NONE
      val refs = class_plan "class root fixture refs" @{const_name cf24_class_program_refs}
      val roots = class_plan "class root fixture roots" @{const_name cf24_class_roots}
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_simp extent
        |> fold Simplifier.add_proc [#procedure refs,#post_procedure refs,
          #procedure roots,#post_procedure roots]
      fun selected field = Const (@{const_name nth},@{typ "nat list \<Rightarrow> nat \<Rightarrow> nat"}) $
        (Const (field,@{typ "comma_frontier24_parametric_bundle \<Rightarrow> nat list"}) $ bundle) $
        @{term "0::nat"}
      val ref_term = selected @{const_name cf24_class_program_refs}
      val root_term = selected @{const_name cf24_class_roots}
      fun witness index program root = Comma_Frontier24_Structure_Proofs.class_root_witness
        ctxt scalar bundle plan index program root
      val good = witness 0 ref_term root_term
      fun rejects label f = (case Exn.capture f () of Exn.Exn _ => ()
        | Exn.Res _ => error (label ^ " unexpectedly accepted"))
      val _ = rejects "Wrong class closure index" (fn () => witness 1 ref_term root_term)
      val _ = rejects "Wrong class output" (fn () => witness 0 ref_term @{term "6::nat"})
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Named class root witness" [good]
    in lthy' end
end
