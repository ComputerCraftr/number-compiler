theory Comma_Frontier24_Certificate_Smoke
  imports Comma_Semantic_B1.Comma_CRT_MDD_Certificates
    Comma_Semantic_B1.Comma_CRT_MDD_Transport
    Comma_Semantic_B1.Comma_Parametric_Continue_Constructors
    Comma_Semantic_B1.Comma_Parametric_Typed_Output
    Comma_Semantic_B1.Comma_Frontier_M204_Generic
    Comma_Semantic_B1.Comma_Frontier_M204_Checker
    Comma_Semantic_B1.Comma_Frontier_M204_Direct_Source_Morphism
    Comma_Semantic_B1.Comma_CRT_MDD_Zip
    Comma_Semantic_B1.Comma_Direct_Action_Constructors
    Comma_Semantic_B1.Comma_Direct_Action_MDD
    Comma_Semantic_B1.Comma_Direct_Action_Simulation
    Comma_Semantic_B1.Comma_Direct_Bellman_Projection
begin

lemma m204_terminal_code_fixture:
  "comma_frontier_m204_code_bellman (\<lambda>_ _. 0) (\<lambda>_ _. 47)"
  by (simp add: comma_frontier_m204_code_bellman_def)

lemma m204_wrong_terminal_code_rejected:
  "\<not> comma_frontier_m204_code_bellman (\<lambda>_ _. 0) (\<lambda>_ _. 48)"
proof
  assume alleged: "comma_frontier_m204_code_bellman (\<lambda>_ _. 0) (\<lambda>_ _. 48)"
  show False
    using alleged[unfolded comma_frontier_m204_code_bellman_def, rule_format, of 0 0]
    by simp
qed

lemma m204_nondecreasing_continue_rejected:
  "\<not> comma_frontier_m204_code_bellman (\<lambda>_ _. 0) (\<lambda>_ _. 1)"
proof
  assume alleged: "comma_frontier_m204_code_bellman (\<lambda>_ _. 0) (\<lambda>_ _. 1)"
  show False
    using alleged[unfolded comma_frontier_m204_code_bellman_def, rule_format, of 0 0]
    by simp
qed

lemma m204_excess_weight_rejected:
  "\<not> comma_frontier_m204_code_bellman (\<lambda>_ _. 243) (\<lambda>_ _. 47)"
proof
  assume alleged: "comma_frontier_m204_code_bellman (\<lambda>_ _. 243) (\<lambda>_ _. 47)"
  show False
    using alleged[unfolded comma_frontier_m204_code_bellman_def, rule_format, of 0 0]
    by simp
qed

lemma m204_nonzero_terminal_shift_rejected:
  "comma_frontier_m204_action_code 5 (Comma_Phase_Class_Fork 2 1) = 0 \<and>
   comma_frontier_m204_action_code 5 (Comma_Phase_Class_Landmine 1) = 0"
  by simp

lemma m204_receiving_phase_checked:
  "comma_frontier_m204_action_code 5 (Comma_Phase_Class_Continue 6 7) = 8 \<and>
   comma_frontier_m204_action_code 6 (Comma_Phase_Class_Continue 6 7) = 0"
  by simp

lemma m204_typed_lift_requires_continue_bound:
  "comma_parametric_typed_mask_code (Comma_Phase_Rank_Mask_Continue 46) = 47 \<and>
   comma_frontier_m204_action_code 0
     (comma_phase_rank_mask_lift 0 (Comma_Phase_Rank_Mask_Continue 46)) = 0"
  by simp

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "M204 typed terminal and descent boundary fixtures"
    @{thms m204_terminal_code_fixture m204_wrong_terminal_code_rejected
      m204_nondecreasing_continue_rejected m204_excess_weight_rejected
      m204_nonzero_terminal_shift_rejected m204_receiving_phase_checked
      m204_typed_lift_requires_continue_bound};
\<close>

ML_file "../comma_semantic_b1_instance/semantic_frontier24_parametric_compiler.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_parametric_runtime.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_entry_arithmetic.ML"
ML_file "semantic_frontier24_literal_projections.ML"
ML_file "../comma_semantic_b1_instance/semantic_crt_mdd_point_eval.ML"
ML_file "semantic_crt_mdd_point_eval_fixture.ML"
ML_file "semantic_crt_mdd_priority_fixture.ML"
ML \<open>Comma_CRT_MDD_Priority_Fixture.run ()\<close>
local_setup \<open>Comma_CRT_MDD_Point_Eval_Fixture.run\<close>
ML_file "../comma_semantic_b1_instance/semantic_frontier24_mdd_import_certificates.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_action_proposal.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_mdd_proposal.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_terminal_proofs.ML"
ML_file "semantic_direct_terminal_fixture.ML"
ML \<open>Comma_Direct_Terminal_Fixture.run @{context}\<close>
ML_file "../comma_semantic_future_instance/semantic_future_zip_producer.ML"
ML_file "../comma_semantic_future_instance/semantic_future_zip_certificates.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_bellman_terminal_proposal.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_bellman_terminal_proofs.ML"
ML_file "semantic_direct_bellman_indexed_shift_fixture.ML"
local_setup \<open>Comma_Direct_Bellman_Indexed_Shift_Fixture.run\<close>
ML_file "semantic_future_zip_producer_fixture.ML"
local_setup \<open>Comma_Semantic_Future_Zip_Producer_Fixture.run\<close>

ML_file "balanced_table_fixture.ML"
local_setup \<open>Comma_Balanced_Table_Fixture.run\<close>
ML_file "../comma_semantic_future_instance/semantic_future_m204_join_proposal.ML"
ML_file "../comma_semantic_future_instance/semantic_future_m204_graph_proposal.ML"
ML_file "semantic_future_m204_join_smoke.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier_m204_candidate_data.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier_m204_bellman_proposal.ML"
ML_file "semantic_frontier_m204_proposal_fixture.ML"
ML \<open>Comma_Frontier_M204_Proposal_Fixture.run ()\<close>
ML_file "../comma_semantic_b1_instance/semantic_frontier_m204_bellman_certificates.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier_m204_bulk_publisher.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier_m204_source_transport.ML"
ML_file "semantic_frontier_m204_certified_fixture.ML"
local_setup \<open>Comma_Frontier_M204_Certified_Fixture.run\<close>
ML_file "semantic_frontier_m204_source_transport_fixture.ML"
local_setup \<open>Comma_Frontier_M204_Source_Transport_Fixture.run\<close>
ML_file "../comma_semantic_b1_instance/semantic_frontier_m204_weight_owner.ML"
ML_file "semantic_frontier_m204_weight_owner_fixture.ML"
local_setup \<open>Comma_Frontier_M204_Weight_Owner_Fixture.run\<close>
ML_file "../comma_semantic_b1_instance/semantic_frontier24_selected_table_plan.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_selector_alignment.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_entry_row_plan.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_row_bindings.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_entry_bindings.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_program_bindings.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_class_bindings.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_selector_proofs.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_structure_proofs.ML"
ML_file "../comma_semantic_b1/crt_mdd_multiway_replay.ML"
ML_file "../comma_semantic_b1_instance/semantic_direct_mdd_evaluation.ML"
ML_file "semantic_direct_mdd_fixture.ML"
local_setup \<open>Comma_Direct_MDD_Fixture.run\<close>
ML_file "semantic_crt_mdd_priority_checked_fixture.ML"
local_setup \<open>Comma_CRT_MDD_Priority_Checked_Fixture.run\<close>
ML_file "../comma_semantic_b1_instance/semantic_frontier24_bundle_publisher.ML"
ML_file "semantic_direct_program_bindings_fixture.ML"
local_setup \<open>Comma_Direct_Program_Bindings_Fixture.run\<close>
definition fixture_indexed_shift :: "nat \<times> nat \<times> nat \<Rightarrow> bool" where
  "fixture_indexed_shift x \<longleftrightarrow> x=(0,1,2)"
definition fixture_indexed_multiway :: "(nat \<times> nat) list \<times> nat \<times> nat \<Rightarrow> bool" where
  "fixture_indexed_multiway x \<longleftrightarrow> x=([(2,3)],0,4)"
ML_file "semantic_frontier24_indexed_requests_fixture.ML"
local_setup \<open>Comma_Frontier24_Indexed_Requests_Fixture.run\<close>
local_setup \<open>Comma_Frontier24_Program_Admission_Fixture.run\<close>
local_setup \<open>Comma_Frontier24_Class_Root_Fixture.run\<close>
ML_file "semantic_frontier24_closure_contract_fixture.ML"
ML \<open>Comma_Frontier24_Closure_Contract_Fixture.run @{context}\<close>
ML_file "semantic_frontier24_reference_selector.ML"
ML_file "semantic_frontier24_structure_smoke.ML"
local_setup \<open>run_frontier24_structure_aggregation_fixture\<close>
ML_file "semantic_frontier24_order_regression.ML"

definition comma_frontier24_unselected_trap_action ::
    "nat \<Rightarrow> comma_source_continuation_action" where
  "comma_frontier24_unselected_trap_action n = Comma_Continuation_Invalid"

definition comma_frontier24_locator_code_smoke :: bool where
  "comma_frontier24_locator_code_smoke =
    (comma_entry_port_refined_locator 1 0 0 = Some (9,0,91))"

definition comma_frontier24_entry_action_code_smoke ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_phase_core_id \<Rightarrow>
      nat \<Rightarrow> comma_source_continuation_action \<Rightarrow> bool" where
  "comma_frontier24_entry_action_code_smoke f residue core wanted expected =
    (comma_phase_program_entry_core_value_action f residue core wanted = expected)"

definition comma_frontier24_lookup_code_smoke ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_lookup_code_smoke bundle =
    (cf24_programs bundle ! 0 = Comma_Near_Boundary_Program 9)"

definition comma_frontier24_lookup_index2_code_smoke ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_lookup_index2_code_smoke bundle =
    (cf24_programs bundle ! 2 = Comma_Near_Boundary_Program 2)"

definition comma_frontier24_core_support_code_smoke :: bool where
  "comma_frontier24_core_support_code_smoke =
    (comma_core_supported_values Comma_Core_23 = [1..<23])"

definition comma_frontier24_transport_code_smoke ::
    "comma_frontier24_parametric_bundle \<Rightarrow> bool" where
  "comma_frontier24_transport_code_smoke bundle =
    comma_frontier24_selector_recipe_matches
      (cf24_programs bundle ! 0) (cf24_selectors bundle ! 0)
      (cf24_action_tokens bundle)"

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val thy = Proof_Context.theory_of ctxt
      val certificate = Code.get_cert ctxt []
        @{const_name comma_phase_program_entry_core_value_action}
      val (_,equations) = Code.equations_of_cert thy certificate
      val (rhs,theorem) = (case equations of
          SOME [((_,(_,rhs)),(SOME theorem,_))] => (rhs,theorem)
        | _ => error "Entry action has unexpected executable equations")
      val _ = if Term.exists_Const
          (fn (name,_) => name = @{const_name comma_entry_stored_tree_locator}) rhs
        then () else error "Entry action code does not use the stored tree"
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Entry action executable equation" [theorem] end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val program = @{term "Comma_Near_Boundary_Program 2"}
      val changed_program = @{term "Comma_Near_Boundary_Program 3"}
      val action = #operator_action Comma_Frontier24_Parametric_Runtime.computation program
      val _ = if action aconv
          #operator_action Comma_Frontier24_Parametric_Runtime.computation changed_program
        then error "Changed selector fixture has the same action" else ()
      val bundle = Term.subst_free
        [(@{term "fixture_action::comma_source_continuation_action"},action)]
        @{term "\<lparr>cf24_programs=[Comma_Near_Boundary_Program 2],
          cf24_selectors=[Comma_Frontier24_Near_Selector 0],
          cf24_action_tokens=[fixture_action], cf24_guard_entries=[],
          cf24_closures=[], cf24_class_program_refs=[], cf24_class_roots=[],
          cf24_radices=[], cf24_nodes=undefined, cf24_zero_root=0\<rparr>"}
      fun plan label field typ =
        Comma_Frontier24_Selected_Table_Plan.make ctxt bundle (Comma_Frontier24_Literal_Projections.make ctxt bundle)
          label field typ 1 NONE
      val programs = plan "transport_programs" @{const_name cf24_programs}
        @{typ comma_semantic_port_program}
      val selectors = plan "transport_selectors" @{const_name cf24_selectors}
        @{typ comma_frontier24_selector_recipe}
      val actions = plan "transport_actions" @{const_name cf24_action_tokens}
        @{typ comma_source_continuation_action}
      val procedures = maps
        Comma_Frontier24_Selected_Table_Plan.procedures
        [programs,selectors,actions]
      val scalar_request = @{term "(0::nat)<1 \<and> (1::nat)<2 \<and> (2::nat)<3"}
      val scalar_reference = Code_Simp.static_conv
        {ctxt=ctxt,simpset=NONE,
         consts=[@{const_name comma_frontier24_selector_rows_checked}]} ctxt
        (Thm.cterm_of ctxt scalar_request)
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
        "Default selector scalar reference"
        (Logic.mk_equals (scalar_request,@{term True})) scalar_reference
      val scalar = Comma_Frontier24_Reference_Selector.code_true ctxt
        "Selector scalar evaluator"
        @{const_name comma_frontier24_selector_rows_checked} [] []
        scalar_request
      val reference = Comma_Frontier24_Reference_Selector.certify_selector ctxt bundle []
      val selector = Comma_Frontier24_Reference_Selector.certify_selector
        ctxt bundle procedures
      val transport = Comma_Frontier24_Bundle_Publisher.selector_transport
        ctxt bundle selector programs selectors actions
      fun check label candidate = Comma_Frontier24_Reference_Selector.code_true
        ctxt label @{const_name comma_frontier24_transport_code_smoke} []
        (#procedure transport::procedures)
        (@{term comma_frontier24_transport_code_smoke} $ candidate)
      val checked = check "Checked selector inside Code_Simp" bundle
      val hits = #hits transport ()
      val _ = if hits>0 then () else
        error "Code_Simp bypassed checked selector transport"
      val foreign_bundle = Term.subst_free [(program,changed_program)] bundle
      val _ = if foreign_bundle aconv bundle then
        error "Foreign selector fixture did not change the program" else ()
      val rejected = Exn.capture (check "Foreign checked selector") foreign_bundle
      val _ = (case rejected of
          Exn.Exn (ERROR message) =>
            if String.isPrefix "Foreign checked selector did not reduce to True" message
            then () else error message
        | _ => error "Checked selector transport admitted a foreign program")
      val _ = if #hits transport ()=hits then () else
        error "A foreign program consumed the checked selector theorem"
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Selector code-form reuse with exact source authority"
      [scalar_reference,scalar,reference,selector,checked] end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val request = @{term comma_frontier24_core_support_code_smoke}
      val reference = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt request)
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
        "Core support dynamic reference" (Logic.mk_equals (request,@{term True})) reference
      val checked = Comma_Frontier24_Reference_Selector.code_true ctxt
        "Core support static evaluator"
        @{const_name comma_frontier24_core_support_code_smoke} [] [] request
      val projected = @{term "comma_core_supported_values Comma_Core_23 = [1..<23]"}
      val selected = Comma_Frontier24_Reference_Selector.code_true ctxt
        "Core support selector evaluator"
        @{const_name comma_frontier24_selector_rows_checked} [] [] projected
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Closed core support evaluation"
      ([reference,checked,selected] @
        @{thms comma_core_value_guard_supported_iff_local_residue
          comma_core_supported_values_residue_image}) end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val bundle = @{term "\<lparr>
        cf24_programs = [Comma_Near_Boundary_Program 9, Comma_Near_Boundary_Program 1],
        cf24_selectors = [], cf24_action_tokens = [], cf24_guard_entries = [],
        cf24_closures = [], cf24_class_program_refs = [], cf24_class_roots = [],
        cf24_radices = [], cf24_nodes = undefined, cf24_zero_root = 0\<rparr>"}
      val program = @{term "Comma_Near_Boundary_Program 9"}
      val plan = Comma_Frontier24_Selected_Table_Plan.make ctxt
        bundle (Comma_Frontier24_Literal_Projections.make ctxt bundle) "projection_fixture" @{const_name cf24_programs}
        @{typ comma_semantic_port_program} 2
        (SOME [program,@{term "Comma_Near_Boundary_Program 1"}])
      val request = @{term "\<lambda>b::comma_frontier24_parametric_bundle.
        cf24_programs b ! 0"} $ bundle
        |> Envir.beta_eta_contract
      val context = Comma_Entry_Arithmetic.natural_context ctxt
        |> fold Simplifier.add_proc [#procedure plan,#post_procedure plan]
      val exact = Simplifier.rewrite context (Thm.cterm_of ctxt request)
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
        "Bundle field projection ignores unrelated opaque node data"
        (Logic.mk_equals (request,program)) exact
      val prior_stats = Comma_Frontier24_Selected_Table_Plan.statistics plan
      val checked = Comma_Frontier24_Reference_Selector.code_true ctxt
        "Selected bundle row inside Code_Simp"
        @{const_name comma_frontier24_lookup_code_smoke} []
        (Comma_Frontier24_Selected_Table_Plan.procedures plan)
        (@{term comma_frontier24_lookup_code_smoke} $ bundle)
      val updated_stats = Comma_Frontier24_Selected_Table_Plan.statistics plan
      val _ = if prior_stats<>updated_stats then () else
        error "Code_Simp bypassed selected bundle row reuse"
      val foreign_bundle = Term.subst_free
        [(program,@{term "Comma_Near_Boundary_Program 8"})] bundle
      val _ = if foreign_bundle aconv bundle then
          error "Foreign-row fixture did not change its selected program"
        else ()
      val foreign_result = Exn.capture (fn () =>
        Comma_Frontier24_Reference_Selector.code_true ctxt
          "Foreign code-form selected row"
          @{const_name comma_frontier24_lookup_code_smoke} []
          (Comma_Frontier24_Selected_Table_Plan.procedures plan)
          (@{term comma_frontier24_lookup_code_smoke} $ foreign_bundle)) ()
      val _ = (case foreign_result of
          Exn.Exn (ERROR message) =>
            if String.isPrefix "Foreign code-form selected row did not reduce to True" message
            then () else error message
        | _ => error "A code-form alias admitted a foreign selected row")
      val _ = if updated_stats =
          Comma_Frontier24_Selected_Table_Plan.statistics plan
        then () else error "A foreign code-form row entered the selected-table cache"
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Direct bundle projection and selected row" [exact,checked] end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val bundle = @{term "\<lparr>
        cf24_programs = [Comma_Near_Boundary_Program 9,
          Comma_Near_Boundary_Program 1, Comma_Near_Boundary_Program 2],
        cf24_selectors = [], cf24_action_tokens = [], cf24_guard_entries = [],
        cf24_closures = [], cf24_class_program_refs = [], cf24_class_roots = [],
        cf24_radices = [], cf24_nodes = undefined, cf24_zero_root = 0\<rparr>"}
      val plan = Comma_Frontier24_Selected_Table_Plan.make ctxt
        bundle (Comma_Frontier24_Literal_Projections.make ctxt bundle) "three_program_index2" @{const_name cf24_programs}
        @{typ comma_semantic_port_program} 3 NONE
      val projection = @{term "\<lambda>b::comma_frontier24_parametric_bundle.
        cf24_programs b"} $ bundle |> Envir.beta_eta_contract
      val definition = Conv.rewrs_conv
        (map (fn theorem => theorem RS @{thm eq_reflection})
          @{thms comma_frontier24_parametric_bundle.select_convs})
        (Thm.cterm_of ctxt projection)
      val aliases = Comma_Selected_List_Alias.make
        {ctxt=ctxt,root_definition=definition,
         validate_equation=Comma_Selected_List_Conversion.validate_equation}
      val compact = #canonical_lookup aliases (Thm.rhs_of definition)
      val transport = #canonical_root aliases (Thm.rhs_of definition)
      val _ = if Thm.is_reflexive compact andalso
          Thm.term_of (Thm.rhs_of transport) aconv projection then () else
        error "Lookup values expanded the bundle or lost projection transport"
      val prior_stats = Comma_Frontier24_Selected_Table_Plan.statistics plan
      val checked = Comma_Frontier24_Reference_Selector.code_true ctxt
        "Code-form selector at index two"
        @{const_name comma_frontier24_lookup_index2_code_smoke} []
        (Comma_Frontier24_Selected_Table_Plan.procedures plan)
        (@{term comma_frontier24_lookup_index2_code_smoke} $ bundle)
      val updated_stats = Comma_Frontier24_Selected_Table_Plan.statistics plan
      val _ = if prior_stats <> updated_stats andalso
          not (String.isSubstring "selected_cells=0 " updated_stats) then ()
        else error "Code_Simp did not reuse the third selected program row"
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Three-entry Code_Simp selected-list index two" [compact,transport,checked] end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val arithmetic_ctxt = Comma_Entry_Arithmetic.natural_context ctxt
      val evaluator = Code_Simp.static_conv
        {ctxt=arithmetic_ctxt,
         simpset=SOME (Simplifier.simpset_of arithmetic_ctxt),
         consts=[@{const_name comma_decisive_entry_clock_key_from_core_residue},
           @{const_name comma_semantic_b1_near_control_port_action}]} arithmetic_ctxt
      fun check label request expected =
        let
          val started = Time.now ()
          val evaluated = evaluator (Thm.cterm_of ctxt request)
          val theorem = Thm.transitive evaluated
            (Simplifier.rewrite arithmetic_ctxt (Thm.rhs_of evaluated))
          val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt label
            (Logic.mk_equals (request,expected)) theorem
          val _ = Comma_Proof_Profile.report
            ("Frontier24 arithmetic component=" ^ label ^ " elapsed_ms=" ^
              Comma_Proof_Profile.elapsed_ms started)
        in theorem end
      val key = check "entry-clock-key"
        @{term "comma_decisive_entry_clock_key_from_core_residue 1 0 23 1"}
        @{term "(0::nat,28::nat)"}
      val period = check "entry-period" @{term "comma_finite_period_fast 1 0"}
        @{term "460::nat"}
      val primary = check "entry-primary" @{term "comma_core_primary 460"}
        @{term "20::nat"}
      val seed = check "entry-core-seed" @{term "comma_core_seed 460"}
        @{term "9::nat"}
      val near = check "near-control"
        @{term "comma_semantic_b1_near_control_port_action 1 0 16"}
        @{term "Comma_Continuation_Goto (Comma_Entry 2 0 26) 0"}
      val parameters = Comma_Direct_Entry_Arithmetic.core_parameter_conversion_plan ctxt
      val gcd_visits = Unsynchronized.ref 0
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=Comma_Selected_List_Conversion.validate_equation}
      val gcd_pattern = Comma_Selected_List_Conversion.schematize
        @{term "gcd (parameter_left::nat) parameter_right"}
      fun gcd_trap raises = Simplifier.make_simproc ctxt
        {name="frontier24_recomputed_core_gcd",kind=Simplifier.Congproc true,
         lhss=[gcd_pattern,#plain_alias codec gcd_pattern],
         proc=fn _ => fn _ => fn _ =>
           (gcd_visits := !gcd_visits+1;
            if raises then error "A checked core parameter recomputed its GCD"
            else NONE),identifier=[]}
      val _ = Simplifier.rewrite
        (put_simpset HOL_basic_ss ctxt |> Simplifier.add_proc (gcd_trap false))
        (Thm.cterm_of ctxt @{term "gcd (460::nat) 100000"})
      val _ = if !gcd_visits>0 then () else error "Core GCD poison control did not fire"
      val _ = gcd_visits:=0
      val reuse_ctxt = arithmetic_ctxt
        |> Simplifier.add_proc (#procedure parameters)
        |> Simplifier.add_proc (gcd_trap true)
      val reuse = Code_Simp.static_conv
        {ctxt=reuse_ctxt,simpset=SOME (Simplifier.simpset_of reuse_ctxt),
         consts=[@{const_name comma_decisive_entry_clock_key_from_core_residue}]} reuse_ctxt
      val started = Time.now ()
      val reused = reuse (Thm.cterm_of ctxt
        @{term "comma_decisive_entry_clock_key_from_core_residue 1 0 23 1"})
      val reused = Thm.transitive reused
        (Simplifier.rewrite arithmetic_ctxt (Thm.rhs_of reused))
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Reused core clock key"
        (Thm.prop_of key) reused
      val _ = if #hits parameters ()>0 andalso !gcd_visits=0 then () else
        error "Core parameter proof reuse bypassed its theorem or reconstructed a GCD"
      val _ = Comma_Proof_Profile.report
        ("Frontier24 arithmetic component=checked-entry-clock-key elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started)
      val fallback_ctxt = arithmetic_ctxt |> Simplifier.add_proc (#procedure parameters)
      val fallback = Code_Simp.static_conv
        {ctxt=fallback_ctxt,simpset=SOME (Simplifier.simpset_of fallback_ctxt),
         consts=[@{const_name comma_core_primary}]} fallback_ctxt
      val before_hits = #hits parameters ()
      val unsupported = fallback (Thm.cterm_of ctxt @{term "comma_core_primary 30"})
      val unsupported = Thm.transitive unsupported
        (Simplifier.rewrite arithmetic_ctxt (Thm.rhs_of unsupported))
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Unlisted core fallback"
        (Logic.mk_equals (@{term "comma_core_primary 30"},@{term "10::nat"})) unsupported
      val _ = if #hits parameters ()=before_hits then () else
        error "Unlisted core consumed an unrelated parameter theorem"
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Entry clock and Near action independent arithmetic fixtures"
      [key,period,primary,seed,near,reused,unsupported] end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val plan = Comma_Direct_Entry_Arithmetic.fixed_entry_port_conversion_plan ctxt
      val scope = put_simpset HOL_basic_ss ctxt |> Simplifier.add_proc (#procedure plan)
      fun unchanged input =
        let
          val theorem = Simplifier.rewrite scope (Thm.cterm_of ctxt input)
          val actual = Thm.term_of (Thm.rhs_of theorem)
        in if actual aconv input then () else
          error ("Fixed Entry port simproc rewrote a rejected request: " ^
            Syntax.string_of_term ctxt input) end
      val _ = unchanged @{term "comma_entry_port_potential (f::nat) 1"}
      val _ = unchanged @{term "comma_entry_port_potential 0 1"}
      val _ = unchanged @{term "comma_entry_port_potential 1 10"}
      val request = @{term "comma_entry_port_potential (0+1) 0"}
      val exact = Simplifier.rewrite scope (Thm.cterm_of ctxt request)
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=Comma_Selected_List_Conversion.validate_equation}
      val decode = #decode codec (Thm.rhs_of exact)
      val decoded = Thm.transitive exact decode
      val normalized = Simplifier.rewrite
        (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of decoded)
      val actual = Thm.transitive decoded normalized
      val raw_reference = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt request)
      val reference_decode = #decode codec (Thm.rhs_of raw_reference)
      val reference = Thm.transitive raw_reference reference_decode
      val reference_normalized = Simplifier.rewrite
        (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of reference)
      val expected = Thm.transitive reference reference_normalized
      val _ = if Thm.term_of (Thm.rhs_of actual) aconv
          Thm.term_of (Thm.rhs_of expected) then () else
        error "Fixed Entry port alias produced a different result"
      val stats = #statistics plan ()
      val _ = if String.isSubstring "fixed_entry_port_proofs=1" stats andalso
          String.isSubstring "fixed_entry_port_rewrites=1" stats then () else
        error ("Fixed Entry port guard or alias was bypassed: " ^ stats)
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Fixed Entry port guard and alias" [actual,expected] end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val plan = Comma_Direct_Entry_Arithmetic.fixed_entry_port_conversion_plan ctxt
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=Comma_Selected_List_Conversion.validate_equation}
      fun check request =
        let
          val raw = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt request)
          val decoded = #decode codec (Thm.rhs_of raw)
          val reference = Thm.transitive raw decoded
          val normalized = Simplifier.rewrite
            (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of reference)
          val exact = Thm.transitive reference normalized
          val (_,args) = strip_comb request
          val predicate = Term.list_comb
            (@{term comma_frontier24_entry_action_code_smoke},
             args @ [Thm.term_of (Thm.rhs_of exact)])
          val checked = Comma_Frontier24_Reference_Selector.code_true ctxt
            "Fixed Entry action result and port facts"
            @{const_name comma_frontier24_entry_action_code_smoke} []
            [#procedure plan] predicate
        in [exact,checked] end
      val cases = [
        @{term "comma_phase_program_entry_core_value_action 1 0 Comma_Core_23 1"},
        @{term "comma_phase_program_entry_core_value_action 6 2 Comma_Core_23 3"},
        @{term "comma_phase_program_entry_core_value_action 9 2 Comma_Core_3 1"}]
      val facts = maps check cases
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Fixed Entry action test" facts end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=Comma_Selected_List_Conversion.validate_equation}
      fun check value =
        let
          val alias = #explicit_alias codec value
          val theorem = #decode codec (Thm.cterm_of ctxt alias)
          val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
            "Signed code numeral alias" (Logic.mk_equals (alias,value)) theorem
        in theorem end
      val facts = map check
        [@{term "(7::int)"}, @{term "(-7::int)"}, @{term "(0::int)"}]
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Signed code numeral aliases" facts end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val result = Comma_Frontier24_Parametric_Compiler.compile ctxt
        Comma_Frontier24_Parametric_Runtime.computation
      val computation = Comma_Frontier24_Parametric_Runtime.computation
      val representatives = Comma_Frontier24_Parametric_Compiler.entry_representatives result
      val representative_table = fold Termtab.update representatives Termtab.empty
      fun distinct_request (rep: Comma_Frontier24_Parametric_Compiler.entry_representative)
          (sector,residue,core,wanted) =
        sector <> #sector rep orelse residue <> #residue rep orelse
        not (core aconv #core rep) orelse wanted <> #wanted rep
      fun candidate program =
        (case strip_comb program of
          (Const (name,_),[sector,_,residue,core]) =>
            if name = @{const_name Comma_Entry_Core_Program} then
              let
                val f = Comma_CRT_MDD_Proof_Utils.dest_nat "Fixture sector" @{typ nat} sector
                val r = Comma_CRT_MDD_Proof_Utils.dest_nat "Fixture residue" @{typ nat} residue
                fun select wanted =
                  let
                    val request = (f,r,core,wanted)
                    val key = #entry_action_key computation f r core wanted
                  in case Termtab.lookup representative_table key of
                      SOME rep => if distinct_request rep request
                        then SOME (rep,request) else NONE
                    | NONE => NONE end
              in get_first select (#supported_values computation core) end
            else NONE
        | _ => NONE)
      val (rep,(sector,residue,core,wanted)) =
        (case get_first candidate (Comma_Frontier24_Parametric_Compiler.programs result) of
          SOME request => request
        | NONE => error "No distinct Entry occurrence shares the representative key")
      val plan = Comma_Frontier24_Bundle_Publisher.Selector_Proofs.entry_representative_plan ctxt result
      val first = #transport plan (#sector rep) (#residue rep) (#core rep) (#wanted rep)
      val second = #transport plan sector residue core wanted
      val request = @{term comma_phase_program_entry_core_value_action} $
        HOLogic.mk_number @{typ nat} sector $ HOLogic.mk_number @{typ nat} residue $
        core $ HOLogic.mk_number @{typ nat} wanted
      val expected = #entry_action computation sector residue core wanted
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Distinct Entry occurrence"
        (Logic.mk_equals (request,expected)) second
      val _ = if String.isSubstring "entry_representative_proofs=1 " (#statistics plan ()) andalso
          String.isSubstring "entry_representative_hits=1 " (#statistics plan ()) andalso
          String.isSubstring "entry_row_transports=2" (#statistics plan ()) then ()
        else error "Distinct Entry occurrences did not reuse one representative"
      fun choose predicate label =
        (case List.find (fn (_,candidate) => predicate candidate) representatives of
          SOME (_,candidate) => candidate
        | NONE => error ("Missing Entry representative for " ^ label))
      fun sector_rep n = choose (fn candidate => #sector candidate=n)
        ("sector " ^ Int.toString n)
      fun action_rep name = choose (fn candidate =>
        (case Term.head_of (#action candidate) of
          Const (actual,_) => actual=name | _ => false)) name
      val coverage = map sector_rep (1 upto 9) @
        map action_rep [@{const_name Comma_Continuation_Goto},
          @{const_name Comma_Continuation_Exit}, @{const_name Comma_Continuation_Fork},
          @{const_name Comma_Continuation_Landmine}]
      val coverage_plan =
        Comma_Frontier24_Bundle_Publisher.Selector_Proofs.entry_representative_plan ctxt result
      fun check_coverage (candidate: Comma_Frontier24_Parametric_Compiler.entry_representative) =
        let
          val theorem = #transport coverage_plan (#sector candidate) (#residue candidate)
            (#core candidate) (#wanted candidate)
          val input = @{term comma_phase_program_entry_core_value_action} $
            HOLogic.mk_number @{typ nat} (#sector candidate) $
            HOLogic.mk_number @{typ nat} (#residue candidate) $
            #core candidate $ HOLogic.mk_number @{typ nat} (#wanted candidate)
        in Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Entry sector/action coverage"
          (Logic.mk_equals (input,#action candidate)) theorem end
      val coverage_facts = map check_coverage coverage
      val negative_mod = #transport coverage_plan 1 19 @{term Comma_Core_23} 18
      val negative_request = @{term comma_phase_program_entry_core_value_action} $
        HOLogic.mk_number @{typ nat} 1 $ HOLogic.mk_number @{typ nat} 19 $
        @{term Comma_Core_23} $ HOLogic.mk_number @{typ nat} 18
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Entry negative modular key"
        (Logic.mk_equals (negative_request,#entry_action computation 1 19 @{term Comma_Core_23} 18))
        negative_mod
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Entry row representative transport" (first::second::negative_mod::coverage_facts) end
\<close>

local_setup \<open>fn lthy =>
    let
      val ctxt = Local_Theory.target_of lthy
      val result = Comma_Frontier24_Parametric_Compiler.compile ctxt
        Comma_Frontier24_Parametric_Runtime.computation
      val near = @{term "Comma_Near_Boundary_Program 2"}
      val near_action = #operator_action Comma_Frontier24_Parametric_Runtime.computation near
      val tokens = Comma_Frontier24_Parametric_Compiler.action_tokens result @ [near_action]
      val literal = HOLogic.mk_list @{typ comma_source_continuation_action} tokens
      val ((local_table,(_,local_definition)),lthy') = Local_Theory.define
        ((Binding.name "comma_selector_family_fixture_actions",NoSyn),
         ((Binding.name "comma_selector_family_fixture_actions_def",[]),literal)) lthy
      val morphism = Local_Theory.target_morphism lthy'
      val named = {table=Morphism.term morphism local_table,
        definition=Morphism.thm morphism local_definition}
      val ctxt' = Local_Theory.target_of lthy'
      val empty_nodes = HOLogic.mk_list @{typ "nat comma_crt_mdd_node"} []
      val full = Comma_Frontier24_Parametric_Runtime.serialize ctxt' empty_nodes result named NONE
      val {programs,selectors,...} = Comma_Frontier24_Selector_Alignment.rows ctxt' full (Comma_Frontier24_Literal_Projections.make ctxt' full)
      val pairs = programs ~~ selectors
      fun is_program name (program,_) =
        (case Term.head_of program of Const (actual,_) => actual=name | _ => false)
      fun choose name = (case List.find (is_program name) pairs of
        SOME pair => pair | NONE => error "Missing selector-family fixture program")
      val near_selector = Comma_Frontier24_Parametric_Runtime.app
        @{const_name Comma_Frontier24_Near_Selector}
        @{typ comma_frontier24_selector_recipe}
        [HOLogic.mk_number @{typ nat} (length tokens - 1)]
      val chosen = [choose @{const_name Comma_Entry_Core_Program}, (near,near_selector)]
      val (program_owner,lthy_programs) = Comma_CRT_Balanced_Table.make
        "selector_family_fixture_programs" @{typ comma_semantic_port_program}
        (map #1 chosen) lthy'
      val (selector_owner,lthy'') = Comma_CRT_Balanced_Table.make
        "selector_family_fixture_selectors" @{typ comma_frontier24_selector_recipe}
        (map #2 chosen) lthy_programs
      val ctxt'' = Local_Theory.target_of lthy''
      val fixture = Term.subst_free
        [(@{term "fixture_programs::comma_semantic_port_program list"},
          #table program_owner),
         (@{term "fixture_selectors::comma_frontier24_selector_recipe list"},
          #table selector_owner),
         (@{term "fixture_tokens::comma_source_continuation_action list"},#table named)]
        @{term "\<lparr>cf24_programs=fixture_programs, cf24_selectors=fixture_selectors,
          cf24_action_tokens=fixture_tokens, cf24_guard_entries=[],cf24_closures=[],
          cf24_class_program_refs=[],cf24_class_roots=[],cf24_radices=[],
          cf24_nodes=[],cf24_zero_root=0\<rparr>"}
      val projections = Comma_Frontier24_Literal_Projections.make ctxt'' fixture
      val action_plan = Comma_Frontier24_Selected_Table_Plan.make_named ctxt'' fixture projections
        "selector_family_fixture_actions" @{const_name cf24_action_tokens}
        @{typ comma_source_continuation_action} (length tokens) named tokens
      val program_plan = Comma_Frontier24_Selected_Table_Plan.make_balanced ctxt'' fixture projections
        "selector_family_fixture_programs" @{const_name cf24_programs}
        @{typ comma_semantic_port_program} (length chosen) program_owner
      val selector_plan = Comma_Frontier24_Selected_Table_Plan.make_balanced ctxt'' fixture projections
        "selector_family_fixture_selectors" @{const_name cf24_selectors}
        @{typ comma_frontier24_selector_recipe} (length chosen) selector_owner
      val token_owner = Comma_Frontier24_Bundle_Publisher.Selector_Proofs.token_owner
        ctxt'' (#table named) action_plan
      val facts = Comma_Frontier24_Bundle_Publisher.Selector_Proofs.selector_family_facts
        ctxt'' result fixture projections (map #1 chosen) (map #2 chosen) action_plan token_owner
      val checked = Comma_Frontier24_Selector_Alignment.certify_indexed ctxt'' fixture projections
        (map #1 chosen) program_owner selector_owner program_plan selector_plan facts
      val (goto_index,goto_source) = (case get_first (fn (index,action) =>
        (case strip_comb action of
          (Const (name,_),[source,_]) =>
            if name = @{const_name Comma_Continuation_Goto} then SOME (index,source) else NONE
        | _ => NONE)) (map_index I tokens) of
          SOME result => result | NONE => error "Missing Goto action in selector fixture")
      val _ = #binding token_owner (HOLogic.mk_number @{typ nat} goto_index)
      val source_request = @{term comma_semantic_port_program_of_source} $ goto_source
      val source_context = Comma_Entry_Arithmetic.natural_context ctxt''
        |> Simplifier.add_proc (#procedure token_owner)
        |> Simplifier.add_simps @{thms comma_semantic_port_program_of_source_def
          comma_finite_position.simps option.map option.case prod.case}
      val first_source = Simplifier.rewrite source_context (Thm.cterm_of ctxt'' source_request)
      val second_source = Simplifier.rewrite source_context (Thm.cterm_of ctxt'' source_request)
      val expected_source = (case #source_program
          Comma_Frontier24_Parametric_Runtime.computation goto_source of
        SOME program => Const (@{const_name Some},fastype_of program -->
                            Type (@{type_name option},[fastype_of program])) $ program
      | NONE => error "Missing proposed Goto source program")
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt'' "Goto source fixture exact program"
        (Logic.mk_equals (source_request,expected_source)) first_source
      val _ = if Thm.prop_of first_source aconv Thm.prop_of second_source andalso
          String.isSubstring "source_proofs=1" (#statistics token_owner ()) andalso
          String.isSubstring "source_hits=1" (#statistics token_owner ()) then ()
        else error "Authenticated Goto source refinement was not reused"
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt''
        "Entry and Near indexed selector family" (first_source::second_source::checked::facts)
      val (candidate,lthy''') = Comma_Frontier24_Parametric_Runtime.candidate
        lthy'' empty_nodes result named
      val ctxt''' = Local_Theory.target_of lthy'''
      fun check_projection field table =
        (case AList.lookup (op =) (#field_projections candidate) field of
          SOME theorem => Comma_CRT_MDD_Proof_Utils.exact_prop ctxt'''
            "Production balanced bundle projection"
            (Logic.mk_equals
              (Const (field,@{typ comma_frontier24_parametric_bundle} --> fastype_of table) $
                #bundle candidate,table)) theorem
        | NONE => error "Production balanced bundle projection is missing")
      val selector_projection = check_projection @{const_name cf24_selectors}
        (#table (#named_selectors candidate))
      val program_projection = check_projection @{const_name cf24_programs}
        (#table (#named_programs candidate))
      val closure_projection = check_projection @{const_name cf24_closures}
        (#table (#named_closures candidate))
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt'''
        "Production balanced bundle projections"
        [program_projection,selector_projection,closure_projection]
    in lthy''' end
\<close>

local_setup \<open>fn lthy =>
    let
      val ctxt = Local_Theory.target_of lthy
      val actions = Comma_Frontier24_Parametric_Runtime.computation
      val action = #entry_action actions 1 0 @{term Comma_Core_1} 1
      val poison = @{term "comma_frontier24_unselected_trap_action 0"}
      val action_slot = @{term "fixture_action::comma_source_continuation_action"}
      val poison_slot = @{term "fixture_poison::comma_source_continuation_action"}
      val bundle = Term.subst_free
        [(action_slot,action),(poison_slot,poison)]
        @{term "\<lparr>
          cf24_programs=[], cf24_selectors=[],
          cf24_action_tokens=[fixture_action,fixture_poison],
          cf24_guard_entries=[], cf24_closures=[],
          cf24_class_program_refs=[], cf24_class_roots=[], cf24_radices=[],
          cf24_nodes=[], cf24_zero_root=0\<rparr>"}
      val plan = Comma_Frontier24_Selected_Table_Plan.make ctxt
        bundle (Comma_Frontier24_Literal_Projections.make ctxt bundle) "entry_case_lazy_actions" @{const_name cf24_action_tokens}
        @{typ comma_source_continuation_action} 2 (SOME [action,poison])
      val visits = Unsynchronized.ref 0
      fun poison_procedure name raises = Simplifier.make_simproc ctxt
        {name=name,kind=Simplifier.Simproc,
         lhss=[Comma_Selected_List_Conversion.schematize
           @{term "comma_frontier24_unselected_trap_action trap_argument"}],
         proc=fn _ => fn _ => fn _ =>
           (visits:= !visits+1;
            if raises then error ("Unselected action-table tail was visited: " ^
              Comma_Frontier24_Selected_Table_Plan.statistics plan) else NONE),
         identifier=[]}
      val positive = poison_procedure "frontier24_poison_positive_control" false
      val _ = ignore (Simplifier.rewrite
        (put_simpset HOL_basic_ss ctxt |> Simplifier.add_proc positive)
        (Thm.cterm_of ctxt poison))
      val _ = if !visits>0 then ()
        else error "Unselected-action poison simproc positive control did not fire"
      val _ = visits:=0
      val trap = poison_procedure "frontier24_unselected_action_trap" true
      val predicate = Term.subst_free
        [(@{term "fixture_actions::comma_source_continuation_action list"},
          HOLogic.mk_list @{typ comma_source_continuation_action} [action,poison])]
        @{term "comma_frontier24_selector_case_action_matches
          1 0 Comma_Core_1
          \<lparr>cf24_case_wanted=1,cf24_case_guard_root=0,
            cf24_case_action_token=0\<rparr> fixture_actions"}
      val checked = Comma_Frontier24_Reference_Selector.code_true ctxt
        "Entry case selects action zero without traversing its tail"
        @{const_name comma_frontier24_selector_case_action_matches} []
        (trap::Comma_Frontier24_Selected_Table_Plan.procedures plan)
        predicate
      val _ = if !visits=0 then ()
        else error "Entry case evaluated an unselected action-table tail"
      val _ = if not (String.isSubstring "selected_cells=0 "
            (Comma_Frontier24_Selected_Table_Plan.statistics plan)) then ()
        else error "Entry case did not consume its selected action-table cell"
      val supported_action = #entry_action actions 1 0 @{term Comma_Core_1} 0
      val literal = HOLogic.mk_list @{typ comma_source_continuation_action}
        [supported_action,poison]
      val ((local_table,(_,local_definition)),lthy') = Local_Theory.define
        ((Binding.name "comma_frontier24_named_actions_fixture",NoSyn),
         ((Binding.name "comma_frontier24_named_actions_fixture_def",[]),literal)) lthy
      val morphism = Local_Theory.target_morphism lthy'
      val table = Morphism.term morphism local_table
      val definition = Morphism.thm morphism local_definition
      val named_ctxt = Local_Theory.target_of lthy'
      val named_bundle = Term.subst_free
        [(@{term "fixture_actions::comma_source_continuation_action list"},table)]
        @{term "\<lparr>
          cf24_programs=[Comma_Entry_Core_Program 1 0 0 Comma_Core_1],
          cf24_selectors=[Comma_Frontier24_Entry_Selector 1 0 0 Comma_Core_1
            [\<lparr>cf24_case_wanted=0,cf24_case_guard_root=0,
              cf24_case_action_token=0\<rparr>]],
          cf24_action_tokens=fixture_actions,
          cf24_guard_entries=[],cf24_closures=[],cf24_class_program_refs=[],
          cf24_class_roots=[],cf24_radices=[],cf24_nodes=[],cf24_zero_root=0\<rparr>"}
      val named_plan = Comma_Frontier24_Selected_Table_Plan.make_named
        named_ctxt named_bundle (Comma_Frontier24_Literal_Projections.make named_ctxt named_bundle) "named_actions_fixture" @{const_name cf24_action_tokens}
        @{typ comma_source_continuation_action} 2 {table=table,definition=definition}
        [supported_action,poison]
      val foreign = Exn.capture (fn () =>
        Comma_Frontier24_Selected_Table_Plan.make_named
          named_ctxt named_bundle (Comma_Frontier24_Literal_Projections.make named_ctxt named_bundle) "foreign_named_actions" @{const_name cf24_action_tokens}
          @{typ comma_source_continuation_action} 2
          {table = @{term "[]::comma_source_continuation_action list"},definition=definition}
          [supported_action,poison]) ()
      val _ = (case foreign of Exn.Exn (ERROR _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "Named action definition admitted a foreign root")
      val named_checked = Comma_Frontier24_Reference_Selector.certify_selector
        named_ctxt named_bundle
        (trap::Comma_Frontier24_Selected_Table_Plan.procedures named_plan)
      val _ = if !visits=0 andalso not (String.isSubstring "selected_cells=0 "
          (Comma_Frontier24_Selected_Table_Plan.statistics named_plan)) then ()
        else error "Named selector unfolded an unrequested action or bypassed lookup"
      val programs = Comma_Frontier24_Selected_Table_Plan.make named_ctxt named_bundle (Comma_Frontier24_Literal_Projections.make named_ctxt named_bundle)
        "named_transport_programs" @{const_name cf24_programs}
        @{typ comma_semantic_port_program} 1 NONE
      val selectors = Comma_Frontier24_Selected_Table_Plan.make named_ctxt named_bundle (Comma_Frontier24_Literal_Projections.make named_ctxt named_bundle)
        "named_transport_selectors" @{const_name cf24_selectors}
        @{typ comma_frontier24_selector_recipe} 1 NONE
      val transport = Comma_Frontier24_Bundle_Publisher.selector_transport named_ctxt
        named_bundle named_checked programs selectors named_plan
      val consumed = Comma_Frontier24_Reference_Selector.code_true named_ctxt
        "Named action selector certificate consumption"
        @{const_name comma_frontier24_transport_code_smoke} []
        (#procedure transport::trap::
          maps Comma_Frontier24_Selected_Table_Plan.procedures
            [programs,selectors,named_plan])
        (@{term comma_frontier24_transport_code_smoke} $ named_bundle)
      val _ = if #hits transport ()>0 andalso !visits=0 then () else
        error "Named action selector transport replayed or bypassed its certificate"
      val _ = Comma_Proof_Dependency_Audit.require_native_clean named_ctxt
        "Literal and named action-table selector ownership"
        [checked,named_checked,consumed,definition]
    in
      lthy'
    end
\<close>

ML \<open>
  val _ =
    let
      val ctxt = @{context}
      val codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=fn input => fn theorem =>
          Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Locator reference decoding"
            (Logic.mk_equals (input,Thm.term_of (Thm.rhs_of theorem))) theorem}
      fun evaluate request =
        let
          val raw = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt request)
          val decoded = #decode codec (Thm.rhs_of raw)
          val exact = Thm.transitive raw decoded
          val normalized = Simplifier.rewrite
            (Comma_Entry_Arithmetic.natural_context ctxt) (Thm.rhs_of exact)
          val result = Thm.transitive exact normalized
          val output = Thm.term_of (Thm.rhs_of result)
          fun canonical_nat term =
            (case try HOLogic.dest_number term of
              SOME (T,n) => T = @{typ nat} andalso n >= 0
                andalso term aconv HOLogic.mk_number @{typ nat} n
            | NONE => false)
          val bounded = (case strip_comb output of
              (Const (name,_),[]) => name = @{const_name None}
            | (Const (name,_),[triple]) =>
                name = @{const_name Some} andalso
                (let val (a,bc) = HOLogic.dest_prod triple
                     val (b,c) = HOLogic.dest_prod bc
                 in forall canonical_nat [a,b,c] end)
            | _ => false) handle TERM _ => false
          val _ = if Comma_CRT_MDD_Proof_Utils.closed output andalso
              Term.size_of_term output <= 128 andalso bounded then ()
            else error ("Locator did not return a bounded closed option: " ^
              Syntax.string_of_term ctxt output)
        in result end
      fun compare (original,stored) =
        let
          val expected = evaluate original
          val actual = evaluate stored
          val _ = if Thm.term_of (Thm.rhs_of expected) aconv
              Thm.term_of (Thm.rhs_of actual) then () else
            error ("Stored tree differs from weighted Entry locator: " ^
              Syntax.string_of_term ctxt original ^ " -> " ^
              Syntax.string_of_term ctxt (Thm.term_of (Thm.rhs_of expected)) ^
              "; stored -> " ^
              Syntax.string_of_term ctxt (Thm.term_of (Thm.rhs_of actual)))
        in [expected,actual] end
      val facts = maps compare
        [(@{term "comma_entry_port_refined_locator 1 0 0"},
          @{term "comma_entry_stored_tree_locator 1 0 0"}),
         (@{term "comma_entry_port_refined_locator 2 0 0"},
          @{term "comma_entry_stored_tree_locator 2 0 0"}),
         (@{term "comma_entry_port_refined_locator 1 0 38"},
          @{term "comma_entry_stored_tree_locator 1 0 38"}),
         (@{term "comma_entry_port_refined_locator 9 2 3"},
          @{term "comma_entry_stored_tree_locator 9 2 3"}),
         (@{term "comma_entry_port_refined_locator 6
            (fst (comma_decisive_entry_clock_key_from_core_residue 6 2 23 3))
            (snd (comma_decisive_entry_clock_key_from_core_residue 6 2 23 3))"},
          @{term "comma_entry_stored_tree_locator 6
            (fst (comma_decisive_entry_clock_key_from_core_residue 6 2 23 3))
            (snd (comma_decisive_entry_clock_key_from_core_residue 6 2 23 3))"})]
      val endpoint = evaluate @{term "comma_entry_stored_tree_locator 1 0 38"}
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
        "Six-port Entry stored-tree endpoint"
        @{prop "comma_entry_stored_tree_locator 1 0 38 \<equiv> Some (4,2,16)"}
        endpoint
      val code_fact = Comma_Frontier24_Reference_Selector.code_true ctxt
        "Entry locator inside Code_Simp"
        @{const_name comma_frontier24_locator_code_smoke} [] []
        @{term comma_frontier24_locator_code_smoke}
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Stored-tree and weighted locator equations"
      (endpoint::code_fact::facts) end
\<close>

ML_file "semantic_frontier24_alignment_fixture.ML"

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Exported certificate smoke definitions"
    @{thms comma_frontier24_unselected_trap_action_def
      comma_frontier24_locator_code_smoke_def
      comma_frontier24_entry_action_code_smoke_def
      comma_frontier24_lookup_code_smoke_def
      comma_frontier24_lookup_index2_code_smoke_def
      comma_frontier24_core_support_code_smoke_def
      comma_frontier24_transport_code_smoke_def};
\<close>

end
