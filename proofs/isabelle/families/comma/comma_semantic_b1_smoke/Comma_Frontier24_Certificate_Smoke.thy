theory Comma_Frontier24_Certificate_Smoke
  imports Comma_Semantic_B1.Comma_CRT_MDD_Certificates
    Comma_Semantic_B1.Comma_CRT_MDD_Transport
    Comma_Semantic_B1.Comma_Parametric_Continue_Closure
begin

ML_file "../comma_semantic_b1_instance/semantic_frontier24_mdd_preimage.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_parametric_compiler.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_parametric_runtime.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_mdd_import_certificates.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_selected_table_plan.ML"
ML_file "../comma_semantic_b1_instance/semantic_frontier24_bundle_publisher.ML"

definition comma_frontier24_unselected_trap_action ::
    "nat \<Rightarrow> comma_source_continuation_action" where
  "comma_frontier24_unselected_trap_action n = Comma_Continuation_Invalid"

definition comma_frontier24_locator_code_smoke :: bool where
  "comma_frontier24_locator_code_smoke =
    (comma_entry_port_refined_locator 1 0 0 = Some (9,0,91))"

definition comma_frontier24_locator_code_args_smoke ::
    "(nat * nat * nat) option \<Rightarrow> bool" where
  "comma_frontier24_locator_code_args_smoke expected =
    (comma_entry_port_refined_locator 9 2 3 = expected)"

definition comma_frontier24_locator_computed_key_smoke ::
    "(nat * nat * nat) option \<Rightarrow> bool" where
  "comma_frontier24_locator_computed_key_smoke expected =
    (comma_entry_port_refined_locator 6
      (fst (comma_decisive_entry_clock_key_from_core_residue 6 2 23 3))
      (snd (comma_decisive_entry_clock_key_from_core_residue 6 2 23 3)) = expected)"

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
        Comma_Frontier24_Selected_Table_Plan.make ctxt bundle
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
      val scalar = Comma_Frontier24_Bundle_Publisher.code_true ctxt
        "Selector scalar evaluator"
        @{const_name comma_frontier24_selector_rows_checked} [] []
        scalar_request
      val reference = Comma_Frontier24_Bundle_Publisher.certify_selector ctxt bundle []
      val selector = Comma_Frontier24_Bundle_Publisher.certify_selector
        ctxt bundle procedures
      val transport = Comma_Frontier24_Bundle_Publisher.selector_transport
        ctxt bundle selector programs selectors actions
      fun check label candidate = Comma_Frontier24_Bundle_Publisher.code_true
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
      val checked = Comma_Frontier24_Bundle_Publisher.code_true ctxt
        "Core support static evaluator"
        @{const_name comma_frontier24_core_support_code_smoke} [] [] request
      val projected = @{term "comma_core_supported_values Comma_Core_23 = [1..<23]"}
      val selected = Comma_Frontier24_Bundle_Publisher.code_true ctxt
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
        bundle "projection_fixture" @{const_name cf24_programs}
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
      val checked = Comma_Frontier24_Bundle_Publisher.code_true ctxt
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
        Comma_Frontier24_Bundle_Publisher.code_true ctxt
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
        bundle "three_program_index2" @{const_name cf24_programs}
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
      val checked = Comma_Frontier24_Bundle_Publisher.code_true ctxt
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
      val parameters = Comma_Frontier24_Bundle_Publisher.core_parameter_conversion_plan ctxt
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
        bundle "entry_case_lazy_actions" @{const_name cf24_action_tokens}
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
      val checked = Comma_Frontier24_Bundle_Publisher.code_true ctxt
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
        named_ctxt named_bundle "named_actions_fixture" @{const_name cf24_action_tokens}
        @{typ comma_source_continuation_action} 2 {table=table,definition=definition}
        [supported_action,poison]
      val foreign = Exn.capture (fn () =>
        Comma_Frontier24_Selected_Table_Plan.make_named
          named_ctxt named_bundle "foreign_named_actions" @{const_name cf24_action_tokens}
          @{typ comma_source_continuation_action} 2
          {table = @{term "[]::comma_source_continuation_action list"},definition=definition}
          [supported_action,poison]) ()
      val _ = (case foreign of Exn.Exn (ERROR _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "Named action definition admitted a foreign root")
      val named_checked = Comma_Frontier24_Bundle_Publisher.certify_selector
        named_ctxt named_bundle
        (trap::Comma_Frontier24_Selected_Table_Plan.procedures named_plan)
      val _ = if !visits=0 andalso not (String.isSubstring "selected_cells=0 "
          (Comma_Frontier24_Selected_Table_Plan.statistics named_plan)) then ()
        else error "Named selector unfolded an unrequested action or bypassed lookup"
      val programs = Comma_Frontier24_Selected_Table_Plan.make named_ctxt named_bundle
        "named_transport_programs" @{const_name cf24_programs}
        @{typ comma_semantic_port_program} 1 NONE
      val selectors = Comma_Frontier24_Selected_Table_Plan.make named_ctxt named_bundle
        "named_transport_selectors" @{const_name cf24_selectors}
        @{typ comma_frontier24_selector_recipe} 1 NONE
      val transport = Comma_Frontier24_Bundle_Publisher.selector_transport named_ctxt
        named_bundle named_checked programs selectors named_plan
      val consumed = Comma_Frontier24_Bundle_Publisher.code_true named_ctxt
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
      val memo = Comma_Frontier24_Bundle_Publisher.locator_conversion_plan ctxt
      val conversion_ctxt = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc (#procedure memo)
      val requests =
        [@{term "comma_entry_port_refined_locator 1 0 0"},
         @{term "comma_entry_port_refined_locator 1 0 0"},
         @{term "comma_entry_port_refined_locator (0+1) 0 0"},
         @{term "comma_entry_port_refined_locator 2 0 0"},
         @{term "comma_entry_port_refined_locator 1 0 38"}]
      fun check request =
        let
          val ct = Thm.cterm_of ctxt request
          val raw_reference = Code_Simp.dynamic_conv ctxt ct
          val reference = Thm.transitive raw_reference
            (Simplifier.rewrite (Comma_Entry_Arithmetic.natural_context ctxt)
              (Thm.rhs_of raw_reference))
          val raw_actual = Simplifier.rewrite conversion_ctxt ct
          val actual = Thm.transitive raw_actual
            (Axclass.overload_conv ctxt (Thm.rhs_of raw_actual))
        in Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
          "Exact locator argument memo and changed sector"
          (Logic.mk_equals (request,Thm.term_of (Thm.rhs_of reference))) actual end
      val facts = map check requests
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
        "Six-port Entry locator endpoint"
        @{prop "comma_entry_port_refined_locator 1 0 38 \<equiv> Some (4,2,16)"}
        (List.last facts)
      val stats = #statistics memo ()
      val _ = if String.isSubstring "locator_hits=2 " stats andalso
          String.isSubstring "locator_misses=3 " stats then () else
        error ("Locator proof reuse did not preserve exact arguments: " ^ stats)
      val fresh = Comma_Frontier24_Bundle_Publisher.locator_conversion_plan ctxt
      val _ = if String.isSubstring "locator_retained=0 " (#statistics fresh ())
        then () else error "Locator proof data escaped its request context"
      val code_fact = Comma_Frontier24_Bundle_Publisher.code_true ctxt
        "Locator reuse inside Code_Simp"
        @{const_name comma_frontier24_locator_code_smoke} [] [#code_procedure fresh]
        @{term comma_frontier24_locator_code_smoke}
      val _ = if String.isSubstring "locator_misses=1 " (#statistics fresh ())
        then () else error "Code_Simp bypassed canonical locator admission"
      val nontrivial =
        Comma_Frontier24_Bundle_Publisher.locator_conversion_plan ctxt
      val request = @{term "comma_entry_port_refined_locator 9 2 3"}
      val raw_reference = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt request)
      val reference_codec = Comma_Selected_List_Alias.make_codec
        {ctxt=ctxt,validate_equation=fn input => fn theorem =>
          Comma_CRT_MDD_Proof_Utils.exact_prop ctxt "Nontrivial locator reference decoding"
            (Logic.mk_equals (input,Thm.term_of (Thm.rhs_of theorem))) theorem}
      val decoded_reference = #decode reference_codec (Thm.rhs_of raw_reference)
      val reference = Thm.transitive raw_reference decoded_reference
      val expected = Thm.term_of (Thm.rhs_of reference)
      val _ = Comma_CRT_MDD_Proof_Utils.exact_prop ctxt
        "Independent nontrivial locator reference"
        (Logic.mk_equals (request,expected)) reference
      val nontrivial_predicate =
        @{term comma_frontier24_locator_code_args_smoke} $ expected
      val nontrivial_fact = Comma_Frontier24_Bundle_Publisher.code_true ctxt
        "Nontrivial locator code-form arguments"
        @{const_name comma_frontier24_locator_code_args_smoke} []
        [#code_procedure nontrivial] nontrivial_predicate
      val nontrivial_stats = #statistics nontrivial ()
      val _ = if String.isSubstring "locator_misses=1 " nontrivial_stats andalso
          String.isSubstring "locator_rejected=0 " nontrivial_stats andalso
          not (String.isSubstring "locator_probes=0 " nontrivial_stats) then ()
        else error ("Code-form locator arguments were not admitted: " ^ nontrivial_stats)
      val key_request = @{term "comma_entry_port_refined_locator 6
        (fst (comma_decisive_entry_clock_key_from_core_residue 6 2 23 3))
        (snd (comma_decisive_entry_clock_key_from_core_residue 6 2 23 3))"}
      val key_raw = Code_Simp.dynamic_conv ctxt (Thm.cterm_of ctxt key_request)
      val key_reference = Thm.transitive key_raw
        (#decode reference_codec (Thm.rhs_of key_raw))
      val key_memo = Comma_Frontier24_Bundle_Publisher.locator_conversion_plan ctxt
      val key_checked = Comma_Frontier24_Bundle_Publisher.code_true ctxt
        "Computed Entry key locator code-form arguments"
        @{const_name comma_frontier24_locator_computed_key_smoke} []
        [#code_procedure key_memo]
        (@{term comma_frontier24_locator_computed_key_smoke} $
          Thm.term_of (Thm.rhs_of key_reference))
      val key_stats = #statistics key_memo ()
      val _ = if String.isSubstring "locator_misses=1 " key_stats andalso
          String.isSubstring "locator_rejected=0 " key_stats then () else
        error ("Computed Entry key bypassed locator admission: " ^ key_stats)
    in Comma_Proof_Dependency_Audit.require_native_clean ctxt
      "Locator exact equations and request-local reuse"
      (key_checked::key_reference::nontrivial_fact::code_fact::
        reference::decoded_reference::facts) end
\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Exported certificate smoke definitions"
    @{thms comma_frontier24_unselected_trap_action_def
      comma_frontier24_locator_code_smoke_def
      comma_frontier24_locator_code_args_smoke_def
      comma_frontier24_locator_computed_key_smoke_def
      comma_frontier24_lookup_code_smoke_def
      comma_frontier24_lookup_index2_code_smoke_def
      comma_frontier24_core_support_code_smoke_def
      comma_frontier24_transport_code_smoke_def};
\<close>

end
