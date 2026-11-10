(* Compile normalized source-port programs by demand-driven CRT cofactors.
   This is a candidate data constructor: its diagrams are not proof authority
   until the source-bound theorem checks them against exact source actions. *)
structure Comma_Semantic_Phase_Action_Program_Compiler =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data

  datatype program_key =
      Entry_Core of int * int * int * int
    | Near_Residual of int * int * int
    | Near_Boundary of int

  fun key_ord (Entry_Core (f1,d1,r1,c1), Entry_Core (f2,d2,r2,c2)) =
        prod_ord int_ord (prod_ord int_ord (prod_ord int_ord int_ord))
          ((f1,(d1,(r1,c1))),(f2,(d2,(r2,c2))))
    | key_ord (Entry_Core _, _) = LESS
    | key_ord (_, Entry_Core _) = GREATER
    | key_ord (Near_Residual (f1,d1,r1), Near_Residual (f2,d2,r2)) =
        prod_ord int_ord (prod_ord int_ord int_ord)
          ((f1,(d1,r1)),(f2,(d2,r2)))
    | key_ord (Near_Residual _, Near_Boundary _) = LESS
    | key_ord (Near_Boundary _, Near_Residual _) = GREATER
    | key_ord (Near_Boundary f1, Near_Boundary f2) = int_ord (f1,f2)

  structure Key_Table = Table
  (
    type key = program_key
    val ord = key_ord
  )

  structure Entry_Port_Table = Table
  (
    type key = int * int
    val ord = prod_ord int_ord int_ord
  )

  type source_program_binding = {source: term, program: term, equation: thm}
  type source_program =
    {source: term, program: term, equation: thm, operator_binding: thm}
  type program_period =
    {key: program_key, period: int, equation: thm,
     operator_equation: thm option}
  type compiler_key = program_key * (int option * int option * int option * int option)
  datatype action_node =
      Terminal_Node of {phase: int, action: term, action_equation: thm}
    | Goto_Node of {phase: int, action: term, action_equation: thm,
        child: compiler_key}
    | Branch_Node of {axis: int, children: (int * compiler_key) list}
  type program_action =
    {key: program_key, environment: int option * int option * int option * int option,
     source: term, program: term, period: int, period_equation: thm,
     node: action_node, diagram: Data.diagram}
  type terminal_reduction =
    {action: term, result: term, terminal_equation: thm, rank_equation: thm}
  type action_context =
    {action: program_action, source_binding: source_program,
     terminal_reduction: terminal_reduction option,
     goto_child_binding: source_program option}
  type certified_state =
    {key: program_key,
     environment: int option * int option * int option * int option,
     source: term, program: term, source_binding: source_program,
     period: int, period_equation: thm, diagram: Data.diagram, exactness: thm}
  type scope_token = unit Unsynchronized.ref
  type state_certifier =
    {certify: action_context -> certified_state list -> thm,
     begin_scope: Data.reservation -> scope_token,
     end_scope: scope_token -> unit,
     current_context: unit -> Proof.context}
  type program_root =
    {key: program_key, source: term, program: term,
     source_binding: source_program, period: int, period_equation: thm,
     diagram: Data.diagram, exactness: thm}
  type result =
    {roots: Data.diagram list,
     root_sources: term list,
     source_programs: source_program list,
     root_programs: program_key list,
     program_roots: program_root list,
     programs: int,
     cofactor_nodes: int,
     cofactor_leaves: int,
     memo_hits: int,
     period_evaluations: int,
     period_cache_hits: int,
     terminal_evaluations: int,
     terminal_cache_hits: int,
     action_conversion_hits: int,
     action_conversion_misses: int,
     quotient_slot_merges: int,
     data_nodes: int}

  val natT = @{typ nat}

  type clock_env = Comma_Semantic_Weighted_CRT_Data_Transport.clock_env

  fun period_component period axis =
    if period > 0 then Integer.gcd (Data.axis_radix axis) period
    else error "CRT quotient requires a positive checked period"

  fun canonical_environment period ((a,b,c,d): clock_env): clock_env =
    let
      fun canonical axis slot =
        Option.map (fn value => value mod period_component period axis) slot
    in (canonical 0 a,canonical 1 b,canonical 2 c,canonical 3 d) end

  fun env_slot (env: clock_env) axis =
    (case (env,axis) of
      ((slot,_,_,_),0) => slot
    | ((_,slot,_,_),1) => slot
    | ((_,_,slot,_),2) => slot
    | ((_,_,_,slot),3) => slot
    | _ => error "CRT environment axis is outside 0..3")

  fun env_update period (env: clock_env) axis slot: clock_env =
    let
      val radix = Data.axis_radix axis
      val _ = if 0 <= slot andalso slot < radix then ()
        else error "CRT environment character is outside its radix"
      val canonical_slot = slot mod period_component period axis
      val old = env_slot env axis
      val _ = (case old of NONE => ()
        | SOME prior => if prior=canonical_slot then ()
            else error "CRT cofactor environment changed an assigned character")
    in
      (case (env,axis) of
        ((_,b,c,d),0) => (SOME canonical_slot,b,c,d)
      | ((a,_,c,d),1) => (a,SOME canonical_slot,c,d)
      | ((a,b,_,d),2) => (a,b,SOME canonical_slot,d)
      | ((a,b,c,_),3) => (a,b,c,SOME canonical_slot)
      | _ => error "CRT environment axis is outside 0..3")
    end

  (* Keep the physical split row while quotienting only its recursive keys. *)
  fun child_key_row period (key: program_key) (env: clock_env) axis
      : (int * compiler_key) list =
    map (fn slot => (slot,(key,env_update period env axis slot)))
      (0 upto (Data.axis_radix axis-1))

  fun option_int_ord (NONE,NONE) = EQUAL
    | option_int_ord (NONE,SOME _) = LESS
    | option_int_ord (SOME _,NONE) = GREATER
    | option_int_ord (SOME x,SOME y) = int_ord (x,y)

  fun env_ord ((a1,b1,c1,d1),(a2,b2,c2,d2)) =
    prod_ord option_int_ord
      (prod_ord option_int_ord (prod_ord option_int_ord option_int_ord))
        ((a1,(b1,(c1,d1))),(a2,(b2,(c2,d2))))

  fun compiler_key_ord ((program1,env1),(program2,env2)) =
    prod_ord key_ord env_ord ((program1,env1),(program2,env2))

  structure Compiler_Table = Table
  (
    type key = compiler_key
    val ord = compiler_key_ord
  )

  val empty_env = Comma_Semantic_Weighted_CRT_Data_Transport.empty_env
  fun phase_of_env env = Comma_Semantic_Weighted_CRT_Data_Transport.phase_of_env
    Data.axis_radix Data.axis_weight env

  fun nat n = HOLogic.mk_number natT n

  fun dest_nat label term =
    (case try HOLogic.dest_number term of
      SOME (typ,value) =>
        if typ = natT andalso 0 <= value then value
        else error (label ^ " is not a natural numeral")
    | NONE => error (label ^ " is not a natural numeral"))

  fun dest_some label term =
    (case Term.strip_comb term of
      (Const (name,_),[value]) =>
        if name = @{const_name Some} then value
        else error (label ^ " is not a successful option: " ^
          Comma_Semantic_Weighted_CRT_Data_Transport.diagnostic_term term)
    | _ => error (label ^ " is not an option value: " ^
        Comma_Semantic_Weighted_CRT_Data_Transport.diagnostic_term term))

  fun key_of_program term =
    (case Term.strip_comb term of
      (Const (name,_),[f,d,residue,core]) =>
        if name = @{const_name Comma_Entry_Core_Program} then
          let
            val core_name = (case Term.strip_comb core of
              (Const (core_name,_),[]) => core_name
            | _ => error "Entry program contains a malformed core tag")
            val core_number =
              if core_name = @{const_name Comma_Core_1} then 1
              else if core_name = @{const_name Comma_Core_3} then 3
              else if core_name = @{const_name Comma_Core_7} then 7
              else if core_name = @{const_name Comma_Core_11} then 11
              else if core_name = @{const_name Comma_Core_13} then 13
              else if core_name = @{const_name Comma_Core_21} then 21
              else if core_name = @{const_name Comma_Core_23} then 23
              else if core_name = @{const_name Comma_Core_27} then 27
              else if core_name = @{const_name Comma_Core_29} then 29
              else error "Entry program contains an unknown core tag"
          in
            Entry_Core (dest_nat "Entry sector" f,
              dest_nat "Entry digit" d, dest_nat "Entry residue" residue,
              core_number)
          end
        else error "Unknown semantic port program constructor"
    | (Const (name,_),[f,d,residual]) =>
        if name = @{const_name Comma_Near_Residual_Program} then
          Near_Residual (dest_nat "Near sector" f,
            dest_nat "Near digit" d,dest_nat "Near residual" residual)
        else error "Unknown semantic port program constructor"
    | (Const (name,_),[f]) =>
        if name = @{const_name Comma_Near_Boundary_Program} then
          Near_Boundary (dest_nat "Boundary sector" f)
        else error "Unknown semantic port program constructor"
    | _ => error "Malformed normalized semantic port program")

  val source_guard_simp_rules = @{thms
    comma_source_continuation_base.simps
    comma_canonical_position_admitted_def
    comma_sector_entry_bound_def}

  val source_program_simp_rules = source_guard_simp_rules @ @{thms
    comma_semantic_port_program_of_source_def
    comma_entry_control_program_def comma_near_control_program_def
    comma_finite_period_fast_def comma_phase_core_modulus.simps
    comma_phase_core_of_modulus_def
    comma_core_period_def comma_core_lift_parameters nth_Cons'
    option.map option.case option.sel option.simps
    map_option_case}

  (* Weak case congruences prevent expansion of unselected branches. The
     sterile database is prepared once; source facts remain caller-owned. *)
  val closed_evaluator_simpset = Simplifier.simpset_of
    (Comma_Semantic_Weighted_CRT_Data_Transport.arithmetic_context @{context}
      |> fold Simplifier.add_cong
        @{thms comma_finite_position.case_cong_weak
          comma_semantic_port_program.case_cong_weak
          option.case_cong_weak map_option_cong}
      |> Simplifier.add_simps
        @{thms comma_finite_position.case comma_semantic_port_program.case
          option.case})
  fun closed_evaluator_context ctxt = put_simpset closed_evaluator_simpset ctxt

  val local_action_code_constants =
    [@{const_name comma_phase_program_operator_nf},
     @{const_name comma_phase_program_at_entry},
     @{const_name comma_phase_program_at_near},
     @{const_name comma_source_continuation_transport},
     @{const_name map_option},
     @{const_name comma_entry_stored_tree_locator},
     @{const_name comma_entry_port_seed},
     @{const_name comma_entry_port_orbit},
     @{const_name comma_entry_port_position},
     @{const_name comma_entry_port_potential},
     @{const_name comma_entry_prefix_tree},
     @{const_name comma_entry_port_search_tree},
     @{const_name comma_entry_port_row},
     @{const_name comma_finite_period},
     @{const_name comma_cycle_length},
     @{const_name comma_phase_digit},
     @{const_name comma_period_displacement},
     @{const_name comma_semantic_b1_terminal_action_result},
     @{const_name comma_rank_mask_action_of_b1_result}]

  fun make_local_action_evaluator ctxt =
    Code_Simp.static_conv
      {ctxt=ctxt,simpset=NONE,consts=local_action_code_constants}

  fun local_code_rewrite ctxt evaluator label term =
    let
      val traced = Comma_Proof_Profile.enabled ()
      val started = Time.now ()
      val _ = if traced then Comma_Proof_Profile.report
        ("local-action-code label=" ^ label ^ " stage=conversion-input head=" ^
          Comma_Semantic_Weighted_CRT_Data_Transport.diagnostic_head term ^
            " term=" ^ Comma_Semantic_Weighted_CRT_Data_Transport.diagnostic_term_in ctxt term)
          else ()
      val _ = if traced then Comma_Proof_Profile.report
        ("local-action-code label=" ^ label ^ " stage=conversion-start") else ()
      val theorem = evaluator ctxt (Thm.cterm_of ctxt term)
      val _ = if traced then Comma_Proof_Profile.report
        ("local-action-code label=" ^ label ^ " stage=conversion-done elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started) else ()
      val _ = if Thm.term_of (Thm.lhs_of theorem) aconv term then ()
        else error "Local code conversion changed its exact input expression"
      val audit_started = Time.now ()
      val _ = if traced then Comma_Proof_Profile.report
        ("local-action-code label=" ^ label ^ " stage=closed-audit-start") else ()
      val checked = Comma_Semantic_Weighted_CRT_Data_Transport.checked_closed
        ctxt label (Thm.prop_of theorem) theorem
      val _ = if traced then Comma_Proof_Profile.report
        ("local-action-code label=" ^ label ^ " stage=closed-audit-done elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms audit_started) else ()
    in {term=Thm.term_of (Thm.rhs_of checked),theorem=checked} end

  fun checked_rewrite ctxt label rules term =
    Comma_Semantic_Weighted_CRT_Data_Transport.checked_rewrite_in
      ctxt (closed_evaluator_context ctxt) label rules term

  fun source_operator_input source =
    Abs ("phase",natT,
      @{term comma_phase_program_action_at_source} $ Bound 0 $ source)

  fun program_operator_value program phase =
    let
      val actionT = @{typ comma_source_continuation_action}
      val some = Const (@{const_name Some},
        actionT --> Type (@{type_name option},[actionT]))
    in some $ (@{term comma_phase_program_operator_nf} $ program $ phase) end

  fun program_operator_input program =
    Abs ("phase",natT,program_operator_value program (Bound 0))

  fun source_operator_output program =
    Abs ("phase",natT,program_operator_value program
      (@{term comma_phase_program_selector_phase} $ program $ Bound 0))

  fun source_operator_equation ctxt (binding: source_program_binding) =
    let
      val source = #source binding
      val program = #program binding
      val left = source_operator_input source
      val right = source_operator_output program
      val proposition = HOLogic.mk_Trueprop (HOLogic.mk_eq (left,right))
      val context = closed_evaluator_context ctxt
        |> Simplifier.add_simps (#equation binding :: source_guard_simp_rules @
          @{thms comma_round_admitted.simps})
      val theorem = Goal.prove context [] [] proposition
        (fn {context,...} =>
          resolve_tac context @{thms comma_phase_program_source_operator_function} 1
          THEN ALLGOALS (asm_full_simp_tac context))
      val checked = Comma_Semantic_Weighted_CRT_Data_Transport.checked_closed
        ctxt "Source-specialized universal operator" proposition theorem
    in checked RS @{thm eq_reflection} end

  fun program_of_source ctxt source =
    let
      val expression = @{term comma_semantic_port_program_of_source} $ source
      val {term=rhs,theorem} = checked_rewrite ctxt
        "Closed source-to-program normalization" source_program_simp_rules expression
      val program = dest_some "Normalized source program" rhs
      val binding: source_program_binding =
        {source=source,program=program,equation=theorem}
      val operator_binding = source_operator_equation ctxt binding
    in
      {source=source,program=program,equation=theorem,
       operator_binding=operator_binding}: source_program
    end

  fun period_of_key ctxt key =
    let
      val expression = (case key of
        Entry_Core (_,_,_,core) => @{term comma_core_period} $ nat core
      | Near_Residual _ => nat 1
      | Near_Boundary _ => nat 1)
      val {term=period_term,theorem} = checked_rewrite ctxt
        "Closed core-period reduction" @{thms comma_core_period_def} expression
      val period = dest_nat "Action-program local period" period_term
      val _ = if period > 0 andalso 924 mod period = 0 then ()
        else error "Action-program period is not a positive CRT divisor"
    in {key=key,period=period,equation=theorem,
        operator_equation=NONE}: program_period end

  val entry_operator_simp_rules = @{thms
    comma_phase_program_at_entry_operator_nf
    comma_phase_program_application_admitted.simps
    comma_phase_program_operator_nf.simps
    comma_c1_b1_entry_core_port_action_def
    comma_decisive_entry_clock_key_def
    comma_decisive_entry_clock_key_with_core_def
    comma_decisive_entry_clock_key_from_core_residue_def
    comma_cyclotomic_clock_core_value_def
    comma_cyclotomic_clock_of_def comma_cyclotomic_phase_def
    comma_cyclotomic_clock.select_convs
    comma_finite_period_fast_def comma_phase_core_modulus.simps
    comma_sector_entry_bound_def comma_core_seed_def comma_core_period_def
    comma_core_lift_parameters nth_Cons'
    comma_entry_stored_tree_locator_def}
    @ [@{thm comma_entry_stored_tree_locator_refines} RS @{thm sym}]

  type fixed_entry_port = {rules: thm list}
  fun fixed_entry_port ctxt evaluator f d: fixed_entry_port =
    let
      val (f_term,d_term) = (nat f,nat d)
      val _ = if 1<=f andalso f<=9 andalso 0<=d andalso d<10 then ()
        else error "Entry port specialization is outside the admitted domain"
      val seed = @{term comma_entry_port_seed} $ f_term $ d_term;
      val potential = @{term comma_entry_port_potential} $ f_term $ d_term
      val period = @{term comma_finite_period} $ f_term $ d_term;
      val tree = @{term comma_entry_port_search_tree} $ f_term $ d_term
      val period_at_seed = @{term comma_finite_period} $ f_term $ seed
      val input = HOLogic.mk_prod (seed, HOLogic.mk_prod (potential,
        HOLogic.mk_prod (period, HOLogic.mk_prod (period_at_seed,tree))))
      val {theorem=bundle,...} = local_code_rewrite ctxt evaluator "Fixed Entry port tuple" input
      val paths = [[0],[1,0],[1,1,0],[1,1,1,0],[1,1,1,1]]
      val projections = Comma_Semantic_Weighted_CRT_Data_Transport.checked_tuple_projections
        ctxt "Fixed Entry port projection" bundle input paths
      val rules = (case projections of [seed_eq,potential_eq,period_eq,seed_period_eq,tree_eq] =>
        let val period_of = @{term comma_finite_period} $ f_term
            val congruence = Thm.combination
              (Thm.reflexive (Thm.cterm_of ctxt period_of)) seed_eq
            val normalized = Thm.transitive (Thm.symmetric congruence) seed_period_eq
            val checked = Comma_Semantic_Weighted_CRT_Data_Transport.checked_closed
              ctxt "Fixed Entry seed-period projection" (Thm.prop_of normalized) normalized
        in [seed_eq,potential_eq,period_eq,checked,tree_eq] end
        | _ => error "Fixed Entry port tuple projection count changed")
    in {rules=rules}: fixed_entry_port end
  fun specialize_entry_operator ctxt program port_rules =
    let
      val key = key_of_program program
      val _ = (case key of Entry_Core _ => ()
        | _ => error "Only an admitted Entry core has a specialized phase operator")
      val operator = program_operator_input program
      val operator_context = closed_evaluator_context ctxt
        |> Simplifier.del_simps @{thms comma_prefix_tree_port_select.simps
          comma_prefix_tree_select.simps}
      val rules = entry_operator_simp_rules @ port_rules
      val started = Time.now ()
      val traced = Comma_Proof_Profile.enabled ()
      val _ = if traced then Comma_Proof_Profile.report
        ("entry-operator-specialization stage=start key=" ^
          Comma_Semantic_Weighted_CRT_Data_Transport.diagnostic_term_in ctxt program) else ()
      val {term=specialized,theorem} =
        Comma_Semantic_Weighted_CRT_Data_Transport.checked_rewrite_in
          ctxt operator_context "Guarded Entry operator specialization" rules operator
      val _ = if Thm.term_of (Thm.lhs_of theorem) aconv operator then ()
        else error "Entry specialization theorem changed its operator input"
      val forbidden = [@{const_name comma_core_primary},
        @{const_name comma_core_modulus}, @{const_name comma_core_seed},
        @{const_name comma_core_period}, @{const_name comma_finite_period_fast},
        @{const_name comma_entry_port_refined_locator},
        @{const_name comma_entry_port_seed},
        @{const_name comma_entry_port_potential},
        @{const_name comma_entry_port_search_tree}]
      fun has_forbidden term = Term.exists_subterm
        (fn Const (name,_) => member (op =) forbidden name | _ => false) term
      fun has_tree_selection term = Term.exists_subterm
        (fn Const (name,_) => name = @{const_name comma_prefix_tree_port_select}
          | _ => false) term
      val _ = if has_forbidden specialized then
          error ("Entry operator retained fixed lift arithmetic: " ^
            Comma_Semantic_Weighted_CRT_Data_Transport.diagnostic_term_in ctxt specialized)
        else ()
      val _ = if has_tree_selection specialized then ()
        else error "Entry operator lost its guarded stored-tree selection"
      val _ = if traced then Comma_Proof_Profile.report
        ("entry-operator-specialization stage=done elapsed_ms=" ^
          Comma_Proof_Profile.elapsed_ms started ^ " operator=" ^
          Comma_Semantic_Weighted_CRT_Data_Transport.diagnostic_term_in ctxt specialized ^
          " static-port=true") else ()
    in theorem end
  fun operator_for_program_with_rules ctxt program port_rules =
    (case key_of_program program of
      Entry_Core _ => SOME (specialize_entry_operator ctxt program port_rules)
    | _ => NONE)
  fun source_delta source =
    (case Term.strip_comb source of
      (Const (name,_),[_,delta,_]) =>
        if name = @{const_name Comma_Entry} orelse
           name = @{const_name Comma_Near}
        then dest_nat "Source occurrence shift" delta
        else error "Phase action source has an unsupported constructor"
    | _ => error "Phase action source is malformed")
  val action_structure_rules = source_guard_simp_rules @ @{thms
    comma_phase_program_action_at_source_def
    comma_phase_program_apply_entry_def
    comma_phase_core_modulus.simps comma_core_period_def
    comma_finite_period_fast_def nth_Cons'
    comma_cyclotomic_clock.select_convs}
  val entry_scalar_arithmetic_rules = @{thms
    comma_entry_diagonal_def comma_recursive_core_residue_def
    comma_core_period_def comma_core_halfcycle_def comma_core_seven_def nth_Cons' list.size}
    @ Comma_Entry_Arithmetic.signed_scalar_rules
  type local_action_cache = Data.term_cache
  type local_action_cache_totals = Data.term_cache_totals
  type program_frame =
    {reservation: Data.reservation, action_cache: local_action_cache,
     periods: program_period Key_Table.table Unsynchronized.ref}
  fun make_local_action_cache ctxt evaluator arena reservation port_rules_for totals =
    Data.make_term_cache ctxt arena reservation (fn row_scratch => fn input =>
      let
        fun normalize_row row =
          let
            val _ = Data.reserve_external arena row_scratch
            val (f,d) = (case Term.strip_comb row of
              (Const (name,_),[sector,digit,_]) =>
                if name = @{const_name comma_entry_port_row} then
                  (dest_nat "Entry row sector" sector,
                   dest_nat "Entry row digit" digit)
                else error "Scalar row normalizer received another operator"
            | _ => error "Scalar row normalizer received a malformed call")
            val context = closed_evaluator_context ctxt
              |> Simplifier.del_simps @{thms comma_entry_port_row_def}
          in #theorem (Comma_Semantic_Weighted_CRT_Data_Transport.checked_rewrite_in
            ctxt context "Canonical Entry scalar row input"
            (@{thms comma_entry_port_row_def} @ action_structure_rules @
              port_rules_for f d) row) end
        fun convert_row row =
          let
            val _ = Data.reserve_external arena row_scratch
            val converted = Comma_Semantic_Weighted_CRT_Data_Transport.checked_rewrite_in
              ctxt (closed_evaluator_context ctxt) "Entry scalar row"
              entry_scalar_arithmetic_rules row
            val _ = if Thm.term_of (Thm.lhs_of (#theorem converted)) aconv row then ()
              else error "Scalar arithmetic conversion changed its exact input"
            fun reject () = error ("Entry scalar row did not reduce to a natural numeral: " ^
              Comma_Semantic_Weighted_CRT_Data_Transport.diagnostic_term_in ctxt row ^
              " => " ^ Comma_Semantic_Weighted_CRT_Data_Transport.diagnostic_term_in ctxt
                (#term converted))
            val _ = (case try HOLogic.dest_number (#term converted) of
              SOME (typ,value) => if typ=natT andalso value >= 0 then () else reject ()
            | NONE => reject ())
          in #theorem converted end
        val row_rewrite = Comma_Semantic_Weighted_CRT_Data_Transport.checked_subterm_rewrite
          ctxt "Entry scalar row substitution" @{const_name comma_entry_port_row}
          3 natT input normalize_row convert_row
        val action_conversion = local_code_rewrite ctxt evaluator
          "Normalized local source action" (#term row_rewrite)
        val composed = Thm.transitive (#theorem row_rewrite) (#theorem action_conversion)
        val converted = Comma_Semantic_Weighted_CRT_Data_Transport.checked_closed ctxt
          "Composed normalized local source action" (Thm.prop_of composed) composed
        val result = Thm.term_of (Thm.rhs_of converted)
      in {term=result,theorem=converted} end) totals
  fun validate_source_operator_binding ctxt (checked_source: source_program) =
    let
      val source = #source checked_source
      val program = #program checked_source
      val programT = fastype_of program
      val some_program = Const (@{const_name Some},
        programT --> Type (@{type_name option},[programT])) $ program
      val source_expected = Logic.mk_equals
        (@{term comma_semantic_port_program_of_source} $ source,some_program)
      val _ = Comma_Semantic_Weighted_CRT_Data_Transport.checked_closed ctxt
        "Checked source-program binding" source_expected (#equation checked_source)
      val expected = Logic.mk_equals
        (source_operator_input source,source_operator_output program)
    in Comma_Semantic_Weighted_CRT_Data_Transport.checked_closed ctxt
      "Checked universal source-operator binding" expected
      (#operator_binding checked_source) end
  fun apply_function_equation ctxt equation argument =
    let
      val applied = Thm.combination equation
        (Thm.reflexive (Thm.cterm_of ctxt argument))
    in Thm.transitive
      (Thm.symmetric (Thm.beta_conversion true (Thm.lhs_of applied)))
      (Thm.transitive applied (Thm.beta_conversion true (Thm.rhs_of applied))) end
  fun action_at_source_checked_using ctxt reduce_action
      (checked_source: source_program) phase operator_equation =
    let
      val source = #source checked_source
      val expression = @{term comma_phase_program_action_at_source} $
        nat phase $ source
      val binding = validate_source_operator_binding ctxt checked_source
      val source_step = apply_function_equation ctxt binding (nat phase)
      val _ = if Thm.term_of (Thm.lhs_of source_step) aconv expression then ()
        else error "Source operator specialization changed its source or phase"
      val {term=application,theorem=application_step} = checked_rewrite ctxt
        "Source operator selector phase"
        @{thms comma_phase_program_selector_phase.simps comma_phase_core_modulus.simps
          comma_core_period_def nth_Cons'}
        (Thm.term_of (Thm.rhs_of source_step))
      val operator_step = (case operator_equation of
        NONE => #theorem (checked_rewrite ctxt "Guarded Near operator quotient"
          @{thms comma_phase_program_operator_nf.simps} application)
      | SOME operator =>
          let
            val local_phase = (case Term.strip_comb
                (dest_some "Source operator application" application) of
              (Const (name,_),[_,value]) =>
                if name = @{const_name comma_phase_program_operator_nf}
                then nat (dest_nat "Canonical program phase" value)
                else error "Source operator application lost its normal form"
            | _ => error "Malformed source operator application")
            val specialized = apply_function_equation ctxt operator local_phase
            val _ = if Thm.term_of (Thm.lhs_of specialized) aconv application then ()
              else error "Shared operator belongs to another program or phase"
          in specialized end)
      val reduced = Thm.term_of (Thm.rhs_of operator_step)
      val structural = Thm.transitive source_step
        (Thm.transitive application_step operator_step)
      val {term=action,theorem=equation} = reduce_action reduced
      val combined = Thm.transitive structural equation
      val checked = Comma_Semantic_Weighted_CRT_Data_Transport.checked_closed
        ctxt "Closed source action reduction" (Thm.prop_of combined) combined
    in {action=dest_some "Admitted source action" action,
        equation=checked} end
  fun result_of_terminal ctxt evaluator action: terminal_reduction =
    let
      val terminal = @{term comma_semantic_b1_terminal_action_result} $ action
      val {term=terminal_result, theorem=terminal_equation} = local_code_rewrite ctxt
        evaluator "Closed terminal-action reduction" terminal
      val value = dest_some "Terminal port action" terminal_result
      val rank_action = @{term comma_rank_mask_action_of_b1_result} $ value
      val {term=result,theorem=rank_equation} = local_code_rewrite ctxt
        evaluator "Closed terminal rank-action reduction" rank_action
    in {action=action,result=result,terminal_equation=terminal_equation,
      rank_equation=rank_equation} end

  fun action_key value =
    (case Term.strip_comb value of
      (Const (name,_),[]) =>
        if name = @{const_name Comma_Phase_Rank_Mask_Invalid} then
          "rank-action:invalid"
        else error "Phase action leaf is not a structural result constructor"
    | (Const (name,_),[first,second]) =>
        if name = @{const_name Comma_Phase_Rank_Mask_Fork} then
          let
            val fork = dest_nat "fork index" first
            val shift = dest_nat "fork shift" second
          in
            if 2 <= fork andalso fork <= 9 andalso shift = 0 then
              "rank-action:fork:" ^ Int.toString fork ^ ":0"
            else error "Rank action contains an unsupported fork control"
          end
        else error "Phase action pair leaf has an unknown constructor"
    | (Const (name,_),[argument]) =>
        if name = @{const_name Comma_Phase_Rank_Mask_Landmine} then
          if dest_nat "landmine shift" argument = 0 then
            "rank-action:landmine:0"
          else error "Rank action contains a shifted landmine control"
        else if name = @{const_name Comma_Phase_Rank_Mask_Continue} then
          let val child = dest_nat "successor class" argument in
            if child < 46 then "rank-action:continue:" ^ Int.toString child
            else error "Rank action names a successor outside the 46 roots"
          end
        else error "Phase action unary leaf has an unknown constructor"
    | _ => error "Phase action leaf is not a closed result constructor")

  fun leaf_payload value: Data.payload = {key=action_key value,value=value}

  fun goto_parts action =
    (case Term.strip_comb action of
      (Const (name,_),[source,shift]) =>
        if name = @{const_name Comma_Continuation_Goto} then
          SOME (source,dest_nat "Goto occurrence shift" shift)
        else NONE
    | _ => NONE)

  (* Child keys retain semantic identity; parent clocks remain guards. *)
  fun global_child_key program: compiler_key = (key_of_program program,empty_env)

  fun root_is_canonical source =
    (case Term.strip_comb source of
      (Const (name,_),[sector,delta,offset]) =>
        if name = @{const_name Comma_Entry} then
          dest_nat "Root sector" sector = 1 andalso
          dest_nat "Root shift" delta = 0 andalso
          dest_nat "Root offset" offset <= 90
        else false
    | _ => false)

end
