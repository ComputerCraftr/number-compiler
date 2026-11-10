(* Source-bound exactness for the final named CRT action roots.  This proof
   follows shallow target cofactors and the checked source-program DAG.  It
   never serializes a tree, expands a phase row, or treats Data.normalize as
   semantic evidence. *)
structure Comma_Semantic_Phase_Action_Program_Certificate =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Compiler = Comma_Semantic_Phase_Action_Program_Compiler
  structure Shallow = Comma_Semantic_Weighted_CRT_Shallow_Certificate
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport
  structure Clock = Comma_Semantic_Phase_Action_Clock_Refinement

  val natT = Clock.natT
  val nat = Clock.nat
  val mk_trueprop = Clock.mk_trueprop
  val mk_imp = Clock.mk_imp
  val mk_conj = Clock.mk_conj
  val mk_eq = Clock.mk_eq
  val mk_less = Clock.mk_less
  val period_env_condition = Clock.period_env_condition
  val prove_simp = Clock.prove_simp
  val period_guard_transport = Clock.period_guard_transport
  val phase_mod_period = Clock.phase_mod_period

  type program_action = Compiler.program_action
  type source_program = Compiler.source_program
  type named_node = Shallow.named_node
  type source_guard_facts = {canonical: thm, admitted: thm, normalized: thm}
  type source_proof_bundle =
    {source: term, program: term, key: Compiler.program_key, period: int,
     source_equation: thm, operator_binding: thm,
     guards: source_guard_facts, period_equation: thm}
  type proof_check_stats =
    {emissions: int, proof_nodes: int, native_calls: int,
     native_failed_calls: int, native_milliseconds: int, closed_profile: string}

  val resultT = @{typ comma_semantic_b1_result}
  val actionT = @{typ comma_phase_rank_mask_action}
  val treeT = Type (@{type_name comma_semantic_weighted_crt_dag}, [actionT])
  val outputPairT = HOLogic.mk_prodT (actionT,natT)
  val optionOutputT = Type (@{type_name option}, [outputPairT])
  fun option_some typ value =
    Const (@{const_name Some},typ --> Type (@{type_name option},[typ])) $ value

  fun applied tree phase =
    Const (@{const_name comma_weighted_crt_apply},
      HOLogic.mk_prodT (natT,treeT) --> natT --> optionOutputT) $
      HOLogic.mk_prod (nat 0,tree) $ phase

  fun applied_some value =
    Const (@{const_name Some}, outputPairT --> optionOutputT) $
      HOLogic.mk_prod (value,nat 0)

  fun round_output source phase =
    @{term comma_semantic_b1_round_output} $ phase $ source

  fun ranked_output source phase =
    @{term comma_rank_mask_action_of_b1_result} $ round_output source phase

  type result =
    {root_sources: term list,
     source_order: thm,
     root_apply_exactness: thm list,
     retained_entries: int,
     proof_check_stats: proof_check_stats}

  fun source_facts check ctxt source =
    let
      val canonical = prove_simp check ctxt "Canonical source guard"
        (@{term comma_canonical_position_admitted} $ source)
        (@{thms comma_canonical_position_admitted_def
          comma_source_continuation_base.simps comma_sector_entry_bound_def
          })
      val admitted = prove_simp check ctxt "Admitted source guard"
        (@{term comma_round_admitted} $ source)
        (@{thms comma_round_admitted.simps comma_sector_entry_bound_def
          comma_source_continuation_base.simps})
      val normalized = prove_simp check ctxt "Canonical source frame"
        (mk_eq (source,@{term comma_source_continuation_base} $ source))
        @{thms comma_source_continuation_base.simps}
    in {canonical=canonical,admitted=admitted,normalized=normalized} end

  fun find_source_program (programs: source_program list) source =
    (case List.find (fn ({source=candidate,...}: source_program) =>
        candidate aconv source) programs of
      SOME record => record
    | NONE => error "Source certificate has no checked normalization record")

  fun source_period_equation check ctxt source program_record
      (program_action: program_action)
      ({canonical,admitted,normalized}: source_guard_facts) =
    let
      val source_program = (program_record: source_program)
      val _ = if #source source_program aconv source andalso
          #program source_program aconv #program program_action andalso
          Compiler.key_of_program (#program source_program)= #key program_action
        then () else error "Source period transport belongs to another semantic program"
      val source_binding = #equation source_program RS @{thm meta_eq_to_obj_eq}
      val period_refinement = @{thm comma_phase_program_source_local_period}
        OF [canonical,admitted,normalized,source_binding]
      val period = #period program_action
      val proposition = mk_eq
        (@{term comma_decisive_sector_period} $ source,nat period)
    in
      prove_simp check ctxt "Source program local period" proposition
        ([period_refinement,#period_equation program_action] @
          @{thms comma_semantic_port_program.case
            comma_semantic_port_program.simps comma_phase_core_modulus.simps})
    end

  fun source_bundle_matches (source_program: source_program)
      (program_action: program_action) (bundle: source_proof_bundle) =
    let
      val {source,program,key,period,source_equation,operator_binding,...} = bundle
    in
      source aconv #source program_action andalso
      program aconv #program program_action andalso
      key = #key program_action andalso period = #period program_action andalso
      #source source_program aconv source andalso
      #program source_program aconv program andalso
      Compiler.key_of_program (#program source_program) = key andalso
      Thm.prop_of (#equation source_program) aconv Thm.prop_of source_equation andalso
      Thm.prop_of (#operator_binding source_program) aconv
        Thm.prop_of operator_binding
    end

  fun make_source_proof_bundle check ctxt
      (source_program: source_program) (program_action: program_action) =
    let
      val source = #source program_action
      val _ = if #source source_program aconv source andalso
          #program source_program aconv #program program_action andalso
          Compiler.key_of_program (#program source_program) = #key program_action
        then () else error "Source proof bundle belongs to another semantic program"
      val guards = source_facts check ctxt source
      val period_equation = source_period_equation check ctxt source
        source_program program_action guards
    in
      {source=source,program= #program program_action,key= #key program_action,
       period= #period program_action,source_equation= #equation source_program,
       operator_binding= #operator_binding source_program,guards=guards,
       period_equation=period_equation}: source_proof_bundle
    end

  fun validate_source_proof_bundle check
      (source_program: source_program) (program_action: program_action)
      (bundle: source_proof_bundle) =
    let
      val _ = if source_bundle_matches source_program program_action bundle then ()
        else error "Cached source proof bundle changed source, key, binding, or period"
      val source = #source program_action
      val {canonical,admitted,normalized} = #guards bundle
      val canonical = check "Cached canonical source guard"
        (mk_trueprop (@{term comma_canonical_position_admitted} $ source)) canonical
      val admitted = check "Cached admitted source guard"
        (mk_trueprop (@{term comma_round_admitted} $ source)) admitted
      val normalized = check "Cached canonical source frame"
        (mk_trueprop (mk_eq (source,
          @{term comma_source_continuation_base} $ source))) normalized
      val period_equation = check "Cached source program local period"
        (mk_trueprop (mk_eq
          (@{term comma_decisive_sector_period} $ source,
            nat (#period program_action)))) (#period_equation bundle)
    in
      {source=source,program= #program program_action,key= #key program_action,
       period= #period program_action,source_equation= #equation source_program,
       operator_binding= #operator_binding source_program,
       guards={canonical=canonical,admitted=admitted,normalized=normalized},
       period_equation=period_equation}: source_proof_bundle
    end

  fun selected_action (node: Compiler.action_node) =
    (case node of
      Compiler.Terminal_Node {action,...} => action
    | Compiler.Goto_Node {action,...} => action
    | Compiler.Branch_Node _ => error "A branch node has no local selected action")

  fun local_action_template check ctxt
      (source_program: source_program) (program_action: program_action)
      (bundle: source_proof_bundle) =
    let
      val _ = if source_bundle_matches source_program program_action bundle then ()
        else error "Local action template received a foreign source proof bundle"
      val source = #source program_action
      val action = selected_action (#node program_action)
      val {canonical,admitted,...} = #guards bundle
      val period_equation = #period_equation bundle
      val phase_period = phase_mod_period check ctxt
        {period = #period program_action, environment = #environment program_action}
      val phase = Free ("phase",natT)
      val representative = nat (Compiler.phase_of_env (#environment program_action))
      val env = period_env_condition phase (#period program_action)
        (#environment program_action)
      val action_at = @{term comma_phase_program_action_at_source} $ phase $ source
      val representative_action = @{term comma_phase_program_action_at_source} $
        representative $ source
      val selected = option_some @{typ comma_source_continuation_action} action
      val proposition = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),env),
          mk_eq (action_at,selected)))
      val action_equation = (case #node program_action of
        Compiler.Terminal_Node {action_equation,...} => action_equation
      | Compiler.Goto_Node {action_equation,...} => action_equation
      | Compiler.Branch_Node _ => error "Cannot make a local action template for a branch")
      val period = #period program_action
      val source_period = @{term comma_decisive_sector_period} $ source
      val source_period_proposition = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),env),
          mk_eq (Clock.mod_nat (phase,source_period),
            Clock.mod_nat (representative,source_period))))
      val source_period_transport = prove_simp check ctxt
        "Compiler cylinder selects the checked source action period"
        source_period_proposition [period_equation,phase_period]
      val periodic_rule = @{thm comma_phase_program_action_at_source_periodic}
        OF [canonical,admitted]
      val periodic_proposition = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),env),
          mk_eq (action_at,representative_action)))
      val periodic_theorem = Goal.prove ctxt [] []
        (mk_trueprop periodic_proposition)
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context [@{thm allI},@{thm impI}] 1) THEN
          resolve_tac context [periodic_rule] 1 THEN
          resolve_tac context
            [source_period_transport RS @{thm spec} RS @{thm mp}] 1 THEN
          assume_tac context 1)
      val checked_periodicity = check
        "Source action is periodic on its checked clock cylinder"
        (mk_trueprop periodic_proposition) periodic_theorem
      val selected_equation = action_equation RS @{thm meta_eq_to_obj_eq}
      val action_theorem = Goal.prove ctxt [] [] (mk_trueprop proposition)
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context [@{thm allI},@{thm impI}] 1) THEN
          resolve_tac context [@{thm trans}] 1 THEN
          resolve_tac context
            [checked_periodicity RS @{thm spec} RS @{thm mp}] 1 THEN
          assume_tac context 1 THEN
          resolve_tac context [selected_equation] 1)
      val _ = if period>0 andalso 924 mod period=0 then ()
        else error "Local action template period is not a CRT divisor"
      val _ = if Term.fastype_of selected =
          @{typ "comma_source_continuation_action option"} then ()
        else error "Local action template has the wrong action type"
    in
      check "Source action is fixed on its clock cylinder"
        (mk_trueprop proposition) action_theorem
    end

  fun local_output_template check ctxt
      (source_program: source_program) (program_action: program_action)
      (terminal_reduction: Compiler.terminal_reduction option) action_uniform
      (bundle: source_proof_bundle) =
    let
      val _ = if source_bundle_matches source_program program_action bundle then ()
        else error "Local output template received a foreign source proof bundle"
      val source = #source program_action
      val {canonical,admitted,normalized} = #guards bundle
      val phase = Free ("phase",natT)
      val env = period_env_condition phase (#period program_action)
        (#environment program_action)
      val result_term = (case #node program_action of
        Compiler.Terminal_Node {action,...} =>
          (case terminal_reduction of
            SOME reduction =>
              if #action reduction aconv action then #result reduction
              else error "Terminal reduction is attached to another source action"
          | NONE => error "Terminal source state omitted its checked reduction")
      | Compiler.Goto_Node {action,...} =>
          (case Compiler.goto_parts action of
            SOME (child,0) => round_output child phase
          | SOME (_,_) => error "Goto source action has an uncertified shift"
          | NONE => error "Compiler Goto metadata contains a non-Goto action")
      | Compiler.Branch_Node _ => error "Branch actions have no terminal output template")
      val conclusion = (case #node program_action of
        Compiler.Terminal_Node _ => mk_eq (ranked_output source phase,result_term)
      | Compiler.Goto_Node {action,...} =>
          (case Compiler.goto_parts action of
            SOME (child,0) => mk_eq (round_output source phase,round_output child phase)
          | SOME (_,_) => error "Goto source action has an uncertified shift"
          | NONE => error "Compiler Goto metadata contains a non-Goto action")
      | Compiler.Branch_Node _ => error "Branch output conclusion is not defined")
      val proposition = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),env),conclusion))
      val slot_output = @{term comma_semantic_b1_source_slot_output} $
        phase $ selected_action (#node program_action)
      val bridge_rule = @{thm
        comma_phase_program_action_at_source_selected_round_output}
        OF [canonical,admitted,normalized]
      val bridge_proposition = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),env),
          mk_eq (slot_output,round_output source phase)))
      val bridge_theorem = Goal.prove ctxt [] []
        (mk_trueprop bridge_proposition)
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context [@{thm allI},@{thm impI}] 1) THEN
          resolve_tac context [bridge_rule] 1 THEN
          resolve_tac context
            [action_uniform RS @{thm spec} RS @{thm mp}] 1 THEN
          assume_tac context 1)
      val checked_bridge = check
        "Selected local action determines the source output"
        (mk_trueprop bridge_proposition) bridge_theorem
      val slot_equation = (case #node program_action of
        Compiler.Terminal_Node {action,...} =>
          (case terminal_reduction of
            SOME reduction =>
              let
                val _ = if #action reduction aconv action then ()
                  else error "Terminal reduction is attached to another source action"
                val terminal_equation = #terminal_equation reduction
                val terminal_value = Compiler.dest_some "Terminal result"
                  (Thm.term_of (Thm.rhs_of terminal_equation))
                val terminal_equation_object =
                  terminal_equation RS @{thm meta_eq_to_obj_eq}
                val slot_proposition = HOLogic.mk_all ("phase",natT,
                  mk_eq (slot_output,terminal_value))
              in
                (terminal_value,prove_simp check ctxt
                  "Selected terminal action has its checked output"
                  slot_proposition
                  (terminal_equation_object ::
                    @{thms comma_semantic_b1_source_slot_output_def
                      comma_source_continuation_action.case}))
              end
          | NONE => error "Terminal source state omitted its checked reduction")
      | Compiler.Goto_Node {action,...} =>
          (case Compiler.goto_parts action of
            SOME (child,0) =>
              let
                val child_output = round_output child phase
                val slot_proposition = HOLogic.mk_all ("phase",natT,
                  mk_eq (slot_output,child_output))
              in (child_output,prove_simp check ctxt
                "Zero-shift Goto action has its checked child output"
                slot_proposition @{thms comma_semantic_b1_source_slot_output_def
                  comma_source_continuation_action.case}) end
          | SOME (_,_) => error "Goto source action has an uncertified shift"
          | NONE => error "Compiler Goto metadata contains a non-Goto action")
      | Compiler.Branch_Node _ => error "Branch actions have no local output template")
      val expected_output = #1 slot_equation
      val slot_output_equation = #2 slot_equation
      val round_proposition = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),env),
          mk_eq (round_output source phase,expected_output)))
      val round_theorem = Goal.prove ctxt [] [] (mk_trueprop round_proposition)
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context [@{thm allI},@{thm impI}] 1) THEN
          resolve_tac context [@{thm trans}] 1 THEN
          resolve_tac context [@{thm sym}] 1 THEN
          resolve_tac context
            [checked_bridge RS @{thm spec} RS @{thm mp}] 1 THEN
          assume_tac context 1 THEN
          resolve_tac context [slot_output_equation RS @{thm spec}] 1)
      val checked_round_output = check
        "Source output is the selected local action output"
        (mk_trueprop round_proposition) round_theorem
      val _ = if (case #node program_action of
            Compiler.Terminal_Node _ => Term.fastype_of result_term=actionT
          | Compiler.Goto_Node _ => Term.fastype_of result_term=resultT
          | Compiler.Branch_Node _ => false) then ()
        else error "Source output template has the wrong result type"
    in
      (case #node program_action of
        Compiler.Goto_Node _ =>
          check "Source output follows its selected zero-shift Goto"
            (mk_trueprop proposition) checked_round_output
      | Compiler.Terminal_Node _ =>
          (case terminal_reduction of
            SOME reduction =>
              let val rank_equation = #rank_equation reduction RS
                    @{thm meta_eq_to_obj_eq}
              in prove_simp check ctxt "Source terminal rank output is exact"
                proposition [checked_round_output,rank_equation] end
          | NONE => error "Terminal source state omitted its checked reduction")
      | Compiler.Branch_Node _ => error "Branch output conclusion is not defined")
    end

  fun source_program_same check ctxt left_record right_record left right =
    if left aconv right then @{thm refl}
    else
      let
        val left_program = #program left_record
        val right_program = #program right_record
        val _ = if left_program aconv right_program then ()
          else error "Source congruence attempted across distinct semantic programs"
        val {canonical=canonical_left,admitted=admitted_left,normalized=normalized_left} =
          source_facts check ctxt left
        val {canonical=canonical_right,admitted=admitted_right,normalized=normalized_right} =
          source_facts check ctxt right
        val phase = Free ("phase",natT)
        val proposition = HOLogic.mk_all ("phase",natT,
          mk_eq (round_output left phase,round_output right phase))
        val congruence = @{thm comma_phase_program_same_key_round_output}
          OF [canonical_left,admitted_left,normalized_left,
            #equation left_record RS @{thm meta_eq_to_obj_eq},
            canonical_right,admitted_right,normalized_right,
            #equation right_record RS @{thm meta_eq_to_obj_eq}]
      in check "Source output congruence for a shared program key"
          (mk_trueprop proposition) congruence end

  fun finish_roots ctxt arena (compiler_result: Compiler.result)
      (target_roots: Data.diagram list)
      (lookup: Data.diagram -> named_node option) : result =
    Data.with_reservation arena (fn lifetime => let
      val scoped_checker = Transport.make_scoped_checker ctxt
        "comma_source_action_root_certificate"
      val check = #check scoped_checker
      val audit = #audit scoped_checker
      val checker_stats = #stats scoped_checker
      val sourceT = @{typ comma_finite_position}
      val source_terms = #root_sources compiler_result
      val root_keys = #root_programs compiler_result
      val _ = if length target_roots=46 andalso
          length (#roots compiler_result)=46 andalso
          length source_terms=46 andalso length root_keys=46 then ()
        else error "Source-root refinement requires the canonical 46-root domain"
      val retained = Unsynchronized.ref 0
      fun retain () =
        (Data.reserve_external arena lifetime; retained := !retained+1)
      fun named diagram =
        (case lookup diagram of
          SOME entry => entry
        | NONE => error "Published universal root has no named action authority")
      fun find_root key =
        (case List.find (fn (root: Compiler.program_root) => #key root=key)
            (#program_roots compiler_result) of
          SOME root => root
        | NONE => error "Source root has no universal semantic-key theorem")
      fun prove_root source target key =
        let
          val root = find_root key
          val _ = if Data.same_action arena target (#diagram root) then ()
            else error "Published action root differs from its universal program root"
          val target_named = named target
          val root_named = named (#diagram root)
          val _ = if #term target_named aconv #term root_named then ()
            else error "Root action and certified semantic key have different named authority"
          val source_record = find_source_program (#source_programs compiler_result) source
          val _ = if Compiler.key_of_program (#program source_record)=key andalso
              Compiler.key_of_program (#program (#source_binding root))=key then ()
            else error "Root occurrence and universal theorem do not share a semantic key"
          val root_phase = Free ("phase",natT)
          val root_guard = period_env_condition root_phase (#period root)
            Compiler.empty_env
          val root_prop = HOLogic.mk_all ("phase",natT,
            mk_imp (mk_conj (mk_less (root_phase,nat 924),root_guard),
              mk_eq (applied (#term root_named) root_phase,
                applied_some (ranked_output (#source root) root_phase))))
          val universal = check "Universal semantic-key root theorem"
            (mk_trueprop root_prop) (#exactness root)
          val congruence = source_program_same check ctxt
            (#source_binding root) source_record (#source root) source
          val phase = Free ("phase",natT)
          val apply_proposition = HOLogic.mk_all ("phase",natT,
            mk_imp (mk_less (phase,nat 924),
              mk_eq (applied (#term target_named) phase,
                applied_some (ranked_output source phase))))
          val theorem = prove_simp check ctxt
            "Canonical weighted root output transport"
            apply_proposition [universal,congruence]
          val _ = retain ()
        in theorem end
      val roots_order = HOLogic.mk_list sourceT source_terms
      val expected_order = @{term
        "map (\<lambda>i. Comma_Entry 1 0 (comma_offset_representatives!i)) [0..<46]"}
      val source_order_prop = mk_eq (roots_order,expected_order)
      val source_order = prove_simp check ctxt "Canonical source root ordering"
        source_order_prop
        (@{thms comma_offset_representatives_def upt_rec list.map nth_Cons'
          list.size(3) list.size(4)})
      fun map_four _ [] [] [] = []
        | map_four f (a::as') (b::bs) (c::cs) =
            f a b c :: map_four f as' bs cs
        | map_four _ _ _ _ = error "Source-root certificate vectors have different lengths"
      val root_apply_exactness = map_four prove_root
        source_terms target_roots root_keys
      val exported_theorems = source_order :: root_apply_exactness
      val _ = audit "Exported source-root exactness" exported_theorems
      val proof_check_stats = checker_stats ()
      val retained_entries = !retained
      val _ = Data.retain_external arena lifetime retained_entries
    in
      {root_sources=source_terms,source_order=source_order,
       root_apply_exactness=root_apply_exactness,
       retained_entries=retained_entries,
       proof_check_stats=proof_check_stats}: result
    end)
end
