(* Exact residue transport for quotient-period source-action certificates. *)
structure Comma_Semantic_Phase_Action_Clock_Refinement =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Compiler = Comma_Semantic_Phase_Action_Program_Compiler
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport

  type clock_env = Compiler.clock_env
  type program_action = Compiler.program_action
  type period_environment = {period: int, environment: clock_env}

  val natT = @{typ nat}
  fun nat value = HOLogic.mk_number natT value
  val natMod = @{term "(mod)::nat \<Rightarrow> nat \<Rightarrow> nat"}
  fun mod_nat (left,right) = natMod $ left $ right
  fun mk_trueprop term = HOLogic.mk_Trueprop term
  fun mk_imp (left,right) = HOLogic.mk_imp (left,right)
  fun mk_conj (left,right) = HOLogic.mk_conj (left,right)
  fun mk_eq (left,right) = HOLogic.mk_eq (left,right)
  fun mk_less (left,right) = HOLogic.mk_binrel @{const_name less} (left,right)

  fun conjoin [] = @{term True}
    | conjoin [term] = term
    | conjoin (term :: rest) = mk_conj (term,conjoin rest)

  fun env_slot (env,axis) = Compiler.env_slot env axis

  fun env_condition phase (env: clock_env) =
    let
      fun one axis slot =
        mk_eq (mod_nat (phase,nat (Data.axis_radix axis)),nat slot)
      val conditions = map_filter (fn axis =>
        Option.map (one axis) (env_slot (env,axis))) (0 upto 3)
    in conjoin conditions end

  (* The producer and certificate use the same finite CRT component owner. *)
  val period_component = Compiler.period_component

  fun period_env_condition phase period (env: clock_env) =
    let
      fun one axis slot =
        mk_eq (mod_nat (phase,nat (period_component period axis)),nat slot)
      val conditions = map_filter (fn axis =>
        Option.map (one axis) (env_slot (env,axis))) (0 upto 3)
    in conjoin conditions end

  fun period_env_extends period (required: clock_env) (selected: clock_env) =
    forall (fn axis =>
      (case env_slot (required,axis) of
        NONE => true
      | SOME canonical =>
          (case env_slot (selected,axis) of
            NONE => false
          | SOME full =>
              full mod period_component period axis = canonical))) (0 upto 3)

  fun prove_simp check ctxt label proposition rules =
    let
      val started = Time.now ()
      val proof_ctxt = Compiler.closed_evaluator_context ctxt
        |> Simplifier.add_simps (Comma_Proof_Rewrite_Rules.nonreflexive_rules rules)
      val _ = if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
        ("clock_refinement prove_simp stage=start label=" ^ label) else ()
      val theorem = Goal.prove proof_ctxt [] [] (mk_trueprop proposition)
        (fn {context,...} => HEADGOAL (asm_full_simp_tac context))
      val _ = if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
        ("clock_refinement prove_simp stage=proved label=" ^ label ^
          " elapsed_ms=" ^ Comma_Proof_Profile.elapsed_ms started) else ()
    in
      check label (mk_trueprop proposition) theorem
    end

  fun gcd_component_divisor check ctxt (period: int) (axis: int) =
    let
      val _ = if 0 <= axis andalso axis < 4 then ()
        else error "CRT GCD component axis is out of range"
      val radix = Data.axis_radix axis
      val component = period_component period axis
      val _ = if component > 0 andalso radix mod component = 0 then ()
        else error "CRT GCD component is not a positive divisor of its radix"
      val gcd_term = @{term "gcd::nat \<Rightarrow> nat \<Rightarrow> nat"} $
        nat radix $ nat period
      val gcd_value = prove_simp check ctxt
        "Closed CRT GCD component agrees with its numeral"
        (mk_eq (gcd_term,nat component)) @{thms gcd_nat.simps}
      val divisor = prove_simp check ctxt
        "GCD component divides its CRT radix"
        (@{term "(dvd)::nat \<Rightarrow> nat \<Rightarrow> bool"} $
          nat component $ nat radix)
        (gcd_value :: @{thms gcd_dvd1 dvd_eq_mod_eq_0
          numeral_mod_numeral})
    in {gcd_value=gcd_value,divisor=divisor} end

  fun period_guard_transport check ctxt (period_environment: period_environment)
      (proof_env: clock_env) =
    let
      val period = #period period_environment
      val compiler_env = #environment period_environment
      val _ = if period_env_extends period compiler_env proof_env then ()
        else error "External full CRT guard does not refine its gcd-period compiler guard"
      val phase = Free ("phase",natT)
      val full_guard = env_condition phase proof_env
      val canonical_guard = period_env_condition phase period compiler_env
      val proposition = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),full_guard),canonical_guard))
      val axis_transports = maps (fn axis =>
        (case (env_slot (compiler_env,axis),env_slot (proof_env,axis)) of
          (SOME canonical,SOME full) =>
            let
              val radix = Data.axis_radix axis
              val component = period_component period axis
              val {divisor,...} = gcd_component_divisor check ctxt period axis
              val slot_remainder = prove_simp check ctxt
                "External slot reduces to its checked canonical GCD slot"
                (mk_eq (mod_nat (nat full,nat component),nat canonical))
                @{thms gcd_nat.simps}
              val phase_selected = Free ("phase",natT)
              val phase_selected_guard = env_condition phase_selected proof_env
              val local_proposition = HOLogic.mk_all ("phase",natT,
                mk_imp (mk_conj (mk_less (phase_selected,nat 924),
                  phase_selected_guard),
                  mk_eq (mod_nat (phase_selected,nat component),
                    nat canonical)))
              val selected_from_guard_prop = HOLogic.mk_all ("phase",natT,
                mk_imp (mk_conj (mk_less (phase,nat 924),full_guard),
                  mk_eq (mod_nat (phase,nat radix),nat full)))
              val selected_from_guard = prove_simp check ctxt
                "Extract the assigned full CRT coordinate from its guard"
                selected_from_guard_prop []
              val slot_rule = Drule.infer_instantiate ctxt
                [(("radix",0),Thm.cterm_of ctxt (nat radix)),
                 (("gcd_residue",0),Thm.cterm_of ctxt (nat component)),
                 (("slot",0),Thm.cterm_of ctxt (nat full))]
                @{thm comma_crt_slot_gcd_residue_transport} OF [divisor]
              val axis_theorem = Goal.prove ctxt [] []
                (mk_trueprop local_proposition)
                (fn {context,...} =>
                  REPEAT_DETERM (resolve_tac context
                    [@{thm allI},@{thm impI}] 1) THEN
                  resolve_tac context [@{thm trans}] 1 THEN
                  resolve_tac context [slot_rule] 1 THEN
                  resolve_tac context
                    [selected_from_guard RS @{thm spec} RS @{thm mp}] 1 THEN
                  assume_tac context 1 THEN
                  resolve_tac context [slot_remainder] 1)
              val checked_axis = check
                "Full CRT slot selects its canonical GCD residue"
                (mk_trueprop local_proposition) axis_theorem
            in [checked_axis] end
        | (SOME _,NONE) =>
            error "Compiler GCD guard is missing its external CRT slot"
        | _ => [])) (0 upto 3)
      fun prove_guard [] context = resolve_tac context [@{thm TrueI}] 1
        | prove_guard [theorem] context =
            resolve_tac context [theorem RS @{thm spec} RS @{thm mp}] 1 THEN
            assume_tac context 1
        | prove_guard (theorem::rest) context =
            resolve_tac context [@{thm conjI}] 1 THEN
            prove_guard [theorem] context THEN
            prove_guard rest context
      val theorem = Goal.prove ctxt [] [] (mk_trueprop proposition)
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context [@{thm allI},@{thm impI}] 1) THEN
          prove_guard axis_transports context)
    in check "Full external CRT guard transports to the gcd-period compiler guard"
      (mk_trueprop proposition) theorem end

  fun phase_mod_period check ctxt (period_environment: period_environment) =
    let
      val phase = Free ("phase",natT)
      val period = #period period_environment
      val environment = #environment period_environment
      val representative = Compiler.phase_of_env environment
      val _ = if period > 0 andalso 924 mod period = 0 then ()
        else error "Source certificate action period is not a positive CRT divisor"
      val _ = List.app (fn axis =>
        (case env_slot (environment,axis) of
          SOME slot =>
            let val component = period_component period axis
            in if 0 <= slot andalso slot < component then ()
              else error "Source compiler environment slot is not gcd-canonical" end
        | NONE =>
            if Data.axis_weight axis mod period = 0 then ()
            else error "Source action leaf omits an active CRT axis")) (0 upto 3)
      val environment_guard = period_env_condition phase period environment
      val proposition = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj
          (mk_less (phase,nat 924),environment_guard),
          mk_eq (mod_nat (phase,nat period),
            mod_nat (nat representative,nat period))))
      fun general () = let
      val period_divides = prove_simp check ctxt
        "Checked local period divides the CRT clock"
        (@{term "(dvd)::nat \<Rightarrow> nat \<Rightarrow> bool"} $ nat period $ nat 924)
        @{thms dvd_eq_mod_eq_0}
      val component_obligations = maps (fn axis =>
        let
          val radix = Data.axis_radix axis
          val weight = Data.axis_weight axis
          val component = period_component period axis
          val {gcd_value,divisor} = gcd_component_divisor check ctxt period axis
          val obligation = (case env_slot (environment,axis) of
            SOME _ => prove_simp check ctxt
              "CRT weight annihilates the quotient after gcd projection"
              (@{term "(dvd)::nat \<Rightarrow> nat \<Rightarrow> bool"} $
                nat period $
                (@{term "(*)::nat \<Rightarrow> nat \<Rightarrow> nat"} $
                  nat weight $ nat component))
              @{thms comma_crt_axis_weight_def comma_crt_axis_radix_def
                gcd_nat.simps dvd_eq_mod_eq_0}
          | NONE => prove_simp check ctxt
              "Unassigned CRT axis is inactive at this action period"
              (mk_eq (mod_nat (nat weight,nat period),nat 0))
              @{thms comma_crt_axis_weight_def comma_crt_axis_radix_def})
          val phase_var = Free ("phase",natT)
          val phase_coordinate = mod_nat (phase_var,nat radix)
          val weighted_coordinate =
            @{term "(*)::nat \<Rightarrow> nat \<Rightarrow> nat"} $
              nat weight $ phase_coordinate
          val phase_transport = (case env_slot (environment,axis) of
            SOME _ =>
              let
                val reduced_coordinate = mod_nat (phase_var,nat component)
                val reduced_weighted =
                  @{term "(*)::nat \<Rightarrow> nat \<Rightarrow> nat"} $
                    nat weight $ reduced_coordinate
                val local_proposition = HOLogic.mk_all ("phase",natT,
                  mk_eq (mod_nat (weighted_coordinate,nat period),
                    mod_nat (reduced_weighted,nat period)))
                val specialized =
                  @{thm comma_crt_weighted_gcd_residue_transport} OF
                    [divisor,obligation]
              in prove_simp check ctxt
                "Weighted CRT residue is transported through this axis GCD"
                local_proposition [specialized,gcd_value] end
          | NONE =>
              let
                val local_proposition = HOLogic.mk_all ("phase",natT,
                  mk_eq (mod_nat (weighted_coordinate,nat period),nat 0))
                val reduced_weighted = mod_nat
                  (@{term "(*)::nat \<Rightarrow> nat \<Rightarrow> nat"} $
                    mod_nat (nat weight,nat period) $ phase_coordinate,
                   nat period)
                val normalized_proposition = HOLogic.mk_all ("phase",natT,
                  mk_eq (mod_nat (weighted_coordinate,nat period),
                    reduced_weighted))
                val normalized_theorem = Goal.prove ctxt [] []
                  (mk_trueprop normalized_proposition)
                  (fn {context,...} =>
                    resolve_tac context [@{thm allI}] 1 THEN
                    resolve_tac context
                      [@{thm mod_mult_left_eq[symmetric]}] 1)
                  |> check "Inactive CRT product reduces its left coefficient"
                    (mk_trueprop normalized_proposition)
                val zero_proposition = HOLogic.mk_all ("phase",natT,
                  mk_eq (reduced_weighted,nat 0))
                val zero_theorem = prove_simp check ctxt
                  "Inactive CRT weight has zero reduced product"
                  zero_proposition
                  (obligation :: @{thms mult_0 mod_0})
                val normalized_at_phase = normalized_theorem RS @{thm spec}
                val zero_at_phase = zero_theorem RS @{thm spec}
                val theorem = Goal.prove ctxt [] []
                  (mk_trueprop local_proposition)
                  (fn {context,...} =>
                    resolve_tac context [@{thm allI}] 1 THEN
                    resolve_tac context [@{thm trans}] 1 THEN
                    resolve_tac context [normalized_at_phase] 1 THEN
                    resolve_tac context [zero_at_phase] 1)
              in check "Inactive CRT weight contributes zero at this period"
                (mk_trueprop local_proposition) theorem end)
        in [divisor,gcd_value,obligation,phase_transport] end) (0 upto 3)
      val add_nat = @{term "(+)::nat \<Rightarrow> nat \<Rightarrow> nat"}
      val multiply_nat = @{term "(*)::nat \<Rightarrow> nat \<Rightarrow> nat"}
      fun sum_four [a,b,c,d] =
            add_nat $ (add_nat $ (add_nat $ a $ b) $ c) $ d
        | sum_four _ = error "CRT residue sum does not have four coordinates"
      val representative_terms = map (fn axis =>
        let
          val coordinate = (case env_slot (environment,axis) of
            NONE => 0 | SOME slot => slot)
        in multiply_nat $ nat (Data.axis_weight axis) $ nat coordinate end)
        (0 upto 3)
      val representative_sum = sum_four representative_terms
      val representative_equation = prove_simp check ctxt
        "Compiler CRT representative is the checked weighted coordinate sum"
        (mk_eq (nat representative,mod_nat (representative_sum,nat 924)))
        @{thms comma_crt_axis_weight_def comma_crt_axis_radix_def}
      val checked_clock_mod = @{thm comma_crt_clock_mod} OF [period_divides]
      val clock = @{term comma_crt_clock} $ phase
      val phase_to_clock_prop = HOLogic.mk_all ("phase",natT,
        mk_eq (mod_nat (phase,nat period),mod_nat (clock,nat period)))
      val phase_to_clock = Goal.prove ctxt [] []
        (mk_trueprop phase_to_clock_prop)
        (fn {context,...} =>
          resolve_tac context [@{thm allI}] 1 THEN
          resolve_tac context [checked_clock_mod RS @{thm sym}] 1)
        |> check "CRT clock residue equals the phase residue at the local period"
          (mk_trueprop phase_to_clock_prop)
      val clock_to_representative_prop = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),environment_guard),
          mk_eq (mod_nat (clock,nat period),
            mod_nat (nat representative,nat period))))
      val phase_weighted_terms = map (fn axis =>
        multiply_nat $ nat (Data.axis_weight axis) $
          mod_nat (phase,nat (Data.axis_radix axis))) (0 upto 3)
      val phase_weighted_sum =
        (case phase_weighted_terms of
          [a,b,c,d] => add_nat $ (add_nat $ (add_nat $ a $ b) $ c) $ d
        | _ => error "CRT weighted phase sum does not have four coordinates")
      val phase_residue_terms = map
        (fn term => mod_nat (term,nat period)) phase_weighted_terms
      val representative_residue_terms = map
        (fn term => mod_nat (term,nat period)) representative_terms
      fun residue_sum_four [a,b,c,d] =
            let
              val first = mod_nat (add_nat $ a $ b,nat period)
              val second = mod_nat (add_nat $ first $ c,nat period)
            in mod_nat (add_nat $ second $ d,nat period) end
        | residue_sum_four _ =
            error "CRT residue sum does not have four coordinates"
      val phase_residue_sum = residue_sum_four phase_residue_terms
      val representative_residue_sum =
        residue_sum_four representative_residue_terms
      val clock_mod_cancel = @{thm mod_mod_cancel} OF [period_divides]
      val clock_raw_prop = HOLogic.mk_all ("phase",natT,
        mk_eq (mod_nat (clock,nat period),
          mod_nat (phase_weighted_sum,nat period)))
      val clock_raw_theorem = Goal.prove ctxt [] []
        (mk_trueprop clock_raw_prop)
        (fn {context,...} =>
          resolve_tac context [@{thm allI}] 1 THEN
          simp_tac (put_simpset HOL_basic_ss context
            |> Simplifier.add_simps
              [@{thm comma_crt_clock_def},clock_mod_cancel]) 1)
        |> check "CRT clock reduces to its checked weighted coordinate sum"
          (mk_trueprop clock_raw_prop)
      val clock_raw_at_phase = clock_raw_theorem RS @{thm spec}
      val representative_mod_prop = mk_eq
        (mod_nat (nat representative,nat period),
         mod_nat (representative_sum,nat period))
      val representative_congruence = Goal.prove ctxt [] []
        (mk_trueprop (mk_eq
          (mod_nat (nat representative,nat period),
           mod_nat (mod_nat (representative_sum,nat 924),nat period))))
        (fn {context,...} =>
          resolve_tac context [@{thm arg_cong}] 1 THEN
          resolve_tac context [representative_equation] 1)
        |> check "Representative period projection follows its checked equation"
          (mk_trueprop (mk_eq
            (mod_nat (nat representative,nat period),
             mod_nat (mod_nat (representative_sum,nat 924),nat period))))
      val representative_mod_theorem = Goal.prove ctxt [] []
        (mk_trueprop representative_mod_prop)
        (fn {context,...} =>
          resolve_tac context [@{thm trans}] 1 THEN
          resolve_tac context [representative_congruence] 1 THEN
          resolve_tac context [clock_mod_cancel] 1)
        |> check "Representative residue equals its weighted coordinate sum"
          (mk_trueprop representative_mod_prop)
      val phase_sum_prop = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),environment_guard),
          mk_eq (mod_nat (phase_weighted_sum,nat period),
            mod_nat (representative_sum,nat period))))
      val phase_transport_rules = map
        (fn axis => List.nth (component_obligations,axis*4+3)) (0 upto 3)
      val phase_residue_prop = HOLogic.mk_all ("phase",natT,
        mk_eq (mod_nat (phase_weighted_sum,nat period),phase_residue_sum))
      val phase_residue_theorem = Goal.prove ctxt [] []
        (mk_trueprop phase_residue_prop)
        (fn {context,...} =>
          resolve_tac context [@{thm allI}] 1 THEN
          resolve_tac context [@{thm comma_crt_mod_four_sum}] 1)
        |> check "CRT weighted phase sum has its exact four-residue form"
          (mk_trueprop phase_residue_prop)
      val representative_residue_prop = mk_eq
        (mod_nat (representative_sum,nat period),representative_residue_sum)
      val representative_residue_theorem = Goal.prove ctxt [] []
        (mk_trueprop representative_residue_prop)
        (fn {context,...} =>
          resolve_tac context [@{thm comma_crt_mod_four_sum}] 1)
        |> check "Compiler representative has its exact four-residue form"
          (mk_trueprop representative_residue_prop)
      val residue_term_facts = map_index (fn (axis,phase_rule) =>
        let
          val phase_rule_at = phase_rule RS @{thm spec}
          val phase_term = Free ("phase",natT)
          val term_proposition = HOLogic.mk_all ("phase",natT,
            mk_imp (mk_conj (mk_less (phase_term,nat 924),environment_guard),
              mk_eq (List.nth (phase_residue_terms,axis),
                List.nth (representative_residue_terms,axis))))
        in prove_simp check ctxt "Guarded CRT coordinate residue"
          term_proposition (phase_rule_at ::
            @{thms mult_0_right mult_0 mod_0}) end) phase_transport_rules
      val residue_term_rules = map
        (fn theorem => theorem RS @{thm spec} RS @{thm mp}) residue_term_facts
      val residue_transport_prop = HOLogic.mk_all ("phase",natT,
        mk_imp (mk_conj (mk_less (phase,nat 924),environment_guard),
          mk_eq (phase_residue_sum,representative_residue_sum)))
      val residue_transport_theorem = Goal.prove ctxt [] []
        (mk_trueprop residue_transport_prop)
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context
            [@{thm allI},@{thm impI}] 1) THEN
          asm_full_simp_tac
            (put_simpset HOL_basic_ss context
              |> Simplifier.add_simps
                (Comma_Proof_Rewrite_Rules.nonreflexive_rules
                  (residue_term_rules @
                    @{thms add_0_left add_0_right mult_0_right mult_0 mod_0}))) 1)
        |> check "GCD guards identify the checked four phase residues"
          (mk_trueprop residue_transport_prop)
      val phase_residue_at_phase = phase_residue_theorem RS @{thm spec}
      val residue_transport_at_phase = residue_transport_theorem RS
        @{thm spec} RS @{thm mp}
      val representative_residue_reverse =
        representative_residue_theorem RS @{thm sym}
      val phase_sum_theorem = Goal.prove ctxt [] []
        (mk_trueprop phase_sum_prop)
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context
            [@{thm allI},@{thm impI}] 1) THEN
          resolve_tac context [@{thm trans}] 1 THEN
          resolve_tac context [phase_residue_at_phase] 1 THEN
          resolve_tac context [@{thm trans}] 1 THEN
          resolve_tac context [residue_transport_at_phase] 1 THEN
          assume_tac context 1 THEN
          resolve_tac context [representative_residue_reverse] 1)
        |> check "GCD guards identify phase and compiler weighted residues"
          (mk_trueprop phase_sum_prop)
      val phase_sum_at_phase = phase_sum_theorem RS @{thm spec} RS @{thm mp}
      val clock_to_representative = Goal.prove ctxt [] []
        (mk_trueprop clock_to_representative_prop)
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context
            [@{thm allI},@{thm impI}] 1) THEN
          resolve_tac context [@{thm trans}] 1 THEN
          resolve_tac context [clock_raw_at_phase] 1 THEN
          resolve_tac context [@{thm trans}] 1 THEN
          resolve_tac context [phase_sum_at_phase] 1 THEN
          assume_tac context 1 THEN
          resolve_tac context [representative_mod_theorem RS @{thm sym}] 1)
        |> check "CRT clock residue equals its gcd-reduced compiler representative"
          (mk_trueprop clock_to_representative_prop)
      val theorem = Goal.prove ctxt [] [] (mk_trueprop proposition)
        (fn {context,...} =>
          REPEAT_DETERM (resolve_tac context [@{thm allI},@{thm impI}] 1) THEN
          resolve_tac context [@{thm trans}] 1 THEN
          resolve_tac context [phase_to_clock RS @{thm spec}] 1 THEN
          resolve_tac context
            [clock_to_representative RS @{thm spec} RS @{thm mp}] 1 THEN
          assume_tac context 1)
        |> check "Source action clock environment after gcd quotienting"
          (mk_trueprop proposition)
      in theorem end
    in
      if period = 1 then
        prove_simp check ctxt "Unit-period CRT residue is constant"
          proposition @{thms mod_by_1}
      else general ()
    end
end
