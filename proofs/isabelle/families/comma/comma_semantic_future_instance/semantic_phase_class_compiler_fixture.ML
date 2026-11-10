(* Candidate construction is deliberately separate from source admission. *)
structure Comma_Semantic_Phase_Class_Compiler_Fixture =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Candidate = Comma_Semantic_Phase_Class_Rank_Candidate
  structure Compiler = Comma_Semantic_Phase_Action_Program_Compiler
  structure Pointwise = Comma_Semantic_Phase_Action_Program_Certificate
  structure Shallow = Comma_Semantic_Weighted_CRT_Shallow_Certificate
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport
  structure Names = Table
  (
    type key = Data.identity
    val ord = Data.identity_ord
  )

  fun rejects label operation =
    (case Exn.capture operation () of
      Exn.Exn (ERROR _) => ()
    | Exn.Exn failure => Exn.reraise failure
    | Exn.Res _ => error ("Phase-class candidate accepted " ^ label))

  fun scalar_row_fixtures ctxt evaluator fixed_port_rules =
    let
      val row_name = @{const_name comma_entry_port_row}
      val natT = @{typ nat}
      val number = HOLogic.mk_number natT
      fun row_at eta = @{term comma_entry_port_row} $ number 1 $ number 0 $ eta
      val row = row_at (number 0)
      val phased_row = row_at (HOLogic.mk_binop @{const_name modulo}
        (HOLogic.mk_binop @{const_name modulo} (number 0,number 924),number 11))
      val duplicate = HOLogic.mk_binop @{const_name plus} (row,phased_row)
      val normalizations = Unsynchronized.ref 0
      val conversions = Unsynchronized.ref 0
      fun normalize call =
        let
          val _ = normalizations := !normalizations + 1
          val context = Compiler.closed_evaluator_context ctxt
            |> Simplifier.del_simps @{thms comma_entry_port_row_def}
        in #theorem (Transport.checked_rewrite_in ctxt context
          "Canonical scalar-row fixture input"
          (@{thms comma_entry_port_row_def} @ Compiler.action_structure_rules @
            fixed_port_rules) call) end
      fun convert call =
        let
          val _ = conversions := !conversions + 1
          val converted = Compiler.local_code_rewrite ctxt evaluator
            "Entry scalar row fixture" call
          val _ = ignore (Compiler.dest_nat "Scalar-row fixture result" (#term converted))
        in #theorem converted end
      val result = Transport.checked_subterm_rewrite ctxt
        "Entry scalar row fixture" row_name 3 natT duplicate normalize convert
      val _ = if #calls result=2 andalso #canonical_calls result=1 andalso
          !normalizations=2 andalso !conversions=1 then ()
        else error "Equivalent closed scalar rows were not normalized and converted once"
      val rejected_calls = Unsynchronized.ref 0
      fun forbidden_converter _ =
        (rejected_calls := !rejected_calls + 1;
         error "Rejected scalar-row fixture reached its converter")
      val rejected_normalizations = Unsynchronized.ref 0
      fun forbidden_normalizer _ =
        (rejected_normalizations := !rejected_normalizations + 1;
         error "Rejected scalar-row fixture reached its normalizer")
      val partial = @{term comma_entry_port_row} $ HOLogic.mk_number natT 1
      val open_call = @{term comma_entry_port_row} $ HOLogic.mk_number natT 1 $
        HOLogic.mk_number natT 2 $ Free ("open_row_argument",natT)
      val _ = rejects "a partial scalar row" (fn () =>
        Transport.checked_subterm_rewrite ctxt "Partial scalar row fixture"
          row_name 3 natT partial forbidden_normalizer forbidden_converter)
      val _ = rejects "an open scalar row" (fn () =>
        Transport.checked_subterm_rewrite ctxt "Open scalar row fixture"
          row_name 3 natT open_call forbidden_normalizer forbidden_converter)
      val _ = rejects "a scalar row with the wrong result type" (fn () =>
        Transport.checked_subterm_rewrite ctxt "Mistyped scalar row fixture"
          row_name 3 HOLogic.boolT row forbidden_normalizer forbidden_converter)
      val _ = if !rejected_normalizations=0 andalso !rejected_calls=0 then ()
        else error "Invalid scalar-row fixture ran work before rejection"
    in () end

  fun direct_scalar_fixtures ctxt oracle =
    let
      val natT = @{typ nat}
      fun number n = HOLogic.mk_number natT n
      fun core_period core =
        let
          val expression = @{term comma_core_period} $ number core
          val reduced = Transport.checked_rewrite_in ctxt
            (Compiler.closed_evaluator_context ctxt) "Scalar fixture core period"
            @{thms comma_core_period_def} expression
        in Compiler.dest_nat "Scalar fixture core period" (#term reduced) end
      fun expression core exponent =
        let
          val residue = @{term comma_recursive_core_residue} $ number core $ number exponent
          val scaled_residue = HOLogic.mk_binop @{const_name times} (number 10,residue)
          val diagonal = @{term comma_entry_diagonal} $ number (10*core) $ number 0 $
            scaled_residue
          val int_of_nat = @{term "int :: nat => int"}
          val diagonal_int = int_of_nat $ diagonal
          val offset_int = int_of_nat $ number (2*core+1)
          val modulus_int = int_of_nat $ number core
          val negative = HOLogic.mk_binop @{const_name minus}
            (diagonal_int,offset_int)
          val remainder = HOLogic.mk_binop @{const_name modulo}
            (negative,modulus_int)
        in @{term "nat :: int => nat"} $ remainder end
      fun exponents core =
        let val period=core_period core
        in distinct (op =) ([0,period-1,period] @
          (if core=29 then [6,7,27,28] else [])) end
      fun compare label expected input =
        let
          val direct = Transport.checked_rewrite_in ctxt
            (Compiler.closed_evaluator_context ctxt) "Direct finite scalar arithmetic"
            Compiler.entry_scalar_arithmetic_rules input
          val oracle_theorem = oracle ctxt (Thm.cterm_of ctxt input)
          val checked_oracle = Transport.checked_closed ctxt "Code_Simp scalar oracle"
            (Thm.prop_of oracle_theorem) oracle_theorem
          val direct_value = (case try HOLogic.dest_number (#term direct) of
            SOME (typ,value) => if typ=natT andalso value >= 0 then value
              else error ("Direct scalar result is not a natural numeral for " ^ label ^ ": " ^
                Transport.diagnostic_term_in ctxt (#term direct))
          | NONE => error ("Direct scalar reduction did not close " ^ label ^ ": " ^
              Transport.diagnostic_term_in ctxt (#term direct)))
          val oracle_value = Compiler.dest_nat "Code_Simp scalar value"
            (Thm.term_of (Thm.rhs_of checked_oracle))
          val _ = if Thm.term_of (Thm.lhs_of checked_oracle) aconv input then ()
            else error "Code_Simp scalar oracle changed its exact input"
          val _ = (case expected of
            NONE => ()
          | SOME value => if direct_value=value then ()
              else error ("Direct scalar regression changed for " ^ label))
        in if direct_value=oracle_value then ()
          else error ("Direct scalar reduction disagrees with Code_Simp for " ^ label) end
      val cases = maps (fn core => map (pair core) (exponents core))
        [1,3,7,11,13,21,23,27,29]
      val _ = List.app (fn (core,exponent) =>
        compare ("core " ^ Int.toString core ^ " exponent " ^ Int.toString exponent)
          NONE (expression core exponent)) cases
      val int_of_nat = @{term "int :: nat => int"}
      val nat_of_int = @{term "nat :: int => nat"}
      val int_remainder = HOLogic.mk_binop @{const_name modulo}
        (HOLogic.mk_binop @{const_name times}
          (int_of_nat $ number 3,
           HOLogic.mk_binop @{const_name minus}
            (int_of_nat $ number 0,int_of_nat $ number 1)),
         int_of_nat $ number 4)
      val phase = nat_of_int $ int_remainder
      val core_clock = HOLogic.mk_binop @{const_name modulo}
        (HOLogic.mk_binop @{const_name plus}
          (HOLogic.mk_binop @{const_name plus}
            (number 1,HOLogic.mk_binop @{const_name times} (number 7,phase)),number 919),
         number 28)
      val core_residue = @{term comma_recursive_core_residue} $ number 29 $ core_clock
      val diagonal_residue = HOLogic.mk_binop @{const_name modulo}
        (HOLogic.mk_binop @{const_name times} (number 24,core_residue),number 29)
      val diagonal = @{term comma_entry_diagonal} $ number 290 $ number 7 $
        HOLogic.mk_binop @{const_name times} (number 10,diagonal_residue)
      val production_row = nat_of_int $ HOLogic.mk_binop @{const_name modulo}
        (HOLogic.mk_binop @{const_name minus} (int_of_nat $ diagonal,int_of_nat $ number 11),
         int_of_nat $ number 29)
      val _ = compare "production core-29 signed-diagonal row" (SOME 1) production_row
    in () end

  fun run ctxt =
    let
      val shared_source = @{term "Comma_Near 5 0 82"}
      val transported_source = @{term "Comma_Near 5 0 202"}
      val shared_program = Compiler.program_of_source ctxt shared_source
      val transported_program = Compiler.program_of_source ctxt transported_source
      val source_checker = Transport.make_scoped_checker ctxt
        "source_program_congruence_fixture"
      val same_program = Pointwise.source_program_same (#check source_checker) ctxt
        shared_program transported_program shared_source transported_source
      val _ = if Thm.nprems_of same_program=0 then ()
        else error "Shared source program retained unproved application guards"
      val distinct_source = @{term "Comma_Near 1 0 82"}
      val distinct_target = @{term "Comma_Near 1 0 92"}
      val _ = rejects "different Near residuals as one semantic action" (fn () =>
        Pointwise.source_program_same (#check source_checker) ctxt
          (Compiler.program_of_source ctxt distinct_source)
          (Compiler.program_of_source ctxt distinct_target)
          distinct_source distinct_target)
      val reporter_failure = Exn.capture (fn () =>
        Transport.capture_with_failure_counts "reporter failure fixture"
          (fn () => error "diagnostic counter failed")
          (fn () => error "original operation failed")) ()
      val _ = (case reporter_failure of
        Exn.Exn (ERROR actual) => if actual="original operation failed" then ()
          else error ("Failure reporter replaced the source error: " ^ actual)
      | Exn.Exn failure => Exn.reraise failure
      | Exn.Res _ => error "Failure counter fixture accepted an operation failure")
      val source = @{term "Comma_Entry 1 0 0"}
      val _ = Comma_Proof_Profile.report
        "phase-action compiler fixture stage=source-program-start"
      val program = Comma_Semantic_Phase_Action_Program_Compiler.program_of_source
        ctxt source
      val other_program = Compiler.program_of_source ctxt
        @{term "Comma_Near 1 0 82"}
      val foreign_operator: Compiler.source_program =
        {source=source,program= #program program,equation= #equation program,
         operator_binding= #operator_binding other_program}
      val _ = rejects "a source binding with another program's universal operator"
        (fn () => ignore (Compiler.validate_source_operator_binding ctxt foreign_operator))
      val _ = rejects "a nonzero occurrence shift as a normalized source binding"
        (fn () => ignore (Compiler.program_of_source ctxt
          @{term "Comma_Entry 1 1 0"}))
      val _ = Comma_Proof_Profile.report
        "phase-action compiler fixture stage=source-program-done"
      val _ = Comma_Semantic_Phase_Action_Program_Compiler.key_of_program
        (#program program)
      val evaluator =
        Comma_Semantic_Phase_Action_Program_Compiler.make_local_action_evaluator ctxt
      val scalar_oracle = Code_Simp.static_conv {ctxt=ctxt,simpset=NONE,
        consts=[@{const_name comma_entry_diagonal},
          @{const_name comma_recursive_core_residue}]}
      val fixed_port = Compiler.fixed_entry_port ctxt evaluator 1 0
      val _ = direct_scalar_fixtures ctxt scalar_oracle
      val _ = scalar_row_fixtures ctxt scalar_oracle (#rules fixed_port)
      val program_term = #program program
      val program_key = Compiler.key_of_program program_term
      val {period,...} = Compiler.period_of_key ctxt program_key
      val _ = if period=22 then ()
        else error "Canonical compiler fixture lost its 22-step Entry period"
      fun quotient_row row_axis row_period row_key =
        map (fn (raw_slot,(_,child_env)) =>
          (raw_slot,Compiler.env_slot child_env row_axis))
          (Compiler.child_key_row row_period row_key Compiler.empty_env row_axis)
      val period_two_program = Compiler.program_of_source ctxt
        @{term "Comma_Entry 4 0 0"}
      val period_two_key = Compiler.key_of_program (#program period_two_program)
      val {period=period_two,...} = Compiler.period_of_key ctxt period_two_key
      val period_two_axis_zero = quotient_row 0 period_two period_two_key
      val period_twenty_two_axis_zero = quotient_row 0 22 program_key
      val period_twenty_two_axis_three = quotient_row 3 22 program_key
      val _ = if period_two=2 andalso period_two_axis_zero =
          [(0,SOME 0),(1,SOME 1),(2,SOME 0),(3,SOME 1)] andalso
          period_twenty_two_axis_zero =
            [(0,SOME 0),(1,SOME 1),(2,SOME 0),(3,SOME 1)] andalso
          period_twenty_two_axis_three =
            map (fn slot => (slot,SOME slot)) (0 upto 10) then ()
        else error "GCD quotient changed the ordered physical CRT child rows"
      val period_twenty_eight_program = Compiler.program_of_source ctxt
        @{term "Comma_Entry 8 0 1"}
      val period_twenty_eight_key =
        Compiler.key_of_program (#program period_twenty_eight_program)
      val {period=period_twenty_eight,...} =
        Compiler.period_of_key ctxt period_twenty_eight_key
      val period_twenty_eight_axis_zero =
        quotient_row 0 period_twenty_eight period_twenty_eight_key
      val period_twenty_eight_axis_two =
        quotient_row 2 period_twenty_eight period_twenty_eight_key
      val active_twenty_two_axes = List.filter
        (fn axis => Data.axis_weight axis mod 22 <> 0) (0 upto 3)
      val active_twenty_eight_axes = List.filter
        (fn axis => Data.axis_weight axis mod 28 <> 0) (0 upto 3)
      val active_two_axes = List.filter
        (fn axis => Data.axis_weight axis mod 2 <> 0) (0 upto 3)
      val _ = if active_two_axes=[0] andalso period_twenty_eight=28 andalso
          period_twenty_eight_key <> program_key andalso
          period_twenty_eight_axis_zero =
            map (fn slot => (slot,SOME slot)) (0 upto 3) andalso
          period_twenty_eight_axis_two =
            map (fn slot => (slot,SOME slot)) (0 upto 6) andalso
          active_twenty_two_axes=[0,3] andalso active_twenty_eight_axes=[0,2]
        then () else error "Period-22/28 axis activity or GCD rows changed"
      val operator_equation = Compiler.operator_for_program_with_rules ctxt program_term
        (#rules fixed_port)
      val action_arena = Data.make_arena 128
      val stale_cache = Unsynchronized.ref (NONE: Compiler.local_action_cache option)
      val action_totals = {hits=Unsynchronized.ref 0,misses=Unsynchronized.ref 0}
      val _ = Comma_Proof_Profile.report
        "phase-action compiler fixture stage=source-action-start"
      val (action,period_shifted_action,wrong_phase_action,action_cache_stats,
          action_scratch_counts) =
        Data.with_reservation action_arena (fn reservation =>
          let
            val cache = Compiler.make_local_action_cache ctxt evaluator
              action_arena reservation (fn f => fn d =>
                if (f,d)=(1,0) then #rules fixed_port
                else error "Compiler fixture requested another fixed port") action_totals
            val _ = stale_cache := SOME cache
            val reduce = #reduce cache
            val phase0 = Compiler.phase_of_env Compiler.empty_env
            val phase_period = Compiler.phase_of_env
              (SOME 2,SOME 1,SOME 1,SOME 0)
            val phase_wrong = Compiler.phase_of_env
              (SOME 3,SOME 2,SOME 2,SOME 1)
            val _ = if phase0=0 andalso phase_period=period andalso
                phase_wrong=period+1 then ()
              else error "Compiler fixture did not construct its distinct CRT environments"
            val scratch_before = #scratch_entries (Data.stats action_arena)
            fun at phase = #action (Compiler.action_at_source_checked_using
              ctxt reduce program phase operator_equation)
            val first = at phase0
            val scratch_first = #scratch_entries (Data.stats action_arena)
            val same_action = at phase_period
            val scratch_hit = #scratch_entries (Data.stats action_arena)
            val distinct_phase_action = at phase_wrong
            val scratch_second = #scratch_entries (Data.stats action_arena)
            val stats = #statistics cache ()
            val failing_cache = Compiler.make_local_action_cache ctxt evaluator
              action_arena reservation (fn _ => fn _ =>
                error "Forced local-action cache fixture failure") action_totals
            val failure_scratch_before = #scratch_entries (Data.stats action_arena)
            val _ = rejects "temporary scalar-row failure" (fn () => ignore
              (Compiler.action_at_source_checked_using ctxt (#reduce failing_cache)
                program phase0 operator_equation))
            val failure_scratch_after = #scratch_entries (Data.stats action_arena)
            val _ = if failure_scratch_before=failure_scratch_after then ()
              else error "Failed scalar-row work leaked scratch reservations"
          in (first,same_action,distinct_phase_action,stats,
            (scratch_before,scratch_first,scratch_hit,scratch_second)) end)
      val action_cache_final_stats = Data.stats action_arena
      val totals_before_stale = (!(#hits action_totals),!(#misses action_totals))
      val _ = rejects "an expired local-action cache" (fn () =>
        case !stale_cache of
          SOME cache => ignore (Compiler.action_at_source_checked_using ctxt
            (#reduce cache) program 0 operator_equation)
        | NONE => error "Compiler fixture lost its local-action cache")
      val totals_after_stale = (!(#hits action_totals),!(#misses action_totals))
      val _ = if totals_before_stale=totals_after_stale andalso
          #scratch_entries (Data.stats action_arena)=0 then ()
        else error "Expired local-action cache performed work after its reservation ended"
      val _ = if #hits action_cache_stats=1 andalso
          #misses action_cache_stats=2 then ()
        else error "Exact local-action cache did not reuse only the period-equivalent phase"
      val _ = (case action_scratch_counts of
        (initial,first,hit,second) =>
          if first=initial+1 andalso hit=first andalso second=hit+1 andalso
              #scratch_entries action_cache_final_stats=0 then ()
          else error "Local-action scratch accounting retained transient row work")
      val _ = if action aconv period_shifted_action then ()
        else error "Period-equivalent CRT environments changed the certified action"
      val (child_zero,child_shifted) =
        (case (Compiler.goto_parts action,
            Compiler.goto_parts period_shifted_action) of
          (SOME (left,0),SOME (right,0)) => (left,right)
        | _ => error "Admitted Entry fixture no longer selects its certified Goto")
      val child_program = Compiler.program_of_source ctxt child_zero
      val child_key = Compiler.global_child_key (#program child_program)
      val {period=child_period,...} =
        Compiler.period_of_key ctxt (#1 child_key)
      val _ = if child_period=6 andalso child_period<>period then ()
        else error "The period-22 Goto did not preserve its distinct child period"
      val scoped = Transport.make_scoped_checker ctxt "assigned_axis_fixture"
      val checked = #check scoped
      fun set_env_slot ((a,b,c,d): Compiler.clock_env) axis slot:
          Compiler.clock_env =
        (case axis of
          0 => (slot,b,c,d)
        | 1 => (a,slot,c,d)
        | 2 => (a,b,slot,d)
        | 3 => (a,b,c,slot)
        | _ => error "Fixture CRT axis is outside 0..3")
      fun canonical_env local_period key =
        fold (fn axis => fn env =>
          if Data.axis_weight axis mod local_period = 0 then env
          else
            (case Compiler.child_key_row local_period key env axis of
              (_,(_,child_env))::_ => child_env
            | _ => error "Compiler omitted a physical CRT child row"))
          (0 upto 3) Compiler.empty_env
      fun full_guard_env local_period canonical =
        fold (fn axis => fn env =>
          (case Compiler.env_slot canonical axis of
            NONE => env
          | SOME canonical_slot =>
              let
                val component = Compiler.period_component local_period axis
                val raw_slot = if component < Data.axis_radix axis
                  then canonical_slot + component else canonical_slot
              in set_env_slot env axis (SOME raw_slot) end))
          (0 upto 3) Compiler.empty_env
      fun theorem_is_closed theorem =
        Thm.nprems_of theorem=0 andalso null (Thm.hyps_of theorem) andalso
        null (Thm.tpairs_of theorem)
      val period_transport_theorems = Unsynchronized.ref ([]: thm list)
      fun check_period_transport (local_period,local_key) =
        let
          val canonical = canonical_env local_period local_key
          val external = full_guard_env local_period canonical
          val period_environment =
            {period=local_period,environment=canonical}
          val phase_theorem = Pointwise.phase_mod_period checked ctxt
            period_environment
          val guard_theorem = Pointwise.period_guard_transport checked ctxt
            period_environment external
          val _ = if theorem_is_closed phase_theorem andalso
              theorem_is_closed guard_theorem then
            period_transport_theorems := phase_theorem :: guard_theorem ::
              !period_transport_theorems
          else error "GCD period fixture emitted an open theorem"
        in (canonical,external) end
      val (canonical_two,external_two) =
        check_period_transport (period_two,period_two_key)
      val _ = check_period_transport (6,#1 child_key)
      val _ = check_period_transport (22,program_key)
      val (canonical_twenty_eight,external_twenty_eight) =
        check_period_transport (period_twenty_eight,period_twenty_eight_key)
      val _ = #audit scoped "GCD period fixture theorem bundle"
        (rev (!period_transport_theorems))
      val _ = if canonical_two <> external_two andalso
          canonical_twenty_eight=external_twenty_eight then ()
        else error "GCD guard fixtures failed to distinguish reduced and full CRT slots"
      val negative_period_key = #1 child_key
      val negative_period = child_period
      val negative_canonical = canonical_env negative_period negative_period_key
      val negative_external = full_guard_env negative_period negative_canonical
      val negative_axis = hd (List.filter
        (fn axis => Data.axis_weight axis mod negative_period <> 0) (0 upto 3))
      val wrong_external = set_env_slot negative_external negative_axis (SOME 1)
      val omitted_environment = set_env_slot negative_canonical negative_axis NONE
      val _ = rejects "a noncongruent full CRT guard in period transport" (fn () =>
        ignore (Pointwise.period_guard_transport checked ctxt
          {period=negative_period,environment=negative_canonical} wrong_external))
      val _ = rejects "an omitted active GCD coordinate" (fn () =>
        ignore (Pointwise.phase_mod_period checked ctxt
          {period=negative_period,environment=omitted_environment}))
      (* Independent sector arithmetic at exponents 22 and 44: whole
         last-digit cycles displace 460; the final nine literal steps cross
         into sector 2 at offset 70.  Exponent 23 crosses at offset 49. *)
      val _ = if child_zero aconv @{term "Comma_Entry 2 0 70"} andalso
          (case Compiler.goto_parts wrong_phase_action of
            SOME (child,0) => child aconv @{term "Comma_Entry 2 0 49"}
          | _ => false) then ()
        else error ("Entry fixture disagrees with independent sector arithmetic: " ^
          Syntax.string_of_term ctxt action)
      val _ = (case Compiler.key_of_program (#program child_program) of
          Compiler.Entry_Core (2,0,70,21) => ()
        | _ => error "Entry fixture Goto lost its checked sector-2 core")
      val _ = if child_zero aconv child_shifted andalso #2 child_key=Compiler.empty_env
        then () else error "Equivalent parent clocks changed the source-independent Goto key"
      val _ = Comma_Proof_Profile.report
        "phase-action compiler fixture stage=source-action-done"
      val _ = (case Term.head_of action of
          Const (name,_) =>
            if member (op =) [@{const_name Comma_Continuation_Goto},
                @{const_name Comma_Continuation_Exit},
                @{const_name Comma_Continuation_Fork},
                @{const_name Comma_Continuation_Landmine}] name then ()
            else error "Canonical source did not reduce to a valid port action"
        | _ => error "Source program left its port action unresolved")
      (* A selected external axis must cofactor the exact same named target
         differently for distinct parent environments, without extending or
         rewriting either environment. *)
      val target_arena = Data.make_arena 128
      fun nat n = HOLogic.mk_number @{typ nat} n
      fun action_leaf slot =
        let
          val value = Const (@{const_name Comma_Phase_Rank_Mask_Fork},
            @{typ nat} --> @{typ nat} --> @{typ comma_phase_rank_mask_action}) $
            nat slot $ nat 0
          val diagram = Data.leaf target_arena
            {key="assigned-axis-fixture:" ^ Int.toString slot,value=value}
          val term = Const (@{const_name Comma_Weighted_CRT_Leaf},
            @{typ comma_phase_rank_mask_action} -->
              @{typ "comma_phase_rank_mask_action comma_semantic_weighted_crt_dag"}) $
            value
        in (diagram,{term=term,
          definition=Thm.reflexive (Thm.cterm_of ctxt term)}) end
      val action_children = map action_leaf [0,1,2,3]
      val action_treeT = @{typ "comma_phase_rank_mask_action comma_semantic_weighted_crt_dag"}
      val edgeT = HOLogic.mk_prodT (@{typ nat},action_treeT)
      val branch_term = Const (@{const_name Comma_Weighted_CRT_Branch},
          @{typ nat} --> HOLogic.listT edgeT --> action_treeT) $ nat 0 $
        HOLogic.mk_list edgeT (map (fn (_,entry) =>
          HOLogic.mk_prod (nat 0,#term entry)) action_children)
      val action_target = Data.raw_branch target_arena 0
        (map (fn (diagram,_) => (0,diagram)) action_children)
      val target_entry = {term=branch_term,
        definition=Thm.reflexive (Thm.cterm_of ctxt branch_term)}
      val named_nodes = fold (fn (diagram,entry) => Names.update
        (Data.identity target_arena diagram,entry))
        ((action_target,target_entry)::action_children) Names.empty
      fun lookup diagram = Names.lookup named_nodes (Data.identity target_arena diagram)
      val shallow = Shallow.make ctxt target_arena
        @{typ comma_phase_rank_mask_action} {lookup=lookup,ensure_named=NONE}
      val selected_two = #cofactor shallow action_target 0 2
      val selected_one = #cofactor shallow action_target 0 1
      val _ = if Data.identity target_arena (#result selected_two) =
          Data.identity target_arena (#1 (List.nth (action_children,2))) andalso
          Data.identity target_arena (#result selected_one) =
          Data.identity target_arena (#1 (List.nth (action_children,1))) andalso
          Data.identity target_arena (#result selected_two) <>
          Data.identity target_arena (#result selected_one)
        then () else error "Assigned clock environments selected the wrong target cofactor"
      val arena = Data.make_arena 128
      val terminal = Data.leaf arena
        {key="class-fixture:fork2",value = @{term "Comma_Phase_Rank_Mask_Fork 2 0"}}
      val stats_before = Data.stats arena
      val _ = Comma_Proof_Profile.report
        "phase-action compiler fixture stage=candidate-start"
      val constructed = Candidate.construct arena (replicate 46 terminal)
      val _ = Comma_Proof_Profile.report
        "phase-action compiler fixture stage=candidate-done"
      val _ = if #composition_levels constructed=5 andalso
          #covered_span constructed=32 andalso
          length (#ranks constructed)=46 then ()
        else error "Phase-class candidate changed its five-level rank composition"
      val _ = List.app (fn rank =>
        case Data.view arena rank of
          Data.View_Leaf {offset,payload={value,...}} =>
            if offset=0 andalso value aconv @{term "0::nat"} then ()
            else error "Terminal candidate has a nonzero rank"
        | Data.View_Branch _ => error "Terminal candidate manufactured clock branches")
        (#ranks constructed)
      val stats_after = Data.stats arena
      val _ = if #serialization_node_visits stats_after =
          #serialization_node_visits stats_before andalso
          #proof_entries stats_after = #proof_entries stats_before then ()
        else error "Candidate data construction serialized or published a theorem"

      (* Independent one-step oracle for a phase-dependent path.  Root zero
         continues to root one; root one continues to root two except at
         phase residue one, where it terminates.  This checks that each
         dyadic square shifts the receiving phase by its left span. *)
      val phase_arena = Data.make_arena 8192
      fun phase_leaf key value = Data.leaf phase_arena {key=key,value=value}
      val phase_terminal = phase_leaf "phase-fixture:terminal"
        @{term "Comma_Phase_Rank_Mask_Fork 2 0"}
      val phase_continue_one = phase_leaf "phase-fixture:continue1"
        @{term "Comma_Phase_Rank_Mask_Continue 1"}
      val phase_continue_two = phase_leaf "phase-fixture:continue2"
        @{term "Comma_Phase_Rank_Mask_Continue 2"}
      val phase_dependent_one = Data.raw_branch_diagrams phase_arena 0
        [phase_continue_two,phase_terminal,phase_continue_two,phase_continue_two]
      val phase_actions = phase_continue_one :: phase_dependent_one ::
        replicate 44 phase_terminal
      val phase_before = Data.stats phase_arena
      val phase_candidate = Candidate.construct phase_arena phase_actions
      val phase_after = Data.stats phase_arena
      val radices = [4,3,7,11]
      fun selected_value arena phase diagram =
        (case Data.view arena diagram of
          Data.View_Leaf {offset,payload={value,...}} =>
            if offset=0 then value
            else error "Candidate fixture found a weighted leaf"
        | Data.View_Branch {offset,axis,children} =>
            let
              val radix = List.nth (radices,axis)
              val (edge,child) = List.nth (children,phase mod radix)
              val _ = if offset=0 andalso edge=0 then ()
                else error "Candidate fixture found a weighted phase branch"
            in selected_value arena phase child end)
      fun numeral term =
        (case try HOLogic.dest_number term of
          SOME (typ,value) =>
            if typ = @{typ nat} andalso value >= 0 then IntInf.toInt value
            else error "Candidate fixture rank is not a natural numeral"
        | NONE => error "Candidate fixture rank did not normalize to a numeral")
      fun reference_action phase diagram =
        (case Term.strip_comb (selected_value phase_arena phase diagram) of
          (Const (name,_),[]) =>
            if name = @{const_name Comma_Phase_Rank_Mask_Invalid} then NONE
            else error "Candidate fixture saw an unknown nullary action"
        | (Const (name,_),[child]) =>
            if name = @{const_name Comma_Phase_Rank_Mask_Continue} then
              SOME (IntInf.toInt (HOLogic.dest_number child |> #2))
            else error "Candidate fixture saw an unknown unary action"
        | (Const (name,_),[_,_]) =>
            if name = @{const_name Comma_Phase_Rank_Mask_Fork} then
              SOME ~1
            else error "Candidate fixture saw an unknown binary action"
        | _ => error "Candidate fixture action leaf is malformed")
      fun reference_rank phase root =
        let
          fun walk steps current clock =
            if current < 0 orelse current >= length phase_actions then NONE
            else (case reference_action clock (List.nth (phase_actions,current)) of
              NONE => NONE
            | SOME child =>
                if child = ~1 then SOME steps
                else if steps >= 26 then NONE
                else walk (steps+1) child ((clock+1) mod 924))
        in walk 0 root phase end
      fun compare_reference root phase =
        let
          val expected = reference_rank phase root
          val actual = SOME (numeral (selected_value phase_arena phase
            (List.nth (#ranks phase_candidate,root))))
        in if actual = expected then ()
          else error "Dyadic candidate rank disagrees with independent linear oracle" end
      val _ = List.app (fn root => List.app (compare_reference root) [0,1,2,3])
        [0,1,2]
      val _ = if #composition_levels phase_candidate=5 andalso
          #covered_span phase_candidate=32 andalso
          #serialization_node_visits phase_after =
            #serialization_node_visits phase_before andalso
          #proof_entries phase_after = #proof_entries phase_before andalso
          #scratch_entries phase_after = #scratch_entries phase_before then ()
        else error "Dyadic candidate altered its work envelope or published proof data"

      fun chain_actions arena height =
        let
          fun action index =
            if index < height then Data.leaf arena
                {key="height-fixture:continue:" ^ Int.toString index,
                 value=Const (@{const_name Comma_Phase_Rank_Mask_Continue},
                   @{typ nat} --> @{typ comma_phase_rank_mask_action}) $
                     HOLogic.mk_number @{typ nat} (index+1)}
            else Data.leaf arena
                {key="height-fixture:terminal:" ^ Int.toString index,
                 value= @{term "Comma_Phase_Rank_Mask_Fork 2 0"}}
        in map action (0 upto 45) end
      val height26_arena = Data.make_arena 8192
      val height26_candidate = Candidate.construct height26_arena
        (chain_actions height26_arena 26)
      val height26_rank = numeral (selected_value height26_arena 0
        (List.nth (#ranks height26_candidate,0)))
      val _ = if height26_rank=26 then ()
        else error "Candidate rejected or changed an admitted height-26 path"
      val height27_arena = Data.make_arena 8192
      val height27_before = Data.stats height27_arena
      val _ = rejects "a source path with height 27" (fn () =>
        Candidate.construct height27_arena (chain_actions height27_arena 27))
      val height27_after = Data.stats height27_arena
      val _ = if #scratch_entries height27_after = #scratch_entries height27_before
        then () else error "Height-27 refusal retained candidate scratch"
      val invalid_arena = Data.make_arena 8192
      val invalid = Data.leaf invalid_arena
        {key="invalid-fixture:root",value= @{term Comma_Phase_Rank_Mask_Invalid}}
      val invalid_terminal = Data.leaf invalid_arena
        {key="invalid-fixture:terminal",
         value= @{term "Comma_Phase_Rank_Mask_Fork 2 0"}}
      val invalid_actions = invalid :: replicate 45 invalid_terminal
      val invalid_before = Data.stats invalid_arena
      val _ = rejects "an invalid action root" (fn () =>
        Candidate.construct invalid_arena invalid_actions)
      val invalid_after = Data.stats invalid_arena
      val _ = if #scratch_entries invalid_after = #scratch_entries invalid_before
        then () else error "Invalid-root refusal retained candidate scratch"
      val continuation = Data.leaf arena
        {key="class-fixture:continue0",value = @{term "Comma_Phase_Rank_Mask_Continue 0"}}
      val _ = rejects "an unresolved temporal cycle" (fn () =>
        Candidate.construct arena (replicate 46 continuation))
      val _ = rejects "a missing root" (fn () =>
        Candidate.construct arena [terminal])
      val _ = rejects "missing source roots" (fn () =>
        Comma_Semantic_Phase_Action_Program_Compiler.make ctxt arena []
          {certify=fn _ => fn _ => error "Empty-root fixture reached state certification",
           begin_scope=fn _ => error "Empty-root fixture reached scope creation",
           end_scope=fn _ => error "Empty-root fixture reached scope closure",
           current_context=fn () => ctxt})
    in () end
end
