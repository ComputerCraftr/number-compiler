(* The issuer must authenticate a demanded terminal relation and reuse it;
   replacing its proposed expression with an unrelated action is rejected. *)
structure Comma_Direct_Program_Bindings_Fixture =
struct
  structure Arithmetic = Comma_Direct_Entry_Arithmetic
  structure Compiler = Comma_Frontier24_Parametric_Compiler
  structure Runtime = Comma_Frontier24_Parametric_Runtime
  structure Issuer = Comma_Direct_Program_Bindings (
    val fixed_entry_port_conversion_plan = Arithmetic.fixed_entry_port_conversion_plan
    val core_parameter_conversion_plan = Arithmetic.core_parameter_conversion_plan)
  structure Entry = Comma_Direct_Entry_Bindings (
    val fixed_entry_port_conversion_plan = Arithmetic.fixed_entry_port_conversion_plan
    val core_parameter_conversion_plan = Arithmetic.core_parameter_conversion_plan)
  fun run lthy =
    let
      val names = Comma_Direct_Expression_Names.make "direct_binding_fixture" lthy
      val action = @{term "Comma_Continuation_Fork 2 0"}
      val expression = #intern names @{term "Comma_Direct_Fork 2 0"}
      val invalid = #intern names @{term Comma_Direct_Invalid}
      val exit_action = @{term "Comma_Continuation_Exit (Comma_Entry 1 0 18) 1"}
      val exit_expression = #intern names @{term "Comma_Direct_Continue 19 1"}
      val rejected_exit = @{term "Comma_Continuation_Exit (Comma_Entry 2 0 18) 1"}
      val wrong_exit_expression = #intern names @{term "Comma_Direct_Continue 18 1"}
      fun terminal_shape action = (case Compiler.parse_action action of
          Compiler.Fork (digit,delta) => SOME (list_comb
            (@{term "Comma_Direct_Fork"},[HOLogic.mk_number @{typ nat} digit,
              HOLogic.mk_number @{typ nat} delta]))
        | Compiler.Landmine delta => SOME (@{term "Comma_Direct_Landmine"} $
            HOLogic.mk_number @{typ nat} delta)
        | _ => NONE)
      fun near sector = @{term "Comma_Near_Boundary_Program"} $
        HOLogic.mk_number @{typ nat} sector
      fun candidate sector =
        let val program = near sector
            val near_action = #operator_action Runtime.computation program
        in Option.map (fn shape => (program,near_action,shape)) (terminal_shape near_action) end
      fun residual_candidate (sector,residual) =
        let
          val h = (if sector < 9 then 2 else 1) + residual
          val digit = (10 - h mod 10) mod 10
          val program = @{term "Comma_Near_Residual_Program"} $
            HOLogic.mk_number @{typ nat} sector $ HOLogic.mk_number @{typ nat} digit $
            HOLogic.mk_number @{typ nat} residual
        in if not (#program_admitted Runtime.computation program) then NONE else
          let val action = #operator_action Runtime.computation program
          in Option.map (fn shape => (program,action,shape)) (terminal_shape action) end
        end
      val (near_program,near_action,near_shape) =
        (case get_first candidate (1 upto 8) of SOME result => result
        | NONE => (case get_first residual_candidate
            (maps (fn sector => map (fn residual => (sector,residual)) (0 upto 60)) (1 upto 9)) of
              SOME result => result | NONE => error "No bounded admitted Near terminal for direct issuer fixture"))
      val near_expression = #intern names near_shape
      val lthy' = #finish names ()
      val ctxt = Local_Theory.target_of lthy'
      val issuer = Issuer.make ctxt Runtime.computation [] [(action,expression)]
        (#body names) (#definition names)
      val first = #source_relation issuer action
      val warm = #source_relation issuer action
      val _ = if Thm.prop_of first aconv Thm.prop_of warm andalso
          String.isSubstring "direct_action_binding_proofs=1" (#statistics issuer ()) andalso
          String.isSubstring "direct_action_binding_hits=1" (#statistics issuer ()) then ()
        else error "Direct issuer did not reuse its checked terminal binding"
      val bad = Issuer.make ctxt Runtime.computation []
        [(action,invalid)] (#body names) (#definition names)
      val _ = (case Exn.capture (#source_relation bad) action of
          Exn.Exn _ => () | Exn.Res _ => error "Direct issuer accepted a changed terminal")
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Direct relation issuer terminal reuse" [first,warm]
      val exit_issuer = Issuer.make ctxt Runtime.computation []
        [(exit_action,exit_expression),(rejected_exit,invalid)]
        (#body names) (#definition names)
      val exit_fact = #source_relation exit_issuer exit_action
      val rejected_fact = #source_relation exit_issuer rejected_exit
      val wrong_exit = Issuer.make ctxt Runtime.computation []
        [(exit_action,invalid)] (#body names) (#definition names)
      val _ = (case Exn.capture (#source_relation wrong_exit) exit_action of
          Exn.Exn _ => () | Exn.Res _ => error "Direct issuer accepted incorrect Exit normalization")
      val wrong_exit_class = Issuer.make ctxt Runtime.computation []
        [(exit_action,wrong_exit_expression)] (#body names) (#definition names)
      val _ = (case Exn.capture (#source_relation wrong_exit_class) exit_action of
          Exn.Exn _ => () | Exn.Res _ => error "Direct issuer accepted incorrect Continue class")
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Direct admitted and rejected Exit binding" [exit_fact,rejected_fact]
      val entry_owner = Entry.make ctxt Runtime.computation [] (#body names) (#definition names)
      val core27 = #support entry_owner @{term Comma_Core_27} [1,10,19]
      val cores = [@{term Comma_Core_1}, @{term Comma_Core_3}, @{term Comma_Core_7},
        @{term Comma_Core_11}, @{term Comma_Core_13}, @{term Comma_Core_21},
        @{term Comma_Core_23}, @{term Comma_Core_27}, @{term Comma_Core_29}]
      val supports = map (fn core => #support entry_owner core
        (#supported_values Runtime.computation core)) cores
      val _ = (case Exn.capture (fn () => #support entry_owner @{term Comma_Core_27} [1,10,18]) () of
          Exn.Exn _ => () | Exn.Res _ => error "Direct support accepted changed Core27 row")
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Direct checked core supports" (core27 :: supports)
      val near_issuer = Issuer.make ctxt Runtime.computation
        [(near_program,near_expression)] [(near_action,near_expression)]
        (#body names) (#definition names)
      val near_fact = #program_action near_issuer near_program
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Direct admitted Near program action" [near_fact]
    in lthy' end
end
