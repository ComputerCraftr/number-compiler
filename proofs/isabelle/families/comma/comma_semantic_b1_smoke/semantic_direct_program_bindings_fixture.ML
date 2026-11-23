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
  structure Rows = Comma_Direct_Entry_Row_Plan (
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
      val action_calls = Unsynchronized.ref 0
      val base = Runtime.computation
      val repeated_key = @{term "42::nat"}
      val counted: Compiler.computation =
        {class_program= #class_program base, source_program= #source_program base,
         program_admitted= #program_admitted base,
         supported_values=fn _ => [1,2], core_modulus= #core_modulus base,
         guard_table= #guard_table base,
         entry_action_key=fn _ => fn _ => fn _ => fn _ => repeated_key,
         entry_action=fn _ => fn _ => fn _ => fn _ =>
           (action_calls := !action_calls + 1;
            if !action_calls = 1 then action
            else error "Duplicate Entry proposal reconstructed its action"),
         operator_action= #operator_action base, exit_code= #exit_code base}
      val entry1 = @{term "Comma_Entry_Core_Program 1 0 0 Comma_Core_1"}
      val entry2 = @{term "Comma_Entry_Core_Program 1 1 1 Comma_Core_1"}
      val counted_owner = Entry.make ctxt counted
        [(entry1,expression),(entry2,expression)] (#body names) (#definition names)
      val _ = if !action_calls = 1 andalso
          #representative counted_owner 1 1 @{term Comma_Core_1} 2 aconv action andalso
          String.isSubstring "entry_row_proposal_requests=4" (#statistics counted_owner ()) andalso
          String.isSubstring "entry_row_action_calls=1" (#statistics counted_owner ())
        then () else error "Entry proposal did not reuse the first action for a repeated key"
      val core27 = #support entry_owner @{term Comma_Core_27} [1,10,19]
      val cores = [@{term Comma_Core_1}, @{term Comma_Core_3}, @{term Comma_Core_7},
        @{term Comma_Core_11}, @{term Comma_Core_13}, @{term Comma_Core_21},
        @{term Comma_Core_23}, @{term Comma_Core_27}, @{term Comma_Core_29}]
      val supports = map (fn core => #support entry_owner core
        (#supported_values Runtime.computation core)) cores
      val chart_core = @{term Comma_Core_23}
      val chart_values = #supported_values Runtime.computation chart_core
      val first_value = List.nth (chart_values,0)
      val second_value = List.nth (chart_values,1)
      fun chart_rep residue wanted =
        let
          val key = #entry_action_key Runtime.computation 1 residue chart_core wanted
          val proposed: Compiler.entry_representative =
            {sector=1,residue=residue,core=chart_core,wanted=wanted,
             action= #entry_action Runtime.computation 1 residue chart_core wanted}
        in (key,proposed) end
      val chart_pairs = maps (fn residue => map (chart_rep residue) chart_values) [0,10]
      val charts = Rows.make ctxt Runtime.computation chart_pairs
      val _ = #prewarm charts 1 0 chart_core
      val first_chart = #prepare charts 1 0 chart_core
      val second_chart = #prepare charts 1 10 chart_core
      val first_transport = #transport_prepared charts first_chart 1 0 chart_core first_value
      val second_transport = #transport_prepared charts second_chart 1 10 chart_core first_value
      val _ = if not (Thm.prop_of first_transport aconv Thm.prop_of second_transport) then ()
        else error "Entry chart merged distinct source offsets"
      val _ = (case Exn.capture
          (fn () => #transport_prepared charts first_chart 1 10 chart_core first_value) () of
          Exn.Exn _ => () | Exn.Res _ => error "Entry chart accepted a foreign source offset")
      val alternate = (case Inttab.lookup first_chart second_value of
          SOME theorem => theorem | NONE => error "Entry chart fixture lacks the second value")
      val swapped_chart = Inttab.update (first_value,alternate) first_chart
      val _ = (case Exn.capture
          (fn () => #transport_prepared charts swapped_chart 1 0 chart_core first_value) () of
          Exn.Exn _ => () | Exn.Res _ => error "Entry chart accepted reordered wanted values")
      val rejected = #entry_action_key Runtime.computation 1 0 chart_core first_value
      val original = #entry_action Runtime.computation 1 0 chart_core first_value
      val changed = if original aconv @{term Comma_Continuation_Invalid}
        then action else @{term Comma_Continuation_Invalid}
      val bad_rep: Compiler.entry_representative =
        {sector=1,residue=0,core=chart_core,wanted=first_value,action=changed}
      val bad_charts = Rows.make ctxt Runtime.computation [(rejected,bad_rep)]
      val _ = (case Exn.capture
          (fn () => #transport_prepared bad_charts first_chart 1 0 chart_core first_value) () of
          Exn.Exn _ => () | Exn.Res _ => error "Entry chart accepted a changed action")
      val chart_stats = #statistics charts ()
      val _ = if String.isSubstring "entry_lift_charts=1" chart_stats andalso
          String.isSubstring "entry_source_charts=2" chart_stats then ()
        else error ("Entry chart did not share its source-independent vector: " ^ chart_stats)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Direct checked Entry charts" [first_transport,second_transport]
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
