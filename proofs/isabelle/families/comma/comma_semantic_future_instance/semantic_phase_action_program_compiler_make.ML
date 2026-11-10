structure Comma_Semantic_Phase_Action_Program_Compiler =
struct
  open Comma_Semantic_Phase_Action_Program_Compiler
  fun make ctxt arena root_sources (certify_state: state_certifier): result =
    let
      val _ = if length root_sources = 46 then ()
        else error "Phase action compiler requires the 46 admitted root sources"
      val _ = if List.all root_is_canonical root_sources then ()
        else error "Phase action root is outside the canonical decade-source domain"
      val _ = if length (distinct (op aconv) root_sources) = 46 then ()
        else error "Phase action compiler received duplicate root sources"
      val compiler_checker =
        Comma_Semantic_Weighted_CRT_Data_Transport.make_scoped_checker ctxt
          "comma_source_action_program_compiler"
      val ctxt = Comma_Semantic_Weighted_CRT_Data_Transport.install_scoped_checker
        ctxt compiler_checker
      val local_evaluator = make_local_action_evaluator ctxt
    in Data.with_reservation arena (fn lifetime => let
      val root_cache = Unsynchronized.ref
        (Key_Table.empty: program_root Key_Table.table)
      val active_roots = Unsynchronized.ref
        (Key_Table.empty: unit Key_Table.table)
      val source_cache = Unsynchronized.ref
        (Termtab.empty: source_program Termtab.table)
      val entry_port_cache = Unsynchronized.ref
        (Entry_Port_Table.empty: fixed_entry_port Entry_Port_Table.table)
      val terminal_cache = Unsynchronized.ref
        (Termtab.empty: terminal_reduction Termtab.table)
      val cofactor_nodes = Unsynchronized.ref 0
      val cofactor_leaves = Unsynchronized.ref 0
      val state_evaluations = Unsynchronized.ref 0
      val memo_hits = Unsynchronized.ref 0
      val quotient_slot_merges = Unsynchronized.ref 0
      val period_evaluations = Unsynchronized.ref 0
      val period_cache_hits = Unsynchronized.ref 0
      val port_evaluations = Unsynchronized.ref 0
      val port_cache_hits = Unsynchronized.ref 0
      val terminal_evaluations = Unsynchronized.ref 0
      val terminal_cache_hits = Unsynchronized.ref 0
      val action_totals = {hits=Unsynchronized.ref 0,misses=Unsynchronized.ref 0}
      val operator_equations = Unsynchronized.ref ([]: thm list)
      val stages = Comma_Semantic_Weighted_CRT_Data_Transport.make_profile
        "source_action" ["local_action","terminal","goto","branch"]
      fun checkpoint () =
        if not (Comma_Proof_Profile.enabled ()) then ()
        else let val data = Data.stats arena
          val _ = Comma_Semantic_Weighted_CRT_Data_Transport.report_counts
            "source-action checkpoint"
            [("sources",Termtab.size (!source_cache)),
             ("completed_programs",Key_Table.size (!root_cache)),
             ("active_programs",Key_Table.size (!active_roots)),
             ("transient_states",!state_evaluations),
             ("nodes",#nodes data),("proof_entries",#proof_entries data),
             ("payload_aliases",#payload_aliases data),
             ("scratch_entries",#scratch_entries data),
             ("peak_entries",#peak_entries data)]
          in Comma_Proof_Profile.report
            (Comma_Semantic_Weighted_CRT_Data_Transport.profile_stats stages) end

      fun reserve_metadata () = Data.reserve_external arena lifetime

      fun entry_port_rules f d =
        (case Entry_Port_Table.lookup (!entry_port_cache) (f,d) of
          SOME fixed => (port_cache_hits := !port_cache_hits + 1; #rules fixed)
        | NONE =>
            let
              val _ = List.app (fn _ => reserve_metadata ()) (0 upto 5)
              val fixed = fixed_entry_port ctxt local_evaluator f d
              val _ = port_evaluations := !port_evaluations + 1
              val _ = entry_port_cache := Entry_Port_Table.update
                ((f,d),fixed) (!entry_port_cache)
            in #rules fixed end)

      fun scoped_operator_for program =
        (case key_of_program program of
          Entry_Core (f,d,_,_) => operator_for_program_with_rules ctxt program
            (entry_port_rules f d)
        | _ => NONE)

      val _ = List.app (fn axis =>
        let
          val radix = Data.axis_radix axis
          val radix_expression = @{term comma_crt_axis_radix} $ nat axis
          val {term=radix_term,...} = checked_rewrite ctxt
            "Closed Isabelle CRT radix" @{thms comma_crt_axis_radix_def}
            radix_expression
          val expected_radix = dest_nat "Isabelle CRT radix" radix_term
          val _ = if radix = expected_radix then ()
            else error "Shared CRT axis radix disagrees with Isabelle"
          val expression = @{term comma_crt_axis_weight} $ nat axis
          val {term=weight_term,...} = checked_rewrite ctxt
            "Closed Isabelle CRT weight" @{thms comma_crt_axis_weight_def}
            expression
          val expected_weight = dest_nat "CRT axis weight" weight_term
          val _ = if Data.axis_weight axis = expected_weight then ()
            else error "Shared CRT axis weight disagrees with Isabelle"
        in () end) (0 upto 3)

      fun source_program_for source =
        let
          val _ = if source_delta source = 0 then ()
            else error "Uncertified nonzero occurrence shift reached the action compiler"
        in
          (case Termtab.lookup (!source_cache) source of
            SOME checked => checked
          | NONE =>
              let
                val checked = program_of_source ctxt source
                val _ = reserve_metadata ()
                val _ = source_cache := Termtab.update
                  (source,checked) (!source_cache)
              in checked end)
        end

      fun program_period_for reservation periods operators key program =
        (case Key_Table.lookup (!periods) key of
          SOME checked =>
            (period_cache_hits := !period_cache_hits + 1;
             if key_of_program program = key then ()
             else error "Cached operator belongs to another semantic program";
             checked)
        | NONE =>
            let
              val base = period_of_key ctxt key
              val _ = if key_of_program program = key then ()
                else error "Operator specialization key disagrees with its program"
              val operator_equation = scoped_operator_for program
              val checked: program_period =
                {key=key, period = #period base, equation = #equation base,
                 operator_equation=operator_equation}
              val _ = Data.reserve_external arena reservation
              val _ = Option.app (fn theorem =>
                (Data.reserve_external arena lifetime;
                 operators := theorem :: !operators)) operator_equation
              val _ = period_evaluations := !period_evaluations + 1
              val _ = periods := Key_Table.update (key,checked) (!periods)
            in checked end)

      fun new_program_frame reservation: program_frame =
        let
          val periods = Unsynchronized.ref
            (Key_Table.empty: program_period Key_Table.table)
          val action_cache = make_local_action_cache ctxt local_evaluator arena
            reservation (fn f => fn d => entry_port_rules f d)
            action_totals
        in {reservation=reservation,action_cache=action_cache,
          periods=periods}: program_frame end

      fun terminal_for action =
        (case Termtab.lookup (!terminal_cache) action of
          SOME checked =>
            (terminal_cache_hits := !terminal_cache_hits + 1;
             checked)
        | NONE =>
            let
              val checked = result_of_terminal ctxt local_evaluator action
              val _ = reserve_metadata ()
              val _ = terminal_evaluations := !terminal_evaluations + 1
              val _ = terminal_cache := Termtab.update
                (action,checked) (!terminal_cache)
            in checked end)

      fun ensure_inactive period axis =
        if Data.axis_weight axis mod period <> 0 then
          error "Attempted to omit a CRT axis that is active for this core"
        else if 924 mod period <> 0 then
          error "Inactive CRT axis period does not divide 924"
        else ()

      fun env_assigned env axis =
        (case env_slot env axis of NONE => false | SOME _ => true)

      fun active_axes period (env: clock_env) =
        let
          val axes = 0 upto 3
          val _ = List.app (fn axis =>
            if env_assigned env axis then ()
            else if Data.axis_weight axis mod period = 0
            then ensure_inactive period axis else ()) axes
        in List.filter (fn axis => not (env_assigned env axis) andalso
          Data.axis_weight axis mod period <> 0) axes end

      fun root_state (root: program_root): certified_state =
        {key= #key root,environment=empty_env,source= #source root,
         program= #program root,source_binding= #source_binding root,
         period= #period root,period_equation= #period_equation root,
         diagram= #diagram root,exactness= #exactness root}

      fun compile_source source =
        let
          val binding = source_program_for source
          val program = #program binding
          val key = key_of_program program
        in
          (case Key_Table.lookup (!root_cache) key of
            SOME root =>
              (ignore (Data.identity arena (#diagram root));
               memo_hits := !memo_hits + 1;
               root_state root)
          | NONE =>
              if Key_Table.defined (!active_roots) key then
                error "Source action program contains a recursive Goto cycle"
              else
                let
                  val _ = active_roots := Key_Table.update (key,()) (!active_roots)
                  val outcome = Exn.capture (fn () => Data.with_reservation arena
                    (fn reservation =>
                      let
                        val scope = #begin_scope certify_state reservation
                        val compilation = Exn.capture (fn () =>
                          let
                            val frame = new_program_frame reservation
                            val memo = Unsynchronized.ref
                              (Compiler_Table.empty:
                                certified_state Compiler_Table.table)
                            val active = Unsynchronized.ref
                              (Compiler_Table.empty: unit Compiler_Table.table)
                          in compile_program frame memo active empty_env key program source end) ()
                        val _ = #end_scope certify_state scope
                      in Exn.release compilation end)) ()
                  val _ = active_roots := Key_Table.delete key (!active_roots)
                  val state = Exn.release outcome
                  val root: program_root =
                    {key= #key state,source= #source state,program= #program state,
                     source_binding= #source_binding state,period= #period state,
                     period_equation= #period_equation state,diagram= #diagram state,
                     exactness= #exactness state}
                  val _ = reserve_metadata ()
                  val _ = root_cache := Key_Table.update (key,root) (!root_cache)
                in state end)
        end

      and compile_program frame memo active env key program source =
        let
          val {reservation,periods,action_cache} = frame
          val {period,equation=period_equation,operator_equation,...} =
            program_period_for reservation periods operator_equations key program
          val canonical_env = canonical_environment period env
          val cache_key = (key,canonical_env)
        in
        (case Compiler_Table.lookup (!memo) cache_key of
          SOME compiled =>
            (ignore (Data.identity arena (#diagram compiled));
             memo_hits := !memo_hits + 1;
             compiled)
        | NONE =>
            if Compiler_Table.defined (!active) cache_key then
              error "Source action program contains a recursive Goto cycle"
            else
              let
                val _ = active := Compiler_Table.update (cache_key,()) (!active)
                val _ = if key_of_program program = key then ()
                  else error "Compiler program key changed during admission"
                val axes = active_axes period canonical_env
                val compiled_result = Exn.capture (fn () =>
                  let
                    val _ = cofactor_nodes := !cofactor_nodes + 1
                    val phase = phase_of_env canonical_env
                    val (candidate_diagram,node,child_states,terminal_record,
                      goto_child_binding) =
                      (case axes of
                        axis :: _ =>
                          let
                            val child_keys = child_key_row period key canonical_env axis
                            val distinct_child_keys = distinct (op =)
                              (map #2 child_keys)
                            val _ = quotient_slot_merges :=
                              !quotient_slot_merges + length child_keys -
                                length distinct_child_keys
                            val children = map (fn (_,child_key as
                                (child_program,child_env)) =>
                              compile_program frame memo active child_env
                                child_program program source) child_keys
                            val child_diagrams = map #diagram children
                            val _ = if List.all (fn child => Data.offset child=0)
                                child_diagrams then ()
                              else error "Source action branch child has a nonzero root offset"
                            val branch = Data.normalized_branch arena axis child_diagrams
                          in (branch,Branch_Node {axis=axis,children=child_keys},
                            children,NONE,NONE) end
                      | [] =>
                          let
                            val _ = cofactor_leaves := !cofactor_leaves + 1
                            val {action,equation=action_equation} =
                              Comma_Semantic_Weighted_CRT_Data_Transport.with_profile
                                stages "local_action" (fn () =>
                                  action_at_source_checked_using ctxt (#reduce action_cache)
                                    (source_program_for source) phase operator_equation)
                          in
                            (case goto_parts action of
                              SOME (child,shift) =>
                                let
                                  val _ = if shift = 0 then ()
                                    else error "Goto requires an uncertified phase transform"
                                  val _ = if source_delta child = 0 then ()
                                    else error "Goto child is not in the canonical source frame"
                                  val child_binding = source_program_for child
                                  val child_program = #program child_binding
                                  val child_key = global_child_key child_program
                                  val child_state = compile_source child
                                  val _ = if #1 child_key = #key child_state andalso
                                      #2 child_key = empty_env then ()
                                    else error "Goto did not compile its own semantic root"
                                in (#diagram child_state,Goto_Node {phase=phase,
                                  action=action,action_equation=action_equation,
                                  child=child_key},[child_state],NONE,
                                  SOME child_binding) end
                            | NONE =>
                                let
                                  val reduction = terminal_for action
                                  val diagram = Data.leaf arena
                                    (leaf_payload (#result reduction))
                                in (diagram,Terminal_Node {phase=phase,
                                  action=action,action_equation=action_equation},[],
                                  SOME reduction,NONE) end)
                          end)
                    val diagram = candidate_diagram
                    val _ = Data.check_diagram arena diagram
                    val compiled: program_action =
                      {key=key,environment=canonical_env,source=source,program=program,
                       period=period,period_equation=period_equation,node=node,
                       diagram=diagram}
                    val source_binding = source_program_for source
                    val context: action_context =
                      {action=compiled,source_binding=source_binding,
                       terminal_reduction=terminal_record,
                       goto_child_binding=goto_child_binding}
                    val stage = (case node of Terminal_Node _ => "terminal"
                      | Goto_Node _ => "goto" | Branch_Node _ => "branch")
                    val theorem =
                      Comma_Semantic_Weighted_CRT_Data_Transport.with_profile
                        stages stage (fn () => #certify certify_state context child_states)
                    val receiving_ctxt = #current_context certify_state ()
                    val _ = #set_context compiler_checker receiving_ctxt
                    val exactness =
                      Comma_Semantic_Weighted_CRT_Data_Transport.checked_closed
                        receiving_ctxt "Universal source-program state exactness"
                        (Thm.prop_of theorem) theorem
                    val state: certified_state =
                      {key=key,environment=canonical_env,source=source,program=program,
                       source_binding=source_binding,period=period,
                       period_equation=period_equation,diagram=diagram,
                       exactness=exactness}
                    val _ = Data.reserve_external arena reservation
                    val _ = memo := Compiler_Table.update (cache_key,state) (!memo)
                    val _ = state_evaluations := !state_evaluations + 1
                    val _ = if !state_evaluations mod 128=0 then checkpoint () else ()
                  in state end) ()
                val _ = active := Compiler_Table.delete cache_key (!active)
              in Exn.release compiled_result end)
        end

      val root_states = Comma_Semantic_Weighted_CRT_Data_Transport.capture_with_failure_counts
        "source-action-compiler failure" (fn () =>
          let val data = Data.stats arena
              val hits = !(#hits action_totals)
              val misses = !(#misses action_totals)
              val roots = Key_Table.dest (!root_cache)
          in [("sources",length (Termtab.dest (!source_cache))), ("periods",!period_evaluations),
            ("terminals",length (Termtab.dest (!terminal_cache))),
            ("actions",!state_evaluations), ("program_keys",length roots),
            ("active",Key_Table.size (!active_roots)),
            ("ports",!port_evaluations),
            ("action_hits",hits), ("action_misses",misses),
            ("nodes",#nodes data), ("proofs",#proof_entries data),
            ("scratch",#scratch_entries data), ("peak",#peak_entries data)] end)
        (fn () => map compile_source root_sources)
      val _ = checkpoint ()
      val roots = map #diagram root_states
      val root_programs = map #key root_states
      val program_roots = map #2 (Key_Table.dest (!root_cache))
      val _ = List.app (Data.check_diagram arena) roots
      val retained_metadata =
        length (Termtab.dest (!source_cache)) +
        length program_roots
      (* Retain source bindings and the one certified root per semantic key. *)
      val _ = Data.retain_external arena lifetime retained_metadata
      val action_conversion_hits = !(#hits action_totals)
      val action_conversion_misses = !(#misses action_totals)
      val source_program_records = map #2 (Termtab.dest (!source_cache))
      val terminal_records = map #2 (Termtab.dest (!terminal_cache))
      val returned_theorems =
        maps (fn ({equation,operator_binding,...}: source_program) =>
          [equation,operator_binding]) source_program_records @
        !operator_equations @
        maps (fn (record: program_root) =>
          [#period_equation record,#exactness record]) program_roots @
        maps (fn ({terminal_equation,rank_equation,...}: terminal_reduction) =>
          [terminal_equation,rank_equation]) terminal_records
      val _ = #audit compiler_checker
        "Source action compiler exported theorem bundle" returned_theorems
      val compiler_proof_stats = #stats compiler_checker ()
      val _ = if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
        ("source-action-compiler proof-audit emissions=" ^
          Int.toString (#emissions compiler_proof_stats) ^
          " proof_nodes=" ^ Int.toString (#proof_nodes compiler_proof_stats) ^
          " native_calls=" ^ Int.toString (#native_calls compiler_proof_stats) ^
          " native_milliseconds=" ^
            Int.toString (#native_milliseconds compiler_proof_stats) ^
          " final_bundle=" ^ Int.toString (length returned_theorems)) else ()
      val _ = if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
        ("local-action-cache hits=" ^ Int.toString action_conversion_hits ^
          " misses=" ^ Int.toString action_conversion_misses) else ()
      val _ = if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
        ("fixed-entry-port evaluations=" ^ Int.toString (!port_evaluations) ^ " cache_hits=" ^
          Int.toString (!port_cache_hits)) else ()
      val _ = if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
        ("source-action quotient_slot_merges=" ^
          Int.toString (!quotient_slot_merges)) else ()
      val _ = if Comma_Proof_Profile.enabled () then Comma_Proof_Profile.report
        ("source-action root_only certified_roots=" ^
          Int.toString (length program_roots) ^ " transient_states=" ^
          Int.toString (!state_evaluations)) else ()
      val stats = Data.stats arena
    in
      {roots=roots,root_sources=root_sources,
       source_programs=source_program_records,
       root_programs=root_programs,
       program_roots=program_roots,
       programs=length program_roots,
       cofactor_nodes= !cofactor_nodes,
       cofactor_leaves= !cofactor_leaves,memo_hits= !memo_hits,
       period_evaluations= !period_evaluations,
       period_cache_hits= !period_cache_hits,
       terminal_evaluations= !terminal_evaluations,
       terminal_cache_hits= !terminal_cache_hits,
       action_conversion_hits=action_conversion_hits,
       action_conversion_misses=action_conversion_misses,
       quotient_slot_merges= !quotient_slot_merges,
       data_nodes= #nodes stats}: result
    end)
    end
end
