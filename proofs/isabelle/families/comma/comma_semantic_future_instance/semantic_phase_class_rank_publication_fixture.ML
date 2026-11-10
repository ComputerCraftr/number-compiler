(* Exercise the transaction boundary with real Local_Theory.define nodes. *)
structure Comma_Semantic_Phase_Class_Rank_Publication_Fixture =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Candidate = Comma_Semantic_Phase_Class_Rank_Candidate
  structure Compiler = Comma_Semantic_Phase_Action_Program_Compiler
  structure State_Certificate = Comma_Semantic_Phase_Action_State_Certificate
  structure Source_Certificate = Comma_Semantic_Phase_Action_Program_Certificate
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport

  fun nat n = HOLogic.mk_number @{typ nat} n

  fun get_some label value =
    (case value of
      SOME result => result
    | NONE => error (label ^ " was not captured by the publication fixture"))

  fun rejects label operation =
    (case Exn.capture operation () of
      Exn.Exn (ERROR _) => ()
    | Exn.Exn failure => Exn.reraise failure
    | Exn.Res _ => error ("Publication fixture accepted stale " ^ label))

  fun closed_definition theorem =
    Thm.nprems_of theorem=0 andalso null (Thm.hyps_of theorem) andalso
    null (Thm.tpairs_of theorem) andalso
    null (Term.add_frees (Thm.prop_of theorem) []) andalso
    null (Thm_Deps.all_oracles [theorem])

  fun has_weighted_zero_output theorem =
    let
      val proposition = Thm.prop_of theorem
      fun is_apply term = (case term of
          Const (name,_) => name = @{const_name comma_weighted_crt_apply}
        | _ => false)
      fun zero_nat term =
        fastype_of term = @{typ nat} andalso
          (case HOLogic.dest_number term of
            (typ,value) => typ = @{typ nat} andalso value = 0)
        handle TERM _ => false
      fun is_zero_result term =
        (case Term.strip_comb term of
          (Const (some_name,_),[pair]) =>
            if some_name <> @{const_name Some} then false
            else (case Term.strip_comb pair of
              (Const (pair_name,_),[_,weight]) =>
                pair_name = @{const_name Pair} andalso zero_nat weight
            | _ => false)
        | _ => false)
      val has_apply = Term.exists_subterm is_apply proposition
      val has_zero_result = Term.exists_subterm is_zero_result proposition
    in has_apply andalso has_zero_result end

  fun rejects_bad_branch_environment ctxt lthy =
    let
      val source = @{term "Comma_Entry 1 0 0"}
      val source_binding = Compiler.program_of_source ctxt source
      val key = Compiler.key_of_program (#program source_binding)
      val {period, equation=period_equation,...} =
        Compiler.period_of_key ctxt key
      val arena = Data.make_arena 64
      val actionT = @{typ comma_phase_rank_mask_action}
      val fork = Const (@{const_name Comma_Phase_Rank_Mask_Fork},
        @{typ nat} --> @{typ nat} --> actionT)
      fun action_leaf slot = Data.leaf arena
        {key="rank-publication-bad-slot:" ^ Int.toString slot,
         value=fork $ nat slot $ nat 0}
      val diagrams = map action_leaf (0 upto 3)
      val diagram = Data.raw_branch arena 0 (map (fn child => (0,child)) diagrams)
      val child_rows = Compiler.child_key_row period key Compiler.empty_env 0
      val action: Compiler.program_action =
        {key=key,environment=Compiler.empty_env,source=source,
         program= #program source_binding,period=period,
         period_equation=period_equation,
         node=Compiler.Branch_Node {axis=0,children=child_rows},diagram=diagram}
      val context: Compiler.action_context =
        {action=action,source_binding=source_binding,terminal_reduction=NONE,
         goto_child_binding=NONE}
      val irrelevant_exactness = @{thm TrueI}
      val children = map_index (fn (slot,child_diagram) =>
        let
          val environment =
            if slot=1 then Compiler.empty_env
            else Compiler.env_update period Compiler.empty_env 0 slot
        in
          {key=key,environment=environment,source=source,
           program= #program source_binding,source_binding=source_binding,
           period=period,period_equation=period_equation,
           diagram=child_diagram,exactness=irrelevant_exactness}:
            Compiler.certified_state
        end) diagrams
      val failure = Exn.capture (fn () =>
        Candidate.with_shallow_transaction arena lthy (fn transaction =>
          let
            val publisher = Candidate.make_shallow_publisher transaction
              actionT "comma_rank_bad_branch_environment_fixture"
            val certifier = State_Certificate.make_state_certifier
              ctxt arena transaction publisher
          in #certify certifier context children end)) ()
      val _ = (case failure of
          Exn.Exn (ERROR message) =>
            if message="Branch slot child does not match its checked quotient key" then ()
            else error ("Wrong branch-environment rejection: " ^ message)
        | Exn.Exn failure => Exn.reraise failure
        | Exn.Res _ => error "State certificate accepted a child with the wrong raw-slot environment")
      val stats = Data.stats arena
      val _ = if #proof_entries stats=0 andalso #scratch_entries stats=0 then ()
        else error "Rejected branch environment retained publisher entries"
      val nonzero_diagram = Data.raw_branch arena 0
        (map_index (fn (slot,child) => (if slot=0 then 1 else 0,child)) diagrams)
      val nonzero_action: Compiler.program_action =
        {key=key,environment=Compiler.empty_env,source=source,
         program= #program source_binding,period=period,
         period_equation=period_equation,
         node=Compiler.Branch_Node {axis=0,children=child_rows},
         diagram=nonzero_diagram}
      val nonzero_context: Compiler.action_context =
        {action=nonzero_action,source_binding=source_binding,
         terminal_reduction=NONE,goto_child_binding=NONE}
      val nonzero_failure = Exn.capture (fn () =>
        Candidate.with_shallow_transaction arena lthy (fn transaction =>
          let
            val publisher = Candidate.make_shallow_publisher transaction
              actionT "comma_rank_nonzero_apply_fixture"
            val certifier = State_Certificate.make_state_certifier
              ctxt arena transaction publisher
          in #certify certifier nonzero_context children end)) ()
      val _ = (case nonzero_failure of
          Exn.Exn (ERROR message) =>
            if message="Shallow rank/action branch retains physical weights" then ()
            else error ("Wrong nonzero-weight rejection: " ^ message)
        | Exn.Exn failure => Exn.reraise failure
        | Exn.Res _ => error "State certificate accepted a nonzero weighted branch")
      val nonzero_stats = Data.stats arena
      val _ = if #proof_entries nonzero_stats=0 andalso
          #scratch_entries nonzero_stats=0 then ()
        else error "Rejected nonzero weighted branch retained publisher entries"
    in () end

  fun certifies_entry9_branch_and_near8_goto ctxt initial_lthy =
    let
      val source = @{term "Comma_Entry 9 0 56"}
      val source_binding = Compiler.program_of_source ctxt source
      val program = #program source_binding
      val key = Compiler.key_of_program program
      val {period, equation=period_equation,...} =
        Compiler.period_of_key ctxt key
      val _ = if period=3 then ()
        else error "Entry-9 callback fixture lost its admitted period-3 program"
      val evaluator = Compiler.make_local_action_evaluator ctxt
      val (sector,digit) = (case key of
          Compiler.Entry_Core (sector,digit,_,_) => (sector,digit)
        | _ => error "Entry-9 callback fixture did not normalize to an Entry core")
      val fixed_port = Compiler.fixed_entry_port ctxt evaluator sector digit
      val operator_equation = Compiler.operator_for_program_with_rules ctxt
        program (#rules fixed_port)
      val arena = Data.make_arena 256
      val action_totals: Compiler.local_action_cache_totals =
        {hits=Unsynchronized.ref 0,misses=Unsynchronized.ref 0}
      val terminal_rows = Data.with_reservation arena (fn reservation =>
        let
          val cache = Compiler.make_local_action_cache ctxt evaluator arena
            reservation (fn _ => fn _ => #rules fixed_port) action_totals
          fun terminal_row slot =
            let
              val environment = Compiler.env_update period Compiler.empty_env 1 slot
              val phase = Compiler.phase_of_env environment
              val {action, equation=action_equation} =
                Compiler.action_at_source_checked_using ctxt (#reduce cache)
                  source_binding phase operator_equation
              val _ = (case Compiler.goto_parts action of
                  NONE => ()
                | SOME _ => error "Entry-9 callback fixture unexpectedly selected a Goto")
              val reduction = Compiler.result_of_terminal ctxt evaluator action
              val diagram = Data.leaf arena
                (Compiler.leaf_payload (#result reduction))
            in
              {slot=slot,environment=environment,phase=phase,action=action,
               action_equation=action_equation,reduction=reduction,diagram=diagram}
            end
        in map terminal_row (0 upto 2) end)
      val goto_source = @{term "Comma_Near 8 0 23"}
      val bundle_row = hd terminal_rows
      val bundle_phase = #phase bundle_row
      val bundle_action = #action bundle_row
      val bundle_action_equation = #action_equation bundle_row
      val bundle_diagram = #diagram bundle_row
      val bundle_program_action: Compiler.program_action =
        {key=key,environment= #environment bundle_row,source=source,program=program,
         period=period,period_equation=period_equation,
         node=Compiler.Terminal_Node {phase=bundle_phase,action=bundle_action,
           action_equation=bundle_action_equation},diagram=bundle_diagram}
      val bundle_checker = Transport.make_scoped_checker ctxt
        "comma_source_proof_bundle_fixture"
      val source_bundle = Source_Certificate.make_source_proof_bundle
        (#check bundle_checker) ctxt source_binding bundle_program_action
      val changed_source_bundle: Source_Certificate.source_proof_bundle =
        {source=goto_source,program= #program source_bundle,
         key= #key source_bundle,period= #period source_bundle,
         source_equation= #source_equation source_bundle,
         operator_binding= #operator_binding source_bundle,
         guards= #guards source_bundle,
         period_equation= #period_equation source_bundle}
      val _ = rejects "a source proof bundle with a changed source" (fn () =>
        Source_Certificate.validate_source_proof_bundle
          (#check bundle_checker) source_binding bundle_program_action
          changed_source_bundle)
      val goto_source_binding = Compiler.program_of_source ctxt goto_source
      val goto_program = #program goto_source_binding
      val goto_key = Compiler.key_of_program goto_program
      val {period=goto_period,equation=goto_period_equation,...} =
        Compiler.period_of_key ctxt goto_key
      val _ = if goto_period=1 then ()
        else error "Near-8 Goto fixture lost its period-one source program"
      val goto_action_totals: Compiler.local_action_cache_totals =
        {hits=Unsynchronized.ref 0,misses=Unsynchronized.ref 0}
      val {action=goto_action, equation=goto_action_equation} =
        Data.with_reservation arena (fn reservation =>
          let
            val cache = Compiler.make_local_action_cache ctxt evaluator arena
              reservation (fn _ => fn _ => []) goto_action_totals
          in Compiler.action_at_source_checked_using ctxt (#reduce cache)
            goto_source_binding 0 NONE end)
      val goto_child_source = (case Compiler.goto_parts goto_action of
          SOME (child,0) => child
        | _ => error "Near-8 callback fixture did not select a zero-shift Goto")
      val _ = if goto_child_source aconv source then ()
        else error "Near-8 callback fixture changed its checked Entry-9 child source"
      val goto_child_binding = source_binding
      val goto_child_key = Compiler.global_child_key (#program goto_child_binding)
      val child_rows = Compiler.child_key_row period key Compiler.empty_env 1
      val (_,final_lthy) = Candidate.with_shallow_transaction arena initial_lthy
        (fn transaction =>
          let
            val publisher = Candidate.make_shallow_publisher transaction
              @{typ comma_phase_rank_mask_action}
              "comma_rank_entry9_callback_fixture"
            val certifier = State_Certificate.make_state_certifier
              ctxt arena transaction publisher
            val stale_row = hd terminal_rows
            val stale_action: Compiler.program_action =
              {key=key,environment= #environment stale_row,source=source,
               program=program,period=period,period_equation=period_equation,
               node=Compiler.Terminal_Node {phase= #phase stale_row,
                 action= #action stale_row,
                 action_equation= #action_equation stale_row},
               diagram= #diagram stale_row}
            val stale_context: Compiler.action_context =
              {action=stale_action,source_binding=source_binding,
               terminal_reduction=SOME (#reduction stale_row),
               goto_child_binding=NONE}
            val stale_stats_before = Data.stats arena
            val stale_nodes_before = Candidate.shallow_publisher_node_count publisher
            val stale_scope = Data.with_reservation arena (fn reservation =>
              #begin_scope certifier reservation)
            val _ = rejects "an expired state proof scope before publication" (fn () =>
              #certify certifier stale_context [])
            val stale_stats_after = Data.stats arena
            val stale_nodes_after = Candidate.shallow_publisher_node_count publisher
            val _ = #end_scope certifier stale_scope
            val _ = if stale_nodes_after=stale_nodes_before andalso
                #proof_entries stale_stats_after = #proof_entries stale_stats_before andalso
                #scratch_entries stale_stats_after = #scratch_entries stale_stats_before
              then () else error "Expired state scope published or retained proof work"
            fun certify_child
                ({slot,environment,phase,action,action_equation,reduction,diagram}:
                  {slot:int,environment:Compiler.clock_env,phase:int,action:term,
                   action_equation:thm,reduction:Compiler.terminal_reduction,
                   diagram:Data.diagram}) =
              let
                val action_record: Compiler.program_action =
                  {key=key,environment=environment,source=source,program=program,
                   period=period,period_equation=period_equation,
                   node=Compiler.Terminal_Node {phase=phase,action=action,
                     action_equation=action_equation},diagram=diagram}
                val context_record: Compiler.action_context =
                  {action=action_record,source_binding=source_binding,
                   terminal_reduction=SOME reduction,goto_child_binding=NONE}
                val exactness = #certify certifier context_record []
                val _ = if closed_definition exactness andalso
                    has_weighted_zero_output exactness then ()
                  else error "Terminal state omitted its full zero-weight apply theorem"
              in
                {key=key,environment=environment,source=source,program=program,
                 source_binding=source_binding,period=period,
                 period_equation=period_equation,diagram=diagram,
                 exactness=exactness}: Compiler.certified_state
              end
            val children = map certify_child terminal_rows
            val child_diagrams = map #diagram children
            val diagram = Data.normalized_branch arena 1 child_diagrams
            val action: Compiler.program_action =
              {key=key,environment=Compiler.empty_env,source=source,
               program=program,period=period,period_equation=period_equation,
               node=Compiler.Branch_Node {axis=1,children=child_rows},
               diagram=diagram}
            val context_record: Compiler.action_context =
              {action=action,source_binding=source_binding,
               terminal_reduction=NONE,goto_child_binding=NONE}
            val exactness = #certify certifier context_record children
            val _ = if closed_definition exactness andalso
                has_weighted_zero_output exactness then ()
              else error "Entry-9 Branch callback omitted full zero-weight apply exactness"
            val branch_state: Compiler.certified_state =
              {key=key,environment=Compiler.empty_env,source=source,
               program=program,source_binding=source_binding,period=period,
               period_equation=period_equation,diagram=diagram,exactness=exactness}
            val goto_diagram = #diagram branch_state
            val goto_action_record: Compiler.program_action =
              {key=goto_key,environment=Compiler.empty_env,source=goto_source,
               program=goto_program,period=goto_period,
               period_equation=goto_period_equation,
               node=Compiler.Goto_Node {phase=0,action=goto_action,
                 action_equation=goto_action_equation,child=goto_child_key},
               diagram=goto_diagram}
            val goto_context_record: Compiler.action_context =
              {action=goto_action_record,source_binding=goto_source_binding,
               terminal_reduction=NONE,goto_child_binding=SOME goto_child_binding}
            val goto_exactness = #certify certifier goto_context_record [branch_state]
            val _ = if closed_definition goto_exactness andalso
                has_weighted_zero_output goto_exactness then ()
              else error "Near-8 Goto callback omitted full zero-weight apply exactness"
          in () end)
    in final_lthy end

  fun certifies_published_multi_axis_bind initial_lthy =
    let
      val arena = Data.make_arena 1024
      val leaves = map (fn value => Data.leaf arena
        {key="published-selector:" ^ Int.toString value,value=nat value}) (0 upto 5)
      fun deep shift = Data.raw_branch arena 2
        (map (fn slot => (0,List.nth (leaves,(slot+shift) mod 6))) (0 upto 6))
      val deeper = map deep (0 upto 5)
      fun row shift = Data.raw_branch arena 0
        (map (fn slot => (0,List.nth (deeper,(slot+shift) mod 6))) (0 upto 3))
      val rows = [row 0,List.nth (deeper,2),row 4]
      val target = Data.normalized_branch arena 1 rows
      val (_,final_lthy) = Candidate.with_shallow_transaction arena initial_lthy
        (fn transaction =>
          let
            val publisher = Candidate.make_shallow_publisher transaction
              @{typ nat} "comma_rank_published_selector_fixture"
            fun ensure_named roots =
              (ignore (Candidate.publish_shallow_roots publisher roots);
               Local_Theory.target_of (Candidate.current_local_theory transaction))
            val ctxt = ensure_named (target::rows)
            val factory = Comma_Semantic_Weighted_CRT_Shallow_Certificate.make
              ctxt arena @{typ nat}
              {lookup=Candidate.shallow_publisher_lookup publisher,
               ensure_named=SOME ensure_named}
            val visits_before = #normalization_node_visits (Data.stats arena)
            val result = #named_bind factory 1 rows target
            val visits_after = #normalization_node_visits (Data.stats arena)
            val _ = if length (#apply_slots result)=3 andalso
                List.all closed_definition (#apply_slots result) andalso
                visits_before=visits_after then ()
              else error "Published multi-axis bind lost exact slots or renormalized its target"
            val repeated = #named_bind factory 1 rows target
            val _ = if Data.same_action arena (#diagram result) (#diagram repeated)
                andalso #named_bind_hits (#stats factory ())=1 then ()
              else error "Published multi-axis bind failed completed-action reuse"
            val collapsed = List.nth (deeper,2)
            val collapsed_result = #named_bind factory 1 (replicate 3 collapsed) collapsed
            val _ = if List.all closed_definition (#apply_slots collapsed_result) then ()
              else error "Published equal-row collapse lost its exact slot theorems"
            val _ = rejects "wrong published multi-axis partition" (fn () =>
              #named_bind factory 1 rows (List.hd rows))
          in () end)
    in final_lthy end

  fun run initial_lthy =
    let
      val payloadT = @{typ nat}
      val arena = Data.make_arena 64
      val leaves = map (fn value => Data.leaf arena
        {key="rank-publication-fixture:" ^ Int.toString value,
         value=nat value}) (0 upto 3)
      val root = Data.raw_branch arena 0 (map (fn child => (0,child)) leaves)
      val committed_transaction = Unsynchronized.ref
        (NONE: Candidate.shallow_transaction option)
      val committed_publisher = Unsynchronized.ref
        (NONE: Candidate.shallow_publisher option)
      val (_,committed_lthy) = Candidate.with_shallow_transaction arena
        initial_lthy (fn transaction =>
          let
            val publisher = Candidate.make_shallow_publisher transaction
              payloadT "comma_rank_publication_fixture"
            val roots = Candidate.publish_shallow_roots publisher [root]
            val definitions = Candidate.shallow_publisher_definitions publisher
            val stats = Data.stats arena
            val node_count = Candidate.shallow_publisher_node_count publisher
            val _ = if length roots=1 andalso length definitions=node_count andalso
                node_count=5 andalso #proof_entries stats=node_count andalso
                #scratch_entries stats=0 then ()
              else error "Published nodes did not transfer scratch into exact proof charges"
            val _ = if List.all closed_definition definitions then ()
              else error "A committed shallow definition is not kernel-checked and closed"
            val _ = case Candidate.shallow_publisher_lookup publisher root of
                SOME _ => ()
              | NONE => error "Published root lookup was missing before transaction commit"
            val _ = committed_transaction := SOME transaction
            val _ = committed_publisher := SOME publisher
          in () end)
      val committed_stats = Data.stats arena
      val committed_tx = get_some "committed transaction" (!committed_transaction)
      val committed_pub = get_some "committed publisher" (!committed_publisher)
      val _ = if #proof_entries committed_stats=5 andalso
          #scratch_entries committed_stats=0 then ()
        else error "Successful commit did not preserve definitions without scratch residue"
      val _ = rejects "committed publisher lookup" (fn () =>
        Candidate.shallow_publisher_lookup committed_pub root)
      val _ = rejects "committed Local_Theory cursor" (fn () =>
        Candidate.current_local_theory committed_tx)

      val abort_arena = Data.make_arena 32
      val abort_leaf = Data.leaf abort_arena
        {key="rank-publication-abort-fixture",value=nat 19}
      val aborted_transaction = Unsynchronized.ref
        (NONE: Candidate.shallow_transaction option)
      val aborted_publisher = Unsynchronized.ref
        (NONE: Candidate.shallow_publisher option)
      val failure = Exn.capture (fn () =>
        Candidate.with_shallow_transaction abort_arena committed_lthy
          (fn transaction =>
            let
              val publisher = Candidate.make_shallow_publisher transaction
                payloadT "comma_rank_publication_abort_fixture"
              val _ = Candidate.publish_shallow_roots publisher [abort_leaf]
              val stats = Data.stats abort_arena
              val _ = if Candidate.shallow_publisher_node_count publisher=1 andalso
                  #proof_entries stats=1 andalso #scratch_entries stats=0 then ()
                else error "Abort fixture did not reach one fully published definition"
              val _ = aborted_transaction := SOME transaction
              val _ = aborted_publisher := SOME publisher
            in error "publication fixture forced abort after one node" end)) ()
      val _ = (case failure of
          Exn.Exn (ERROR message) =>
            if message="publication fixture forced abort after one node" then ()
            else error ("Unexpected publication fixture failure: " ^ message)
        | Exn.Exn failure => Exn.reraise failure
        | Exn.Res _ => error "Publication transaction unexpectedly accepted forced abort")
      val abort_stats = Data.stats abort_arena
      val aborted_tx = get_some "aborted transaction" (!aborted_transaction)
      val aborted_pub = get_some "aborted publisher" (!aborted_publisher)
      val _ = if #proof_entries abort_stats=0 andalso
          #scratch_entries abort_stats=0 then ()
        else error "Aborted publication leaked retained proofs or temporary scratch"
      val _ = rejects "aborted publisher lookup" (fn () =>
        Candidate.shallow_publisher_lookup aborted_pub abort_leaf)
      val _ = rejects "aborted Local_Theory cursor" (fn () =>
        Candidate.current_local_theory aborted_tx)
      val positive_lthy = certifies_entry9_branch_and_near8_goto
        (Local_Theory.target_of committed_lthy) committed_lthy
      val _ = rejects_bad_branch_environment
        (Local_Theory.target_of positive_lthy) positive_lthy
      val published_lthy = certifies_published_multi_axis_bind positive_lthy
    in published_lthy end
end
