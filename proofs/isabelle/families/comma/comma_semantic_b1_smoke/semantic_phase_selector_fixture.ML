structure Comma_Phase_Selector_Application_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Point = Comma_CRT_MDD_Point_Eval
  structure Proposal = Comma_Direct_MDD_Proposal
  structure Evaluation = Comma_Direct_MDD_Evaluation
  structure Phase = Comma_Semantic_Phase_Selector
  val nat = HOLogic.mk_number @{typ nat}

  fun reject label attempt =
    (case Exn.capture attempt () of
      Exn.Exn (ERROR _) => ()
    | Exn.Exn (THM _) => ()
    | Exn.Exn exn => Exn.reraise exn
    | Exn.Res _ => error ("Phase selector accepted " ^ label))

  fun run lthy =
    let
      val names = Comma_Direct_Expression_Names.make "phase_selector_fixture" lthy
      val fork = #intern names @{term "Comma_Direct_Fork 2 0"}
      val landmine = #intern names @{term "Comma_Direct_Landmine 0"}
      fun entry core rows = #intern names (@{term Comma_Direct_Entry} $ core $
        HOLogic.mk_list @{typ "nat * comma_direct_action_expression"}
          (map (fn (wanted,action) => HOLogic.mk_prod (nat wanted,action)) rows))
      val core = @{term Comma_Core_7}
      val expression = entry core [(1,fork),(3,landmine)]
      val delayed = #intern names (@{term Comma_Direct_Goto} $ expression $ nat 924)
      val alternate = entry core [(1,landmine),(3,fork)]
      val wrong_core_expression = entry @{term Comma_Core_13} [(1,fork),(3,landmine)]
      val named = #finish names ()
      val produced = Proposal.build Comma_Frontier24_Parametric_Runtime.computation
        (#body names) [expression,delayed,alternate] []
      val arena = #arena produced
      val phase_owner = Phase.make arena
      val _ = (case Phase.propose phase_owner
          (Free ("unknown_phase_core",@{typ comma_phase_core_id})) 0 [] of
          NONE => () | SOME _ => error "Unclassified phase core was admitted")
      val _ = reject "a negative phase shift" (fn () =>
        Phase.propose phase_owner core ~1 [1])
      val _ = reject "duplicate wanted labels" (fn () =>
        Phase.propose phase_owner core 0 [1,1])
      val (entry_now, entry_delayed, entry_alternate) = (case #classes produced of
          [first,Proposal.Application {step=Proposal.Goto second,...},third] =>
            (first,second,third)
        | _ => error "Expected direct and delayed applications")
      fun chart (Proposal.Application {step=Proposal.Entry (_,selector),...}) = #chart selector
        | chart _ = error "Expected Entry application"
      val current_chart = chart entry_now
      val delayed_chart = chart entry_delayed
      val _ = if Arena.action_index arena (#root current_chart) =
          Arena.action_index arena (#root delayed_chart)
        then () else error "Selector phase did not reuse after 924 ticks"
      val _ = if not (null (#guards produced)) then error "Phase chart constructed old Boolean guards"
        else ()
      val (store, result) = Store.make "phase_selector_fixture_nodes" arena named
      val ctxt = Store.context store
      fun evaluator () = Evaluation.make store arena (#guards produced) (#body names) (#definition names)
      val owner = evaluator ()
      val first = #certify owner entry_now
      val second = #certify owner entry_delayed
      val _ = if Thm.prop_of first aconv Thm.prop_of second then
          error "Selector phase merged the two application propositions" else ()
      fun at phase application = #payload (Point.prove store phase
        (Store.action_index store (Proposal.root application)))
      val _ = if at 0 entry_now = 55 andalso at 5 entry_now = 47 andalso
          at 0 entry_delayed = 0 andalso at 5 entry_delayed = 0 then ()
        else error "Selector lost the absolute Fork or Landmine clock"
      val _ = if #payload (Point.prove store 1
          (Store.action_index store (#root current_chart))) = 0
        then () else error "Unsupported wanted value did not select the true default"
      val _ = (case entry_now of
          Proposal.Application {shift,root,step,...} =>
            reject "a different core with the same period" (fn () =>
              #certify (evaluator ()) (Proposal.Application
                {expression=wrong_core_expression,shift=shift,root=root,step=step})))
      val _ = (case #phase current_chart of
          NONE => error "No issued phase chart in matched fixture"
        | SOME proposal =>
            let
              val template = #template proposal
              val rows = (case #rows template of
                  (i,left)::(j,right)::rest => (i,right)::(j,left)::rest
                | _ => error "Expected two mapped slots in incomplete support")
              val changed:Phase.template =
                {period= #period template,offset= #offset template,base= #base template,
                 shifted= #shifted template,root= #root template,fallback= #fallback template,
                 rows=rows}
              val corrupted:Proposal.selector_chart =
                {wanted= #wanted current_chart,root= #root current_chart,
                 steps= #steps current_chart,
                 phase=SOME {shift= #shift proposal,template=changed}}
            in (case entry_now of
              Proposal.Application {expression,shift,root,step=Proposal.Entry (entry_rows,selector)} =>
                let
                  val changed_selector:Proposal.selector =
                    {chart=corrupted,key= #key selector,fallback= #fallback selector}
                in reject "swapped slots in the frozen result" (fn () =>
                  #certify (evaluator ()) (Proposal.Application
                    {expression=expression,shift=shift,root=root,
                     step=Proposal.Entry (entry_rows,changed_selector)})) end
            | _ => error "Expected Entry application") end)
      val _ = (case entry_alternate of
          Proposal.Application {expression,shift,root,step=Proposal.Entry (entry_rows,selector)} =>
            let
              val chart = #chart selector
              val wrong_chart:Proposal.selector_chart =
                {wanted= #wanted chart,root= #fallback selector,steps= #steps chart,
                 phase= #phase chart}
              val wrong_selector:Proposal.selector =
                {chart=wrong_chart,key= #key selector,fallback= #fallback selector}
            in reject "cached selector under a different chart root" (fn () =>
              #certify owner (Proposal.Application
                {expression=expression,shift=shift,root=root,
                 step=Proposal.Entry (entry_rows,wrong_selector)})) end
        | _ => error "Expected alternate Entry application")
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Phase chart with absolute application shifts" [first,second]
    in result end
end
