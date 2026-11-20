(* Direct expression authority is owned by its receiving frozen Store. *)
structure Comma_Direct_MDD_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Proposal = Comma_Direct_MDD_Proposal
  structure Evaluation = Comma_Direct_MDD_Evaluation

  fun run lthy =
    let
      val names = Comma_Direct_Expression_Names.make "direct_mdd_fixture" lthy
      val fork = #intern names @{term "Comma_Direct_Fork 2 0"}
      val other_fork = #intern names @{term "Comma_Direct_Fork 3 0"}
      val core23_fork = #intern names @{term "Comma_Direct_Fork 4 0"}
      val landmine = #intern names @{term "Comma_Direct_Landmine 0"}
      val child = #intern names (@{term Comma_Direct_Goto} $ fork $ @{term "0::nat"})
      fun entry core rows = #intern names (@{term Comma_Direct_Entry} $ core $
        HOLogic.mk_list @{typ "nat * comma_direct_action_expression"}
          (map (fn (wanted,action) => HOLogic.mk_prod
            (HOLogic.mk_number @{typ nat} wanted,action)) rows))
      val expression = entry @{term Comma_Core_1} [(0,child)]
      val branching = entry @{term Comma_Core_11} [(0,other_fork),(1,landmine)]
      val core23_entry = entry @{term Comma_Core_23} [(1,core23_fork)]
      fun reject label attempt =
        (case Exn.capture attempt () of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn (THM _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error ("Direct MDD owner accepted " ^ label))
      val _ = reject "definition before publication" (fn () => #definition names fork)
      val _ = reject "body before publication" (fn () => #body names fork)
      val named_lthy = #finish names ()
      val collision = Comma_Direct_Expression_Names.make "direct_mdd_fixture" named_lthy
      val collision_name = #intern collision @{term Comma_Direct_Invalid}
      val _ = reject "duplicate expression prefix" (fn () => #finish collision ())
      val _ = reject "definition after failed publication" (fn () => #definition collision collision_name)
      val proposal = Proposal.build Comma_Frontier24_Parametric_Runtime.computation
        (#body names) [expression,other_fork,branching,core23_entry] []
      val arena = #arena proposal
      val (store,lthy') = Store.make "direct_expression_fixture_nodes" arena named_lthy
      val ctxt = Local_Theory.target_of lthy'
      val poison_expression_access = Unsynchronized.ref false
      fun body expression = if !poison_expression_access then
          error "Warm parent revisited expression body" else #body names expression
      fun definition expression = if !poison_expression_access then
          error "Warm parent revisited expression definition" else #definition names expression
      val owner = Evaluation.make store arena (#guards proposal) body definition
      val application = hd (#classes proposal)
      val first = #certify owner application
      val branch_application = List.nth (#classes proposal,2)
      val branch_fact = #certify owner branch_application
      val core23_fact = #certify owner (List.nth (#classes proposal,3))
      val _ = (case branch_application of
          Proposal.Application {expression,shift,root,step=Proposal.Entry (rows,key)} =>
            (case rows of [left,right] =>
              let
                fun fresh altered =
                  let val cold = Evaluation.make store arena (#guards proposal) body definition
                  in #certify cold (Proposal.Application
                    {expression=expression,shift=shift,root=root,step=Proposal.Entry (altered,key)}) end
                val wrong_guard =
                  {wanted= #wanted left,guard= #guard right,shifted= #shifted right,
                   child= #child left}: Proposal.entry_row
                val wrong_child =
                  {wanted= #wanted left,guard= #guard left,shifted= #shifted left,
                   child= #child right}: Proposal.entry_row
                val _ = reject "cold Entry missing row" (fn () => fresh [left])
                val _ = reject "cold Entry wrong guard" (fn () => fresh [wrong_guard,right])
                val _ = reject "cold Entry wrong child" (fn () => fresh [wrong_child,right])
              in () end
            | _ => error "Expected two Entry rows in tampering fixture")
        | _ => error "Expected Entry application in tampering fixture")
      val root = Proposal.root application
      val foreign_arena = Arena.create [3,4,7,11]
      val foreign = Arena.action_some foreign_arena 46
      val poison = Proposal.Application {expression=expression,shift=0,
        root=foreign,step=Proposal.Terminal}
      val _ = poison_expression_access := true
      val warm = #certify owner (Proposal.Application
        {expression=expression,shift=0,root=root,step=Proposal.Goto poison})
      val _ = poison_expression_access := false
      val _ = if Thm.prop_of first aconv Thm.prop_of warm andalso
          String.isSubstring "direct_mdd_application_hits=1" (#statistics owner ()) then ()
        else error "Warm direct expression changed its checked result"
      val wrong_root = Proposal.root (List.nth (#classes proposal,1))
      val _ = reject "changed root under a cached expression" (fn () =>
        #certify owner (Proposal.Application {expression=expression,shift=0,
          root=wrong_root,step=Proposal.Terminal}))
      val _ = reject "foreign Store root" (fn () => #certify owner poison)
      val _ = reject "negative application shift" (fn () =>
        #certify owner (Proposal.Application {expression=expression,shift= ~1,
          root=root,step=Proposal.Terminal}))
      val _ = reject "open expression" (fn () =>
        #certify owner (Proposal.Application
          {expression=Free ("unissued_expression",@{typ comma_direct_action_expression}),
           shift=0,root=root,step=Proposal.Terminal}))
      val _ = reject "changed terminal shift" (fn () =>
        #certify owner (Proposal.Application {expression=fork,
          shift=1,root=root,step=Proposal.Terminal}))
      val _ = reject "publication after expression owner sealed" (fn () =>
        #intern names @{term "Comma_Direct_Fork 4 0"})
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Direct expression composition and warm-parent authority"
          [first,branch_fact,core23_fact,warm]
    in lthy' end
end
