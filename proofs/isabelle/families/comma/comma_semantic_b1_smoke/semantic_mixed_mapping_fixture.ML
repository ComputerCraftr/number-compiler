structure Comma_Mixed_Mapping_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Replay = Comma_CRT_MDD_Bind_Replay
  structure Point = Comma_CRT_MDD_Point_Eval

  fun run lthy =
    let
      val arena = Arena.create [3,2]
      val a = Arena.action_some arena 0
      val b = Arena.action_some arena 1
      val child = Arena.action_branch arena 1 [a,b]
      val source = Arena.action_branch arena 0 [child,b,child]
      val one = Arena.action_some arena 10
      val two = Arena.action_some arena 20
      val target = Arena.action_branch arena 1 [one,two]
      val fallback = Arena.action_some arena 30
      val output = Arena.bind_action_to_action arena source fallback [(1,target),(2,target)]
      val changed_output = Arena.bind_action_to_action arena source fallback
        [(1,target),(2,fallback)]
      val (store,lthy') = Store.make "comma_mixed_mapping_fixture_nodes" arena lthy
      fun root value = Store.action_index store value
      val replay = Replay.make store
      val key = (root source, root fallback, [(1,root target),(2,root target)])
      val theorem = Replay.bind_eval_phase replay key
      val report = Replay.statistics replay
      val _ = if String.isSubstring "mapping_family_builds=0" report
        then error "Mixed mapping fixture did not construct a mapping family" else ()
      val _ = if #payload (Point.prove store 0 (root output)) = 11 then ()
        else error "Mixed mapping selected the wrong output"
      val changed = Replay.bind_eval_phase replay
        (root source,root fallback,[(1,root target),(2,root fallback)])
      val _ = if #payload (Point.prove store 1 (root output)) <>
          #payload (Point.prove store 1 (root changed_output)) then ()
        else error "Mixed mapping ignored a changed target"
      val _ = Comma_Proof_Dependency_Audit.require_native_clean (Store.context store)
        "Mixed mapping fixture" [theorem,changed]
    in lthy' end
end
