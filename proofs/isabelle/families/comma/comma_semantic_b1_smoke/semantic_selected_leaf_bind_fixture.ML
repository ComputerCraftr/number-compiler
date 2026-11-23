(* Selected-source bind regressions retain the checked fallback and order. *)
structure Comma_Selected_Leaf_Bind_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Replay = Comma_CRT_MDD_Bind_Replay
  structure Point = Comma_CRT_MDD_Point_Eval

  fun statistic name report =
    let
      val prefix = name ^ "="
      val token = (case List.find (String.isPrefix prefix)
          (String.tokens (fn character => character = #" ") report) of
        SOME value => value
      | NONE => error ("Selected bind statistic is missing: " ^ name))
    in the (Int.fromString (String.extract (token, String.size prefix, NONE))) end

  fun run lthy =
    let
      val arena = Arena.create [3,2]
      val a = Arena.action_some arena 10
      val b = Arena.action_some arena 20
      val fallback = Arena.action_some arena 30
      val selector = Arena.action_branch arena 0
        [Arena.action_some arena 0, Arena.action_some arena 1, Arena.action_some arena 2]
      val rotated_selector = Arena.action_branch arena 0
        [Arena.action_some arena 1, Arena.action_some arena 0, Arena.action_some arena 2]
      val target = Arena.action_branch arena 0 [a,b,fallback]
      val swapped = Arena.action_branch arena 1 [b,a]
      val output = Arena.bind_action_to_action arena selector fallback [(1,target),(2,swapped)]
      val wrong_target = Arena.bind_action_to_action arena selector fallback
        [(1,swapped),(2,target)]
      val wrong_fallback = Arena.bind_action_to_action arena selector a [(1,target),(2,swapped)]
      val rotated_output = Arena.bind_action_to_action arena rotated_selector fallback
        [(1,target),(2,swapped)]
      val (store,lthy') = Store.make "comma_selected_leaf_bind_fixture_nodes" arena lthy
      fun root action = Store.action_index store action
      val replay = Replay.make store
      val key = (root selector,root fallback,[(1,root target),(2,root swapped)])
      val certificate = Replay.bind_eval_phase replay key
      val report = Replay.statistics replay
      val _ = if statistic "selected_leaf_branches" report = 1 andalso
          statistic "bind_certificate_nodes" report = 1 andalso
          statistic "mapping_family_builds" report = 0 then ()
        else error "Selected bind rebuilt leaf or mapping-family certificates"
      val rotated_key = (root rotated_selector,root fallback,
        [(1,root target),(2,root swapped)])
      val rotated_certificate = Replay.bind_eval_phase replay rotated_key
      val shared_report = Replay.statistics replay
      val _ = if statistic "selected_cofactor_hits" shared_report > 0 andalso
          statistic "selected_target_hits" shared_report > 0 then ()
        else error "Selected bind did not reuse compatible checked cofactors and targets"
      val previous_report = Replay.statistics replay
      val _ = Replay.bind_eval_phase replay key
      val warm_report = Replay.statistics replay
      val _ = if List.all (fn name =>
          statistic name previous_report = statistic name warm_report)
          ["bind_certificate_nodes", "payload_cover_nodes",
           "cofactor_family_builds", "mapping_family_builds",
           "selected_leaf_branches", "selected_leaf_rows",
           "selected_cofactor_builds", "selected_target_builds"] then ()
        else error "Selected bind warm request repeated proof construction"
      fun value action phase = #payload (Point.prove store phase (root action))
      val _ = if value output 0 = 11 andalso value output 1 = 11 andalso
          value output 2 = 31 then ()
        else error "Selected bind changed an ordered output or fallback"
      val _ = if value wrong_target 0 <> value output 0 andalso
          value wrong_fallback 2 <> value output 2 then ()
        else error "Selected bind failed to distinguish target or fallback changes"
      val _ = if value rotated_output 0 <> value output 0 then ()
        else error "Selected bind ignored a changed source phase"
      val _ = Comma_Proof_Dependency_Audit.require_native_clean (Store.context store)
        "Selected leaf bind preserves target, order and fallback"
        [certificate,rotated_certificate]
    in lthy' end
end
