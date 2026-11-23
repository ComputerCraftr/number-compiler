(* A checked multi-terminal selector chart preserves the exact projected
   action at nonzero phases.  This exercises the shared bind owner used by
   direct B1 Entries without constructing a family source graph. *)
structure Comma_Direct_Chart_Bind_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Bind_Replay = Comma_CRT_MDD_Bind_Replay
  structure Point = Comma_CRT_MDD_Point_Eval

  fun run lthy =
    let
      val arena = Arena.create [3,2]
      val selector = Arena.action_branch arena 0
        [Arena.action_some arena 0, Arena.action_some arena 1,
         Arena.action_some arena 2]
      val child_one = Arena.action_branch arena 1
        [Arena.action_some arena 50, Arena.action_some arena 51]
      val child_two = Arena.action_branch arena 1
        [Arena.action_some arena 55, Arena.action_some arena 56]
      val fallback = Arena.action_some arena 0
      val selected = Arena.bind_action_to_action arena selector fallback
        [(1,child_one),(2,child_two)]
      val wrong_children = Arena.bind_action_to_action arena selector fallback
        [(1,child_two),(2,child_one)]
      val (store,lthy') = Store.make "comma_direct_chart_bind_fixture_nodes" arena lthy
      val ctxt = Store.context store
      val replay = Bind_Replay.make store
      fun root action = Store.action_index store action
      val mapping = (root selector,root fallback,
        [(1,root child_one),(2,root child_two)])
      val swapped_mapping = (root selector,root fallback,
        [(1,root child_two),(2,root child_one)])
      val selected_certificate = Bind_Replay.bind_eval_phase replay mapping
      val wrong_certificate = Bind_Replay.bind_eval_phase replay
        swapped_mapping
      val selected_witness = Store.bind_witness store mapping
      val wrong_witness = Store.bind_witness store swapped_mapping
      val _ = if #result selected_witness = root selected andalso
          #result wrong_witness = root wrong_children then ()
        else error "MDD chart witness disagrees with its published root"

      fun assert_value label phase action payload =
        let val result = Point.prove store phase (root action)
        in if #payload result = payload then #theorem result else error label end
      val selected_phase_three = assert_value
        "MDD chart exact projection at phase 3" 3 selected 52
      val selected_phase_four = assert_value
        "MDD chart exact projection at phase 4" 4 selected 56
      val selected_phase_five = assert_value
        "MDD chart unbound label at phase 5" 5 selected 1
      val swapped_phase_three = assert_value
        "MDD swapped-child projection at phase 3" 3 wrong_children 57
      val swapped_phase_four = assert_value
        "MDD swapped-child projection at phase 4" 4 wrong_children 51

      val foreign_arena = Arena.create [3,2]
      val foreign_root = Arena.action_some foreign_arena 50
      fun reject_foreign_store_root () =
        (case Exn.capture (fn () => Store.action_index store foreign_root) () of
          Exn.Exn (ERROR _) => ()
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error "MDD receiving Store accepted a foreign arena root")
      val _ = reject_foreign_store_root ()
      val _ = if null (Thm.hyps_of selected_certificate) andalso
          null (Thm.tpairs_of selected_certificate) andalso
          null (Thm.hyps_of wrong_certificate) andalso
          null (Thm.tpairs_of wrong_certificate) then ()
        else error "MDD chart bind certificate is not closed"
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Shared MDD chart binding, exact projection and store ownership"
        [selected_certificate,wrong_certificate,selected_phase_three,selected_phase_four,
         selected_phase_five,swapped_phase_three,swapped_phase_four]
    in lthy' end
end
