(* Small exact path and boundary tests for the shared point evaluator. *)
structure Comma_CRT_MDD_Point_Eval_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Point = Comma_CRT_MDD_Point_Eval

  fun run lthy =
    let
      val arena = Arena.create [3,4,7,11]
      val roots = Arena.seed_prefix arena
        [Arena.Seed_Leaf 1,Arena.Seed_Leaf 2,Arena.Seed_Branch (0,[0,1,0])]
      val (store,lthy1) = Store.make "mdd_point_fixture_nodes" arena lthy
      val leaf = Store.action_index store (List.nth (roots,0))
      val branch = Store.action_index store (List.nth (roots,2))
      fun expect root phase payload =
        let val result = Point.prove store phase root
        in if #payload result = payload then () else error "MDD point fixture payload differs" end
      fun rejects text attempt =
        (case Exn.capture attempt () of
          Exn.Exn exn => if String.isSubstring text (Runtime.exn_message exn) then ()
            else error ("MDD point fixture failed for an unrelated reason: " ^ Runtime.exn_message exn)
        | Exn.Res _ => error "MDD point fixture accepted an invalid request")
      val _ = expect leaf 0 1
      val _ = expect branch 0 1
      val _ = expect branch 1 2
      val _ = rejects "outside its frozen certificate table"
        (fn () => Point.prove store 0 (Store.node_count store))
      val _ = rejects "phase must be nonnegative" (fn () => Point.prove store ~1 branch)
    in lthy1 end
end
