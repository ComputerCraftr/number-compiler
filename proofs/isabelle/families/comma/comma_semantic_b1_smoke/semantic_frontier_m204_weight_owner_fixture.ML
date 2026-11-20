(* Negative owner lifecycle checks.  A positive publication requires the real
   kernel-checked M204 Bellman theorem, not a synthetic assumed certificate. *)
structure Comma_Frontier_M204_Weight_Owner_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Owner = Comma_Frontier_M204_Weight_Owner

  fun run lthy =
    let
      val arena = Arena.create [3,4,7,11]
      val root = Arena.action_none arena
      val (store,lthy1) = Store.make "m204_owner_fixture_store" arena lthy
      val ctxt = Local_Theory.target_of lthy1
      val weight = @{term "\<lambda>phase::nat. \<lambda>cid::nat. (0::nat)"}
      fun rejects expected attempt =
        (case Exn.capture attempt () of
          Exn.Exn exn =>
            if String.isSubstring expected (Runtime.exn_message exn) then ()
            else error ("M204 owner fixture failed for an unrelated reason: " ^
              Runtime.exn_message exn)
        | Exn.Res _ => error "M204 weight owner accepted an invalid publication")
      val _ = rejects "No M204 weight authority" (fn () => Owner.retrieve ctxt weight)
      val _ = rejects "M204 issued weight definition" (fn () =>
        Owner.publish store arena (replicate 46 root) weight @{thm TrueI} @{thm TrueI} lthy1)
      val _ = rejects "No M204 weight authority" (fn () => Owner.retrieve ctxt weight)
    in lthy1 end
end
