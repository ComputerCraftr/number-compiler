(* Kernel replay of overlapping priority cases and fallback. *)
structure Comma_CRT_MDD_Priority_Checked_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena

  fun run lthy =
    let
      val arena = Arena.create [3,4,7,11]
      val no = Arena.boolean_false arena
      val yes = Arena.boolean_true arena
      val guard = Arena.boolean_branch arena 0 [no,yes,no]
      val guard_later = Arena.boolean_branch arena 1 [no,yes,no,yes]
      val first = Arena.action_some arena 2
      val second = Arena.action_some arena 5
      val fallback = Arena.action_none arena
      val requests = [[],[(no,first)],[(yes,first),(yes,second)],
        [(guard,first),(yes,second)],
        [(guard,first),(no,second),(yes,second),(yes,first)],
        [(guard,second),(yes,first)],[(guard_later,first),(yes,second)]]
      val proposals = map (fn rows => Arena.priority_select arena rows fallback) requests
      val (store,lthy1) = Comma_CRT_MDD_Certificate_Store.make
        "mdd_priority_fixture_nodes" arena lthy
      val replay = Comma_CRT_MDD_Multiway_Replay.make store
      val facts = map (Comma_CRT_MDD_Multiway_Replay.certify replay o #2) proposals
      val guard_id = Arena.boolean_index arena guard
      val later_id = Arena.boolean_index arena guard_later
      val cofactor_cache = !(#cofactors replay)
      val _ = if !(#cofactor_hits replay) > 0 andalso
          Comma_CRT_MDD_Multiway_Replay.Cofactor_Key.defined cofactor_cache (0,0,guard_id) andalso
          Comma_CRT_MDD_Multiway_Replay.Cofactor_Key.defined cofactor_cache (0,1,guard_id) andalso
          Comma_CRT_MDD_Multiway_Replay.Family_Key.defined (!(#families replay)) (0,guard_id) andalso
          Comma_CRT_MDD_Multiway_Replay.Cofactor_Key.defined cofactor_cache (1,0,later_id) andalso
          (case Comma_CRT_MDD_Certificate_Store.node store guard_id of
             Comma_CRT_MDD_Certificate_Store.Branch (_,cs) => List.nth (cs,0) <> List.nth (cs,1)
           | _ => false) then ()
        else error "Priority cofactor reuse did not distinguish axis and slot"
      val alternate = #2 (List.nth (proposals,4))
      val normalized = Comma_CRT_MDD_Certificate_Store.priority_normalize store alternate
      val _ = if alternate <> normalized then ()
        else error "Priority raw fixture unexpectedly has canonical form"
      val normalization_before = !(#normalization_proofs replay)
      val hits_before = !(#memo_hits replay)
      val cofactors_before = !(#cofactor_misses replay)
      val warm = Comma_CRT_MDD_Multiway_Replay.certify replay alternate
      val _ = if Thm.prop_of warm aconv Thm.prop_of (List.nth (facts,4)) andalso
          !(#normalization_proofs replay) = normalization_before andalso
          !(#memo_hits replay) = hits_before+1 andalso
          !(#cofactor_misses replay) = cofactors_before then ()
        else error "Warm raw priority request repeated normalization or changed theorem"
      val _ = Comma_CRT_MDD_Multiway_Replay.certify replay normalized
      val _ = if !(#normalization_proofs replay) = normalization_before then ()
        else error "Warm canonical priority request repeated normalization"
      val _ = (case Exn.capture (Comma_CRT_MDD_Multiway_Replay.certify replay)
          ([(999999,0)],0) of Exn.Exn _ => ()
        | Exn.Res _ => error "Priority replay accepted an out-of-range node index")
      val _ = Comma_Proof_Dependency_Audit.require_native_clean
        (Local_Theory.target_of lthy1) "Priority fixture kernel certificates" facts
    in lthy1 end
end
