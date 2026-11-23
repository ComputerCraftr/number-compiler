structure Comma_Direct_Slot_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Replay = Comma_CRT_MDD_Bind_Replay
  structure Slots = Comma_CRT_MDD_Indexed_Slots

  fun run lthy =
    let
      val arena = Arena.create [2]
      val first = Arena.action_some arena 0
      val second = Arena.action_some arena 1
      val left = Arena.action_some arena 6
      val right = Arena.action_some arena 7
      val fallback = Arena.action_some arena 8
      val first_mapping = [(1,left)]
      val second_mapping = [(2,right)]
      val wrong_child = [(1,right)]
      val wrong_label = [(1,left),(6,right)]
      fun witness source mapping = Arena.bind_action_to_action arena source fallback mapping
      val first_out = witness first first_mapping
      val second_out = witness second second_mapping
      val _ = witness first wrong_child
      val _ = witness first wrong_label
      val selected_source = Arena.action_branch arena 0 [first,second]
      val selected_out = witness selected_source first_mapping
      val selected_expected = Arena.action_branch arena 0 [left,fallback]
      val _ = if Arena.action_index arena selected_out = Arena.action_index arena selected_expected
        then () else error "Selected bind did not preserve slot order or the fallback"
      val (store, lthy') = Store.make "comma_direct_slot_fixture_nodes" arena lthy
      val (foreign, result_ctxt) = Store.make "comma_foreign_slot_fixture_nodes" arena lthy'
      fun key owner source mapping =
        let val index = Store.action_index owner
        in (index source, index fallback, map (apsnd index) mapping) end
      val replay = Replay.make store
      val selected_key = key store selected_source first_mapping
      val _ = (case #step (Store.bind_witness store selected_key) of
          Arena.Bind_Selected_Leaf_Branch _ => ()
        | _ => error "Selected bind fixture has no selected-leaf witness")
      val selected_thm = Replay.certify_bind replay selected_key
      val first_thm = Replay.certify_bind replay (key store first first_mapping)
      val second_thm = Replay.certify_bind replay (key store second second_mapping)
      val wrong_child_thm = Replay.certify_bind replay (key store first wrong_child)
      val wrong_label_thm = Replay.certify_bind replay (key store first wrong_label)
      val foreign_thm =
        Replay.certify_bind (Replay.make foreign) (key foreign first first_mapping)

      val natT = @{typ nat}
      val pairT = HOLogic.mk_prodT (natT, natT)
      val index = Store.action_index store
      val numeral = HOLogic.mk_number natT
      fun roots values = HOLogic.mk_list natT (map (numeral o index) values)
      fun mapping_term rows = HOLogic.mk_list pairT
        (map (fn (label, child) => HOLogic.mk_prod (numeral label, numeral (index child))) rows)
      val fields =
        [HOLogic.mk_list (HOLogic.listT pairT) (map mapping_term [first_mapping, second_mapping]),
         roots [fallback, fallback], roots [first, second], roots [first_out, second_out]]
      val ct = Thm.cterm_of result_ctxt
      val slot = Free ("direct_fixture_slot", natT)
      val indexed = map (fn field =>
        Thm.term_of (Slots.nth_ct result_ctxt (ct field) (ct slot))) fields
      val bind = @{term "comma_crt_mdd_bind_certificate ::
        nat list => nat comma_crt_mdd_node list => (nat * nat) list =>
        nat => nat => nat => bool"}
      val predicate = ct (Term.lambda slot
        (list_comb (bind, Store.radices store :: Store.table store :: indexed)))
      val successor = #equation
        (Comma_Selected_List_Conversion.make_successor_cache result_ctxt 2)
      val convert = Slots.bind_conversion result_ctxt successor
        (map (Thm.reflexive o ct) fields)
      val adapt = Slots.adapt result_ctxt predicate convert
      val positive = [adapt 0 first_thm, adapt 1 second_thm]

      fun reject label i theorem =
        (case Exn.capture (fn () => adapt i theorem) () of
          Exn.Exn (ERROR message) =>
            if String.isPrefix "Concrete MDD bind slot proves a different proposition" message
            then () else error ("Unexpected " ^ label ^ " rejection: " ^ message)
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error ("Direct slot accepted " ^ label))
      val _ = reject "wrong slot" 1 first_thm
      val _ = reject "wrong child" 0 wrong_child_thm
      val _ = reject "wrong label" 0 wrong_label_thm
      val _ = reject "foreign Store" 0 foreign_thm
      val _ = Comma_Proof_Dependency_Audit.require_native_clean result_ctxt
        "Direct indexed bind slot fixture" (selected_thm :: positive)
    in result_ctxt end
end
