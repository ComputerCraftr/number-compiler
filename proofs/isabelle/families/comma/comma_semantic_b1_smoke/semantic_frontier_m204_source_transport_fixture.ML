(* Bounded source transport boundary tests.  These do not claim an
   authoritative physical class-step theorem. *)
structure Comma_Frontier_M204_Source_Transport_Fixture =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Transport = Comma_Frontier_M204_Source_Transport
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun run lthy =
    let
      val source_arena = Arena.create [3,4,7,11]
      val work_arena = Arena.create [3,4,7,11]
      val source_root = Arena.action_some source_arena 6
      val work_root = Arena.action_some work_arena 6
      val (source,lthy1) = Store.make "m204_transport_fixture_source" source_arena lthy
      val (work,lthy2) = Store.make "m204_transport_fixture_work" work_arena lthy1
      val ctxt = Local_Theory.target_of lthy2
      val source_id = Store.action_index source source_root
      val work_id = Store.action_index work work_root
      val source_value = Store.phase_leaf source source_id
      val work_value = Store.phase_leaf work work_id
      val phase = Free ("m204_fixture_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val source_at = Thm.forall_elim phase_ct source_value
      val work_at = Thm.forall_elim phase_ct work_value
      val point = @{thm trans} OF [source_at,@{thm sym} OF [work_at]]
      val equality = Thm.forall_intr phase_ct point
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 independent bounded phase equality" [equality]
      val roots = replicate 46 work_root
      val source_roots = replicate 46 source_root
      val facts = replicate 46 equality
      val work_ids = HOLogic.mk_list natT (map (nat o Store.action_index work) roots)
      val action = @{term comma_frontier_m204_mdd_value} $
        Store.radices work $ Store.table work $ work_ids
      fun rejects expected attempt =
        (case Exn.capture attempt () of
          Exn.Exn exn =>
            if String.isSubstring expected (Runtime.exn_message exn) then ()
            else error ("M204 transport fixture failed for an unrelated reason: " ^
              Runtime.exn_message exn)
        | Exn.Res _ => error "M204 transport fixture accepted an invalid request")
      val _ = rejects "matching 46-root stores" (fn () =>
        Transport.prove source (tl source_roots) work roots facts @{thm TrueI} action)
      val foreign_arena = Arena.create [3,4,7,11]
      val foreign_root = Arena.action_some foreign_arena 6
      val _ = rejects "root belongs to another arena" (fn () =>
        Transport.prove source (foreign_root :: tl source_roots) work roots facts
          @{thm TrueI} action)
      val _ = rejects "not the selected frozen MDD vector" (fn () =>
        Transport.prove source source_roots work roots facts @{thm TrueI}
          @{term "\<lambda>phase::nat. \<lambda>cid::nat. (0::nat)"})
      val _ = rejects "M204 universal class-action authority" (fn () =>
        Transport.prove source source_roots work roots facts @{thm TrueI} action)
    in lthy2 end
end
