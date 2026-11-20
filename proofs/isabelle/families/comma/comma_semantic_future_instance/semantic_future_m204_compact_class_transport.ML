(* Authenticate the compact class table against the existing checked work
   table. Candidate node indices are only requests; every root equality is a
   native MDD zip theorem between two frozen, wellformed Stores. *)
structure Comma_Future_M204_Compact_Class_Transport =
struct
  structure Arena = Comma_CRT_MDD_Arena
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Zip = Comma_Semantic_Future_Zip_Certificates
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun prove source_store source_roots (export:Arena.exported)
      work_store work_roots comparison_roots =
    let
      val ctxt = Store.context work_store
      val _ = if length source_roots=16 andalso length work_roots=16 andalso
          length comparison_roots=16 andalso length (#roots export)=16 andalso
          Store.radices source_store aconv Store.radices work_store then ()
        else error "Compact class transport has incompatible roots or radices"
      val source_ids = map (Store.action_index source_store) source_roots
      val recorded = map (fn index => List.nth (#source_indices export,index)) (#roots export)
        handle Subscript => error "Compact class export has an invalid source transcript"
      val _ = if source_ids=recorded then ()
        else error "Compact class export does not name its authenticated roots"
      val work_ids = map (Store.action_index work_store) work_roots
      val equal = @{term "\<lambda>x::nat. \<lambda>y::nat. if x=y then (1::nat) else 0"}
      fun leaf_rule x y z = Goal.prove ctxt [] []
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (equal $ nat x $ nat y,nat z)))
        (fn {context,...} => simp_tac context 1)
      val replay = Zip.make ctxt source_store work_store work_store equal leaf_rule
      val phase = Free ("future_compact_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val rule = Drule.infer_instantiate ctxt [( ("phase",0),phase_ct)]
        @{thm comma_frontier_m204_import_equal}
      fun row ((source,target),comparison) =
        let
          val truth = Store.action_index work_store comparison
          val _ = (case Store.node work_store truth of Store.Leaf 1 => ()
            | _ => error "Compact class comparison is not the true leaf")
          val certificate = Zip.certify replay source target truth
          val true_at = Thm.forall_elim phase_ct (Store.phase_leaf work_store truth)
          val point = rule OF [certificate,Store.wellformed source_store,
            Store.wellformed work_store,Store.bound source_store source,
            Store.bound work_store target,true_at]
        in Thm.forall_intr phase_ct point end
      val facts = ListPair.mapEq row (source_ids ~~ work_ids,comparison_roots)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Compact class Store root transports" facts
    in facts end
end
