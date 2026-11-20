(* Kernel replay of the shared symbolic operations in an M204 Bellman
   proposal.  These operation theorems are not, by themselves, an exact
   physical one-step authority or a release certificate. *)
signature COMMA_FRONTIER_M204_BELLMAN_CERTIFICATES =
sig
  type store = Comma_CRT_MDD_Certificate_Store.store
  type result =
    {step_import_evals: thm list, shifts: thm list,
     comparisons: thm list, bind_certificates: thm list,
     d_covers: thm list, d_labels: int list}
  val replay: store -> store ->
    Comma_Frontier_M204_Bellman_Proposal.result -> result
end

structure Comma_Frontier_M204_Bellman_Certificates:
  COMMA_FRONTIER_M204_BELLMAN_CERTIFICATES =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Proposal = Comma_Frontier_M204_Bellman_Proposal
  structure Shift = Comma_CRT_MDD_Operation_Replay
  structure Bind = Comma_CRT_MDD_Bind_Replay
  structure Zip = Comma_Semantic_Future_Zip_Certificates
  type store = Store.store
  type result =
    {step_import_evals: thm list, shifts: thm list,
     comparisons: thm list, bind_certificates: thm list,
     d_covers: thm list, d_labels: int list}
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun replay step_source_store store (candidate: Proposal.result) : result =
    let
      val ctxt = Store.context store
      val _ = if length (#d_roots candidate)=46 andalso
          length (#step_roots candidate)=46 andalso length (#shifted candidate)=46 andalso
          length (#roots candidate)=46 andalso length (#bind_keys candidate)=46 then ()
        else error "M204 replay requires 46 complete operation rows"
      val shift_replay = Shift.make store
      val bind_replay = Bind.make store
      val equal = @{term "\<lambda>x::nat. \<lambda>y::nat. if x=y then (1::nat) else 0"}
      val plus9 = @{term "\<lambda>x::nat. \<lambda>y::nat. if x=y+9 then (1::nat) else 0"}
      fun leaf_rule operation x y z =
        let val prop = HOLogic.mk_Trueprop
          (HOLogic.mk_eq (operation $ nat x $ nat y,nat z))
        in Goal.prove ctxt [] [] prop (fn {context,...} => simp_tac context 1) end
      val equal_zip = Zip.make ctxt store store store equal (leaf_rule equal)
      val plus_zip = Zip.make ctxt store store store plus9 (leaf_rule plus9)
      val true_index = Store.boolean_index store (hd (#roots candidate))
      val _ = (case Store.node store true_index of Store.Leaf 1 => ()
        | _ => error "M204 import comparison requires the checked true leaf")
      fun authenticated_source_roots source_store source_handles
          (export: Comma_CRT_MDD_Arena.exported) =
        let
          val actual = map (Store.action_index source_store) source_handles
          val recorded = map (fn local_index =>
            List.nth (#source_indices export,local_index)) (#roots export)
          val _ = if actual=recorded then ()
            else error "M204 source transcript differs from authenticated source roots"
        in actual end
      val step_import_zip = Zip.make ctxt step_source_store store store equal (leaf_rule equal)
      val step_imports = ListPair.mapEq (fn (old,root) =>
        Zip.certify step_import_zip old (Store.action_index store root) true_index)
        (authenticated_source_roots step_source_store (#source_step_roots candidate)
          (#step_export candidate),#step_roots candidate)
      val source_ids = authenticated_source_roots step_source_store
        (#source_step_roots candidate) (#step_export candidate)
      val phase = Free ("m204_import_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val true_at = Thm.forall_elim phase_ct (Store.phase_leaf store true_index)
      val import_rule = Drule.infer_instantiate ctxt
        [(("phase",0),phase_ct)] @{thm comma_frontier_m204_import_equal}
      fun import_eval (cid,cert) =
        let
          val source = List.nth (source_ids,cid)
          val target = Store.action_index store (List.nth (#step_roots candidate,cid))
          val pointwise = import_rule OF [cert,Store.wellformed step_source_store,
            Store.wellformed store,Store.bound step_source_store source,
            Store.bound store target,true_at]
        in Thm.forall_intr phase_ct pointwise end
      val step_import_evals = map_index import_eval step_imports
      val d_labels = sort int_ord (fold (fn root => union (op =)
        (Comma_CRT_MDD_Arena.action_support (#arena candidate) root))
        (#d_roots candidate) [])
      val _ = if List.all (fn value => 0 <= value andalso value <= 242) d_labels
        then () else error "M204 support exceeds the admitted D bound"
      val d_covers = map (fn root => Bind.certify_cover bind_replay
        (Store.action_index store root) d_labels) (#d_roots candidate)
      val shifts = ListPair.mapEq (fn (root,shifted) =>
        Shift.certify_shift shift_replay 1
          (Store.action_index store root) (Store.action_index store shifted))
        (#d_roots candidate,#shifted candidate)
      fun comparison ({left,right,result,plus9,...}: Proposal.comparison) =
        Zip.certify (if plus9 then plus_zip else equal_zip) left right result
      val comparisons = map comparison (#comparisons candidate)
      val bind_certificates = map (Bind.certify_bind bind_replay) (#bind_keys candidate)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "M204 symbolic operation replay" (step_import_evals @ d_covers @ shifts @ comparisons @ bind_certificates)
    in {step_import_evals=step_import_evals,shifts=shifts,
      comparisons=comparisons,bind_certificates=bind_certificates,
      d_covers=d_covers,d_labels=d_labels} end
end
