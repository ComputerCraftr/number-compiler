(* Kernel replay of the proposed future join operations.  This is not a
   source-to-class theorem: its component proofs must still be assembled with
   the physical-source and class-row authorities. *)
structure Comma_Future_M204_Join_Replay =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Shift = Comma_CRT_MDD_Operation_Replay
  structure Bind = Comma_CRT_MDD_Bind_Replay
  structure Zip = Comma_Semantic_Future_Zip_Certificates
  structure Proposal = Comma_Future_M204_Join_Proposal
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun replay source_store weight_store store
      source_ids weight_ids (candidate: Proposal.result) =
    let
      val ctxt = Store.context store
      val arena = #arena candidate
      fun ai root = Store.action_index store root
      val shift = Shift.make_periodic store
      val bind = Bind.make store
      val equality = @{term "\<lambda>x::nat. \<lambda>y::nat. if x=y then (1::nat) else 0"}
      fun rule opterm x y z =
        Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
          (HOLogic.mk_eq (opterm $ nat x $ nat y,nat z)))
          (fn {context,...} => simp_tac context 1)
      val true_id = Store.boolean_index store (Arena.boolean_true arena)
      val false_id = Store.boolean_index store (Arena.boolean_false arena)
      val _ = (case (Store.node store true_id,Store.node store false_id) of
          (Store.Leaf 1,Store.Leaf 0) => ()
        | _ => error "Future join lacks authenticated Boolean terminals")
      fun imports source_store actual (export: Arena.exported) roots =
        let
          val recorded = map (fn i => List.nth (#source_indices export,i)) (#roots export)
          val _ = if actual=recorded andalso length actual=length roots then ()
            else error "Future join imported roots do not match their source store"
          val zip = Zip.make ctxt source_store store store equality (rule equality)
        in ListPair.mapEq (fn (old,root) => Zip.certify zip old (ai root) true_id)
          (actual,roots) end
      val source_imports = imports source_store source_ids (#source_export candidate) (#sources candidate)
      val weight_imports = imports weight_store weight_ids (#weight_export candidate) (#weights candidate)
      val import_phase = Free ("future_join_import_phase",natT)
      val import_phase_ct = Thm.cterm_of ctxt import_phase
      val import_rule = Drule.infer_instantiate ctxt [(("phase",0),import_phase_ct)]
        @{thm comma_frontier_m204_import_equal}
      val true_at = Thm.forall_elim import_phase_ct (Store.phase_leaf store true_id)
      fun import_evals source_store source_ids roots certificates =
        map (fn ((old,root),certificate) =>
          Thm.forall_intr import_phase_ct
            (import_rule OF [certificate,Store.wellformed source_store,Store.wellformed store,
              Store.bound source_store old,Store.bound store (ai root),true_at]))
          (ListPair.zip (ListPair.zip (source_ids,roots),certificates))
      val source_import_evals = import_evals source_store source_ids (#sources candidate) source_imports
      val weight_import_evals = import_evals weight_store weight_ids (#weights candidate) weight_imports
      val future_plus_ten = @{term "\<lambda>x::nat. x+10"}
      fun mapped_leaf source target =
        Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
          (HOLogic.mk_eq (Envir.beta_norm (future_plus_ten $ nat source), nat target)))
          (fn {context,...} => simp_tac (Comma_Entry_Arithmetic.natural_context context) 1)
      val mapped_shift = Shift.make_mapped_on shift future_plus_ten mapped_leaf
      val mapped_weights = map (fn ({source,output,amount,add}: Proposal.mapped_weight) =>
        if amount=1 andalso add=10 then
          Shift.certify_mapped_shift mapped_shift amount source output
        else error "Future mapped weight changed its phase or +10 encoding")
        (#mapped_weights candidate)
      val mapped_weight_evals = map (fn ({source,output,amount,add}: Proposal.mapped_weight) =>
        if amount=1 andalso add=10 then
          Shift.mapped_shift_eval_phase mapped_shift amount source output
        else error "Future mapped weight has a noncanonical operation")
        (#mapped_weights candidate)
      val shifts = map (fn ({source,amount,output}: Proposal.shift) =>
        Shift.certify_shift shift amount source output) (#shifts candidate)
      val shift_evals = map (fn ({source,amount,output}: Proposal.shift) =>
        Shift.shift_eval_phase shift amount source output) (#shifts candidate)
      fun add_operation n = Abs ("x",natT,Abs ("y",natT,
        Const (@{const_name plus},natT --> natT --> natT) $ Bound 1 $ nat n))
      val add_one = add_operation 1
      val add_ten = add_operation 10
      val one_checker = Zip.make ctxt store store store add_one (rule add_one)
      val ten_checker = Zip.make ctxt store store store add_ten (rule add_ten)
      fun zipped ({left,right,output,add}: Proposal.zip) =
        let val checker = if add=1 then one_checker else if add=10 then ten_checker
              else error "Future join has an unsupported arithmetic zip"
        in Zip.certify checker left right output end
      val zips = map zipped (#zips candidate)
      val phase = Free ("future_join_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val zip_rule = Drule.infer_instantiate ctxt [(("phase",0),phase_ct)]
        @{thm comma_crt_mdd_zip_certificate_phase}
      val wf = Store.wellformed store
      val zip_evals = map (fn certificate =>
        Thm.forall_intr phase_ct (zip_rule OF [certificate,wf,wf,wf])) zips
      fun checked_bind key output =
        let val witness = Arena.bind_witness arena key
            val _ = if #result witness = output then ()
              else error "Future join bind transcript has the wrong output"
        in Bind.certify_bind bind key end
      val masks = map (fn ({source,label,output}: Proposal.mask) =>
        checked_bind (source,false_id,[(label,true_id)]) output) (#masks candidate)
      val selections = map (fn ({guard,yes,no,output}: Proposal.selection) =>
        checked_bind (guard,no,[(0,no),(1,yes)]) output) (#selections candidate)
      val mask_evals = map (fn ({source,label,...}: Proposal.mask) =>
        Bind.bind_eval_phase bind (source,false_id,[(label,true_id)])) (#masks candidate)
      val selection_evals = map (fn ({guard,yes,no,...}: Proposal.selection) =>
        Bind.bind_eval_phase bind (guard,no,[(0,no),(1,yes)])) (#selections candidate)
      val cover_cache = Unsynchronized.ref Inttab.empty
      fun support root =
        let val id = ai root
        in case Inttab.lookup (!cover_cache) id of SOME theorem => theorem
          | NONE => let
              val theorem = Bind.certify_cover bind id (Arena.action_support arena root)
              val _ = cover_cache := Inttab.update (id,theorem) (!cover_cache)
            in theorem end
        end
      val source_covers = map support (#sources candidate)
      val output_covers = map support (#outputs candidate)
      val facts = source_imports @ source_import_evals @ weight_imports @ weight_import_evals @
        mapped_weights @ mapped_weight_evals @ shifts @ shift_evals @ zips @ zip_evals @
        masks @ mask_evals @ selections @ selection_evals @ source_covers @ output_covers
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Future M204 join operation replay" facts
    in {source_imports=source_imports,source_import_evals=source_import_evals,
      weight_imports=weight_imports,weight_import_evals=weight_import_evals,
      shifts=shifts,shift_evals=shift_evals,zips=zips,zip_evals=zip_evals,
      mapped_weights=mapped_weights,mapped_weight_evals=mapped_weight_evals,
      masks=masks,mask_evals=mask_evals,selections=selections,
      selection_evals=selection_evals,source_covers=source_covers,
      output_covers=output_covers} end
end
