(* Kernel replay of the proposed source/class MDD comparisons.  Matching
   roots are useful only together with the separately proved source bindings. *)
structure Comma_Future_M204_Graph_Replay =
struct
  structure Store = Comma_CRT_MDD_Certificate_Store
  structure Arena = Comma_CRT_MDD_Arena
  structure Zip = Comma_Semantic_Future_Zip_Certificates
  structure Proposal = Comma_Future_M204_Graph_Proposal
  val natT = @{typ nat}
  fun nat n = HOLogic.mk_number natT n

  fun replay store rows row_selector row_count (candidate: Proposal.result) =
    let
      val ctxt = Store.context store
      val control = @{term "\<lambda>rows::comma_future_m204_row list. \<lambda>x::nat. \<lambda>y::nat.
        comma_future_m204_graph_control rows x"} $ rows
      val child_n = @{term "\<lambda>rows::comma_future_m204_row list. \<lambda>x::nat. \<lambda>y::nat.
        comma_future_m204_graph_child rows x 0"} $ rows
      val child_z = @{term "\<lambda>rows::comma_future_m204_row list. \<lambda>x::nat. \<lambda>y::nat.
        comma_future_m204_graph_child rows x 1"} $ rows
      val actual = @{term "\<lambda>x::nat. \<lambda>y::nat. if x=0 then 0 else (x-1) mod 9+1"}
      val class_bound = @{term "\<lambda>rows::comma_future_m204_row list. \<lambda>x::nat. \<lambda>y::nat.
        if x < length rows then (1::nat) else 0"} $ rows
      val equal = @{term "\<lambda>x::nat. \<lambda>y::nat. if x=y then (1::nat) else 0"}
      val scalar = Comma_Entry_Arithmetic.natural_context ctxt
        |> Simplifier.add_proc row_selector
        |> Simplifier.add_simps (row_count :: @{thms fst_conv snd_conv option.simps
             nth_Cons_0 nth_Cons_Suc list.size Let_def
             comma_future_m204_graph_control_def comma_future_m204_graph_child_def})
      fun leaf_rule operation x y z =
        Goal.prove ctxt [] [] (HOLogic.mk_Trueprop
          (HOLogic.mk_eq (operation $ nat x $ nat y,nat z)))
          (fn _ => simp_tac scalar 1)
      fun checker operation = Zip.make ctxt store store store operation (leaf_rule operation)
      val control_zip = checker control
      val n_zip = checker child_n
      val z_zip = checker child_z
      val actual_zip = checker actual
      val bound_zip = checker class_bound
      val equal_zip = checker equal
      fun certify ({operation,left,right,output}: Proposal.comparison) =
        Zip.certify (case operation of Proposal.Graph_Control => control_zip
          | Proposal.Graph_N => n_zip | Proposal.Graph_Z => z_zip
          | Proposal.Actual_Control => actual_zip | Proposal.Class_Bound => bound_zip
          | Proposal.Equal => equal_zip)
          left right output
      val comparisons = map certify (#comparisons candidate)
      val phase = Free ("future_graph_phase",natT)
      val phase_ct = Thm.cterm_of ctxt phase
      val phase_rule = Drule.infer_instantiate ctxt
        [(("phase",0),phase_ct)] @{thm comma_crt_mdd_zip_certificate_phase}
      val wf = Store.wellformed store
      val evaluations = map (fn certificate =>
        Thm.forall_intr phase_ct (phase_rule OF [certificate,wf,wf,wf])) comparisons
      fun checked_true root =
        let val id = Store.action_index store root
            val _ = (case Store.node store id of Store.Leaf 1 => ()
              | _ => error "Future graph equality root is not true")
        in Store.phase_leaf store id end
      val true_roots = map checked_true (#roots candidate @ #class_bounds candidate)
      val _ = Comma_Proof_Dependency_Audit.require_native_clean ctxt
        "Future M204 graph replay" (comparisons @ evaluations @ true_roots)
    in {comparisons=comparisons,evaluations=evaluations,true_roots=true_roots} end
end
