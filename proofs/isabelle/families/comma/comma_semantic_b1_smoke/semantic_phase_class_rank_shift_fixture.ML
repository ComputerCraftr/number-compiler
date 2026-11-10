(* Bounded data-only phase-shift fixture with four distinct rank leaves. *)
structure Comma_Semantic_Phase_Class_Rank_Shift_Fixture =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Shift = Comma_Semantic_Phase_Class_Rank_Shift_Certificate

  val natT = @{typ nat}
  val rankT = @{typ "nat comma_semantic_weighted_crt_dag"}
  val edgeT = HOLogic.mk_prodT (natT,rankT)

  fun literal ctxt arena diagram =
    (case Data.view arena diagram of
      Data.View_Leaf {offset=0,payload={value,...}} =>
        Const (@{const_name Comma_Weighted_CRT_Leaf},natT --> rankT) $ value
    | Data.View_Branch {offset=0,axis,children} =>
        let
          val rows = map (fn (weight,child) =>
            HOLogic.mk_prod (HOLogic.mk_number natT weight,
              literal ctxt arena child)) children
        in Const (@{const_name Comma_Weighted_CRT_Branch},
          natT --> HOLogic.listT edgeT --> rankT) $
          HOLogic.mk_number natT axis $ HOLogic.mk_list edgeT rows end
    | _ => error "Rank shift fixture retained a physical weight")

  fun run ctxt =
    let
      val arena = Data.make_arena 128
      val leaves = map (fn n => Data.leaf arena
        {key="shift-fixture:" ^ Int.toString n,
         value=HOLogic.mk_number natT n}) [0,1,2,3]
      val source = Data.raw_branch_diagrams arena 0 leaves
      val target = Data.shift arena 1 source
      fun named diagram =
        let val term = literal ctxt arena diagram
        in {term=term,definition=Thm.reflexive (Thm.cterm_of ctxt term)} end
      val stats_before = Data.stats arena
      val certifier = Shift.make ctxt arena named
      val theorem = #certify certifier source target
      val again = #certify certifier source target
      val stats = #stats certifier ()
      val stats_after = Data.stats arena
      val _ = if Thm.prop_of theorem aconv Thm.prop_of again andalso
          #shift_proofs stats=5 andalso
          #serialization_node_visits stats_after =
            #serialization_node_visits stats_before then ()
        else error "Rank shift lost structural proof reuse or serialized data"
    in () end
end
