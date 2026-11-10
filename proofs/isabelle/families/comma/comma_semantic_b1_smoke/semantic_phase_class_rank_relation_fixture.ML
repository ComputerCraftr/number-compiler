(* Data-only test of the memoized relation compiler.  This deliberately has
   no source class or admission theorem. *)
structure Comma_Semantic_Phase_Class_Rank_Relation_Fixture =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Shallow = Comma_Semantic_Weighted_CRT_Shallow_Certificate
  structure Compiler = Comma_Semantic_Phase_Class_Rank_Relation_Compiler

  fun rejects operation =
    (case Exn.capture operation () of
      Exn.Exn (ERROR _) => ()
    | Exn.Exn failure => Exn.reraise failure
    | Exn.Res _ => error "A false whole-root rank relation was certified")

  fun literal_named ctxt arena payloadT diagram =
    let
      val view = Data.view arena diagram
      val treeT = Type (@{type_name comma_semantic_weighted_crt_dag},[payloadT])
      val term = (case view of
        Data.View_Leaf {offset=0,payload={value,...}} =>
          Const (@{const_name Comma_Weighted_CRT_Leaf},payloadT --> treeT) $ value
      | _ => error "Terminal relation fixture changed its leaf schema")
    in SOME {term=term,definition=Thm.reflexive (Thm.cterm_of ctxt term)} end

  fun run ctxt =
    let
      val arena = Data.make_arena 128
      val action = Data.leaf arena
        {key="relation-fixture:fork",value = @{term "Comma_Phase_Rank_Mask_Fork 2 0"}}
      val rank = Data.leaf arena {key="relation-fixture:rank0",
        value = @{term "0::nat"}}
      val bad_rank = Data.leaf arena {key="relation-fixture:rank27",
        value = @{term "27::nat"}}
      val action_cert = Shallow.make ctxt arena
        @{typ comma_phase_rank_mask_action}
        {lookup=literal_named ctxt arena @{typ comma_phase_rank_mask_action},
         ensure_named=NONE}
      val rank_cert = Shallow.make ctxt arena @{typ nat}
        {lookup=literal_named ctxt arena @{typ nat},ensure_named=NONE}
      val rankT = @{typ "nat comma_semantic_weighted_crt_dag"}
      val successors = Abs ("child",@{typ nat},
        Const (@{const_name None},Type (@{type_name option},[rankT])))
      val certifier = Compiler.make ctxt arena successors
        {action_named= #named action_cert,rank_named= #named rank_cert,
         action_shape= #shape action_cert,rank_shape= #shape rank_cert,
         action_cofactor= #cofactor action_cert,
         rank_cofactor= #cofactor rank_cert,
         target_view=fn _ => fn _ => error "Terminal action requested a successor",
         leaf_equations=fn _ => fn _ => [],
         successor_shape=fn _ => error "Terminal action requested a shape"}
      val first = #certify certifier action rank
      val second = #certify certifier action rank
      val stats = #stats certifier ()
      val _ = if Thm.prop_of first aconv Thm.prop_of second andalso
          #joint_proofs stats=1 andalso #terminal_templates stats=1 andalso
          #branch_visits stats=0 then ()
        else error "Terminal relation did not reuse its checked ProofID"
      val _ = rejects (fn () => #certify certifier action bad_rank)
    in () end
end
