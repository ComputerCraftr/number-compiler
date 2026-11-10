(* Memoized semantic rank relation over issued shallow CRT nodes.  The caller
   supplies checked root/shift facts; this traversal produces one HOL relation
   theorem per distinct joint state and keeps the cofactor environment in its
   memo key.  Only the Continue-selected target is inspected. *)
structure Comma_Semantic_Phase_Class_Rank_Relation_Compiler =
struct
  structure Data = Comma_Semantic_Weighted_CRT_Data
  structure Shallow = Comma_Semantic_Weighted_CRT_Shallow_Certificate
  structure Candidate = Comma_Semantic_Phase_Class_Rank_Candidate
  structure Joint = Comma_Semantic_Phase_Class_Rank_Joint_Certifier
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport
  structure Memo = Table
  (
    type key = (Data.identity * Data.identity) * (int * int) list
    val ord = prod_ord (prod_ord Data.identity_ord Data.identity_ord)
      (list_ord (prod_ord int_ord int_ord))
  )
  structure Leaf_Memo = Table
  (
    type key = Data.identity * Data.identity
    val ord = prod_ord Data.identity_ord Data.identity_ord
  )
  structure Continue_Memo = Table
  (
    type key = (Data.identity * Data.identity) * Data.identity
    val ord = prod_ord (prod_ord Data.identity_ord Data.identity_ord)
      Data.identity_ord
  )

  val natT = @{typ nat}
  val rankT = @{typ "nat comma_semantic_weighted_crt_dag"}
  val optionRankT = Type (@{type_name option},[rankT])
  val raw = Const (@{const_name comma_weighted_crt_cofactor_all_raw},
    natT --> natT --> rankT --> HOLogic.mk_prodT (natT,rankT))
  val snd_raw = Const (@{const_name snd},
    HOLogic.mk_prodT (natT,rankT) --> rankT)
  val map_option_const = Const (@{const_name map_option},
    (rankT --> rankT) --> optionRankT --> optionRankT)

  fun nat n = HOLogic.mk_number natT n

  fun pull_successors axis slot successors =
    let
      val pull = Abs ("tree",rankT,
        snd_raw $ (raw $ nat axis $ nat slot $ Bound 0))
    in Abs ("child",natT,
      map_option_const $ pull $ (successors $ Bound 0)) end

  fun make ctxt arena successors
      {action_named,rank_named,action_shape,rank_shape,
       action_cofactor,rank_cofactor,target_view,leaf_equations,
       successor_shape} =
    let
      val memo = Unsynchronized.ref (Memo.empty: thm Memo.table)
      val terminal_templates = Unsynchronized.ref
        (Leaf_Memo.empty: thm Leaf_Memo.table)
      val continue_templates = Unsynchronized.ref
        (Continue_Memo.empty: thm Continue_Memo.table)
      val constructed = Unsynchronized.ref 0
      val leaf_visits = Unsynchronized.ref 0
      val branch_visits = Unsynchronized.ref 0
      val scoped = Transport.make_scoped_checker ctxt "joint_rank"
      val check = #check scoped

      fun terminal_or_selected action path =
        (case Data.view arena action of
          Data.View_Leaf {offset,payload} =>
            if offset<>0 then error "Rank relation action has a root weight"
            else (case Candidate.action_label payload of
              Candidate.Continue child =>
                (case Data.view arena (target_view path child) of
                  Data.View_Leaf {offset=0,...} => true
                | _ => false)
            | _ => true)
        | Data.View_Branch _ => false)

      fun rank_is_leaf rank =
        (case Data.view arena rank of
          Data.View_Leaf {offset=0,...} => true
        | _ => false)

      fun terminal_action action =
        (case Data.view arena action of
          Data.View_Leaf {offset=0,payload} =>
            (case Candidate.action_label payload of
              Candidate.Terminal => true | _ => false)
        | _ => false)

      fun terminal_proof action current
          (action_entry: Shallow.named_node)
          (rank_entry: Shallow.named_node) successors =
        let
          val key = (Data.identity arena action,Data.identity arena current)
          val template =
            (case Leaf_Memo.lookup (!terminal_templates) key of
              SOME theorem => theorem
            | NONE => Data.with_reservation arena (fn reservation =>
                let
                  val _ = Data.reserve_external arena reservation
                  val theorem = Joint.terminal_template check ctxt
                    {action= #term action_entry,current= #term rank_entry,
                     definitions=[#definition action_entry,
                       #definition rank_entry]}
                  val _ = Data.retain_external arena reservation 1
                  val _ = terminal_templates :=
                    Leaf_Memo.update (key,theorem) (!terminal_templates)
                in theorem end))
        in Joint.instantiate_terminal check ctxt template
          (#term action_entry) (#term rank_entry) successors end

      fun continue_proof path action current
          (action_entry: Shallow.named_node)
          (rank_entry: Shallow.named_node)
          successors child =
        let
          val target = target_view path child
          val target_entry = rank_named target
          val later =
            (case Data.view arena target of
              Data.View_Leaf {offset=0,payload} =>
                (case Candidate.rank_value payload of
                  SOME rank => rank
                | NONE => error "Continue target rank is unresolved")
            | _ => error "Continue target rank is not a leaf")
          val key = ((Data.identity arena action,
            Data.identity arena current),Data.identity arena target)
          val template =
            (case Continue_Memo.lookup (!continue_templates) key of
              SOME theorem => theorem
            | NONE => Data.with_reservation arena (fn reservation =>
                let
                  val _ = Data.reserve_external arena reservation
                  val theorem = Joint.continue_template check ctxt
                    {action= #term action_entry,current= #term rank_entry,
                     target= #term target_entry,child=child,later=later,
                     definitions=[#definition action_entry,
                       #definition rank_entry,#definition target_entry]}
                  val _ = Data.retain_external arena reservation 1
                  val _ = continue_templates :=
                    Continue_Memo.update (key,theorem) (!continue_templates)
                in theorem end))
        in Joint.instantiate_continue check ctxt template
          (#term action_entry) (#term rank_entry) successors
          (leaf_equations path action) end

      fun visit axis path action current successors =
        let
          val key = ((Data.identity arena action,Data.identity arena current),path)
        in
          (case Memo.lookup (!memo) key of
            SOME theorem => theorem
          | NONE => Data.with_reservation arena (fn reservation =>
              let
                val _ = Data.reserve_external arena reservation
                val _ = if axis=length path andalso axis<=4 then ()
                  else error "Rank relation cofactor environment is malformed"
                val action_entry: Shallow.named_node = action_named action
                val rank_entry: Shallow.named_node = rank_named current
                val theorem =
                  if terminal_or_selected action path andalso
                      rank_is_leaf current then
                    let
                      val _ = leaf_visits := !leaf_visits+1
                    in if terminal_action action then
                         terminal_proof action current action_entry
                           rank_entry successors
                       else (case Data.view arena action of
                         Data.View_Leaf {payload,...} =>
                           (case Candidate.action_label payload of
                             Candidate.Continue child =>
                               continue_proof path action current action_entry
                                 rank_entry successors child
                           | _ => error "Rank relation has an invalid action leaf")
                       | _ => error "Rank relation leaf changed shape") end
                  else if axis<4 then
                    let
                      val _ = branch_visits := !branch_visits+1
                      val radix = Data.axis_radix axis
                      fun child slot =
                        let
                          val action_result: Shallow.cofactor_result =
                            action_cofactor action axis slot
                          val rank_result: Shallow.cofactor_result =
                            rank_cofactor current axis slot
                          val next_path = path @ [(axis,slot)]
                          val next_successors =
                            pull_successors axis slot successors
                          val theorem = visit (axis+1) next_path
                            (#result action_result) (#result rank_result)
                            next_successors
                        in (theorem,[#equation action_result,
                          #equation rank_result]) end
                      val rows = map child (0 upto (radix-1))
                      val child_proofs = map #1 rows
                      val equations = maps #2 rows
                    in Joint.certify_from_cofactors check ctxt
                      {axis=axis,action= #term action_entry,
                       current= #term rank_entry,successors=successors,
                       action_shape=action_shape action axis,
                       current_shape=rank_shape current axis,
                       successor_shape=successor_shape path,
                       cofactor_equations=equations,
                       children=child_proofs} end
                  else error "Rank relation retained a nonleaf after four axes"
                val _ = Data.retain_external arena reservation 1
                val _ = memo := Memo.update (key,theorem) (!memo)
                val _ = constructed := !constructed+1
              in theorem end))
        end
    in
      {certify=fn action => fn current =>
         visit 0 [] action current successors,
       audit= #audit scoped,
       stats=fn () => {joint_proofs= !constructed,
         terminal_templates=Leaf_Memo.size (!terminal_templates),
         continue_templates=Continue_Memo.size (!continue_templates),
         leaf_visits= !leaf_visits,branch_visits= !branch_visits,
         proof_audit= #stats scoped ()}}
    end
end
