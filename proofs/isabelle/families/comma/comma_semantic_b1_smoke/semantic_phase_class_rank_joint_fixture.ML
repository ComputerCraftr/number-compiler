(* A data-only proof fixture.  It never publishes a source action or B32
   admission.  The four-slot branch tests chronological cofactor assembly. *)
structure Comma_Semantic_Phase_Class_Rank_Joint_Fixture =
struct
  structure Joint = Comma_Semantic_Phase_Class_Rank_Joint_Certifier
  structure Transport = Comma_Semantic_Weighted_CRT_Data_Transport

  val natT = @{typ nat}
  val actionT = Joint.actionT
  val rankT = Joint.rankT

  fun numeral n = HOLogic.mk_number natT n

  fun leaf payloadT value =
    Const (@{const_name Comma_Weighted_CRT_Leaf},
      payloadT --> Type (@{type_name comma_semantic_weighted_crt_dag},
        [payloadT])) $ value

  fun branch treeT children =
    let
      val edgeT = HOLogic.mk_prodT (natT,treeT)
      val rows = HOLogic.mk_list edgeT
        (map (fn child => HOLogic.mk_prod (numeral 0,child)) children)
    in Const (@{const_name Comma_Weighted_CRT_Branch},
      natT --> HOLogic.listT edgeT --> treeT) $ numeral 0 $ rows end

  fun cofactor_tree treeT tree slot =
    let
      val pairT = HOLogic.mk_prodT (natT,treeT)
      val raw = Const (@{const_name comma_weighted_crt_cofactor_all_raw},
        natT --> natT --> treeT --> pairT) $ numeral 0 $ numeral slot $ tree
    in Const (@{const_name snd},pairT --> treeT) $ raw end

  fun prove ctxt proposition rules =
    Goal.prove ctxt [] [] proposition
      (fn {context,...} =>
        HEADGOAL (simp_tac (Simplifier.add_simps rules context)))

  fun cofactor_equation ctxt treeT tree terminal slot =
    prove ctxt (HOLogic.mk_Trueprop
      (HOLogic.mk_eq (cofactor_tree treeT tree slot,terminal)))
      @{thms comma_weighted_crt_cofactor_all_raw.simps}

  fun shape_equation ctxt treeT tree =
    let
      val shape = Const (@{const_name comma_weighted_crt_shape},
        natT --> treeT --> HOLogic.boolT) $ numeral 0 $ tree
    in prove ctxt (HOLogic.mk_Trueprop shape)
      @{thms comma_weighted_crt_shape.simps comma_crt_axis_radix_def}
    end

  fun rejects operation =
    (case Exn.capture operation () of
      Exn.Exn (ERROR _) => ()
    | Exn.Exn failure => Exn.reraise failure
    | Exn.Res _ => error "A false synthetic rank relation was certified")

  fun run ctxt =
    let
      val scoped = Transport.make_scoped_checker ctxt "joint_fixture"
      val check = #check scoped
      val action_leaves = map
        (leaf @{typ comma_phase_rank_mask_action})
        [@{term "Comma_Phase_Rank_Mask_Fork 2 0"},
         @{term "Comma_Phase_Rank_Mask_Fork 3 0"},
         @{term "Comma_Phase_Rank_Mask_Fork 4 0"},
         @{term "Comma_Phase_Rank_Mask_Fork 5 0"}]
      val rank_leaf = leaf natT (numeral 0)
      val successors = Abs ("child",natT,
        Const (@{const_name None},Type (@{type_name option},[rankT])))
      val leaf_relations = map (fn action => Joint.certify_leaf check ctxt
        {action=action,current=rank_leaf,successors=successors,
         definitions=[]}) action_leaves
      val terminal_template = Joint.terminal_template check ctxt
        {action=hd action_leaves,current=rank_leaf,definitions=[]}
      val terminal_instance = Joint.instantiate_terminal check ctxt
        terminal_template (hd action_leaves) rank_leaf successors
      val _ = if List.all (fn theorem => Thm.nprems_of theorem=0)
          (terminal_instance :: leaf_relations) then ()
        else error "Synthetic terminal relation retained a premise"
      val _ = rejects (fn () => Joint.certify_leaf check ctxt
        {action=hd action_leaves,current=leaf natT (numeral 27),
         successors=successors,definitions=[]})
      val continue_action = leaf @{typ comma_phase_rank_mask_action}
        @{term "Comma_Phase_Rank_Mask_Continue 0"}
      val continue_rank = leaf natT (numeral 1)
      val optionRankT = Type (@{type_name option},[rankT])
      val if_option = Const (@{const_name If},HOLogic.boolT -->
        optionRankT --> optionRankT --> optionRankT)
      val eq_nat = Const (@{const_name HOL.eq},natT --> natT --> HOLogic.boolT)
      val selected_successors = Abs ("child",natT,
        if_option $ (eq_nat $ Bound 0 $ numeral 0) $
          (Const (@{const_name Some},rankT -->
            optionRankT) $ rank_leaf) $
          Const (@{const_name None},optionRankT))
      val selected_equation = prove ctxt (HOLogic.mk_Trueprop
        (HOLogic.mk_eq (selected_successors $ numeral 0,
          Const (@{const_name Some},rankT -->
            Type (@{type_name option},[rankT])) $ rank_leaf))) []
      val continue_template = Joint.continue_template check ctxt
        {action=continue_action,current=continue_rank,
         target=rank_leaf,child=0,later=0,definitions=[]}
      val continue_instance = Joint.instantiate_continue check ctxt
        continue_template continue_action continue_rank
        selected_successors [selected_equation]
      val _ = if Thm.nprems_of continue_instance=0 then ()
        else error "Synthetic Continue relation retained a premise"
      val _ = rejects (fn () => Joint.continue_template check ctxt
        {action=continue_action,current=rank_leaf,
         target=rank_leaf,child=0,later=0,definitions=[]})
      val action_branch = branch actionT action_leaves
      val rank_branch = branch rankT (replicate 4 rank_leaf)
      val shape_action = shape_equation ctxt actionT action_branch
      val shape_rank = shape_equation ctxt rankT rank_branch
      val child_var = Free ("child",natT)
      val target_var = Free ("target",rankT)
      val target_option = Const (@{const_name Some},rankT -->
        Type (@{type_name option},[rankT])) $ target_var
      val target_shape = Const (@{const_name comma_weighted_crt_shape},
        natT --> rankT --> HOLogic.boolT) $ numeral 0 $ target_var
      val no_successors = prove ctxt
        (HOLogic.mk_Trueprop (HOLogic.mk_all ("child",natT,
          HOLogic.mk_all ("target",rankT,
            HOLogic.mk_imp
              (HOLogic.mk_eq (successors $ child_var,target_option),
               target_shape))))) []
      val cases = maps (fn (slot,action_leaf) =>
        [cofactor_equation ctxt actionT action_branch action_leaf slot,
         cofactor_equation ctxt rankT rank_branch rank_leaf slot])
        (map_index I action_leaves)
      val branch_relation = Joint.certify_from_cofactors check ctxt
        {axis=0,action=action_branch,current=rank_branch,
         successors=successors,action_shape=shape_action,
         current_shape=shape_rank,successor_shape=no_successors,
         cofactor_equations=cases,children=leaf_relations}
      val _ = if Thm.nprems_of branch_relation=0 then ()
        else error "Synthetic branch relation retained a premise"
      val _ = #audit scoped "Synthetic joint rank relations"
        (branch_relation :: continue_instance :: terminal_instance ::
          leaf_relations)
    in () end
end
