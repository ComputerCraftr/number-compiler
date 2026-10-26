(* Pure term and proof assembly for one postorder graph node.  The weighted
   DAG owner retains the graph, node table, normalized-child table, and budget. *)
structure Comma_Semantic_Weighted_CRT_Local_Node_Compiler =
struct
  fun action_function nat natT invalid_action children_of action_of_cid cid =
    let
      val child = Free ("child_cid",natT)
      val actionT = fastype_of invalid_action
      val conditional = Const (@{const_name If},
        HOLogic.boolT --> actionT --> actionT --> actionT)
      val body = fold_rev (fn child_cid => fn fallback =>
        conditional $ HOLogic.mk_eq (child,nat child_cid) $
          action_of_cid child_cid $ fallback)
          (distinct (op =) (children_of cid)) invalid_action
    in Term.lambda child body end

  fun local_actions compiler_const nodes_term nat natT invalid_action
      lookup_node goto_children action_of_cid graph cids =
    let
      fun children_of cid =
        (case lookup_node graph cid of
          NONE => error "Weighted CRT compiler graph node disappeared"
        | SOME node => goto_children node)
    in map (fn cid => (cid,
      compiler_const $ nodes_term $ nat cid $
        action_function nat natT invalid_action children_of action_of_cid cid)) cids
    end

  val local_rules = @{thms
    comma_semantic_b1_crt_compile_node_from_children_def
    comma_semantic_b1_crt_leaf_def
    comma_semantic_b1_crt_invalid_action_def
    comma_weighted_crt_selector_aux.simps
    comma_weighted_crt_bind.simps
    comma_semantic_b1_node.select_convs
    fst_conv snd_conv list.map nth_Cons_0 nth_Cons_Suc nth_Cons' upt_rec}

  fun certify_local_actions compiler_rules checked_expression cid_of raw_of
      builds actions =
    if length builds <> length actions then
      error "Postorder compiler terms and node records differ in length"
    else map (fn (build,(cid,expected)) =>
      if cid_of build = cid then
        checked_expression (raw_of build) expected (compiler_rules @ local_rules)
      else error "Postorder compiler terms changed CID order")
      (ListPair.zip (builds,actions))
end
