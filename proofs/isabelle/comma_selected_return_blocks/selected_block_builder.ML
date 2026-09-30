structure Comma_Selected_Block_Builder =
struct
  fun make arithmetic certify =
    let
      val records = @{thms comma_selected_return_block.select_convs}
      val normalization = arithmetic addsimps
        (@{thms comma_selected_block_leaf_def comma_selected_block_then_def
          comma_selected_block_repeat_def} @ records)
        |> fold Simplifier.add_cong
          @{thms comma_selected_choice_join_opaque_cong
            comma_selected_choice_repeat_opaque_cong}
      val leaf_context = arithmetic delsimps
        @{thms comma_boundary_valid_def comma_total_children_def}
      fun leaf choice valid defined macro ordered target_valid sibling =
        let
          val rule = if choice then @{thm comma_selected_block_Z_certified}
            else @{thm comma_selected_block_N_certified}
          val prefix = (rule OF [valid,defined,macro])
            |> Simplifier.full_simplify leaf_context
          val facts = if choice then [ordered,target_valid,sibling]
            else [ordered,target_valid]
        in (prefix OF facts) |> Simplifier.simplify normalization |> certify end
      fun join left right =
        (@{thm comma_selected_block_then_certified} OF [left,right])
        |> Simplifier.full_simplify normalization |> certify
      fun reduce [theorem] = theorem
        | reduce [] = error "Cannot publish an empty selected-return block"
        | reduce theorems =
            let fun pairs (a::b::rest) = join a b :: pairs rest
                  | pairs rest = rest
            in reduce (pairs theorems) end
      fun observe block =
        (@{thm comma_selected_block_choice_path} OF [block])
        |> Simplifier.simplify (arithmetic addsimps
          (@{thms comma_selected_choice_word.simps append.simps} @ records)) |> certify
    in {leaf=leaf,join=join,reduce=reduce,observe=observe} end
end
