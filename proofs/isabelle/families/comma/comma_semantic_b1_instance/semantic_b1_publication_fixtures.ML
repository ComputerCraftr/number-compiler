(* Selected-list and publication-serialization boundary fixtures. *)
structure Comma_Semantic_B1_Publication_Fixtures =
struct
  fun check_selected_list ctxt =
    let
      fun make_selector name table pattern extents =
        let
          val selector = Comma_Selected_List_Conversion.make
            {ctxt = ctxt, name = name,
             root_definition = Thm.reflexive (Thm.cterm_of ctxt table),
             table_pattern = pattern, extents = extents}
          val context = put_simpset HOL_basic_ss ctxt
            |> Simplifier.add_proc (#procedure selector)
        in fn term => Simplifier.rewrite context (Thm.cterm_of ctxt term) end
      val nested_table = @{term "[[0,1,2,3]::nat list, [1], [2]]"}
      val nested_select = make_selector "nested_extent_regression" nested_table
        @{term "([[0,1,2,3]::nat list, [1], [2]]) ! row ! slot"} [2, 3]
      val valid_nested = nested_select
        @{term "([[0,1,2,3]::nat list, [1], [2]]) ! 1 ! 0"}
      val _ = if Thm.term_of (Thm.rhs_of valid_nested) aconv @{term "1::nat"}
        then () else error "Selected-list nested selector failed on an admitted row"
      val rejected_parent = Exn.capture nested_select
        @{term "([[0,1,2,3]::nat list, [1], [2]]) ! 2 ! 0"}
      val rejected_slot = Exn.capture nested_select
        @{term "([[0,1,2,3]::nat list, [1], [2]]) ! 0 ! 3"}
      val three_table = @{term "[0::nat, 1, 2]"}
      val select_three = make_selector "selected_suffix_index_two" three_table
        @{term "[0::nat, 1, 2] ! index"} [3]
      val selected_two = select_three @{term "[0::nat, 1, 2] ! 2"}
      val _ = if Thm.term_of (Thm.rhs_of selected_two) aconv @{term "2::nat"}
        then () else error "Selected-list suffix regression failed at index 2"
      val unoverloaded_zero = Thm.term_of (Thm.rhs_of
        (Axclass.unoverload_conv ctxt
          (Thm.cterm_of ctxt @{term "0::nat"})))
      val unoverloaded_nth = Const (@{const_name nth},
        fastype_of three_table --> @{typ nat} --> @{typ nat}) $
          three_table $ unoverloaded_zero
      val selected_unoverloaded = select_three unoverloaded_nth
      val _ = if Thm.term_of (Thm.rhs_of selected_unoverloaded) aconv @{term "0::nat"}
        then () else error "Selected-list failed to normalize an unoverloaded index"
      val four_table = @{term "[0::nat, 1, 2, 3]"}
      val select_four = make_selector "selected_suffix_index_three" four_table
        @{term "[0::nat, 1, 2, 3] ! index"} [4]
      val selected_three = select_four @{term "[0::nat, 1, 2, 3] ! 3"}
      val _ = if Thm.term_of (Thm.rhs_of selected_three) aconv @{term "3::nat"}
        then () else error "Selected-list suffix regression failed at index 3"
      val length_table = @{term "[[0::nat,1,2], [3,4,5]]"}
      val length_select = make_selector "opaque_head_length" length_table
        @{term "[[0::nat,1,2], [3,4,5]] ! index"} [2]
      val selected_length = length_select @{term "length [[0::nat,1,2], [3,4,5]]"}
      val _ = if Thm.term_of (Thm.rhs_of selected_length) aconv @{term "2::nat"}
        then () else error "Selected-list outer-spine length regression failed"
      fun check_rejected label result =
        (case result of
          Exn.Exn (ERROR message) =>
            if message = "Selected-list nested index exceeds its depth-specific extent"
            then () else error message
        | Exn.Exn exn => Exn.reraise exn
        | Exn.Res _ => error ("Nested selected-list admitted an out-of-extent " ^ label))
    in
      check_rejected "parent" rejected_parent;
      check_rejected "slot" rejected_slot
    end

  fun check_lift_serialization ctxt encoded_refs encoded_descriptors =
    let
      val expected_refs = @{term
        "[[Comma_B1_Lift_Terminal_Ref 2 7, Comma_B1_Lift_Goto_Ref 3 17 4]]"}
      val wrong_lift = @{term
        "[[Comma_B1_Lift_Terminal_Ref 2 7, Comma_B1_Lift_Goto_Ref 3 17 5]]"}
      val expected_descriptors = @{term
        "([\<lparr>comma_semantic_b1_crt_lift_descriptor_period = 4,
           comma_semantic_b1_crt_lift_descriptor_slot = 3,
           comma_semantic_b1_crt_lift_descriptor_template_cid = 9,
           comma_semantic_b1_crt_lift_descriptor_net_shift = 17\<rparr>]
          :: comma_semantic_b1_crt_lift_descriptor list)"}
      fun prove proposition = Goal.prove ctxt [] [] proposition
        (fn {context, ...} => Simplifier.simp_tac
          (context addsimps [@{thm comma_semantic_b1_crt_lift_descriptor.make_def}]) 1)
      val serialized_refs = prove (HOLogic.mk_Trueprop
        (HOLogic.mk_eq (encoded_refs, expected_refs)))
      val wrong_lift_rejected = prove (HOLogic.mk_Trueprop
        (HOLogic.mk_not (HOLogic.mk_eq (encoded_refs, wrong_lift))))
      val serialized_descriptors = prove (HOLogic.mk_Trueprop
        (HOLogic.mk_eq (encoded_descriptors, expected_descriptors)))
    in
      Thm.consolidate [serialized_refs, wrong_lift_rejected, serialized_descriptors]
    end
end
