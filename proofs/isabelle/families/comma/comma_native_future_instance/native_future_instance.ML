structure Comma_Native_Future_Instance_Check =
struct
  fun context ctxt =
    let
      val shape = @{thm comma_native_rank_tables_full_shape}
      val shape_proposition = @{prop
        "comma_native_rank_table_full_shape comma_rank_codes_N \<and>
         comma_native_rank_table_full_shape comma_rank_codes_Z"}
      val _ = if Thm.prop_of shape aconv shape_proposition andalso
          Thm.nprems_of shape=0 andalso null (Thm.hyps_of shape) andalso
          null (Thm_Deps.all_oracles [shape])
        then () else error "Rank candidate table shapes are not kernel-checked"
      val (n_proc, _) = Comma_Future_Rank_Lookup.selected_table ctxt "N"
        @{thm comma_rank_codes_N_def}
      val (z_proc, _) = Comma_Future_Rank_Lookup.selected_table ctxt "Z"
        @{thm comma_rank_codes_Z_def}
      val (b32_proc, _) =
        Comma_Future_Rank_Lookup.selected_table_with_extents ctxt "B32"
          @{thm comma_checked_sparse_B32_rows_table_def}
          @{term "comma_checked_sparse_B32_rows_table ! i"} [46]
      val simp = @{thms comma_native_rank_table_code_def
        comma_native_rank_decode_def comma_native_rank_measure_def
        comma_native_rank_table_full_shape_def
        comma_native_rank_tables_full_shape
        comma_native_rank_row_checked_def comma_native_rank_check_def
        comma_native_B32_boundary_step_def comma_native_boundary_step_def
        comma_native_decade_summary_def comma_sparse_decade_summary_def
        comma_sparse_lookup.simps comma_native_boundary_children_def
        comma_native_outcome_delta_def comma_native_survivor_step_def
        comma_native_safe_run_execute.simps comma_native_safe_runs_execute.simps
        comma_nine_run_cycle_def comma_boundary_states_def
        comma_boundary_valid_def comma_boundary_kind.simps
        comma_boundary_states_set comma_decade_state.case
        comma_finite_outcome.case comma_word_result.case
        option.case option.map option.inject
        option.distinct prod.case if_True if_False Let_def
        comma_checked_sparse_B32_fiber_count
        comma_checked_sparse_B32_rows_at_valid
        comma_checked_sparse_B32_rows_valid
        comma_sparse_table_valid_def
        list_all_iff list_all_Nil_iff list_all_Cons_iff
        list.distinct list.inject list.map concat.simps append.simps
        replicate.simps nth_Cons' take.simps drop.simps]
    in
      ctxt
      |> Simplifier.add_proc n_proc
      |> Simplifier.add_proc z_proc
      |> Simplifier.add_proc b32_proc
      |> Simplifier.add_simps simp
    end

  fun exact_closed ctxt proposition theorem =
    if Thm.nprems_of theorem=0 andalso null (Thm.hyps_of theorem) andalso
        Thm.prop_of theorem aconv proposition andalso
        null (Thm_Deps.all_oracles [theorem])
    then theorem
    else error "Native finite checker did not prove the closed requested proposition"

  fun prove ctxt simpset proposition =
    let
      val theorem = Goal.prove ctxt [] [] proposition
        (fn _ => asm_full_simp_tac simpset 1)
    in exact_closed ctxt proposition theorem end

  fun publish_rank_check lthy =
    let
      val ctxt = Local_Theory.target_of lthy
      val simpset = context ctxt
      val rank_check = @{prop
        "(comma_native_rank_table_full_shape comma_rank_codes_N \<and>
          comma_native_rank_table_full_shape comma_rank_codes_Z) \<and>
          comma_native_rank_check comma_native_rank_measure
            comma_native_B32_boundary_step"}
      val entry = @{prop
        "comma_native_safe_runs_execute comma_native_B32_boundary_step
          comma_native_rank_measure [(False,1)] (Comma_N,2,10) =
          Some ((Comma_N,7,12),2)"}
      val cycle = @{prop
        "comma_native_safe_runs_execute comma_native_B32_boundary_step
          comma_native_rank_measure comma_nine_run_cycle
          (Comma_N,7,12) = Some ((Comma_N,7,12),924)"}
      val near = @{prop
        "comma_native_rank_measure (Comma_N,2,10)=None"}
      val zero = @{prop
        "comma_native_rank_measure (Comma_Z,2,10)=Some 7"}
      val checked = prove ctxt simpset rank_check
      val entry_checked = prove ctxt simpset entry
      val cycle_checked = prove ctxt simpset cycle
      val near_checked = prove ctxt simpset near
      val zero_checked = prove ctxt simpset zero
      val lthy = #2 (Local_Theory.note
        ((Binding.name "comma_native_rank_shape_and_check_checked", []), [checked]) lthy)
      val lthy = #2 (Local_Theory.note
        ((Binding.name "comma_native_run_entry_checked", []), [entry_checked]) lthy)
      val lthy = #2 (Local_Theory.note
        ((Binding.name "comma_native_run_cycle_checked", []), [cycle_checked]) lthy)
      val lthy = #2 (Local_Theory.note
        ((Binding.name "comma_native_near_child_unranked_checked", []), [near_checked]) lthy)
    in
      #2 (Local_Theory.note
        ((Binding.name "comma_native_zero_child_ranked_checked", []), [zero_checked]) lthy)
    end
end
