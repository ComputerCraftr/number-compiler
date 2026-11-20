theory Comma_Parametric_Typed_Entry
  imports Comma_Parametric_Entry_Closure
begin

lemma comma_frontier24_entry_closure_typed_rows:
  assumes certified: "comma_frontier24_closure_certified bundle"
    and closure_mem: "closure \<in> set (cf24_closures bundle)"
    and shape: "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program: "cf24_programs bundle ! cf24_closure_program_ref closure =
      Comma_Entry_Core_Program f d residue core"
    and child_exact:
      "\<And>child_index. child_index < closure_index \<Longrightarrow>
        comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
          (cf24_closure_output_root (cf24_closures bundle ! child_index)) =
        Some (child_code
          (cf24_programs bundle ! cf24_closure_program_ref
            (cf24_closures bundle ! child_index))
          (cf24_closure_full_shift (cf24_closures bundle ! child_index)))"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
      (cf24_closure_output_root closure) = Some
      (foldr (\<lambda>row tail.
        if comma_crt_eval (phase + cf24_closure_full_shift closure)
          (comma_core_value_guard core (cf24_closure_case_wanted row))
        then comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
          (cf24_action_tokens bundle ! cf24_closure_case_action_token row) child_code
        else tail) (cf24_closure_cases closure) 0)"
proof -
  let ?cases = "cf24_closure_cases closure"
  let ?pairs = "map (\<lambda>row. (cf24_closure_case_shifted_guard_root row,
    cf24_closure_case_action_output_root row)) ?cases"
  have table: "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    using certified by (rule comma_frontier24_closure_certifiedD(1))
  have shape_rows: "list_all (\<lambda>row.
      comma_frontier24_case_guard_imported bundle core
        (cf24_closure_case_wanted row) (cf24_closure_case_guard_root row) \<and>
      comma_frontier24_action_output_linked bundle closure_index closure
        (cf24_closure_case_action_token row) (cf24_closure_case_action_output_root row)
        (cf24_closure_case_child row)) ?cases"
    by (rule comma_frontier24_entry_closure_shapeD[OF shape program])
  have not_near: "cf24_closure_near_token closure=None"
    by (rule comma_frontier24_entry_closure_shapeD(3)[OF shape program])
  have priority: "comma_crt_mdd_multiway_certificate (cf24_radices bundle) (cf24_nodes bundle)
      ?pairs (cf24_zero_root bundle) (cf24_closure_output_root closure)"
    by (rule comma_frontier24_closure_multiway_certificate[OF certified closure_mem not_near])
  have zero: "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_zero_root bundle) = Some 0"
  proof -
    have leaf: "cf24_nodes bundle ! cf24_zero_root bundle = Comma_CRT_MDD_Leaf 0"
      and bound: "cf24_zero_root bundle < length (cf24_nodes bundle)"
      using certified by (auto simp: comma_frontier24_closure_certified_def
        comma_frontier24_closure_structure_checked_def)
    show ?thesis by (rule comma_crt_mdd_eval_phase_leaf[OF table bound leaf])
  qed
  have row_guard: "\<And>row. row\<in>set ?cases \<Longrightarrow>
    comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
      (cf24_closure_case_shifted_guard_root row) =
    Some (if comma_crt_eval (phase + cf24_closure_full_shift closure)
      (comma_core_value_guard core (cf24_closure_case_wanted row)) then 1 else 0)"
  proof -
    fix row assume member: "row\<in>set ?cases"
    have imported: "comma_frontier24_case_guard_imported bundle core
      (cf24_closure_case_wanted row) (cf24_closure_case_guard_root row)"
      using shape_rows member by (simp add: list_all_iff)
    show "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
      (cf24_closure_case_shifted_guard_root row) =
      Some (if comma_crt_eval (phase + cf24_closure_full_shift closure)
        (comma_core_value_guard core (cf24_closure_case_wanted row)) then 1 else 0)"
      by (rule comma_frontier24_closure_case_guard_value[OF certified closure_mem member imported])
  qed
  have row_action: "\<And>row. row\<in>set ?cases \<Longrightarrow>
    comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
      (cf24_closure_case_action_output_root row) =
    Some (comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
      (cf24_action_tokens bundle ! cf24_closure_case_action_token row) child_code)"
  proof -
    fix row assume member: "row\<in>set ?cases"
    have linked: "comma_frontier24_action_output_linked bundle closure_index closure
      (cf24_closure_case_action_token row) (cf24_closure_case_action_output_root row)
      (cf24_closure_case_child row)"
      using shape_rows member by (simp add: list_all_iff)
    show "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
      (cf24_closure_case_action_output_root row) =
      Some (comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
        (cf24_action_tokens bundle ! cf24_closure_case_action_token row) child_code)"
      using comma_frontier24_action_output_linked_typed[OF table linked child_exact] program
      by (simp add: comma_phase_program_sector.simps)
  qed
  have evaluate:
    "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
      (cf24_closure_output_root closure) =
     comma_crt_mdd_multiway_eval (cf24_radices bundle) (cf24_nodes bundle)
       (\<lambda>_. phase) ?pairs (cf24_zero_root bundle)"
    by (rule comma_crt_mdd_multiway_certificate_phase[OF priority table])
  have rows: "comma_crt_mdd_multiway_eval (cf24_radices bundle) (cf24_nodes bundle)
       (\<lambda>_. phase) ?pairs (cf24_zero_root bundle) = Some
      (foldr (\<lambda>row tail. if comma_crt_eval (phase + cf24_closure_full_shift closure)
          (comma_core_value_guard core (cf24_closure_case_wanted row))
        then comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
          (cf24_action_tokens bundle ! cf24_closure_case_action_token row) child_code
        else tail) ?cases 0)"
  proof -
    have eval: "\<And>root. comma_crt_mdd_eval (cf24_radices bundle) (cf24_nodes bundle)
      (\<lambda>_. phase) root = comma_crt_mdd_eval_phase (cf24_radices bundle)
        (cf24_nodes bundle) phase root"
      using table by (simp only: comma_crt_mdd_eval_phase_def comma_crt_mdd_eval_def if_True)
    have fold_rows:
      "foldr (\<lambda>row tail.
        case comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
          (cf24_closure_case_shifted_guard_root row) of
          None \<Rightarrow> None | Some g \<Rightarrow>
            (if g=1 then comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
              phase (cf24_closure_case_action_output_root row) else if g=0 then tail else None))
        xs (Some 0) = Some (foldr (\<lambda>row tail.
          if comma_crt_eval (phase+cf24_closure_full_shift closure)
            (comma_core_value_guard core (cf24_closure_case_wanted row))
          then comma_parametric_typed_action_code f (cf24_closure_full_shift closure)
            (cf24_action_tokens bundle ! cf24_closure_case_action_token row) child_code
          else tail) xs 0)" if "set xs \<subseteq> set ?cases" for xs
      using that
    proof (induction xs)
      case Nil
      then show ?case by simp
    next
      case (Cons row tail)
      have member: "row\<in>set ?cases" and subset: "set tail \<subseteq> set ?cases"
        using Cons.prems by auto
      show ?case using row_guard[OF member] row_action[OF member] Cons.IH[OF subset]
        by (simp split: if_splits)
    qed
    show ?thesis using fold_rows[of ?cases]
      by (simp only: comma_crt_mdd_multiway_eval_def foldr_map comp_def split_beta fst_conv snd_conv eval zero)

  qed
  show ?thesis using evaluate rows by simp

qed

lemma comma_parametric_typed_entry_fold_exact:
  assumes structural:
    "comma_phase_program_structurally_admitted
      (Comma_Entry_Core_Program f d residue core)"
  shows "foldr (\<lambda>wanted tail.
      if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
      then comma_parametric_typed_action_code f shift
        (comma_phase_program_entry_core_value_action f residue core wanted)
        (\<lambda>child child_shift. comma_parametric_typed_mask_code
          (comma_semantic_phase_program_fold comma_phase_program_full_action_output
            phase child child_shift))
      else tail) (comma_core_supported_values core) 0 =
    comma_parametric_typed_mask_code
      (comma_semantic_phase_program_fold comma_phase_program_full_action_output
        phase (Comma_Entry_Core_Program f d residue core) shift)"
proof -
  let ?program = "Comma_Entry_Core_Program f d residue core"
  obtain wanted where member: "wanted \<in> set (comma_core_supported_values core)"
    and active: "comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)"
    and unique: "\<forall>x\<in>set (comma_core_supported_values core).
      \<forall>y\<in>set (comma_core_supported_values core).
        comma_crt_eval (phase+shift) (comma_core_value_guard core x) \<longrightarrow>
        comma_crt_eval (phase+shift) (comma_core_value_guard core y) \<longrightarrow> x=y"
    and selected_step: "comma_phase_program_step_at ?program phase shift =
      comma_phase_program_step_of_action (comma_source_continuation_transport shift
        (comma_phase_program_entry_core_value_action f residue core wanted))"
    by (rule comma_entry_supported_selected_step[OF structural])
  have goto_bounds:
    "comma_phase_program_step_at ?program phase shift =
       Comma_Program_Goto child child_shift \<Longrightarrow>
      f<comma_phase_program_sector child \<and>
      comma_phase_program_sector child\<le>9"
    for child child_shift
  proof -
    assume goto:
      "comma_phase_program_step_at ?program phase shift =
         Comma_Program_Goto child child_shift"
    have bounds:
      "comma_phase_program_sector ?program <
          comma_phase_program_sector child \<and>
       comma_phase_program_sector child\<le>9"
      by (rule comma_phase_program_step_goto_sector_bounds[OF goto])
    show ?thesis using bounds by simp
  qed
  have goto_action:
    "\<And>source delta child.
      comma_phase_program_entry_core_value_action f residue core wanted =
        Comma_Continuation_Goto source delta \<Longrightarrow>
      comma_semantic_port_program_of_source source = Some child \<Longrightarrow>
      f < comma_phase_program_sector child \<and> comma_phase_program_sector child \<le> 9"
  proof -
    fix source delta child
    assume action: "comma_phase_program_entry_core_value_action f residue core wanted =
        Comma_Continuation_Goto source delta"
      and binding: "comma_semantic_port_program_of_source source = Some child"
    have step: "comma_phase_program_step_at ?program phase shift =
        Comma_Program_Goto child (shift+delta)"
      using selected_step action binding
      by (simp add: comma_source_continuation_transport.simps
        comma_phase_program_step_of_action.simps add.commute)
    show "f < comma_phase_program_sector child \<and> comma_phase_program_sector child \<le> 9"
      by (rule goto_bounds[OF step])
  qed
  have selected:
    "comma_parametric_typed_action_code f shift
        (comma_phase_program_entry_core_value_action f residue core wanted)
        (\<lambda>child child_shift. comma_parametric_typed_mask_code
          (comma_semantic_phase_program_fold comma_phase_program_full_action_output
            phase child child_shift)) =
      comma_parametric_typed_mask_code
        (comma_phase_program_full_action_of_source_action phase shift
          (comma_phase_program_entry_core_value_action f residue core wanted))"
    by (rule comma_parametric_typed_action_code_full_action[OF goto_action])
  have fold:
    "foldr (\<lambda>wanted tail.
      if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
      then comma_parametric_typed_action_code f shift
        (comma_phase_program_entry_core_value_action f residue core wanted)
        (\<lambda>child child_shift. comma_parametric_typed_mask_code
          (comma_semantic_phase_program_fold comma_phase_program_full_action_output
            phase child child_shift))
      else tail) (comma_core_supported_values core) 0 =
      comma_parametric_typed_action_code f shift
        (comma_phase_program_entry_core_value_action f residue core wanted)
        (\<lambda>child child_shift. comma_parametric_typed_mask_code
          (comma_semantic_phase_program_fold comma_phase_program_full_action_output
            phase child child_shift))"
    by (rule comma_list_guarded_value_fold_selected[OF unique member active])
  have action_step:
    "comma_phase_program_full_action_of_source_action phase shift
        (comma_phase_program_entry_core_value_action f residue core wanted) =
      comma_semantic_phase_program_fold comma_phase_program_full_action_output
        phase ?program shift"
    using comma_phase_program_full_action_source_step[of phase shift
        "comma_phase_program_entry_core_value_action f residue core wanted"]
      comma_phase_program_full_action_fold_step[of phase ?program shift]
      selected_step by simp
  show ?thesis using fold selected action_step by simp
qed

lemma comma_frontier24_entry_closure_typed_exact:
  assumes certified: "comma_frontier24_closure_certified bundle"
    and closure_mem: "closure \<in> set (cf24_closures bundle)"
    and shape: "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program: "cf24_programs bundle ! cf24_closure_program_ref closure =
      Comma_Entry_Core_Program f d residue core"
    and child_exact:
      "\<And>child_index. child_index < closure_index \<Longrightarrow>
        comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
          (cf24_closure_output_root (cf24_closures bundle ! child_index)) =
        Some (comma_parametric_typed_mask_code
          (comma_semantic_phase_program_fold comma_phase_program_full_action_output phase
            (cf24_programs bundle ! cf24_closure_program_ref
              (cf24_closures bundle ! child_index))
            (cf24_closure_full_shift (cf24_closures bundle ! child_index))))"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
      (cf24_closure_output_root closure) =
    Some (comma_parametric_typed_mask_code
      (comma_semantic_phase_program_fold comma_phase_program_full_action_output phase
        (cf24_programs bundle ! cf24_closure_program_ref closure)
        (cf24_closure_full_shift closure)))"
proof -
  have index: "cf24_closure_program_ref closure < length (cf24_programs bundle)"
    using shape by (auto simp: comma_frontier24_closure_shape_checked_def)
  have program_member: "cf24_programs bundle ! cf24_closure_program_ref closure
      \<in> set (cf24_programs bundle)"
    by (rule nth_mem[OF index])
  have structural: "comma_phase_program_structurally_admitted
      (Comma_Entry_Core_Program f d residue core)"
    using certified program_member program
    by (auto simp: comma_frontier24_closure_certified_def
      comma_frontier24_closure_structure_checked_def list_all_iff)
  note rows = comma_frontier24_entry_closure_typed_rows
    [OF certified closure_mem shape program child_exact]
  note row_fold = comma_frontier24_entry_rows_typed_fold[OF shape program,
    where phase=phase and child_code="\<lambda>child child_shift.
      comma_parametric_typed_mask_code
        (comma_semantic_phase_program_fold comma_phase_program_full_action_output
          phase child child_shift)"]
  note source_fold = comma_parametric_typed_entry_fold_exact[OF structural,
    where phase=phase and shift="cf24_closure_full_shift closure"]
  show ?thesis using rows row_fold source_fold program by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Authenticated typed Entry selection"
    @{thms comma_frontier24_entry_closure_typed_rows comma_parametric_typed_entry_fold_exact
      comma_frontier24_entry_closure_typed_exact};
\<close>

end
