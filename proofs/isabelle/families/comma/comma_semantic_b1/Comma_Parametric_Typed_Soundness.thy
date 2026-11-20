theory Comma_Parametric_Typed_Soundness
  imports Comma_Parametric_Typed_Entry
    Comma_Program_Continue_Guard_Exact Comma_Frontier_M204_Generic
begin

lemma comma_frontier24_near_closure_typed_exact:
  assumes certified: "comma_frontier24_closure_certified bundle"
    and closure_mem: "closure \<in> set (cf24_closures bundle)"
    and shape: "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program: "cf24_programs bundle ! cf24_closure_program_ref closure = program"
    and near_program:
      "case program of Comma_Near_Residual_Program f d residual \<Rightarrow> True
       | Comma_Near_Boundary_Program f \<Rightarrow> True | _ \<Rightarrow> False"
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
  obtain token where selector:
      "cf24_selectors bundle ! cf24_closure_program_ref closure =
        Comma_Frontier24_Near_Selector token"
    and token: "cf24_closure_near_token closure = Some token"
    using shape program near_program
    by (cases "cf24_selectors bundle ! cf24_closure_program_ref closure")
      (auto simp: comma_frontier24_closure_shape_checked_def
        comma_frontier24_selector_recipe_matches_def
        split: comma_semantic_port_program.splits)
  obtain action_root where action_root:
      "cf24_closure_near_action_output_root closure = Some action_root"
      "cf24_closure_output_root closure = action_root"
    using shape program selector token near_program
    by (cases "cf24_closure_near_action_output_root closure")
      (auto simp: comma_frontier24_closure_shape_checked_def
        split: comma_semantic_port_program.splits
          comma_frontier24_selector_recipe.splits option.splits)
  have linked:
    "comma_frontier24_action_output_linked bundle closure_index closure
      token action_root (cf24_closure_near_child closure)"
    using shape program selector token action_root(1) near_program
    by (auto simp: comma_frontier24_closure_shape_checked_def
      split: comma_semantic_port_program.splits
        comma_frontier24_selector_recipe.splits option.splits)
  have table:
    "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
    using certified by (rule comma_frontier24_closure_certifiedD(1))
  have token_exact:
    "cf24_action_tokens bundle ! token =
      comma_phase_program_operator_nf program 0"
    using shape program selector token near_program
    by (auto simp: comma_frontier24_closure_shape_checked_def
      comma_frontier24_selector_recipe_matches_def
      split: comma_semantic_port_program.splits
        comma_frontier24_selector_recipe.splits)
  have program_index:
    "cf24_closure_program_ref closure < length (cf24_programs bundle)"
    using shape by (auto simp: comma_frontier24_closure_shape_checked_def)
  have program_member: "cf24_programs bundle ! cf24_closure_program_ref closure
      \<in> set (cf24_programs bundle)"
    by (rule nth_mem[OF program_index])
  have structural:
    "comma_phase_program_structurally_admitted program"
    using certified program_member program
    by (auto simp: comma_frontier24_closure_certified_def
      comma_frontier24_closure_structure_checked_def list_all_iff)
  have step:
    "comma_phase_program_step_at program phase
        (cf24_closure_full_shift closure) =
      comma_phase_program_step_of_action
        (comma_source_continuation_transport
          (cf24_closure_full_shift closure)
          (cf24_action_tokens bundle ! token))"
    using structural token_exact near_program
    by (cases program)
      (auto simp: comma_phase_continue_near_residual_step_action
        comma_phase_continue_near_boundary_step_action)
  have goto_bounds:
    "\<And>child child_shift.
      comma_phase_program_step_at program phase
        (cf24_closure_full_shift closure) =
        Comma_Program_Goto child child_shift \<Longrightarrow>
      comma_phase_program_sector program <
        comma_phase_program_sector child \<and>
      comma_phase_program_sector child \<le> 9"
    by (rule comma_phase_program_step_goto_sector_bounds)
  have goto_action:
    "\<And>source delta child.
      cf24_action_tokens bundle ! token = Comma_Continuation_Goto source delta \<Longrightarrow>
      comma_semantic_port_program_of_source source = Some child \<Longrightarrow>
      comma_phase_program_sector program < comma_phase_program_sector child \<and>
        comma_phase_program_sector child \<le> 9"
  proof -
    fix source delta child
    assume action: "cf24_action_tokens bundle ! token = Comma_Continuation_Goto source delta"
      and binding: "comma_semantic_port_program_of_source source = Some child"
    have action_step: "comma_phase_program_step_at program phase (cf24_closure_full_shift closure) =
        Comma_Program_Goto child (cf24_closure_full_shift closure + delta)"
      using step action binding
      by (simp add: comma_source_continuation_transport.simps
        comma_phase_program_step_of_action.simps add.commute)
    show "comma_phase_program_sector program < comma_phase_program_sector child \<and>
        comma_phase_program_sector child \<le> 9"
      by (rule goto_bounds[OF action_step])
  qed
  note linked_output = comma_frontier24_action_output_linked_typed
    [OF table linked child_exact]
  note typed_code_fact = comma_parametric_typed_action_code_full_action[OF goto_action, where phase=phase]
  have action_step:
    "comma_phase_program_full_action_of_source_action phase (cf24_closure_full_shift closure)
        (cf24_action_tokens bundle ! token) =
      comma_semantic_phase_program_fold comma_phase_program_full_action_output phase
        program (cf24_closure_full_shift closure)"
    using comma_phase_program_full_action_source_step[of phase "cf24_closure_full_shift closure"
        "cf24_action_tokens bundle ! token"]
      comma_phase_program_full_action_fold_step[of phase program "cf24_closure_full_shift closure"]
      step by simp
  show ?thesis using linked_output typed_code_fact action_step action_root(2) program by simp
qed

lemma comma_frontier24_closures_typed_exact:
  assumes certified: "comma_frontier24_closure_certified bundle"
    and bound: "i < length (cf24_closures bundle)"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
      (cf24_closure_output_root (cf24_closures bundle ! i)) =
    Some (comma_parametric_typed_mask_code
      (comma_semantic_phase_program_fold comma_phase_program_full_action_output phase
        (cf24_programs bundle ! cf24_closure_program_ref (cf24_closures bundle ! i))
        (cf24_closure_full_shift (cf24_closures bundle ! i))))"
  using bound
proof (induction i arbitrary: phase rule: less_induct)
  case (less i)
  let ?closure = "cf24_closures bundle ! i"
  let ?program = "cf24_programs bundle ! cf24_closure_program_ref ?closure"
  have structural: "comma_frontier24_closure_structure_checked bundle"
    using certified by (rule comma_frontier24_closure_certifiedD(2))
  have member: "?closure \<in> set (cf24_closures bundle)"
    using less.prems by (rule nth_mem)
  have shape: "comma_frontier24_closure_shape_checked bundle (i,?closure)"
    by (rule comma_frontier24_closure_at_checked_from_closures[OF structural less.prems])
  have child:
    "\<And>j. j < i \<Longrightarrow>
      comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle) phase
        (cf24_closure_output_root (cf24_closures bundle ! j)) =
      Some (comma_parametric_typed_mask_code
        (comma_semantic_phase_program_fold comma_phase_program_full_action_output phase
          (cf24_programs bundle ! cf24_closure_program_ref (cf24_closures bundle ! j))
          (cf24_closure_full_shift (cf24_closures bundle ! j))))"
    using less.IH less.prems by auto
  show ?case
  proof (cases ?program)
    case (Comma_Entry_Core_Program f d residue core)
    show ?thesis by (rule comma_frontier24_entry_closure_typed_exact
      [OF certified member shape Comma_Entry_Core_Program child])
  next
    case (Comma_Near_Residual_Program f d residual)
    have near: "case ?program of Comma_Near_Residual_Program f d residual \<Rightarrow> True
      | Comma_Near_Boundary_Program f \<Rightarrow> True | _ \<Rightarrow> False"
      using Comma_Near_Residual_Program by simp
    show ?thesis by (rule comma_frontier24_near_closure_typed_exact
      [OF certified member shape refl near child])
  next
    case (Comma_Near_Boundary_Program f)
    have near: "case ?program of Comma_Near_Residual_Program f d residual \<Rightarrow> True
      | Comma_Near_Boundary_Program f \<Rightarrow> True | _ \<Rightarrow> False"
      using Comma_Near_Boundary_Program by simp
    show ?thesis by (rule comma_frontier24_near_closure_typed_exact
      [OF certified member shape refl near child])
  qed
qed

lemma comma_frontier24_class_roots_typed_exact:
  assumes certified: "comma_frontier24_bundle_semantic_certified bundle"
    and phase: "phase < 924" and cid: "cid < 46"
  shows "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_class_roots bundle ! cid) =
    Some (comma_frontier_m204_action_code phase
      (comma_semantic_phase_program_class_step phase cid))"
proof -
  have structural:
    "comma_frontier24_bundle_semantic_structure_checked bundle"
    using certified by (rule comma_frontier24_bundle_semantic_certifiedD(2))
  have roots_checked:
    "comma_frontier24_class_roots_checked bundle"
    using structural by (auto simp: comma_frontier24_bundle_semantic_structure_checked_def)
  have root_rows:
    "list_all (\<lambda>class_id.
      (case comma_semantic_phase_program_for_class class_id of
         None \<Rightarrow> False
       | Some selected_program \<Rightarrow>
           cf24_class_program_refs bundle ! class_id <
             length (cf24_programs bundle) \<and>
           cf24_programs bundle !
             (cf24_class_program_refs bundle ! class_id) = selected_program \<and>
           (\<exists>selected_closure\<in>set (cf24_closures bundle).
             cf24_closure_program_ref selected_closure =
               cf24_class_program_refs bundle ! class_id \<and>
             cf24_closure_full_shift selected_closure = 0 \<and>
             cf24_closure_output_root selected_closure =
               cf24_class_roots bundle ! class_id)))
      [0..<46]"
    using roots_checked
    by (simp add: comma_frontier24_class_roots_checked_def)
  have class_range: "cid \<in> {0..<46}"
    using cid by simp
  have class_row:
    "(case comma_semantic_phase_program_for_class cid of
       None \<Rightarrow> False
     | Some selected_program \<Rightarrow>
         cf24_class_program_refs bundle ! cid <
           length (cf24_programs bundle) \<and>
         cf24_programs bundle !
           (cf24_class_program_refs bundle ! cid) = selected_program \<and>
         (\<exists>selected_closure\<in>set (cf24_closures bundle).
           cf24_closure_program_ref selected_closure =
             cf24_class_program_refs bundle ! cid \<and>
           cf24_closure_full_shift selected_closure = 0 \<and>
           cf24_closure_output_root selected_closure =
             cf24_class_roots bundle ! cid))"
    using root_rows class_range by (simp add: list_all_iff)
  have class_program_some:
    "comma_semantic_phase_program_for_class cid \<noteq> None"
  proof (cases "comma_semantic_phase_program_for_class cid")
    case None
    with class_row show ?thesis by simp
  next
    case (Some selected_program)
    then show ?thesis by simp
  qed
  obtain canonical where canonical:
      "comma_semantic_phase_program_for_class cid = Some canonical"
    using class_program_some by (cases "comma_semantic_phase_program_for_class cid") auto
  have class_binding:
    "cf24_class_program_refs bundle ! cid < length (cf24_programs bundle) \<and>
     cf24_programs bundle ! (cf24_class_program_refs bundle ! cid) = canonical \<and>
     (\<exists>selected_closure\<in>set (cf24_closures bundle).
        cf24_closure_program_ref selected_closure =
          cf24_class_program_refs bundle ! cid \<and>
        cf24_closure_full_shift selected_closure=0 \<and>
        cf24_closure_output_root selected_closure =
          cf24_class_roots bundle ! cid)"
    using class_row canonical by simp
  obtain closure where closure:
      "closure \<in> set (cf24_closures bundle)"
      "cf24_closure_program_ref closure =
        cf24_class_program_refs bundle ! cid"
      "cf24_closure_full_shift closure=0"
      "cf24_closure_output_root closure=cf24_class_roots bundle ! cid"
    using class_binding by blast
  obtain index where index:
      "index < length (cf24_closures bundle)"
      "cf24_closures bundle ! index=closure"
    using closure(1) by (auto simp: in_set_conv_nth)
  have class_program_ref:
    "cf24_programs bundle ! cf24_closure_program_ref closure = canonical"
    using closure(2) class_binding by simp
  have closure_certified: "comma_frontier24_closure_certified bundle"
    using certified by (simp only: comma_frontier24_full_iff_closures_and_classes; blast)
  have root:
    "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (cf24_class_roots bundle ! cid) =
      Some (comma_parametric_typed_mask_code
        (comma_phase_program_full_action_output phase
          (comma_semantic_phase_program_round phase canonical 0)))"
    using comma_frontier24_closures_typed_exact[OF closure_certified index(1), where phase=phase]
      index(2) closure(3,4) class_program_ref
      comma_phase_program_full_action_fold_fusion by simp
  have step:
    "comma_phase_rank_mask_lift phase
      (comma_phase_program_full_action_output phase
        (comma_semantic_phase_program_round phase canonical 0)) =
      comma_semantic_phase_program_class_step phase cid"
    by (rule comma_phase_program_full_action_class_exact[OF phase cid canonical])
  have valid: "comma_semantic_phase_class_valid phase cid"
    using phase cid by (simp add: comma_semantic_phase_class_valid_def)
  have clock_bound:
    "\<And>next_phase next_class.
      comma_semantic_phase_program_class_step phase cid =
        Comma_Phase_Class_Continue next_phase next_class \<Longrightarrow>
      next_phase=(phase+1) mod 924 \<and> next_class<46"
    using comma_semantic_phase_program_class_step_continue_closed[OF valid]
    by (auto simp: comma_semantic_phase_class_valid_def)
  let ?output = "comma_phase_program_full_action_output phase
    (comma_semantic_phase_program_round phase canonical 0)"
  have encoding: "comma_parametric_typed_mask_code ?output =
      comma_frontier_m204_action_code phase (comma_phase_rank_mask_lift phase ?output)"
  proof (cases ?output)
    case Comma_Phase_Rank_Mask_Invalid
    then show ?thesis by simp
  next
    case (Comma_Phase_Rank_Mask_Fork digit delta)
    then show ?thesis by simp
  next
    case (Comma_Phase_Rank_Mask_Landmine delta)
    then show ?thesis by simp
  next
    case (Comma_Phase_Rank_Mask_Continue target)
    have continued: "comma_semantic_phase_program_class_step phase cid =
        Comma_Phase_Class_Continue ((phase+1) mod 924) target"
      using step Comma_Phase_Rank_Mask_Continue by simp
    have target: "target < 46" using clock_bound[OF continued] by simp
    show ?thesis using Comma_Phase_Rank_Mask_Continue target by simp
  qed
  show ?thesis using root step encoding by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Authenticated typed Near closure"
    @{thms comma_frontier24_near_closure_typed_exact
      comma_frontier24_closures_typed_exact comma_frontier24_class_roots_typed_exact};
\<close>

end
