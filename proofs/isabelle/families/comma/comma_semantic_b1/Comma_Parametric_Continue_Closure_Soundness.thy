theory Comma_Parametric_Continue_Closure_Soundness
  imports Comma_Parametric_Entry_Closure
    Comma_Symbolic_Class_Step
begin

lemma comma_frontier24_near_closure_hit:
  assumes certified: "comma_frontier24_bundle_semantic_certified bundle"
    and closure_mem: "closure \<in> set (cf24_closures bundle)"
    and shape:
      "comma_frontier24_closure_shape_checked bundle (closure_index,closure)"
    and program: "cf24_programs bundle ! cf24_closure_program_ref closure = program"
    and near_program:
      "case program of Comma_Near_Residual_Program f d residual \<Rightarrow> True
       | Comma_Near_Boundary_Program f \<Rightarrow> True
       | _ \<Rightarrow> False"
    and child_hit:
      "\<And>child_index target. child_index < closure_index \<Longrightarrow>
        (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
          phase
          (cf24_closure_output_root (cf24_closures bundle ! child_index)) =
            Some (Suc target)) \<longleftrightarrow>
        comma_semantic_phase_program_continue_guard phase
          (cf24_programs bundle !
            cf24_closure_program_ref (cf24_closures bundle ! child_index))
          (cf24_closure_full_shift
            (cf24_closures bundle ! child_index)) target"
  shows
    "(comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_closure_output_root closure) = Some (Suc target)) \<longleftrightarrow>
     comma_semantic_phase_program_continue_guard phase
       (cf24_programs bundle ! cf24_closure_program_ref closure)
       (cf24_closure_full_shift closure) target"
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
    using certified by (rule comma_frontier24_bundle_semantic_certifiedD(1))
  have output_hit_indexed:
    "(comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
       phase action_root = Some (Suc target)) \<longleftrightarrow>
      comma_phase_continue_action_observer phase
        (comma_phase_program_sector
          (cf24_programs bundle ! cf24_closure_program_ref closure))
        (cf24_closure_full_shift closure)
        (cf24_action_tokens bundle ! token) target"
    by (rule comma_frontier24_action_output_linked_hit[OF table linked child_hit])
  have output_hit:
    "(comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
       phase action_root = Some (Suc target)) \<longleftrightarrow>
      comma_phase_continue_action_observer phase
        (comma_phase_program_sector program)
        (cf24_closure_full_shift closure)
        (cf24_action_tokens bundle ! token) target"
    using output_hit_indexed program by simp
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
  have structural:
    "comma_phase_program_structurally_admitted program"
    using certified program_index program
    by (auto simp: comma_frontier24_bundle_semantic_certified_def
      comma_frontier24_bundle_semantic_structure_checked_def list_all_iff)
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
  have action_step:
    "comma_phase_continue_action_observer phase
      (comma_phase_program_sector program)
      (cf24_closure_full_shift closure)
      (cf24_action_tokens bundle ! token) target =
     comma_phase_continue_step_observer phase target
      (comma_phase_program_step_at program phase
        (cf24_closure_full_shift closure))"
    by (rule comma_phase_continue_action_observer_step_exact
      [OF step goto_bounds])
  have guard_step:
    "comma_semantic_phase_program_continue_guard phase program
      (cf24_closure_full_shift closure) target =
     comma_phase_continue_step_observer phase target
      (comma_phase_program_step_at program phase
        (cf24_closure_full_shift closure))"
    by (rule comma_semantic_phase_program_continue_guard_step)
  show ?thesis
    using output_hit action_step guard_step action_root(2) program by simp
qed


lemma comma_frontier24_closures_continue_hit:
  assumes certified: "comma_frontier24_bundle_semantic_certified bundle"
  shows "\<forall>i. i < length (cf24_closures bundle) \<longrightarrow>
    (\<forall>phase target.
      (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (cf24_closure_output_root (cf24_closures bundle ! i)) =
          Some (Suc target)) \<longleftrightarrow>
      comma_semantic_phase_program_continue_guard phase
        (cf24_programs bundle !
          cf24_closure_program_ref (cf24_closures bundle ! i))
        (cf24_closure_full_shift (cf24_closures bundle ! i)) target)"
proof (rule allI)
  fix i
  show "i < length (cf24_closures bundle) \<longrightarrow>
    (\<forall>phase target.
      (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (cf24_closure_output_root (cf24_closures bundle ! i)) =
          Some (Suc target)) \<longleftrightarrow>
      comma_semantic_phase_program_continue_guard phase
        (cf24_programs bundle !
          cf24_closure_program_ref (cf24_closures bundle ! i))
        (cf24_closure_full_shift (cf24_closures bundle ! i)) target)"
  proof (induction i rule: less_induct)
    case (less i)
    show ?case
    proof
      assume i_bound: "i < length (cf24_closures bundle)"
      show "\<forall>phase target.
        (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
          phase (cf24_closure_output_root (cf24_closures bundle ! i)) =
            Some (Suc target)) \<longleftrightarrow>
        comma_semantic_phase_program_continue_guard phase
          (cf24_programs bundle !
            cf24_closure_program_ref (cf24_closures bundle ! i))
          (cf24_closure_full_shift (cf24_closures bundle ! i)) target"
      proof (rule allI)
        fix phase
        show "\<forall>target.
          (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
            phase (cf24_closure_output_root (cf24_closures bundle ! i)) =
              Some (Suc target)) \<longleftrightarrow>
          comma_semantic_phase_program_continue_guard phase
            (cf24_programs bundle !
              cf24_closure_program_ref (cf24_closures bundle ! i))
            (cf24_closure_full_shift (cf24_closures bundle ! i)) target"
        proof (rule allI)
          fix target
          let ?closure = "cf24_closures bundle ! i"
          have structural:
            "comma_frontier24_bundle_semantic_structure_checked bundle"
            using certified by (rule comma_frontier24_bundle_semantic_certifiedD(2))
          have closure_mem: "?closure \<in> set (cf24_closures bundle)"
            using i_bound by (rule nth_mem)
          have shape:
            "comma_frontier24_closure_shape_checked bundle (i,?closure)"
            by (rule comma_frontier24_closure_at_checked
              [OF structural i_bound])
          have child_hit:
            "\<And>child_index child_target.
              child_index < i \<Longrightarrow>
              (comma_crt_mdd_eval_phase (cf24_radices bundle)
                (cf24_nodes bundle) phase
                (cf24_closure_output_root
                  (cf24_closures bundle ! child_index)) =
                  Some (Suc child_target)) \<longleftrightarrow>
              comma_semantic_phase_program_continue_guard phase
                (cf24_programs bundle !
                  cf24_closure_program_ref
                    (cf24_closures bundle ! child_index))
                (cf24_closure_full_shift
                  (cf24_closures bundle ! child_index)) child_target"
          proof -
            fix child_index child_target
            assume child_index: "child_index < i"
            have child_bound:
              "child_index < length (cf24_closures bundle)"
              using child_index i_bound by simp
            have child_induction:
              "child_index < length (cf24_closures bundle) \<longrightarrow>
                (\<forall>phase target.
                  (comma_crt_mdd_eval_phase (cf24_radices bundle)
                    (cf24_nodes bundle) phase
                    (cf24_closure_output_root
                      (cf24_closures bundle ! child_index)) =
                      Some (Suc target)) \<longleftrightarrow>
                  comma_semantic_phase_program_continue_guard phase
                    (cf24_programs bundle !
                      cf24_closure_program_ref
                        (cf24_closures bundle ! child_index))
                    (cf24_closure_full_shift
                      (cf24_closures bundle ! child_index)) target)"
              by (rule less.IH[OF child_index])
            show "(comma_crt_mdd_eval_phase (cf24_radices bundle)
                (cf24_nodes bundle) phase
                (cf24_closure_output_root
                  (cf24_closures bundle ! child_index)) =
                  Some (Suc child_target)) \<longleftrightarrow>
              comma_semantic_phase_program_continue_guard phase
                (cf24_programs bundle !
                  cf24_closure_program_ref
                    (cf24_closures bundle ! child_index))
                (cf24_closure_full_shift
                  (cf24_closures bundle ! child_index)) child_target"
              using child_induction child_bound by blast
          qed
          let ?program =
            "cf24_programs bundle ! cf24_closure_program_ref ?closure"
          show "(comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
              phase (cf24_closure_output_root ?closure) = Some (Suc target)) \<longleftrightarrow>
            comma_semantic_phase_program_continue_guard phase ?program
              (cf24_closure_full_shift ?closure) target"
          proof (cases ?program)
            case (Comma_Entry_Core_Program f d residue core)
            have program:
              "cf24_programs bundle ! cf24_closure_program_ref ?closure =
                Comma_Entry_Core_Program f d residue core"
              using Comma_Entry_Core_Program by simp
            show ?thesis
              by (rule comma_frontier24_entry_closure_hit
                [OF certified closure_mem shape program child_hit])
          next
            case (Comma_Near_Residual_Program f d residual)
            have program:
              "cf24_programs bundle ! cf24_closure_program_ref ?closure =
                Comma_Near_Residual_Program f d residual"
              using Comma_Near_Residual_Program by simp
            have near_program:
              "case Comma_Near_Residual_Program f d residual of
                 Comma_Near_Residual_Program f d residual \<Rightarrow> True
               | Comma_Near_Boundary_Program f \<Rightarrow> True
               | _ \<Rightarrow> False"
              by simp
            show ?thesis
              by (rule comma_frontier24_near_closure_hit
                [OF certified closure_mem shape program near_program child_hit])
          next
            case (Comma_Near_Boundary_Program f)
            have program:
              "cf24_programs bundle ! cf24_closure_program_ref ?closure =
                Comma_Near_Boundary_Program f"
              using Comma_Near_Boundary_Program by simp
            have near_program:
              "case Comma_Near_Boundary_Program f of
                 Comma_Near_Residual_Program f d residual \<Rightarrow> True
               | Comma_Near_Boundary_Program f \<Rightarrow> True
               | _ \<Rightarrow> False"
              by simp
            show ?thesis
              by (rule comma_frontier24_near_closure_hit
                [OF certified closure_mem shape program near_program child_hit])
          qed
        qed
      qed
    qed
  qed
qed

lemma comma_frontier24_eval_from_continue_hits:
  fixes action :: "nat comma_phase_class_action"
  assumes total: "\<exists>payload. evaluate = Some payload"
    and continued_phase:
      "\<And>actual_phase target.
        action = Comma_Phase_Class_Continue actual_phase target \<Longrightarrow>
        actual_phase = expected_phase"
    and hits:
      "\<And>target. (evaluate = Some (Suc target)) \<longleftrightarrow>
        action = Comma_Phase_Class_Continue expected_phase target"
  shows "evaluate =
    (case action of
       Comma_Phase_Class_Continue _ target \<Rightarrow> Some (Suc target)
     | _ \<Rightarrow> Some 0)"
proof (cases action)
  case Comma_Phase_Class_Invalid
  obtain payload where payload: "evaluate=Some payload"
    using total by blast
  show ?thesis using payload hits Comma_Phase_Class_Invalid
    by (cases payload) auto
next
  case (Comma_Phase_Class_Fork a d)
  obtain payload where payload: "evaluate=Some payload"
    using total by blast
  show ?thesis using payload hits Comma_Phase_Class_Fork
    by (cases payload) auto
next
  case (Comma_Phase_Class_Landmine d)
  obtain payload where payload: "evaluate=Some payload"
    using total by blast
  show ?thesis using payload hits Comma_Phase_Class_Landmine
    by (cases payload) auto
next
  case (Comma_Phase_Class_Continue actual_phase actual_class)
  have phase_exact: "actual_phase=expected_phase"
    by (rule continued_phase[OF Comma_Phase_Class_Continue])
  have hit: "evaluate=Some (Suc actual_class)"
    using hits[of actual_class] Comma_Phase_Class_Continue phase_exact by simp
  show ?thesis using hit Comma_Phase_Class_Continue by simp
qed

lemma comma_frontier24_class_roots_exact:
  assumes certified: "comma_frontier24_bundle_semantic_certified bundle"
    and phase: "phase < 924"
    and cid: "cid < 46"
  shows
    "comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
      phase (cf24_class_roots bundle ! cid) =
     (case comma_semantic_phase_program_class_step phase cid of
        Comma_Phase_Class_Continue _ target \<Rightarrow> Some (Suc target)
      | _ \<Rightarrow> Some 0)"
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
  have root_hits:
    "\<And>target.
      (comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (cf24_class_roots bundle ! cid) = Some (Suc target)) \<longleftrightarrow>
      comma_semantic_phase_program_class_step phase cid =
        Comma_Phase_Class_Continue ((phase+1) mod 924) target"
  proof -
    fix target
    have indexed_hit:
      "(comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (cf24_closure_output_root (cf24_closures bundle ! index)) =
          Some (Suc target)) \<longleftrightarrow>
       comma_semantic_phase_program_continue_guard phase
         (cf24_programs bundle ! cf24_closure_program_ref
           (cf24_closures bundle ! index))
         (cf24_closure_full_shift (cf24_closures bundle ! index)) target"
      using comma_frontier24_closures_continue_hit[OF certified] index(1)
      by blast
    have closure_hit:
      "(comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (cf24_closure_output_root closure) = Some (Suc target)) \<longleftrightarrow>
       comma_semantic_phase_program_continue_guard phase canonical 0 target"
      using indexed_hit index(2) closure(3,4) class_program_ref by simp
    have class_guard:
      "comma_semantic_phase_program_continue_guard phase canonical 0 target =
       (comma_semantic_phase_program_class_step phase cid =
         Comma_Phase_Class_Continue ((phase+1) mod 924) target)"
      using canonical phase cid
        comma_semantic_phase_program_class_continue_guard_exact
          [OF phase cid, of target]
      by (simp add: comma_semantic_phase_program_class_continue_guard_def)
    show "(comma_crt_mdd_eval_phase (cf24_radices bundle) (cf24_nodes bundle)
        phase (cf24_class_roots bundle ! cid) = Some (Suc target)) \<longleftrightarrow>
      comma_semantic_phase_program_class_step phase cid =
        Comma_Phase_Class_Continue ((phase+1) mod 924) target"
      using closure_hit class_guard closure(3,4) by simp
  qed
  let ?action = "comma_semantic_phase_program_class_step phase cid"
  have valid: "comma_semantic_phase_class_valid phase cid"
    using phase cid by (simp add: comma_semantic_phase_class_valid_def)
  have continued_phase:
    "\<And>next_phase next_class.
      ?action=Comma_Phase_Class_Continue next_phase next_class \<Longrightarrow>
      next_phase=(phase+1) mod 924"
    by (rule comma_semantic_phase_program_class_step_continue_closed(1)
      [OF valid])
  have total:
    "\<exists>payload. comma_crt_mdd_eval_phase (cf24_radices bundle)
      (cf24_nodes bundle) phase (cf24_class_roots bundle ! cid) =
      Some payload"
  proof -
    have table:
      "comma_crt_mdd_table_wellformed (cf24_radices bundle) (cf24_nodes bundle)"
      using certified by (rule comma_frontier24_bundle_semantic_certifiedD(1))
    have root_bound: "cf24_class_roots bundle ! cid < length (cf24_nodes bundle)"
    proof -
      have "cf24_closure_output_root closure < length (cf24_nodes bundle)"
        using structural index
        by (auto dest: comma_frontier24_closure_at_checked
          simp: comma_frontier24_closure_shape_checked_def)
      then show ?thesis using closure(4) by simp
    qed
    show ?thesis by (rule comma_crt_mdd_eval_phase_total[OF table root_bound])
  qed
  show ?thesis
    by (rule comma_frontier24_eval_from_continue_hits
      [OF total continued_phase root_hits])
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Parametric Continue source closure refinement"
    @{thms comma_frontier24_closures_continue_hit comma_frontier24_class_roots_exact};
\<close>

end
