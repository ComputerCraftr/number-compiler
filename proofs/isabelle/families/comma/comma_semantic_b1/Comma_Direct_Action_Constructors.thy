theory Comma_Direct_Action_Constructors
  imports Comma_Parametric_Typed_Entry Comma_CRT_MDD_Multiway Comma_CRT_MDD_Shift
    Comma_Frontier_M204_Generic
begin

text \<open>These constructor laws compose checked MDD operations with the
program semantics. They do not certify a proposed expression graph or its
binding to the class and physical source roots.\<close>

datatype comma_direct_action_expression =
    Comma_Direct_Invalid
  | Comma_Direct_Continue nat nat
  | Comma_Direct_Fork nat nat
  | Comma_Direct_Landmine nat
  | Comma_Direct_Goto comma_direct_action_expression nat
  | Comma_Direct_Entry comma_phase_core_id "(nat \<times> comma_direct_action_expression) list"

fun comma_direct_action_interpret ::
  "comma_direct_action_expression \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    comma_phase_rank_mask_action" where
  "comma_direct_action_interpret Comma_Direct_Invalid phase shift =
    Comma_Phase_Rank_Mask_Invalid"
| "comma_direct_action_interpret (Comma_Direct_Continue target delta) phase shift =
    (if (phase+(delta+shift)) mod 924 = (phase+1) mod 924
      then Comma_Phase_Rank_Mask_Continue target else Comma_Phase_Rank_Mask_Invalid)"
| "comma_direct_action_interpret (Comma_Direct_Fork digit delta) phase shift =
    Comma_Phase_Rank_Mask_Fork digit (shift+delta)"
| "comma_direct_action_interpret (Comma_Direct_Landmine delta) phase shift =
    Comma_Phase_Rank_Mask_Landmine (shift+delta)"
| "comma_direct_action_interpret (Comma_Direct_Goto child delta) phase shift =
    comma_direct_action_interpret child phase (shift+delta)"
| "comma_direct_action_interpret (Comma_Direct_Entry core rows) phase shift =
    foldr (\<lambda>(wanted,child) tail.
      if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
      then comma_direct_action_interpret child phase shift else tail)
      rows Comma_Phase_Rank_Mask_Invalid"

lemma comma_direct_action_expression_congruence:
  assumes "left = right"
  shows "comma_direct_action_interpret left phase shift =
    comma_direct_action_interpret right phase shift"
  using assms by simp

lemma comma_direct_action_terminal_transport:
  "comma_direct_action_interpret (Comma_Direct_Fork digit delta)
      phase shift = comma_phase_program_full_action_output phase
        (Comma_Round_Fork digit (shift+delta))"
  "comma_direct_action_interpret (Comma_Direct_Landmine delta)
      phase shift = comma_phase_program_full_action_output phase
        (Comma_Round_Landmine (shift+delta))"
  by (simp_all only: comma_direct_action_interpret.simps
      comma_phase_program_full_action_terminal)

lemma comma_direct_action_exit_normalization:
  assumes admitted: "comma_decade_root_admitted (Comma_Entry f source_delta off)"
  shows "comma_phase_program_full_action_of_source_action phase shift
      (Comma_Continuation_Exit (Comma_Entry f source_delta off) delta) =
    comma_direct_action_interpret
      (Comma_Direct_Continue (comma_offset_orbit off) (source_delta+delta)) phase shift"
  using admitted
  apply (simp only: comma_phase_program_full_action_of_source_action_def
    comma_phase_program_full_action_exit_exact)
  by (simp add: comma_decade_root_admitted_def add.assoc add.commute add.left_commute)

lemma comma_direct_action_exit_invalid:
  assumes rejected: "\<not> comma_decade_root_admitted source"
  shows "comma_phase_program_full_action_of_source_action phase shift
      (Comma_Continuation_Exit source delta) =
    comma_direct_action_interpret Comma_Direct_Invalid phase shift"
  using rejected
  apply (simp only: comma_phase_program_full_action_of_source_action_def
    comma_phase_program_full_action_exit_exact)
  by (cases source) (auto simp: comma_decade_root_admitted_def)

lemma comma_direct_action_terminal_normalization:
  "comma_phase_program_full_action_of_source_action phase shift
      (Comma_Continuation_Fork digit delta) =
    comma_direct_action_interpret (Comma_Direct_Fork digit delta) phase shift"
  "comma_phase_program_full_action_of_source_action phase shift
      (Comma_Continuation_Landmine delta) =
    comma_direct_action_interpret (Comma_Direct_Landmine delta) phase shift"
  "comma_phase_program_full_action_of_source_action phase shift
      Comma_Continuation_Invalid =
    comma_direct_action_interpret Comma_Direct_Invalid phase shift"
  by (simp_all only: comma_phase_program_full_action_of_source_action_def
      comma_source_continuation_action.case comma_direct_action_interpret.simps
      comma_phase_program_full_action_terminal)

lemma comma_direct_action_goto_transport:
  "comma_direct_action_interpret (Comma_Direct_Goto child delta) phase shift =
    comma_direct_action_interpret child phase (shift+delta)"
  by simp

lemma comma_direct_action_program_step:
  assumes step: "comma_phase_program_step_at program phase shift =
    comma_phase_program_step_of_action (comma_source_continuation_transport shift action)"
  shows "comma_semantic_phase_program_fold comma_phase_program_full_action_output
      phase program shift =
    comma_phase_program_full_action_of_source_action phase shift action"
  using step comma_phase_program_full_action_fold_step[of phase program shift]
    comma_phase_program_full_action_source_step[of phase shift action]
  by simp

lemma comma_direct_action_entry_interpret:
  assumes admitted: "comma_phase_program_structurally_admitted
      (Comma_Entry_Core_Program f d residue core)"
    and children: "\<And>wanted. wanted \<in> set (comma_core_supported_values core) \<Longrightarrow>
      comma_direct_action_interpret (child wanted) phase shift =
        comma_phase_program_full_action_of_source_action phase shift
          (comma_phase_program_entry_core_value_action f residue core wanted)"
  shows "comma_direct_action_interpret
      (Comma_Direct_Entry core (map (\<lambda>wanted. (wanted,child wanted))
        (comma_core_supported_values core))) phase shift =
    comma_semantic_phase_program_fold comma_phase_program_full_action_output
      phase (Comma_Entry_Core_Program f d residue core) shift"
proof -
  obtain wanted where member: "wanted \<in> set (comma_core_supported_values core)"
    and active: "comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)"
    and unique: "\<forall>x\<in>set (comma_core_supported_values core).
      \<forall>y\<in>set (comma_core_supported_values core).
        comma_crt_eval (phase+shift) (comma_core_value_guard core x) \<longrightarrow>
        comma_crt_eval (phase+shift) (comma_core_value_guard core y) \<longrightarrow> x=y"
    and step: "comma_phase_program_step_at (Comma_Entry_Core_Program f d residue core)
      phase shift = comma_phase_program_step_of_action (comma_source_continuation_transport shift
        (comma_phase_program_entry_core_value_action f residue core wanted))"
    by (rule comma_entry_supported_selected_step[OF admitted])
  have folded: "foldr (\<lambda>wanted tail.
      if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
      then comma_direct_action_interpret (child wanted) phase shift else tail)
      (comma_core_supported_values core) Comma_Phase_Rank_Mask_Invalid =
    comma_direct_action_interpret (child wanted) phase shift"
    by (rule comma_list_guarded_value_fold_selected[OF unique member active])
  show ?thesis using folded children[OF member] comma_direct_action_program_step[OF step]
    by (simp add: foldr_map comp_def split_beta)
qed

lemma comma_direct_action_goto:
  assumes child: "comma_semantic_port_program_of_source source = Some program"
    and checked: "comma_crt_mdd_eval_phase radices nodes phase root =
      Some (comma_parametric_typed_mask_code
        (comma_semantic_phase_program_fold comma_phase_program_full_action_output
          phase program (shift+delta)))"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (comma_parametric_typed_mask_code
      (comma_phase_program_full_action_of_source_action phase shift
        (Comma_Continuation_Goto source delta)))"
  using checked child
  by (simp only: comma_phase_program_full_action_of_source_action_def
      comma_source_continuation_action.case option.case)

lemma comma_direct_action_terminal_leaf:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and bound: "root < length nodes"
    and leaf: "nodes ! root = Comma_CRT_MDD_Leaf
      (comma_parametric_typed_mask_code
        (comma_phase_program_full_action_of_source_action phase shift action))"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (comma_parametric_typed_mask_code
      (comma_phase_program_full_action_of_source_action phase shift action))"
  by (rule comma_crt_mdd_eval_phase_leaf[OF wf bound leaf])

lemma comma_direct_action_shift:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and shift: "comma_crt_mdd_root_shift_certificate radices nodes amount source target"
  shows "comma_crt_mdd_eval_phase radices nodes phase target =
    comma_crt_mdd_eval_phase radices nodes (phase+amount) source"
  by (rule comma_crt_mdd_root_shift_certificate_eval_phase[OF wf shift])

lemma comma_direct_action_priority:
  assumes cert: "comma_crt_mdd_multiway_certificate radices nodes cases fallback output"
    and wf: "comma_crt_mdd_table_wellformed radices nodes"
    and guards: "\<And>guard action. (guard,action) \<in> set cases \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase guard =
        Some (if active guard action then 1 else 0)"
    and actions: "\<And>guard action. (guard,action) \<in> set cases \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase action = Some (value guard action)"
    and fallback: "comma_crt_mdd_eval_phase radices nodes phase fallback = Some initial"
  shows "comma_crt_mdd_eval_phase radices nodes phase output =
    Some (foldr (\<lambda>(guard,action) tail.
      if active guard action then value guard action else tail) cases initial)"
proof -
  have exact: "comma_crt_mdd_multiway_eval radices nodes (\<lambda>_. phase) cases fallback =
    Some (foldr (\<lambda>(guard,action) tail.
      if active guard action then value guard action else tail) cases initial)"
    by (rule comma_crt_mdd_multiway_value)
      (use guards actions fallback in \<open>simp_all only: comma_crt_mdd_eval_phase_def\<close>)
  show ?thesis using comma_crt_mdd_multiway_certificate_phase[OF cert wf] exact
    by simp
qed

lemma comma_direct_action_entry:
  assumes admitted: "comma_phase_program_structurally_admitted
      (Comma_Entry_Core_Program f d residue core)"
    and wf: "comma_crt_mdd_table_wellformed radices nodes"
    and priority: "comma_crt_mdd_multiway_certificate radices nodes
      (map (\<lambda>wanted. (guard wanted, action wanted))
        (comma_core_supported_values core)) fallback root"
    and guards: "\<And>wanted. wanted \<in> set (comma_core_supported_values core) \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase (guard wanted) =
        Some (if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
          then 1 else 0)"
    and actions: "\<And>wanted. wanted \<in> set (comma_core_supported_values core) \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase (action wanted) =
        Some (comma_parametric_typed_action_code f shift
          (comma_phase_program_entry_core_value_action f residue core wanted)
          (\<lambda>child child_shift. comma_parametric_typed_mask_code
            (comma_semantic_phase_program_fold comma_phase_program_full_action_output
              phase child child_shift)))"
    and fallback: "comma_crt_mdd_eval_phase radices nodes phase fallback = Some 0"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (comma_parametric_typed_mask_code
      (comma_semantic_phase_program_fold comma_phase_program_full_action_output
        phase (Comma_Entry_Core_Program f d residue core) shift))"
proof -
  let ?value = "\<lambda>wanted. comma_parametric_typed_action_code f shift
    (comma_phase_program_entry_core_value_action f residue core wanted)
    (\<lambda>child child_shift. comma_parametric_typed_mask_code
      (comma_semantic_phase_program_fold comma_phase_program_full_action_output
        phase child child_shift))"
  let ?active = "\<lambda>wanted. comma_crt_eval (phase+shift)
    (comma_core_value_guard core wanted)"
  have rows: "comma_crt_mdd_multiway_eval radices nodes (\<lambda>_. phase)
      (map (\<lambda>wanted. (guard wanted, action wanted)) xs) fallback =
    Some (foldr (\<lambda>wanted tail. if ?active wanted then ?value wanted else tail) xs 0)"
    if subset: "set xs \<subseteq> set (comma_core_supported_values core)" for xs
    using subset
  proof (induction xs)
    case Nil
    then show ?case using fallback
      by (simp add: comma_crt_mdd_multiway_eval_def comma_crt_mdd_eval_phase_def)
  next
    case (Cons wanted xs)
    have member: "wanted \<in> set (comma_core_supported_values core)"
      using Cons.prems by auto
    have tail: "set xs \<subseteq> set (comma_core_supported_values core)"
      using Cons.prems by auto
    show ?case using guards[OF member] actions[OF member] Cons.IH[OF tail]
      by (simp add: comma_crt_mdd_multiway_eval_def comma_crt_mdd_eval_phase_def)
  qed
  have evaluated: "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (foldr (\<lambda>wanted tail. if ?active wanted then ?value wanted else tail)
      (comma_core_supported_values core) 0)"
    using comma_crt_mdd_multiway_certificate_phase[OF priority wf]
      rows[of "comma_core_supported_values core"] by simp
  show ?thesis using evaluated comma_parametric_typed_entry_fold_exact[OF admitted,
    where phase=phase and shift=shift] by simp
qed

lemma comma_direct_action_near:
  assumes step: "comma_phase_program_step_at program phase shift =
      comma_phase_program_step_of_action (comma_source_continuation_transport shift action)"
    and checked: "comma_crt_mdd_eval_phase radices nodes phase root =
      Some (comma_parametric_typed_mask_code
        (comma_phase_program_full_action_of_source_action phase shift action))"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (comma_parametric_typed_mask_code
      (comma_semantic_phase_program_fold comma_phase_program_full_action_output
        phase program shift))"
  using checked comma_direct_action_program_step[OF step] by simp

lemma comma_direct_action_class_binding:
  assumes phase: "phase < 924" and cid: "cid < 46"
    and binding: "comma_semantic_phase_program_for_class cid = Some program"
    and checked: "comma_crt_mdd_eval_phase radices nodes phase root =
      Some (comma_parametric_typed_mask_code
        (comma_semantic_phase_program_fold comma_phase_program_full_action_output
          phase program 0))"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (comma_frontier_m204_action_code phase
      (comma_semantic_phase_program_class_step phase cid))"
proof -
  let ?output = "comma_phase_program_full_action_output phase
    (comma_semantic_phase_program_round phase program 0)"
  have step: "comma_phase_rank_mask_lift phase ?output =
      comma_semantic_phase_program_class_step phase cid"
    by (rule comma_phase_program_full_action_class_exact[OF phase cid binding])
  have valid: "comma_semantic_phase_class_valid phase cid"
    using phase cid by (simp add: comma_semantic_phase_class_valid_def)
  have bound: "\<And>p c. comma_semantic_phase_program_class_step phase cid =
      Comma_Phase_Class_Continue p c \<Longrightarrow> c < 46"
    using comma_semantic_phase_program_class_step_continue_closed[OF valid]
    by (auto simp: comma_semantic_phase_class_valid_def)
  have encoding: "comma_parametric_typed_mask_code ?output =
      comma_frontier_m204_action_code phase (comma_phase_rank_mask_lift phase ?output)"
  proof (cases ?output)
    case (Comma_Phase_Rank_Mask_Continue target)
    have continued: "comma_semantic_phase_program_class_step phase cid =
        Comma_Phase_Class_Continue ((phase+1) mod 924) target"
      using step Comma_Phase_Rank_Mask_Continue by simp
    have "target < 46" by (rule bound[OF continued])
    then show ?thesis using Comma_Phase_Rank_Mask_Continue by simp
  qed simp_all
  show ?thesis using checked step encoding comma_phase_program_full_action_fold_fusion by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Direct action constructors"
    @{thms comma_direct_action_expression_congruence
      comma_direct_action_terminal_transport comma_direct_action_exit_normalization
      comma_direct_action_exit_invalid comma_direct_action_terminal_normalization
      comma_direct_action_goto_transport comma_direct_action_program_step
      comma_direct_action_entry_interpret comma_direct_action_goto
      comma_direct_action_terminal_leaf comma_direct_action_shift
      comma_direct_action_priority comma_direct_action_entry
      comma_direct_action_near comma_direct_action_class_binding};
\<close>

end
