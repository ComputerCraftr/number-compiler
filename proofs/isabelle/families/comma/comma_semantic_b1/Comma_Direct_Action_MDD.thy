theory Comma_Direct_Action_MDD
  imports Comma_Direct_Action_Constructors
begin

text \<open>Composition of checked MDD operations over semantic expressions.
All roots are applications in the receiving table, and all shifts remain
explicit interpretation data.\<close>

lemma comma_direct_expression_entry_projected_mdd:
  fixes project :: "comma_phase_rank_mask_action \<Rightarrow> nat"
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and priority: "comma_crt_mdd_multiway_certificate radices nodes
      (map (\<lambda>(wanted,child). (guard wanted, child_root wanted child)) rows) fallback root"
    and guards: "\<And>wanted child. (wanted,child) \<in> set rows \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase (guard wanted) =
        Some (if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
          then 1 else 0)"
    and children: "\<And>wanted child. (wanted,child) \<in> set rows \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase (child_root wanted child) =
        Some (project (comma_direct_action_interpret child phase shift))"
    and fallback: "comma_crt_mdd_eval_phase radices nodes phase fallback =
      Some (project Comma_Phase_Rank_Mask_Invalid)"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (project (comma_direct_action_interpret (Comma_Direct_Entry core rows) phase shift))"
proof -
  have rows: "comma_crt_mdd_multiway_eval radices nodes (\<lambda>_. phase)
      (map (\<lambda>(wanted,child). (guard wanted, child_root wanted child)) xs) fallback =
    Some (project (foldr (\<lambda>(wanted,child) tail.
        if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
        then comma_direct_action_interpret child phase shift else tail)
      xs Comma_Phase_Rank_Mask_Invalid))"
    if subset: "set xs \<subseteq> set rows" for xs
    using subset
  proof (induction xs)
    case Nil
    then show ?case using fallback
      by (simp add: comma_crt_mdd_multiway_eval_def comma_crt_mdd_eval_phase_def)
  next
    case (Cons item xs)
    obtain wanted child where item: "item = (wanted,child)" by (cases item) auto
    have member: "(wanted,child) \<in> set rows" using Cons.prems item by auto
    have tail: "set xs \<subseteq> set rows" using Cons.prems by auto
    show ?case using guards[OF member] children[OF member] Cons.IH[OF tail]
      by (simp add: item comma_crt_mdd_multiway_eval_def comma_crt_mdd_eval_phase_def)
  qed
  show ?thesis using comma_crt_mdd_multiway_certificate_phase[OF priority wf]
    rows[of rows] by simp
qed


lemma comma_direct_rows_all_phaseD:
  assumes "list_all (\<lambda>row. \<forall>phase. P phase row) rows"
  shows "list_all (P phase) rows"
  using assms by (auto simp: list_all_iff)

lemma comma_direct_expression_entry_projected_rows_mdd:
  fixes project :: "comma_phase_rank_mask_action \<Rightarrow> nat"
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and priority: "comma_crt_mdd_multiway_certificate radices nodes
      (map (\<lambda>(wanted,child). (guard wanted, child_root wanted child)) rows) fallback root"
    and guards: "list_all (\<lambda>(wanted,child).
      comma_crt_mdd_eval_phase radices nodes phase (guard wanted) =
        Some (if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
          then 1 else 0)) rows"
    and children: "list_all (\<lambda>(wanted,child).
      comma_crt_mdd_eval_phase radices nodes phase (child_root wanted child) =
        Some (project (comma_direct_action_interpret child phase shift))) rows"
    and fallback: "comma_crt_mdd_eval_phase radices nodes phase fallback =
      Some (project Comma_Phase_Rank_Mask_Invalid)"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (project (comma_direct_action_interpret (Comma_Direct_Entry core rows) phase shift))"
proof (rule comma_direct_expression_entry_projected_mdd
    [where radices=radices and nodes=nodes and phase=phase and shift=shift
       and core=core and rows=rows and guard=guard and child_root=child_root
       and fallback=fallback and root=root and project=project,
     OF wf priority _ _ fallback])
  fix wanted child
  assume member: "(wanted,child) \<in> set rows"
  show "comma_crt_mdd_eval_phase radices nodes phase (guard wanted) =
    Some (if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
      then 1 else 0)"
    using guards member by (auto simp: list_all_iff)
next
  fix wanted child
  assume member: "(wanted,child) \<in> set rows"
  show "comma_crt_mdd_eval_phase radices nodes phase (child_root wanted child) =
    Some (project (comma_direct_action_interpret child phase shift))"
    using children member by (auto simp: list_all_iff)
qed

lemma comma_direct_expression_entry_mdd:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and priority: "comma_crt_mdd_multiway_certificate radices nodes
      (map (\<lambda>(wanted,child). (guard wanted, child_root wanted child)) rows) fallback root"
    and guards: "\<And>wanted child. (wanted,child) \<in> set rows \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase (guard wanted) =
        Some (if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
          then 1 else 0)"
    and children: "\<And>wanted child. (wanted,child) \<in> set rows \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase (child_root wanted child) =
        Some (comma_parametric_typed_mask_code
          (comma_direct_action_interpret child phase shift))"
    and fallback: "comma_crt_mdd_eval_phase radices nodes phase fallback = Some 0"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (comma_parametric_typed_mask_code
      (comma_direct_action_interpret (Comma_Direct_Entry core rows) phase shift))"
proof -
  have fallback_code: "comma_crt_mdd_eval_phase radices nodes phase fallback =
      Some (comma_parametric_typed_mask_code Comma_Phase_Rank_Mask_Invalid)"
    using fallback by simp
  show ?thesis by (rule comma_direct_expression_entry_projected_mdd
    [where project=comma_parametric_typed_mask_code, OF wf priority guards children fallback_code])
qed

lemma comma_direct_expression_goto_projected_mdd:
  fixes project :: "comma_phase_rank_mask_action \<Rightarrow> nat"
  assumes child: "comma_crt_mdd_eval_phase radices nodes phase root =
      Some (project (comma_direct_action_interpret expression phase (shift+delta)))"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (project (comma_direct_action_interpret (Comma_Direct_Goto expression delta) phase shift))"
  using child by simp

lemma comma_direct_expression_goto_mdd:
  assumes child: "comma_crt_mdd_eval_phase radices nodes phase root =
      Some (comma_parametric_typed_mask_code
        (comma_direct_action_interpret expression phase (shift+delta)))"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (comma_parametric_typed_mask_code
      (comma_direct_action_interpret (Comma_Direct_Goto expression delta) phase shift))"
  using child by simp

lemma comma_direct_expression_terminal_mdd:
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and bound: "root < length nodes"
    and leaf: "nodes ! root = Comma_CRT_MDD_Leaf
      (comma_parametric_typed_mask_code (comma_direct_action_interpret expression phase shift))"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (comma_parametric_typed_mask_code (comma_direct_action_interpret expression phase shift))"
  by (rule comma_crt_mdd_eval_phase_leaf[OF wf bound leaf])

lemma comma_direct_expression_terminal_codes:
  "comma_parametric_typed_mask_code
    (comma_direct_action_interpret Comma_Direct_Invalid phase shift) = 0"
  "comma_parametric_typed_mask_code
    (comma_direct_action_interpret (Comma_Direct_Continue target delta) phase shift) =
      (if (delta+shift) mod 924 = 1 then Suc target else 0)"
  "comma_parametric_typed_mask_code
    (comma_direct_action_interpret (Comma_Direct_Fork digit delta) phase shift) =
      (if 2 \<le> digit \<and> digit \<le> 9 \<and> shift+delta=0 then 45+digit else 0)"
  "comma_parametric_typed_mask_code
    (comma_direct_action_interpret (Comma_Direct_Landmine delta) phase shift) =
      (if shift+delta=0 then 55 else 0)"
proof -
  have cancel: "(phase + k) mod 924 = (phase + 1) mod 924 \<longleftrightarrow> k mod 924 = 1"
    for k :: nat
  proof -
    have "[phase+k=phase+1] (mod 924) \<longleftrightarrow> [k=1] (mod 924)"
      by (rule cong_add_lcancel_nat)
    then show ?thesis by (simp add: cong_def)
  qed
  have cancel_suc: "(phase + k) mod 924 = (Suc phase) mod 924 \<longleftrightarrow>
      k mod 924 = 1" for k :: nat
    using cancel[of k] by simp
  show "comma_parametric_typed_mask_code
    (comma_direct_action_interpret Comma_Direct_Invalid phase shift) = 0" by simp
  show "comma_parametric_typed_mask_code
    (comma_direct_action_interpret (Comma_Direct_Continue target delta) phase shift) =
      (if (delta+shift) mod 924 = 1 then Suc target else 0)"
    by (simp add: cancel cancel_suc)
  show "comma_parametric_typed_mask_code
    (comma_direct_action_interpret (Comma_Direct_Fork digit delta) phase shift) =
      (if 2 \<le> digit \<and> digit \<le> 9 \<and> shift+delta=0 then 45+digit else 0)" by simp
  show "comma_parametric_typed_mask_code
    (comma_direct_action_interpret (Comma_Direct_Landmine delta) phase shift) =
      (if shift+delta=0 then 55 else 0)" by simp
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Direct expression MDD composition"
    @{thms comma_direct_expression_entry_projected_mdd comma_direct_expression_entry_mdd
      comma_direct_expression_goto_projected_mdd comma_direct_expression_goto_mdd
      comma_direct_expression_terminal_mdd comma_direct_expression_terminal_codes};
\<close>

end
