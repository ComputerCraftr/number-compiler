theory Comma_Direct_Action_Simulation
  imports Comma_Direct_Action_Constructors
begin

lemma comma_direct_core_guard_import:
  assumes target_wf: "comma_crt_mdd_table_wellformed [3,4,7,11] nodes"
    and imported: "comma_crt_mdd_root_map_certificate [3,4,7,11]
      (comma_frontier24_core_guard_nodes core wanted) nodes
      (\<lambda>b. if b then 1 else 0) (comma_frontier24_core_guard_root core) root"
  shows "comma_crt_mdd_eval_phase [3,4,7,11] nodes phase root =
    Some (if comma_crt_eval phase (comma_core_value_guard core wanted) then 1 else 0)"
  using comma_crt_mdd_root_map_certificate_eval_phase
    [OF comma_frontier24_core_guard_nodes_wellformed target_wf imported]
    comma_frontier24_core_guard_phase_eval[of core wanted phase]
  by simp

text \<open>The relation is a checked finite semantic constructor graph. Its
source bindings are independent of MDD root identities and accumulated shift.\<close>

inductive comma_direct_program_relation ::
    "comma_semantic_port_program \<Rightarrow> comma_direct_action_expression \<Rightarrow> bool"
  and comma_direct_source_relation ::
    "comma_source_continuation_action \<Rightarrow> comma_direct_action_expression \<Rightarrow> bool" where
  entry:
    "comma_phase_program_structurally_admitted (Comma_Entry_Core_Program f d residue core) \<Longrightarrow>
     (\<And>wanted. wanted \<in> set (comma_core_supported_values core) \<Longrightarrow>
       comma_direct_source_relation
         (comma_phase_program_entry_core_value_action f residue core wanted) (children wanted)) \<Longrightarrow>
     comma_direct_program_relation (Comma_Entry_Core_Program f d residue core)
       (Comma_Direct_Entry core (map (\<lambda>wanted. (wanted, children wanted))
         (comma_core_supported_values core)))"
| near:
    "(\<And>phase shift. comma_phase_program_step_at program phase shift =
       comma_phase_program_step_of_action (comma_source_continuation_transport shift action)) \<Longrightarrow>
     comma_direct_source_relation action expression \<Longrightarrow>
     comma_direct_program_relation program expression"
| goto:
    "comma_semantic_port_program_of_source source = Some program \<Longrightarrow>
     comma_direct_program_relation program expression \<Longrightarrow>
     comma_direct_source_relation (Comma_Continuation_Goto source delta)
       (Comma_Direct_Goto expression delta)"
| exit_admitted:
    "comma_decade_root_admitted (Comma_Entry f source_delta off) \<Longrightarrow>
     comma_direct_source_relation (Comma_Continuation_Exit (Comma_Entry f source_delta off) delta)
       (Comma_Direct_Continue (comma_offset_orbit off) (source_delta+delta))"
| exit_invalid:
    "\<not> comma_decade_root_admitted source \<Longrightarrow>
     comma_direct_source_relation (Comma_Continuation_Exit source delta) Comma_Direct_Invalid"
| fork:
    "comma_direct_source_relation (Comma_Continuation_Fork digit delta)
      (Comma_Direct_Fork digit delta)"
| landmine:
    "comma_direct_source_relation (Comma_Continuation_Landmine delta)
      (Comma_Direct_Landmine delta)"
| invalid:
    "comma_direct_source_relation Comma_Continuation_Invalid Comma_Direct_Invalid"

lemma comma_direct_program_entry_rows:
  assumes admitted: "comma_phase_program_structurally_admitted (Comma_Entry_Core_Program f d residue core)"
    and support: "map fst rows = comma_core_supported_values core"
    and unique: "distinct (map fst rows)"
    and relations: "list_all (\<lambda>(wanted,child). comma_direct_source_relation
      (comma_phase_program_entry_core_value_action f residue core wanted) child) rows"
  shows "comma_direct_program_relation (Comma_Entry_Core_Program f d residue core)
    (Comma_Direct_Entry core rows)"
proof -
  let ?child = "\<lambda>w. the (map_of rows w)"
  have selected: "?child wanted = child" if "(wanted,child) \<in> set rows" for wanted child
    using map_of_is_SomeI[OF unique that] by simp
  have shape: "map (\<lambda>w. (w, ?child w)) (comma_core_supported_values core) = rows"
    unfolding support[symmetric] map_map comp_def
  proof (rule map_idI)
    fix row
    assume member: "row \<in> set rows"
    obtain wanted child where row: "row = (wanted, child)" by (cases row) auto
    have pair_member: "(wanted, child) \<in> set rows" using member unfolding row .
    show "(fst row, ?child (fst row)) = row"
      unfolding row fst_conv selected[OF pair_member] by (rule refl)
  qed
  have children: "comma_direct_source_relation
      (comma_phase_program_entry_core_value_action f residue core wanted) (?child wanted)"
    if "wanted \<in> set (comma_core_supported_values core)" for wanted
  proof -
    have "wanted \<in> fst ` set rows"
      using that unfolding support[symmetric] set_map .
    then obtain row where member: "row \<in> set rows" and key: "fst row = wanted"
      by (elim imageE) (simp add: eq_commute)
    have pair: "(wanted, snd row) \<in> set rows" using member by (simp add: key[symmetric])
    have checked: "comma_direct_source_relation
        (comma_phase_program_entry_core_value_action f residue core wanted) (snd row)"
      using relations pair by (auto simp: list_all_iff)
    show ?thesis unfolding selected[OF pair] by (rule checked)
  qed
  show ?thesis using comma_direct_program_relation_comma_direct_source_relation.entry[OF admitted children]
    by (simp only: shape)
qed

lemma comma_direct_relation_sound_all:
  shows "comma_direct_program_relation program expression \<Longrightarrow>
      \<forall>phase shift. comma_direct_action_interpret expression phase shift =
        comma_semantic_phase_program_fold comma_phase_program_full_action_output phase program shift"
    and "comma_direct_source_relation action expression \<Longrightarrow>
      \<forall>phase shift. comma_direct_action_interpret expression phase shift =
        comma_phase_program_full_action_of_source_action phase shift action"
proof (induction rule: comma_direct_program_relation_comma_direct_source_relation.inducts)
  case (entry f d residue core children)
  show ?case
  proof (intro allI)
    fix phase shift
    show "comma_direct_action_interpret
      (Comma_Direct_Entry core (map (\<lambda>wanted. (wanted,children wanted))
        (comma_core_supported_values core))) phase shift =
      comma_semantic_phase_program_fold comma_phase_program_full_action_output phase
        (Comma_Entry_Core_Program f d residue core) shift"
    proof (rule comma_direct_action_entry_interpret[OF entry.hyps(1)])
      fix wanted
      assume member: "wanted \<in> set (comma_core_supported_values core)"
      show "comma_direct_action_interpret (children wanted) phase shift =
        comma_phase_program_full_action_of_source_action phase shift
          (comma_phase_program_entry_core_value_action f residue core wanted)"
        by (rule entry.IH[OF member, rule_format])
    qed
  qed
next
  case (near program action expression)
  show ?case
  proof (intro allI)
    fix phase shift
    show "comma_direct_action_interpret expression phase shift =
      comma_semantic_phase_program_fold comma_phase_program_full_action_output phase program shift"
      using near.IH[rule_format, of phase shift]
        comma_direct_action_program_step[OF near.hyps(1)[of phase shift]] by simp
  qed
next
  case (goto source program expression delta)
  show ?case
  proof (intro allI)
    fix phase shift
    show "comma_direct_action_interpret (Comma_Direct_Goto expression delta) phase shift =
      comma_phase_program_full_action_of_source_action phase shift (Comma_Continuation_Goto source delta)"
      using goto.IH[rule_format, of phase "shift+delta"] goto.hyps(1)
      by (simp add: comma_phase_program_full_action_of_source_action_def)
  qed
next
  case (exit_admitted f source_delta off delta)
  show ?case using comma_direct_action_exit_normalization[OF exit_admitted.hyps] by simp
next
  case (exit_invalid source delta)
  show ?case using comma_direct_action_exit_invalid[OF exit_invalid.hyps] by simp
next
  case (fork digit delta)
  show ?case using comma_direct_action_terminal_normalization(1) by simp
next
  case (landmine delta)
  show ?case using comma_direct_action_terminal_normalization(2) by simp
next
  case invalid
  show ?case using comma_direct_action_terminal_normalization(3) by simp
qed

lemmas comma_direct_relation_sound = comma_direct_relation_sound_all[rule_format]

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Direct program and source simulation"
    @{thms comma_direct_core_guard_import comma_direct_relation_sound};
\<close>

end
