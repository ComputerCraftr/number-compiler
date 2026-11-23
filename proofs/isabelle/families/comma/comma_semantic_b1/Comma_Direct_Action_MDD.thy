theory Comma_Direct_Action_MDD
  imports Comma_Direct_Action_Simulation
begin

text \<open>Composition of checked MDD operations over semantic expressions.
All roots are applications in the receiving table, and all shifts remain
explicit interpretation data.\<close>

text \<open>A classified Entry chart is a single natural-valued selector.  The
  selected payload is one plus the cyclotomic core value, or zero if that
  value is absent from the admitted row alphabet.  Child actions are bound
  to this shared chart later; no priority witness is part of this law.\<close>

definition comma_direct_entry_selector_code ::
  "comma_phase_core_id \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_direct_entry_selector_code core wanteds phase shift =
    foldr (\<lambda>wanted tail.
      if comma_crt_eval (phase+shift) (comma_core_value_guard core wanted)
      then Suc wanted else tail) wanteds 0"

lemma comma_direct_entry_selector_code_value:
  "comma_direct_entry_selector_code core wanteds phase shift =
    (let core_value = comma_cyclotomic_clock_core_value
       (comma_cyclotomic_clock_of (phase+shift))
       (comma_phase_core_modulus core)
     in if core_value \<in> set wanteds then Suc core_value else 0)"
  unfolding comma_direct_entry_selector_code_def
  by (induction wanteds) (auto simp: comma_core_value_guard_eval Let_def)

text \<open>The slot table is ordered by the small cyclotomic period. Missing
wanted values deliberately select zero. All source-specific shifts remain in
the final selector equation.\<close>

definition comma_phase_selector_table ::
  "comma_phase_core_id \<Rightarrow> nat list \<Rightarrow> nat list" where
  "comma_phase_selector_table core wanteds =
    map (\<lambda>slot. let value = 10^slot mod comma_phase_core_modulus core in
      if value \<in> set wanteds then Suc value else 0)
      [0..<comma_core_period (comma_phase_core_modulus core)]"

lemma comma_phase_selector_table_length:
  "length (comma_phase_selector_table core wanteds) =
    comma_core_period (comma_phase_core_modulus core)"
  by (simp add: comma_phase_selector_table_def)

lemma comma_phase_selector_table_exact:
  "comma_direct_entry_selector_code core wanteds phase shift =
    comma_phase_selector_table core wanteds !
      ((phase+shift+919) mod comma_core_period (comma_phase_core_modulus core))"
proof -
  let ?c = "comma_phase_core_modulus core"
  let ?T = "comma_core_period ?c"
  have catalog: "?c \<in> {1,3,7,11,13,21,23,27,29}"
    by (rule comma_phase_core_modulus_domain)
  have periods: "?T \<in> {1,2,3,6,22,28}"
    by (rule comma_phase_core_clock_period_small)
  have positive: "0 < ?T" using periods by auto
  have phase: "comma_cyclotomic_phase (comma_cyclotomic_clock_of (phase+shift)) ?T 919 =
      (phase+shift+919) mod ?T"
    using comma_cyclotomic_clock_projection[OF periods, of "phase+shift" 919]
    by simp
  show ?thesis
    using comma_recursive_core_residue_refines[OF catalog, of "(phase+shift+919) mod ?T"]
    by (simp add: comma_direct_entry_selector_code_value
        comma_cyclotomic_clock_core_value_def phase comma_phase_selector_table_def
        positive nth_map nth_upt Let_def)
qed

lemma comma_phase_selector_shift_congruent:
  fixes phase shift reduced T :: nat
  assumes "shift mod T = reduced mod T"
  shows "(phase+shift+919) mod T = (phase+reduced+919) mod T"
proof -
  have first: "(phase+shift) mod T = (phase+reduced) mod T"
    by (rule mod_add_cong) (simp_all add: assms)
  show ?thesis by (rule mod_add_cong) (simp_all add: first)
qed


lemma comma_phase_selector_offset:
  fixes phase shift offset T :: nat
  assumes "offset = (shift+919) mod T"
  shows "(phase+offset) mod T = (phase+shift+919) mod T"
  by (simp only: assms mod_add_right_eq add.assoc)

lemma comma_phase_selector_finite_period:
  fixes evaluate :: "nat \<Rightarrow> nat option"
  assumes positive: "0 < P"
    and divisor: "T dvd P"
    and periodic: "\<And>r. evaluate (r+P) = evaluate r"
    and rows: "list_all (\<lambda>r. evaluate r = Some (Suc (r mod T))) [0..<P]"
  shows "evaluate phase = Some (Suc (phase mod T))"
proof -
  have iterate: "\<And>r k. evaluate (r+k*P) = evaluate r"
  proof -
    fix r k
    show "evaluate (r+k*P) = evaluate r"
    proof (induction k)
      case 0
      then show ?case by simp
    next
      case (Suc k)
      have step: "evaluate ((r+k*P)+P) = evaluate (r+k*P)"
        by (rule periodic)
      show ?case using step Suc.IH by (simp add: mult.commute add.assoc add.commute add.left_commute)
    qed
  qed
  have decomposition: "phase mod P + (phase div P)*P = phase"
    using div_mult_mod_eq[of phase P] by (simp add: add.commute mult.commute)
  have phase_reduced: "evaluate phase = evaluate (phase mod P)"
    using iterate[of "phase mod P" "phase div P"] decomposition by simp
  have bound: "phase mod P < P" by (rule mod_less_divisor[OF positive])
  have row: "evaluate (phase mod P) = Some (Suc ((phase mod P) mod T))"
    using rows bound by (simp add: list_all_iff)
  show ?thesis using phase_reduced row mod_mod_cancel[OF divisor] by simp
qed

lemma comma_phase_selector_bind_exact_expanded:
  fixes nodes :: "nat comma_crt_mdd_node list"
  assumes table: "comma_crt_mdd_table_wellformed radices nodes"
    and bind: "comma_crt_mdd_bind_certificate radices nodes mapping fallback source result"
    and source: "comma_crt_mdd_eval_phase radices nodes phase source =
      Some (Suc ((phase+shift+919) mod comma_core_period (comma_phase_core_modulus core)))"
    and outputs: "\<And>i. i < comma_core_period (comma_phase_core_modulus core) \<Longrightarrow>
      comma_crt_mdd_eval_phase radices nodes phase
        (case map_of mapping (Suc i) of None \<Rightarrow> fallback | Some root \<Rightarrow> root) =
      Some (comma_phase_selector_table core wanteds ! i)"
  shows "comma_crt_mdd_eval_phase radices nodes phase result =
    Some (comma_direct_entry_selector_code core wanteds phase shift)"
proof -
  let ?T = "comma_core_period (comma_phase_core_modulus core)"
  let ?slot = "(phase+shift+919) mod ?T"
  have periods: "?T \<in> {1,2,3,6,22,28}"
    by (rule comma_phase_core_clock_period_small)
  have positive: "0 < ?T" using periods by auto
  have bound: "?slot < ?T" by (rule mod_less_divisor[OF positive])
  show ?thesis
    using comma_crt_mdd_bind_certificate_eval_phase[OF table bind, of phase]
      source outputs[OF bound] comma_phase_selector_table_exact[of core wanteds phase shift]
    by (simp add: comma_crt_mdd_bind_target_def)
qed

lemma comma_phase_selector_slot_rows:
  assumes rows: "list_all (\<lambda>i. \<forall>p. Q i p) [0..<T]"
  shows "\<And>i. i<T \<Longrightarrow> Q i phase"
  using rows by (auto simp: list_all_iff)

lemma comma_direct_entry_bind_selected:
  fixes selected_wanted :: nat and fallback_root :: nat and default_payload :: nat
    and rows :: "(nat \<times> 'a) list"
    and evaluate :: "nat \<Rightarrow> nat option"
    and child_root :: "nat \<Rightarrow> 'a \<Rightarrow> nat"
    and child_value :: "'a \<Rightarrow> nat"
  assumes children: "list_all (\<lambda>(wanted,child).
       evaluate (child_root wanted child) = Some (child_value child)) rows"
    and fallback: "evaluate fallback_root = Some default_payload"
  shows "evaluate (comma_crt_mdd_bind_target fallback_root
    (map (\<lambda>(wanted,child). (Suc wanted, child_root wanted child)) rows)
    (if selected_wanted \<in> set (map fst rows) then Suc selected_wanted else 0)) =
    Some (foldr (\<lambda>(w,child) tail. if w=selected_wanted then child_value child else tail)
      rows default_payload)"
  using children
proof (induction rows)
  case Nil
  then show ?case using fallback
    by (simp add: comma_crt_mdd_bind_target_def)
next
  case (Cons item rows)
  obtain w child where item: "item=(w,child)" by (cases item) auto
  have head: "evaluate (child_root w child) = Some (child_value child)"
    using Cons.prems by (simp add: item)
  have rest: "list_all (\<lambda>(w,c). evaluate (child_root w c) = Some (child_value c)) rows"
    using Cons.prems by (simp add: item)
  show ?case using head Cons.IH[OF rest]
    by (cases "w=selected_wanted")
       (simp_all add: item comma_crt_mdd_bind_target_def)
qed

lemma comma_direct_entry_project_fold:
  fixes selected_label :: nat and rows :: "(nat \<times> 'a) list"
    and project :: "'b \<Rightarrow> 'c" and action_of :: "'a \<Rightarrow> 'b"
    and invalid :: 'b
  shows "foldr (\<lambda>(wanted,child) tail.
    if selected_label=wanted then project (action_of child) else tail) rows (project invalid) =
   project (foldr (\<lambda>(wanted,child) tail.
    if selected_label=wanted then action_of child else tail) rows invalid)"
  by (induction rows) (auto split: prod.splits)

lemma comma_direct_expression_entry_bind_projected_rows_mdd:
  fixes project :: "comma_phase_rank_mask_action \<Rightarrow> nat"
  assumes wf: "comma_crt_mdd_table_wellformed radices nodes"
    and binding: "comma_crt_mdd_bind_certificate radices nodes
      (map (\<lambda>(wanted,child). (Suc wanted, child_root wanted child)) rows)
      fallback chart root"
    and selector: "comma_crt_mdd_eval_phase radices nodes phase chart =
      Some (comma_direct_entry_selector_code core (map fst rows) phase shift)"
    and children: "list_all (\<lambda>(wanted,child).
      comma_crt_mdd_eval_phase radices nodes phase (child_root wanted child) =
        Some (project (comma_direct_action_interpret child phase shift))) rows"
    and fallback: "comma_crt_mdd_eval_phase radices nodes phase fallback =
      Some (project Comma_Phase_Rank_Mask_Invalid)"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (project (comma_direct_action_interpret
      (Comma_Direct_Entry core rows) phase shift))"
proof -
  let ?v = "comma_cyclotomic_clock_core_value
    (comma_cyclotomic_clock_of (phase+shift)) (comma_phase_core_modulus core)"
  have selected: "comma_crt_mdd_eval_phase radices nodes phase
      (comma_crt_mdd_bind_target fallback
        (map (\<lambda>(wanted,child). (Suc wanted, child_root wanted child)) rows)
        (if ?v \<in> set (map fst rows) then Suc ?v else 0)) =
    Some (foldr (\<lambda>(wanted,child) tail.
      if wanted=?v then project (comma_direct_action_interpret child phase shift)
      else tail) rows (project Comma_Phase_Rank_Mask_Invalid))"
    by (rule comma_direct_entry_bind_selected[OF children fallback])
  have chart_value: "comma_direct_entry_selector_code core (map fst rows)
      phase shift = (if ?v \<in> set (map fst rows) then Suc ?v else 0)"
    by (simp only: comma_direct_entry_selector_code_value Let_def)
  have result: "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (foldr (\<lambda>(wanted,child) tail.
      if wanted=?v then project (comma_direct_action_interpret child phase shift)
      else tail) rows (project Comma_Phase_Rank_Mask_Invalid))"
    using comma_crt_mdd_bind_certificate_eval_phase[OF wf binding]
      selector selected chart_value by simp
  have selected_order: "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (foldr (\<lambda>(wanted,child) tail.
      if ?v=wanted then project (comma_direct_action_interpret child phase shift)
      else tail) rows (project Comma_Phase_Rank_Mask_Invalid))"
    using result by (simp add: eq_commute)
  have projection: "foldr (\<lambda>(wanted,child) tail.
      if ?v=wanted then project (comma_direct_action_interpret child phase shift)
      else tail) rows (project Comma_Phase_Rank_Mask_Invalid) =
    project (comma_direct_action_interpret (Comma_Direct_Entry core rows) phase shift)"
    using comma_direct_entry_project_fold[where selected_label="?v" and rows=rows
      and project=project and action_of="\<lambda>child. comma_direct_action_interpret child phase shift"
      and invalid=Comma_Phase_Rank_Mask_Invalid]
    by (simp only: comma_direct_action_interpret.simps comma_core_value_guard_eval)
  show ?thesis using selected_order projection by simp
qed

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


text \<open>Application equivalence is separate from occurrence duration. A
single complete row is an alias only when its guard is true for every phase;
the original shift is retained unchanged. The guard premise is checked from
the concrete core and complete ordered support, not guessed from a sample.\<close>
lemma comma_direct_core_one_guard:
  "comma_crt_eval clock (comma_core_value_guard Comma_Core_1 0)"
  by (simp add: comma_core_value_guard_eval comma_cyclotomic_clock_core_value_def
      comma_recursive_core_residue_def)

lemma comma_direct_core_three_guard:
  "comma_crt_eval clock (comma_core_value_guard Comma_Core_3 1)"
  by (simp add: comma_core_value_guard_eval comma_cyclotomic_clock_core_value_def
      comma_recursive_core_residue_def)

lemma comma_direct_period_one_support:
  "comma_core_supported_values Comma_Core_1 = [0]"
  "comma_core_supported_values Comma_Core_3 = [1]"
  by (simp_all add: upt_rec comma_core_supported_values_local_period comma_core_period_def
      comma_cyclotomic_clock_core_value_def comma_recursive_core_residue_def)

lemma comma_direct_single_row_alias:
  assumes guard: "\<And>clock. comma_crt_eval clock (comma_core_value_guard core wanted)"
  shows "comma_direct_action_interpret
      (Comma_Direct_Entry core [(wanted, Comma_Direct_Goto child 0)]) phase shift =
    comma_direct_action_interpret child phase shift"
  using guard by simp

lemma comma_direct_single_row_alias_mdd:
  assumes guard: "\<And>clock. comma_crt_eval clock (comma_core_value_guard core wanted)"
    and child: "comma_crt_mdd_eval_phase radices nodes phase root =
      Some (project (comma_direct_action_interpret child phase shift))"
  shows "comma_crt_mdd_eval_phase radices nodes phase root =
    Some (project (comma_direct_action_interpret
      (Comma_Direct_Entry core [(wanted, Comma_Direct_Goto child 0)]) phase shift))"
  using child comma_direct_single_row_alias[OF guard, of child phase shift] by simp

text \<open>Physical source authentication remains a receiving fact. The
projected-action cache carries the evaluation theorem and leaves every
source occurrence weight with its original owner.\<close>
lemma comma_direct_period_one_physical_and_projected:
  assumes canonical: "comma_canonical_position_admitted (Comma_Entry f 0 x)"
    and admitted: "comma_round_admitted (Comma_Entry f 0 x)"
    and period: "comma_decisive_sector_period (Comma_Entry f 0 x) = 1"
    and port: "comma_semantic_b1_entry_near_port_action f x 0 =
      Comma_Continuation_Goto source 0"
    and binding: "comma_semantic_port_program_of_source source = Some program"
    and relation: "comma_direct_program_relation program child"
    and guard: "\<And>clock. comma_crt_eval clock (comma_core_value_guard core wanted)"
    and evaluation: "comma_crt_mdd_eval_phase radices nodes phase root =
      Some (project (comma_direct_action_interpret child phase shift))"
  shows "comma_phase_program_action_at_source phase (Comma_Entry f 0 x) =
      Some (Comma_Continuation_Goto source 0) \<and>
    comma_crt_mdd_eval_phase radices nodes phase root =
      Some (project (comma_direct_action_interpret
        (Comma_Direct_Entry core [(wanted, Comma_Direct_Goto child 0)]) phase shift)) \<and>
    comma_direct_action_interpret child phase shift =
      comma_phase_program_full_action_of_source_action phase shift
        (Comma_Continuation_Goto source 0)"
proof -
  have action: "comma_source_continuation_action_at (Comma_Entry f 0 x) phase =
      Comma_Continuation_Goto source 0"
    by (rule comma_semantic_b1_entry_period_one_direct_goto_action[OF admitted period port])
  have physical: "comma_phase_program_action_at_source phase (Comma_Entry f 0 x) =
      Some (Comma_Continuation_Goto source 0)"
    using comma_phase_program_action_at_source_exact[OF canonical admitted, of phase]
      comma_source_continuation_signature_slot[OF admitted, of phase] action by simp
  have projected: "comma_crt_mdd_eval_phase radices nodes phase root =
      Some (project (comma_direct_action_interpret
        (Comma_Direct_Entry core [(wanted, Comma_Direct_Goto child 0)]) phase shift))"
    using evaluation comma_direct_single_row_alias[OF guard, of child phase shift] by simp
  have child: "comma_direct_action_interpret child phase shift =
      comma_phase_program_full_action_of_source_action phase shift
        (Comma_Continuation_Goto source 0)"
    using comma_direct_relation_sound(1)[OF relation, of phase shift] binding
    by (simp add: comma_phase_program_full_action_of_source_action_def)
  show ?thesis using physical projected child by blast
qed

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Direct expression MDD composition"
    @{thms comma_direct_period_one_support comma_direct_single_row_alias_mdd
      comma_direct_period_one_physical_and_projected
      comma_phase_selector_table_exact comma_phase_selector_offset
      comma_phase_selector_finite_period comma_phase_selector_bind_exact_expanded
      comma_phase_selector_slot_rows
      comma_direct_expression_entry_bind_projected_rows_mdd
      comma_direct_expression_entry_projected_mdd comma_direct_expression_entry_mdd
      comma_direct_expression_goto_projected_mdd comma_direct_expression_goto_mdd
      comma_direct_expression_terminal_mdd comma_direct_expression_terminal_codes};
\<close>

end
