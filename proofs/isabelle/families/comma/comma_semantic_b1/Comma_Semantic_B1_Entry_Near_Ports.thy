theory Comma_Semantic_B1_Entry_Near_Ports
  imports Comma_C1_B1_Source_Action Comma_Semantic_B1_Guarded_Port_Action
begin

text \<open>
For an admitted normalized Entry, each source selector slot is transported
through the C1 Entry bridge to its exact decisive closed-Near endpoint.
These lemmas expose that finite local-period formula to the graph producer;
the terminal headroom remains an occurrence coordinate, not a semantic ID.
The theorem uses the physical exponent 924+slot only to witness the
selector residue.  It does not merge the physical C1 clock or its weighted
carry with the 924 selector clock.
\<close>

definition comma_semantic_b1_entry_near_terminal ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_semantic_b1_entry_near_terminal f offset slot =
    snd (comma_near_closed_germ f
      (comma_finite_headroom f slot 0 offset))"

definition comma_semantic_b1_entry_near_port_action ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action" where
  "comma_semantic_b1_entry_near_port_action f offset slot =
    comma_semantic_b1_near_control_port_action f 0
      (comma_semantic_b1_entry_near_terminal f offset slot)"

lemma comma_semantic_b1_entry_slot_decisive_near:
  fixes f offset slot :: nat
  assumes admitted: "comma_round_admitted (Comma_Entry f 0 offset)"
    and slot: "slot < comma_decisive_sector_period (Comma_Entry f 0 offset)"
  shows "comma_decisive_sector_target slot (Comma_Entry f 0 offset) =
    Comma_Near f 0 (comma_semantic_b1_entry_near_terminal f offset slot)"
proof -
  have sector: "1 \<le> f" "f \<le> 9" using admitted by simp_all
  have offset: "offset \<le> 98" using admitted by simp
  have period_divides:
      "comma_decisive_sector_period (Comma_Entry f 0 offset) dvd 924"
    using comma_decisive_sector_period_admitted(2)[OF admitted] .
  have period_le:
      "comma_decisive_sector_period (Comma_Entry f 0 offset) \<le> 924"
    using dvd_imp_le[OF period_divides] by simp
  have slot_lt_924: "slot < 924" using slot period_le by arith
  have phase: "(slot + 924) mod 924 = slot"
    using slot_lt_924 by simp
  let ?headroom =
    "comma_finite_headroom f ((slot + 924) mod 924) 0 offset"
  have bridge:
      "comma_python_entry_b1_slot_matches (slot + 924) f 0 offset
        (Comma_Near f 0 ?headroom)"
    by (rule comma_c1_entry_b1_slot_bridge[OF sector(1) sector(2)
      _ offset]) simp
  have endpoint:
      "comma_decisive_sector_target ((slot + 924) mod 924)
          (Comma_Entry f 0 offset) =
        Comma_Near f 0
          (snd (comma_near_closed_germ f ?headroom))"
    using bridge
    by (auto simp: comma_python_entry_b1_slot_matches_def Let_def)
  show ?thesis
    using endpoint phase
    by (simp add: comma_semantic_b1_entry_near_terminal_def)
qed

lemma comma_semantic_b1_entry_slot_action_near:
  fixes f offset slot :: nat
  assumes admitted: "comma_round_admitted (Comma_Entry f 0 offset)"
    and slot: "slot < comma_decisive_sector_period (Comma_Entry f 0 offset)"
  shows "comma_semantic_b1_source_port_action (Comma_Entry f 0 offset) slot =
    comma_semantic_b1_entry_near_port_action f offset slot"
  using comma_semantic_b1_entry_slot_decisive_near[OF admitted slot]
  by (simp add: comma_semantic_b1_source_port_action_def
      comma_semantic_b1_entry_near_port_action_def
      comma_source_continuation_base.simps)

lemma comma_semantic_b1_entry_source_ports_near:
  fixes f offset :: nat
  assumes admitted: "comma_round_admitted (Comma_Entry f 0 offset)"
  shows "comma_semantic_b1_source_port_actions (Comma_Entry f 0 offset) =
    map (comma_semantic_b1_entry_near_port_action f offset)
      [0..<comma_decisive_sector_period (Comma_Entry f 0 offset)]"
proof -
  let ?period = "comma_decisive_sector_period (Comma_Entry f 0 offset)"
  have pointwise:
    "\<And>slot. slot \<in> set [0..<?period] \<Longrightarrow>
      comma_semantic_b1_source_port_action (Comma_Entry f 0 offset) slot =
        comma_semantic_b1_entry_near_port_action f offset slot"
  proof -
    fix slot
    assume slot: "slot \<in> set [0..<?period]"
    have bound: "slot < ?period" using slot by simp
    show "comma_semantic_b1_source_port_action (Comma_Entry f 0 offset) slot =
        comma_semantic_b1_entry_near_port_action f offset slot"
      by (rule comma_semantic_b1_entry_slot_action_near[OF admitted bound])
  qed
  show ?thesis
    unfolding comma_semantic_b1_source_port_actions_def
      comma_source_continuation_base.simps
    by (rule map_cong[OF refl]) (rule pointwise)
qed

lemma comma_semantic_b1_source_action_at_port:
  fixes source :: comma_finite_position and phase :: nat
  assumes admitted: "comma_round_admitted source"
    and phase: "phase < comma_decisive_sector_period
      (comma_source_continuation_base source)"
  shows "comma_source_continuation_action_at source phase =
    comma_semantic_b1_source_port_action source phase"
proof -
  let ?period = "comma_decisive_sector_period
    (comma_source_continuation_base source)"
  have positive: "0 < ?period"
    by (rule comma_decisive_sector_period_admitted(1)
      [OF comma_source_continuation_base_admitted[OF admitted]])
  have ports:
    "comma_source_continuation_id source =
      (?period, comma_semantic_b1_source_port_actions source)"
    by (rule comma_semantic_b1_source_id_ports[OF admitted])
  show ?thesis using ports phase positive
    by (simp add: comma_source_continuation_action_at_def
        comma_semantic_b1_source_port_actions_def)
qed

text \<open>
Offsets that agree modulo the checked finite period at a fixed leading
sector have the same complete local control-port row.  This is a genuine
pre-evaluation transport law: its assumptions are scalar source coordinates,
not an already constructed action list or graph-validity fact.  It does not
identify physical elapsed time or weighted carry.
\<close>

lemma comma_semantic_b1_entry_headroom_modular_rebase:
  fixes f x y slot :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and digit: "x mod 10 = y mod 10"
    and residue:
      "x mod (comma_finite_period_fast f (x mod 10)) =
       y mod (comma_finite_period_fast f (x mod 10))"
  shows "comma_finite_headroom f slot 0 x =
    comma_finite_headroom f slot 0 y"
proof -
  let ?P = "comma_finite_period f (x mod 10)"
  let ?power = "comma_power_residue ?P (slot mod 924)"
  let ?e = "comma_finite_guard_extra f"
  have dx: "x mod 10 < 10" by simp
  have dy: "y mod 10 < 10" by simp
  have fast_x: "comma_finite_period_fast f (x mod 10) = ?P"
    by (rule comma_finite_period_fast_correct[OF sector dx])
  have exact_period: "comma_finite_period f (y mod 10) = ?P"
    using digit by simp
  have residue_exact: "x mod ?P = y mod ?P"
    using residue by (simp only: fast_x)
  have int_residue: "int x mod int ?P = int y mod int ?P"
  proof -
    have cast: "int (x mod ?P) = int (y mod ?P)"
      by (rule arg_cong[where f="\<lambda>n::nat. int n", OF residue_exact])
    show ?thesis using cast
      by (simp only: of_nat_mod of_nat_numeral of_nat_0 of_nat_1)
  qed
  have remainder:
    "(int ?power - int x - int (1 + ?e)) mod int ?P =
     (int ?power - int y - int (1 + ?e)) mod int ?P"
  proof -
    have first:
      "(int ?power - int x) mod int ?P =
       (int ?power - int y) mod int ?P"
      by (rule mod_diff_cong[OF refl int_residue])
    show ?thesis by (rule mod_diff_cong[OF first refl])
  qed
  have left:
    "comma_finite_headroom f slot 0 x =
     1 + ?e + nat ((int ?power - int x - int (1 + ?e)) mod int ?P)"
    by (simp add: comma_finite_headroom_def Let_def)
  have right:
    "comma_finite_headroom f slot 0 y =
     1 + ?e + nat ((int ?power - int y - int (1 + ?e)) mod int ?P)"
    using exact_period
    by (simp add: comma_finite_headroom_def Let_def)
  show ?thesis using left right remainder by simp
qed

lemma comma_semantic_b1_entry_control_port_modular_rebase:
  fixes f x y slot :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and digit: "x mod 10 = y mod 10"
    and residue:
      "x mod (comma_finite_period_fast f (x mod 10)) =
       y mod (comma_finite_period_fast f (x mod 10))"
  shows "comma_semantic_b1_entry_near_port_action f x slot =
    comma_semantic_b1_entry_near_port_action f y slot"
  using comma_semantic_b1_entry_headroom_modular_rebase[OF sector digit residue]
  by (simp add: comma_semantic_b1_entry_near_port_action_def
      comma_semantic_b1_entry_near_terminal_def)

lemma comma_semantic_b1_entry_local_period_modular_rebase:
  fixes f x y :: nat
  assumes digit: "x mod 10 = y mod 10"
  shows "comma_decisive_sector_period (Comma_Entry f 0 x) =
    comma_decisive_sector_period (Comma_Entry f 0 y)"
  using digit by (simp add: comma_decisive_sector_period_def)

lemma comma_semantic_b1_entry_source_id_modular_rebase:
  fixes f x y :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and x_bound: "x \<le> 98" and y_bound: "y \<le> 98"
    and digit: "x mod 10 = y mod 10"
    and residue:
      "x mod (comma_finite_period_fast f (x mod 10)) =
       y mod (comma_finite_period_fast f (x mod 10))"
  shows "comma_source_continuation_id (Comma_Entry f 0 x) =
         comma_source_continuation_id (Comma_Entry f 0 y)"
proof -
  have admitted_x: "comma_round_admitted (Comma_Entry f 0 x)"
    using sector x_bound by simp
  have admitted_y: "comma_round_admitted (Comma_Entry f 0 y)"
    using sector y_bound by simp
  let ?Tx = "comma_decisive_sector_period (Comma_Entry f 0 x)"
  let ?Ty = "comma_decisive_sector_period (Comma_Entry f 0 y)"
  have period: "?Tx = ?Ty"
    by (rule comma_semantic_b1_entry_local_period_modular_rebase[OF digit])
  have ports_x:
    "comma_semantic_b1_source_port_actions (Comma_Entry f 0 x) =
      map (comma_semantic_b1_entry_near_port_action f x) [0..<?Tx]"
    by (rule comma_semantic_b1_entry_source_ports_near[OF admitted_x])
  have ports_y:
    "comma_semantic_b1_source_port_actions (Comma_Entry f 0 y) =
      map (comma_semantic_b1_entry_near_port_action f y) [0..<?Ty]"
    by (rule comma_semantic_b1_entry_source_ports_near[OF admitted_y])
  have mapped:
    "map (comma_semantic_b1_entry_near_port_action f x) [0..<?Tx] =
     map (comma_semantic_b1_entry_near_port_action f y) [0..<?Tx]"
  proof (rule map_cong[OF refl])
    fix slot
    assume "slot \<in> set [0..<?Tx]"
    show "comma_semantic_b1_entry_near_port_action f x slot =
      comma_semantic_b1_entry_near_port_action f y slot"
      by (rule comma_semantic_b1_entry_control_port_modular_rebase
        [OF sector digit residue])
  qed
  have id_x:
    "comma_source_continuation_id (Comma_Entry f 0 x) =
      (?Tx, comma_semantic_b1_source_port_actions (Comma_Entry f 0 x))"
    using comma_semantic_b1_source_id_ports[OF admitted_x]
    by (simp add: comma_source_continuation_base.simps)
  have id_y:
    "comma_source_continuation_id (Comma_Entry f 0 y) =
      (?Ty, comma_semantic_b1_source_port_actions (Comma_Entry f 0 y))"
    using comma_semantic_b1_source_id_ports[OF admitted_y]
    by (simp add: comma_source_continuation_base.simps)
  show ?thesis using id_x id_y ports_x ports_y mapped period by simp
qed

lemma comma_semantic_b1_entry_modular_rebase_f5_0_60:
  "comma_source_continuation_id (Comma_Entry 5 0 0) =
   comma_source_continuation_id (Comma_Entry 5 0 60)"
proof -
  have sector: "(1::nat) \<le> 5" "(5::nat) \<le> 9" by simp_all
  have admitted_x: "comma_round_admitted (Comma_Entry 5 0 0)" by simp
  have admitted_y: "comma_round_admitted (Comma_Entry 5 0 60)" by simp
  have x_bound: "(0::nat) \<le> 98" using admitted_x by simp
  have y_bound: "(60::nat) \<le> 98" using admitted_y by simp
  have digit: "(0::nat) mod 10 = 60 mod 10" by simp
  have period: "comma_finite_period_fast 5 (0 mod 10) = 60"
    by (simp add: comma_finite_period_fast_def)
  have residue:
    "0 mod (comma_finite_period_fast 5 (0 mod 10)) =
     60 mod (comma_finite_period_fast 5 (0 mod 10))"
    using period by simp
  show ?thesis
    by (rule comma_semantic_b1_entry_source_id_modular_rebase
      [OF sector(1) sector(2) x_bound y_bound digit residue])
qed

lemma comma_semantic_b1_entry_modular_rebase_f1_0_10_same_digit_period_distinct_residue:
  "(0::nat) mod 10 = 10 mod 10"
  "comma_finite_period_fast 1 (0 mod 10) = 460"
  "comma_finite_period_fast 1 (10 mod 10) = 460"
  "(0::nat) mod 460 \<noteq> 10 mod 460"
  by (tactic \<open>
    ALLGOALS (simp_tac
      (Simplifier.add_simps (@{thms comma_finite_period_fast_def nth_Cons'}) (Comma_Entry_Arithmetic.natural_context @{context})))
  \<close>)

lemma comma_semantic_b1_entry_modular_rebase_f1_0_10_different_ports:
  "comma_semantic_b1_entry_near_port_action 1 0 0 \<noteq>
   comma_semantic_b1_entry_near_port_action 1 10 0"
proof -
  have headroom_x: "comma_finite_headroom 1 0 0 0 = 300"
  proof -
    have fast: "comma_finite_headroom_fast 1 0 0 0 = 300"
      by (tactic \<open>simp_tac
        (Simplifier.add_simps (@{thms comma_finite_headroom_fast_def comma_finite_period_fast_def
            comma_power_residue_fast_def comma_power_table_def comma_short_period_def
            nth_Cons' of_nat_numeral of_nat_0 of_nat_1
            zmod_zminus1_eq_if zmod_zminus2_eq_if}) (Comma_Entry_Arithmetic.natural_context @{context})) 1\<close>)
    have correct:
      "comma_finite_headroom_fast 1 0 0 0 = comma_finite_headroom 1 0 0 0"
      by (rule comma_finite_headroom_fast_correct) simp_all
    show ?thesis using fast correct by simp
  qed
  have headroom_y: "comma_finite_headroom 1 0 0 10 = 290"
  proof -
    have fast: "comma_finite_headroom_fast 1 0 0 10 = 290"
      by (tactic \<open>simp_tac
        (Simplifier.add_simps (@{thms comma_finite_headroom_fast_def comma_finite_period_fast_def
            comma_power_residue_fast_def comma_power_table_def comma_short_period_def
            nth_Cons' of_nat_numeral of_nat_0 of_nat_1
            zmod_zminus1_eq_if zmod_zminus2_eq_if}) (Comma_Entry_Arithmetic.natural_context @{context})) 1\<close>)
    have correct:
      "comma_finite_headroom_fast 1 0 0 10 = comma_finite_headroom 1 0 0 10"
      by (rule comma_finite_headroom_fast_correct) simp_all
    show ?thesis using fast correct by simp
  qed
  have germ_x: "snd (comma_near_closed_germ 1 300) = 12"
    by (tactic \<open>simp_tac (Comma_Fast_Kernel.context @{context}) 1\<close>)
  have germ_y: "snd (comma_near_closed_germ 1 290) = 2"
    by (tactic \<open>simp_tac (Comma_Fast_Kernel.context @{context}) 1\<close>)
  show ?thesis using headroom_x headroom_y germ_x germ_y
    by (simp add: comma_semantic_b1_entry_near_port_action_def
        comma_semantic_b1_entry_near_terminal_def
        comma_semantic_b1_near_control_port_action_def
        comma_semantic_b1_next_port_action_def comma_round_crossing_def Let_def)
qed

text \<open>
A period-one normalized Entry has one pointwise source action.  If its direct
Entry/Near port formula gives a zero-shift Goto, this theorem transports that
formula to every continuation clock without constructing a materialized port
list or graph-validity premise.  Period one here is only the parent's selector
period; it says nothing about the child's completed-return period.
\<close>

lemma comma_semantic_b1_entry_period_one_direct_goto_action:
  fixes f x :: nat and child :: comma_finite_position and clock :: nat
  assumes admitted:
      "comma_round_admitted (Comma_Entry f 0 x)"
    and period:
      "comma_decisive_sector_period (Comma_Entry f 0 x) = 1"
    and direct_port:
      "comma_semantic_b1_entry_near_port_action f x 0 =
        Comma_Continuation_Goto child 0"
  shows "comma_source_continuation_action_at
      (Comma_Entry f 0 x) clock = Comma_Continuation_Goto child 0"
proof -
  let ?source = "Comma_Entry f 0 x"
  let ?period = "comma_decisive_sector_period ?source"
  have base: "comma_source_continuation_base ?source = ?source" by simp
  have base_period:
      "comma_decisive_sector_period
          (comma_source_continuation_base ?source) = 1"
    using period base by simp
  have phase_zero: "clock mod ?period=0" using period by simp
  have source_phase_bound: "clock mod ?period < ?period"
    using period by simp
  have base_phase_bound:
      "clock mod ?period < comma_decisive_sector_period
        (comma_source_continuation_base ?source)"
    using source_phase_bound base by simp
  have source_port:
      "comma_source_continuation_action_at ?source (clock mod ?period) =
        comma_semantic_b1_source_port_action ?source (clock mod ?period)"
    by (rule comma_semantic_b1_source_action_at_port
      [OF admitted base_phase_bound])
  have entry_port:
      "comma_semantic_b1_source_port_action ?source (clock mod ?period) =
        comma_semantic_b1_entry_near_port_action f x (clock mod ?period)"
    by (rule comma_semantic_b1_entry_slot_action_near
      [OF admitted source_phase_bound])
  have clock_reduction:
      "comma_source_continuation_action_at ?source clock =
        comma_source_continuation_action_at ?source (clock mod ?period)"
    by (simp add: comma_source_continuation_action_at_def
      comma_source_continuation_id_def Let_def
      comma_source_continuation_base.simps period)
  show ?thesis
    using clock_reduction source_port entry_port phase_zero direct_port
    by simp
qed

text \<open>
The source-slot round theorem already follows the exact endpoint packet and
crossing recurrence.  Reusing it here gives completed-return equality; the
DAG's existing Goto-decrease theorem separately supplies the strict-sector
fact needed by a bottom-up representative lookup.  Both observations use the
same original phase; in particular the child is evaluated at `phase`, not at
`phase mod parent_period` (which would erase the clock when that period is 1).
\<close>

lemma comma_semantic_b1_entry_period_one_direct_goto_completed:
  fixes f x :: nat and child :: comma_finite_position
  assumes admitted:
      "comma_round_admitted (Comma_Entry f 0 x)"
    and period:
      "comma_decisive_sector_period (Comma_Entry f 0 x) = 1"
    and direct_port:
      "comma_semantic_b1_entry_near_port_action f x 0 =
        Comma_Continuation_Goto child 0"
  shows "(\<forall>phase.
      comma_semantic_b1_round_output phase (Comma_Entry f 0 x) =
        comma_semantic_b1_round_output phase child)
    \<and> comma_round_admitted child
    \<and> 9-comma_sector_number child <
      9-comma_sector_number (Comma_Entry f 0 x)"
proof -
  let ?source = "Comma_Entry f 0 x"
  have base: "?source=comma_source_continuation_base ?source" by simp
  have period_source:
      "comma_decisive_sector_period ?source=1" using period .
  have action_at_zero:
      "comma_source_continuation_action_at ?source 0 =
        Comma_Continuation_Goto child 0"
    by (rule comma_semantic_b1_entry_period_one_direct_goto_action
      [OF admitted period direct_port])
  have packet_action:
      "comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet 0 ?source) =
          Comma_Continuation_Goto child 0"
  proof -
    have signature:
      "comma_source_continuation_action_at ?source 0 =
        comma_source_continuation_action_of_packet
          (comma_decisive_endpoint_packet 0
            (comma_source_continuation_base ?source))"
      by (rule comma_source_continuation_signature_slot[OF admitted])
    show ?thesis using signature action_at_zero base by simp
  qed
  have child_rank:
      "comma_round_admitted child \<and>
        9-comma_sector_number child < 9-comma_sector_number ?source"
    by (rule comma_source_continuation_goto_decreases[OF admitted packet_action])
  have slot_action:
      "comma_semantic_b1_source_slot_action ?source 0 =
        Comma_Continuation_Goto child 0"
  proof -
    have exact:
      "comma_semantic_b1_source_slot_action ?source 0 =
        comma_source_continuation_action_at ?source 0"
      by (rule comma_semantic_b1_source_slot_action_refines[OF admitted])
    show ?thesis using exact action_at_zero by simp
  qed
  show ?thesis
  proof (intro conjI)
    show "\<forall>phase.
        comma_semantic_b1_round_output phase ?source =
          comma_semantic_b1_round_output phase child"
    proof (intro allI)
      fix phase
      have slot_bound: "0<comma_decisive_sector_period ?source"
        using period_source by simp
      have selected: "phase mod comma_decisive_sector_period ?source=0"
        using period_source by simp
      have source_output:
          "comma_semantic_b1_source_slot_output phase
              (comma_semantic_b1_source_slot_action ?source 0) =
            comma_semantic_b1_round_output phase ?source"
        by (rule comma_semantic_b1_source_slot_round_output
          [OF base admitted slot_bound selected])
      have child_output:
          "comma_semantic_b1_source_slot_output phase
              (comma_semantic_b1_source_slot_action ?source 0) =
            comma_semantic_b1_round_output phase child"
        using slot_action
        by (simp add: comma_semantic_b1_source_slot_output_def)
      show "comma_semantic_b1_round_output phase ?source =
          comma_semantic_b1_round_output phase child"
        using source_output child_output by simp
    qed
  next
    show "comma_round_admitted child"
      using child_rank by simp
  next
    show "9-comma_sector_number child <
        9-comma_sector_number ?source"
      using child_rank by simp
  qed
qed


lemma comma_guarded_source_port_action_periodic:
  assumes admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
  shows "comma_semantic_b1_source_port_action source slot =
    comma_semantic_b1_source_port_action source
      (slot mod comma_decisive_sector_period source)"
proof -
  let ?period = "comma_decisive_sector_period source"
  have same: "slot mod ?period = (slot mod ?period) mod ?period"
    by simp
  have target:
    "comma_decisive_sector_target slot source =
      comma_decisive_sector_target (slot mod ?period) source"
    by (rule comma_decisive_sector_target_period[OF admitted same])
  show ?thesis using target normalized
    by (simp add: comma_semantic_b1_source_port_action_def)
qed

lemma comma_guarded_source_action_at_port:
  assumes admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
  shows "comma_source_continuation_action_at source phase =
    comma_semantic_b1_source_port_action source phase"
proof -
  let ?period = "comma_decisive_sector_period source"
  have positive: "0 < ?period"
    by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
  have slot: "phase mod ?period < ?period" using positive by simp
  have exact_slot:
    "comma_source_continuation_action_at source (phase mod ?period) =
      comma_semantic_b1_source_port_action source (phase mod ?period)"
    using comma_semantic_b1_source_action_at_port[OF admitted, of
      "phase mod ?period"] normalized slot by simp
  have action_periodic:
    "comma_source_continuation_action_at source phase =
      comma_source_continuation_action_at source (phase mod ?period)"
    using normalized
    by (simp add: comma_source_continuation_action_at_def
        comma_source_continuation_id_def Let_def)
  have port_periodic:
    "comma_semantic_b1_source_port_action source phase =
      comma_semantic_b1_source_port_action source (phase mod ?period)"
    by (rule comma_guarded_source_port_action_periodic[OF admitted normalized])
  show ?thesis using exact_slot action_periodic port_periodic by simp
qed

lemma comma_semantic_b1_action_at_selected_port:
  assumes admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
  shows "comma_source_continuation_action_at source phase =
    comma_semantic_b1_source_port_action source
      (phase mod comma_decisive_sector_period source)"
  by (rule trans[OF comma_guarded_source_action_at_port[OF admitted normalized]
    comma_guarded_source_port_action_periodic[OF admitted normalized]])

lemma comma_semantic_b1_port_round_output:
  assumes admitted: "comma_round_admitted source"
    and normalized: "source=comma_source_continuation_base source"
  shows "comma_semantic_b1_source_slot_output phase
      (comma_semantic_b1_source_port_action source phase) =
    comma_semantic_b1_round_output phase source"
proof -
  let ?period = "comma_decisive_sector_period source"
  let ?slot = "phase mod ?period"
  have positive: "0<?period"
    by (rule comma_decisive_sector_period_admitted(1)[OF admitted])
  have slot: "?slot<?period" using positive by simp
  have source_slot:
    "comma_semantic_b1_source_slot_action source ?slot =
      comma_source_continuation_action_at source ?slot"
    by (rule comma_semantic_b1_source_slot_action_refines[OF admitted])
  have port_slot:
    "comma_source_continuation_action_at source ?slot =
      comma_semantic_b1_source_port_action source ?slot"
    by (rule comma_semantic_b1_source_action_at_port[OF admitted])
      (use normalized slot in simp)
  have periodic:
    "comma_semantic_b1_source_port_action source phase =
      comma_semantic_b1_source_port_action source ?slot"
    by (rule comma_guarded_source_port_action_periodic[OF admitted normalized])
  have exact:
    "comma_semantic_b1_source_slot_output phase
      (comma_semantic_b1_source_slot_action source ?slot) =
      comma_semantic_b1_round_output phase source"
    by (rule comma_semantic_b1_source_slot_round_output
      [OF normalized admitted slot refl])
  show ?thesis using exact source_slot port_slot periodic by simp
qed

ML \<open>
  val checked = @{thms comma_guarded_source_action_at_port
    comma_semantic_b1_action_at_selected_port comma_guarded_source_port_action_periodic
    comma_semantic_b1_port_round_output comma_semantic_b1_entry_slot_decisive_near
    comma_semantic_b1_entry_slot_action_near
    comma_semantic_b1_entry_source_ports_near
    comma_semantic_b1_source_action_at_port
    comma_semantic_b1_entry_period_one_direct_goto_action
    comma_semantic_b1_entry_period_one_direct_goto_completed
    comma_semantic_b1_entry_headroom_modular_rebase
    comma_semantic_b1_entry_control_port_modular_rebase
    comma_semantic_b1_entry_local_period_modular_rebase
    comma_semantic_b1_entry_source_id_modular_rebase
    comma_semantic_b1_entry_modular_rebase_f5_0_60
    comma_semantic_b1_entry_modular_rebase_f1_0_10_same_digit_period_distinct_residue
    comma_semantic_b1_entry_modular_rebase_f1_0_10_different_ports};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Entry-to-decisive-Near port transport depends on an oracle";
\<close>

end
