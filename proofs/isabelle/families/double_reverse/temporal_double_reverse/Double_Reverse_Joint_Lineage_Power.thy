theory Double_Reverse_Joint_Lineage_Power
  imports Double_Reverse_F5_Action_Power
    Double_Reverse_Carry_Phase_Weights
begin

text \<open>A periodic-lineage action is derived from the exact finite ring
successor, not from a caller-supplied carry word.  The temporal cycle begins
at an explicit preperiod boundary.  A joint shift must preserve both that
ring state and the selected spatial port phase before a block action can be
reused and powered.\<close>

definition double_reverse_ring_decimal :: "nat list \<Rightarrow> bool" where
  "double_reverse_ring_decimal word \<longleftrightarrow>
    (\<forall>i<length word. word ! i < 10)"

lemma double_reverse_ring_digit_decimal:
  assumes nonempty: "word \<noteq> []"
      and decimal: "double_reverse_ring_decimal word"
  shows "double_reverse_ring_digit word i < 10"
proof -
  have index: "i mod length word < length word"
    using nonempty by simp
  show ?thesis
    using decimal index
    by (simp add: double_reverse_ring_decimal_def
        double_reverse_ring_digit_def)
qed

lemma double_reverse_ring_inward_step_decimal:
  assumes nonempty: "word \<noteq> []"
      and decimal: "double_reverse_ring_decimal word"
  shows "double_reverse_ring_decimal
    (double_reverse_ring_inward_step word)"
proof -
  have output_cells_bounded:
    "double_reverse_ring_inward_step word ! i < 10"
    if "i < length (double_reverse_ring_inward_step word)" for i
  proof -
    have bound: "i < length word"
      using that by (simp add: double_reverse_ring_inward_step_length)
    have word_nonempty: "0 < length word"
      using nonempty by simp
    have exact:
      "double_reverse_ring_inward_step word ! i =
        double_reverse_t2_digit
          (double_reverse_ring_digit word i)
          (double_reverse_ring_digit word (i+1))
          (double_reverse_ring_digit word (i+2))"
    by (rule double_reverse_ring_inward_step_digit[OF word_nonempty bound])
    show ?thesis using exact by (simp add: double_reverse_t2_output_bounded)
  qed
  show ?thesis
    using output_cells_bounded
    by (simp add: double_reverse_ring_decimal_def)
qed

lemma double_reverse_ring_inward_step_nonempty:
  assumes nonempty: "word \<noteq> []"
  shows "double_reverse_ring_inward_step word \<noteq> []"
proof -
  have step_length:
    "length (double_reverse_ring_inward_step word) = length word"
    by (simp add: double_reverse_ring_inward_step_length)
  have source_length: "0 < length word"
    using nonempty by simp
  have positive_step: "0 < length (double_reverse_ring_inward_step word)"
    using step_length source_length by arith
  show ?thesis
    using positive_step
    by (cases "double_reverse_ring_inward_step word") auto
qed

lemma double_reverse_ring_inward_run_decimal:
  assumes nonempty: "word \<noteq> []"
      and decimal: "double_reverse_ring_decimal word"
  shows "double_reverse_ring_decimal
    (double_reverse_ring_inward_run steps word)"
  using nonempty decimal
proof (induction steps arbitrary: word)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have child_nonempty:
    "double_reverse_ring_inward_step word \<noteq> []"
    by (rule double_reverse_ring_inward_step_nonempty[OF Suc.prems(1)])
  have child_decimal:
    "double_reverse_ring_decimal (double_reverse_ring_inward_step word)"
    by (rule double_reverse_ring_inward_step_decimal[OF Suc.prems])
  show ?case
    using Suc.IH[OF child_nonempty child_decimal] by simp
qed

lemma double_reverse_ring_inward_run_length:
  "length (double_reverse_ring_inward_run steps word) = length word"
  by (induction steps arbitrary: word)
    (simp_all add: double_reverse_ring_inward_step_length)

lemma double_reverse_ring_inward_run_nonempty:
  assumes nonempty: "word \<noteq> []"
  shows "double_reverse_ring_inward_run steps word \<noteq> []"
proof -
  have run_length:
    "length (double_reverse_ring_inward_run steps word) = length word"
    by (rule double_reverse_ring_inward_run_length)
  have source_positive: "0 < length word"
    using nonempty by simp
  have run_positive:
    "0 < length (double_reverse_ring_inward_run steps word)"
    using run_length source_positive by arith
  show ?thesis
    using run_positive by (cases "double_reverse_ring_inward_run steps word") auto
qed

lemma double_reverse_ring_inward_ports_valid:
  assumes nonempty: "word \<noteq> []"
      and decimal: "double_reverse_ring_decimal word"
  shows "double_reverse_open_inputs_valid
    (double_reverse_ring_inward_ports steps word position)"
  using nonempty decimal
proof (induction steps arbitrary: word position)
  case 0
  then show ?case by (simp add: double_reverse_open_inputs_valid_def)
next
  case (Suc steps)
  have child_nonempty:
    "double_reverse_ring_inward_step word \<noteq> []"
    by (rule double_reverse_ring_inward_step_nonempty[OF Suc.prems(1)])
  have child_decimal:
    "double_reverse_ring_decimal (double_reverse_ring_inward_step word)"
    by (rule double_reverse_ring_inward_step_decimal[OF Suc.prems])
  have left_bound:
    "double_reverse_ring_digit word (position + steps) < 10"
    by (rule double_reverse_ring_digit_decimal[OF Suc.prems])
  have right_bound:
    "double_reverse_ring_digit word (position + steps + 2) < 10"
    by (rule double_reverse_ring_digit_decimal[OF Suc.prems])
  have tail:
    "double_reverse_open_inputs_valid
      (double_reverse_ring_inward_ports steps
        (double_reverse_ring_inward_step word) position)"
    by (rule Suc.IH[OF child_nonempty child_decimal])
  show ?case
    using left_bound right_bound tail
    by (simp add: double_reverse_ring_inward_ports.simps
        double_reverse_open_inputs_valid_def)
qed

theorem double_reverse_ring_inward_trace_exact:
  assumes nonempty: "word \<noteq> []"
  shows "double_reverse_open_stencil_trace
      (double_reverse_ring_digit word (position + steps))
      (double_reverse_ring_inward_ports steps word position) =
    double_reverse_ring_digit
      (double_reverse_ring_inward_run steps word) position"
  using nonempty
proof (induction steps arbitrary: word position)
  case 0
  then show ?case by (simp add: double_reverse_ring_digit_def)
next
  case (Suc steps)
  have child_nonempty:
    "double_reverse_ring_inward_step word \<noteq> []"
    by (rule double_reverse_ring_inward_step_nonempty[OF Suc.prems])
  have stencil:
    "double_reverse_ring_digit (double_reverse_ring_inward_step word)
       (position + steps) =
      double_reverse_t2_digit
        (double_reverse_ring_digit word (position + steps))
        (double_reverse_ring_digit word (position + steps + 1))
        (double_reverse_ring_digit word (position + steps + 2))"
  proof -
    have word_positive: "0 < length word"
      using Suc.prems by simp
    show ?thesis
      by (rule double_reverse_ring_inward_step_ring_digit[OF word_positive])
  qed
  have tail:
    "double_reverse_open_stencil_trace
        (double_reverse_ring_digit
          (double_reverse_ring_inward_step word) (position + steps))
        (double_reverse_ring_inward_ports steps
          (double_reverse_ring_inward_step word) position) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run steps
          (double_reverse_ring_inward_step word)) position"
    by (rule Suc.IH[OF child_nonempty])
  show ?case
    using stencil tail
    by (simp add: double_reverse_open_stencil_trace.simps
        double_reverse_ring_inward_ports.simps)
qed

theorem double_reverse_f5_ring_lineage_action_exact:
  assumes nonempty: "word \<noteq> []"
      and decimal: "double_reverse_ring_decimal word"
      and center: "double_reverse_ring_digit word (position + steps) < 10"
  shows "double_reverse_f5_apply
      (double_reverse_f5_open_trace_action
        (double_reverse_ring_digit word (position + steps))
        (double_reverse_ring_inward_ports steps word position))
      (double_reverse_ring_digit word (position + steps) mod 5) =
    double_reverse_ring_digit
      (double_reverse_ring_inward_run steps word) position mod 5"
proof -
  have valid:
    "double_reverse_open_inputs_valid
      (double_reverse_ring_inward_ports steps word position)"
    by (rule double_reverse_ring_inward_ports_valid[OF nonempty decimal])
  have trace:
    "double_reverse_open_stencil_trace
        (double_reverse_ring_digit word (position + steps))
        (double_reverse_ring_inward_ports steps word position) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run steps word) position"
    by (rule double_reverse_ring_inward_trace_exact[OF nonempty])
  show ?thesis
    using double_reverse_f5_open_trace_action_refines_trace[OF center valid]
      trace by simp
qed

lemma double_reverse_ring_inward_ports_length:
  "length (double_reverse_ring_inward_ports steps word position) = steps"
  by (induction steps arbitrary: word position) simp_all

theorem double_reverse_f5_ring_lineage_path_telescope:
  assumes word_nonempty: "word \<noteq> []"
      and row_decimal:
        "double_reverse_ring_decimal
          (double_reverse_ring_inward_run start word)"
  shows "int (double_reverse_ring_digit
      (double_reverse_ring_inward_run steps
        (double_reverse_ring_inward_run start word)) position mod 5) mod 5 =
    (2 ^ (2 * steps) *
        int (double_reverse_ring_digit
          (double_reverse_ring_inward_run start word) (position + steps)) +
      double_reverse_f5_physical_path_offset
        (double_reverse_ring_digit
          (double_reverse_ring_inward_run start word) (position + steps))
        (double_reverse_ring_inward_ports steps
          (double_reverse_ring_inward_run start word) position)) mod 5"
proof -
  let ?row = "double_reverse_ring_inward_run start word"
  let ?center = "double_reverse_ring_digit ?row (position + steps)"
  let ?ports = "double_reverse_ring_inward_ports steps ?row position"
  have ports_length: "length ?ports = steps"
    by (rule double_reverse_ring_inward_ports_length)
  have row_nonempty: "?row \<noteq> []"
    by (rule double_reverse_ring_inward_run_nonempty[OF word_nonempty])
  have center_decimal: "?center < 10"
    by (rule double_reverse_ring_digit_decimal[OF row_nonempty row_decimal])
  have ports_valid: "double_reverse_open_inputs_valid ?ports"
    by (rule double_reverse_ring_inward_ports_valid[OF row_nonempty row_decimal])
  have ring_trace:
    "double_reverse_open_stencil_trace ?center ?ports =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run steps ?row) position"
    by (rule double_reverse_ring_inward_trace_exact[OF row_nonempty])
  have action_endpoint:
    "double_reverse_f5_apply
        (double_reverse_f5_open_trace_action ?center ?ports) (?center mod 5) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run steps ?row) position mod 5"
  proof -
    have action_trace:
      "double_reverse_f5_apply
          (double_reverse_f5_open_trace_action ?center ?ports) (?center mod 5) =
        double_reverse_open_stencil_trace ?center ?ports mod 5"
      by (rule double_reverse_f5_open_trace_action_refines_trace
        [OF center_decimal ports_valid])
    show ?thesis using action_trace ring_trace by simp
  qed
  have action_telescope:
    "int (double_reverse_f5_apply
        (double_reverse_f5_open_trace_action ?center ?ports) (?center mod 5)) mod 5 =
      (2 ^ (2 * steps) * int ?center +
        double_reverse_f5_physical_path_offset ?center ?ports) mod 5"
  proof -
    have exact:
      "int (double_reverse_f5_apply
          (double_reverse_f5_open_trace_action ?center ?ports) (?center mod 5)) mod 5 =
        (2 ^ (double_reverse_f5_ticks
            (double_reverse_f5_open_trace_action ?center ?ports)) * int ?center +
          double_reverse_f5_physical_path_offset ?center ?ports) mod 5"
      by (rule double_reverse_f5_admitted_path_action_telescope
        [OF center_decimal ports_valid])
    have ticks:
      "double_reverse_f5_ticks
          (double_reverse_f5_open_trace_action ?center ?ports) = 2 * steps"
      by (simp add: double_reverse_f5_open_trace_action_ticks
          ports_length)
    show ?thesis using exact ticks by simp
  qed
  show ?thesis using action_endpoint action_telescope by simp
qed

definition double_reverse_ring_eventual_cycle ::
    "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
  "double_reverse_ring_eventual_cycle start period word \<longleftrightarrow>
    0 < period \<and>
    double_reverse_ring_inward_run (start + period) word =
      double_reverse_ring_inward_run start word"

lemma double_reverse_ring_repeated_state_yields_eventual_cycle:
  assumes ordered: "start < finish"
      and repeated:
        "double_reverse_ring_inward_run finish word =
          double_reverse_ring_inward_run start word"
  shows "double_reverse_ring_eventual_cycle start (finish - start) word"
proof -
  have positive: "0 < finish - start" using ordered by simp
  have finish: "start + (finish - start) = finish"
    using ordered by arith
  show ?thesis
    using positive repeated finish
    by (simp add: double_reverse_ring_eventual_cycle_def)
qed

lemma double_reverse_ring_eventual_periodic:
  assumes cycle: "double_reverse_ring_eventual_cycle start period word"
  shows "double_reverse_ring_inward_run (start + offset + period) word =
    double_reverse_ring_inward_run (start + offset) word"
proof -
  have base:
    "double_reverse_ring_inward_run (start + period) word =
      double_reverse_ring_inward_run start word"
    using cycle by (simp add: double_reverse_ring_eventual_cycle_def)
  have left:
    "double_reverse_ring_inward_run (start + period + offset) word =
      double_reverse_ring_inward_run offset
        (double_reverse_ring_inward_run (start + period) word)"
    by (rule double_reverse_ring_inward_run_add)
  have right:
    "double_reverse_ring_inward_run (start + offset) word =
      double_reverse_ring_inward_run offset
        (double_reverse_ring_inward_run start word)"
    by (rule double_reverse_ring_inward_run_add)
  show ?thesis
    using base left right by (simp add: ac_simps)
qed

lemma double_reverse_ring_eventual_shift_periodic:
  assumes cycle: "double_reverse_ring_eventual_cycle start period word"
      and shift: "period dvd shift"
  shows "double_reverse_ring_inward_run (start + offset + shift) word =
    double_reverse_ring_inward_run (start + offset) word"
proof -
  obtain copies where copies: "shift = period * copies"
    using shift by (rule dvdE)
  have repeated:
    "double_reverse_ring_inward_run
        (start + offset + period * copies) word =
      double_reverse_ring_inward_run (start + offset) word"
  proof (induction copies)
    case 0
    then show ?case by simp
  next
    case (Suc copies)
    have step:
      "double_reverse_ring_inward_run
          (start + (offset + period * copies) + period) word =
        double_reverse_ring_inward_run (start + (offset + period * copies)) word"
      by (rule double_reverse_ring_eventual_periodic[OF cycle])
    show ?case
      using Suc.IH step by (simp add: algebra_simps add.assoc)
  qed
  show ?thesis using repeated copies by simp
qed

lemma double_reverse_ring_digit_shift_period:
  assumes nonempty: "word \<noteq> []"
      and shift: "length word dvd amount"
  shows "double_reverse_ring_digit word (index + amount) =
    double_reverse_ring_digit word index"
proof -
  obtain copies where amount: "amount = length word * copies"
    using shift by (rule dvdE)
  have zero: "(length word * copies) mod length word = 0" by simp
  have sum:
    "(index + length word * copies) mod length word =
      ((index mod length word) +
        (length word * copies) mod length word) mod length word"
    by (rule mod_add_eq[symmetric])
  show ?thesis
    using amount zero sum nonempty
    by (simp add: double_reverse_ring_digit_def)
qed

lemma double_reverse_ring_inward_ports_shift_period:
  assumes nonempty: "word \<noteq> []"
      and shift: "length word dvd amount"
  shows "double_reverse_ring_inward_ports steps word (index + amount) =
    double_reverse_ring_inward_ports steps word index"
  using nonempty shift
proof (induction steps arbitrary: word index)
  case 0
  then show ?case by simp
next
  case (Suc steps)
  have child_nonempty:
    "double_reverse_ring_inward_step word \<noteq> []"
    by (rule double_reverse_ring_inward_step_nonempty[OF Suc.prems(1)])
  have child_shift:
    "length (double_reverse_ring_inward_step word) dvd amount"
    using Suc.prems(2) by (simp add: double_reverse_ring_inward_step_length)
  have left:
    "double_reverse_ring_digit word
        (index + amount + steps) =
      double_reverse_ring_digit word (index + steps)"
  proof -
    have shifted:
      "double_reverse_ring_digit word ((index + steps) + amount) =
        double_reverse_ring_digit word (index + steps)"
      by (rule double_reverse_ring_digit_shift_period[OF Suc.prems])
    show ?thesis using shifted by (simp add: algebra_simps)
  qed
  have right:
    "double_reverse_ring_digit word
        (index + amount + steps + 2) =
      double_reverse_ring_digit word (index + steps + 2)"
  proof -
    have shifted:
      "double_reverse_ring_digit word ((index + steps + 2) + amount) =
        double_reverse_ring_digit word (index + steps + 2)"
      by (rule double_reverse_ring_digit_shift_period[OF Suc.prems])
    show ?thesis using shifted by (simp add: algebra_simps)
  qed
  have tail:
    "double_reverse_ring_inward_ports steps
        (double_reverse_ring_inward_step word) (index + amount) =
      double_reverse_ring_inward_ports steps
        (double_reverse_ring_inward_step word) index"
    by (rule Suc.IH[OF child_nonempty child_shift])
  show ?case using left right tail
    by (simp add: double_reverse_ring_inward_ports.simps)
qed

definition double_reverse_ring_lineage_segment_action ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      double_reverse_f5_action" where
  "double_reverse_ring_lineage_segment_action word output_position total_steps
      start span =
    (let row = double_reverse_ring_inward_run start word;
         index = output_position + total_steps - start - span
     in double_reverse_f5_open_trace_action
          (double_reverse_ring_digit row (index + span))
          (double_reverse_ring_inward_ports span row index))"

theorem double_reverse_ring_lineage_segment_refines_endpoint:
  assumes nonempty: "word \<noteq> []"
      and decimal: "double_reverse_ring_decimal
        (double_reverse_ring_inward_run start word)"
      and bounds: "start + span \<le> total_steps"
  shows "double_reverse_f5_apply
      (double_reverse_ring_lineage_segment_action word output_position
        total_steps start span)
      (double_reverse_ring_digit
        (double_reverse_ring_inward_run start word)
        (output_position + total_steps - start) mod 5) =
    double_reverse_ring_digit
      (double_reverse_ring_inward_run (start + span) word)
      (output_position + total_steps - start - span) mod 5"
proof -
  let ?row = "double_reverse_ring_inward_run start word"
  let ?index = "output_position + total_steps - start - span"
  have row_nonempty: "?row \<noteq> []"
    by (rule double_reverse_ring_inward_run_nonempty[OF nonempty])
  have center_index: "?index + span = output_position + total_steps - start"
    using bounds by arith
  have action_exact:
    "double_reverse_f5_apply
      (double_reverse_f5_open_trace_action
        (double_reverse_ring_digit ?row (?index + span))
        (double_reverse_ring_inward_ports span ?row ?index))
      (double_reverse_ring_digit ?row (?index + span) mod 5) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run span ?row) ?index mod 5"
  proof (rule double_reverse_f5_ring_lineage_action_exact[OF row_nonempty decimal])
    show "double_reverse_ring_digit ?row (?index + span) < 10"
      by (rule double_reverse_ring_digit_decimal[OF row_nonempty decimal])
  qed
  show ?thesis
    using action_exact center_index
    by (simp add: double_reverse_ring_lineage_segment_action_def
        double_reverse_ring_inward_run_add add.assoc Let_def)
qed

lemma double_reverse_ring_lineage_segment_joint_shift:
  assumes nonempty: "word \<noteq> []"
      and cycle: "double_reverse_ring_eventual_cycle cycle_start temporal_period word"
      and temporal: "temporal_period dvd shift"
      and spatial: "length word dvd shift"
      and start: "cycle_start \<le> block_start"
      and extent: "block_start + shift + span \<le> total_steps"
  shows "double_reverse_ring_lineage_segment_action word output_position
      total_steps block_start span =
    double_reverse_ring_lineage_segment_action word output_position
      total_steps (block_start + shift) span"
proof -
  have offset: "block_start = cycle_start + (block_start - cycle_start)"
    using start by arith
  have row:
    "double_reverse_ring_inward_run (block_start + shift) word =
      double_reverse_ring_inward_run block_start word"
    using double_reverse_ring_eventual_shift_periodic[OF cycle temporal,
      of "block_start - cycle_start"] offset
    by (simp add: add.assoc)
  let ?index = "output_position + total_steps - block_start - span"
  let ?shifted_index =
    "output_position + total_steps - (block_start + shift) - span"
  have index_relation: "?shifted_index + shift = ?index"
    using extent by arith
  have row_nonempty:
    "double_reverse_ring_inward_run block_start word \<noteq> []"
    by (rule double_reverse_ring_inward_run_nonempty[OF nonempty])
  have row_spatial:
    "length (double_reverse_ring_inward_run block_start word) dvd shift"
    by (simp add: double_reverse_ring_inward_run_length spatial)
  have port_rebase:
    "double_reverse_ring_inward_ports span
        (double_reverse_ring_inward_run block_start word)
        (?shifted_index + shift) =
      double_reverse_ring_inward_ports span
        (double_reverse_ring_inward_run block_start word) ?shifted_index"
    by (rule double_reverse_ring_inward_ports_shift_period
      [OF row_nonempty row_spatial])
  have center_rebase:
    "double_reverse_ring_digit
        (double_reverse_ring_inward_run block_start word)
        (?shifted_index + span + shift) =
      double_reverse_ring_digit
        (double_reverse_ring_inward_run block_start word)
        (?shifted_index + span)"
    by (rule double_reverse_ring_digit_shift_period
      [OF row_nonempty row_spatial])
  have center_coordinate:
    "?index + span = ?shifted_index + span + shift"
    using index_relation by (simp add: algebra_simps)
  show ?thesis
    using row port_rebase center_rebase center_coordinate
    by (simp only: double_reverse_ring_lineage_segment_action_def Let_def
        row index_relation port_rebase center_rebase center_coordinate)
qed

fun double_reverse_ring_lineage_cycle_fold ::
    "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      double_reverse_f5_action" where
  "double_reverse_ring_lineage_cycle_fold word output_position total_steps
      cycle_start joint_period 0 = double_reverse_f5_identity"
| "double_reverse_ring_lineage_cycle_fold word output_position total_steps
      cycle_start joint_period (Suc copies) =
    double_reverse_f5_then
      (double_reverse_ring_lineage_cycle_fold word output_position total_steps
        cycle_start joint_period copies)
      (double_reverse_ring_lineage_segment_action word output_position total_steps
        (cycle_start + copies * joint_period) joint_period)"

theorem double_reverse_ring_lineage_cycle_fold_power:
  fixes output_position :: nat
  assumes nonempty: "word \<noteq> []"
      and cycle:
        "double_reverse_ring_eventual_cycle cycle_start temporal_period word"
      and temporal: "temporal_period dvd joint_period"
      and spatial: "length word dvd joint_period"
      and joint_positive: "0 < joint_period"
      and extent: "cycle_start + copies * joint_period \<le> total_steps"
  defines "block_action \<equiv>
      double_reverse_ring_lineage_segment_action word output_position total_steps
        cycle_start joint_period"
  shows "double_reverse_ring_lineage_cycle_fold word output_position total_steps
      cycle_start joint_period copies =
    double_reverse_f5_action_power block_action copies"
  using extent
proof (induction copies)
  case 0
  then show ?case
    by (simp add: double_reverse_f5_identity_def block_action_def)
next
  case (Suc copies)
  have old_extent: "cycle_start + copies * joint_period \<le> total_steps"
    using Suc.prems joint_positive
    by (simp add: algebra_simps; arith)
  have temporal_shift:
    "temporal_period dvd copies * joint_period"
    by (rule dvd_mult[OF temporal])
  have spatial_shift:
    "length word dvd copies * joint_period"
    by (rule dvd_mult[OF spatial])
  have start_refl: "cycle_start \<le> cycle_start" by simp
  have shifted_extent:
    "cycle_start + copies * joint_period + joint_period \<le> total_steps"
    using Suc.prems by (simp add: algebra_simps)
  have shifted_block:
    "double_reverse_ring_lineage_segment_action word output_position total_steps
        cycle_start joint_period =
      double_reverse_ring_lineage_segment_action word output_position total_steps
        (cycle_start + copies * joint_period) joint_period"
    by (rule double_reverse_ring_lineage_segment_joint_shift
      [OF nonempty cycle temporal_shift spatial_shift start_refl shifted_extent])
  have induction:
    "double_reverse_ring_lineage_cycle_fold word output_position total_steps
        cycle_start joint_period copies =
      double_reverse_f5_action_power block_action copies"
    by (rule Suc.IH[OF old_extent])
  show ?case
    using induction shifted_block
    by (simp add: block_action_def)
qed

lemma double_reverse_f5_action_power_weighted_phase_exact:
  assumes exact: "double_reverse_f5_offset action mod 5 =
    double_reverse_f5_weighted_phase_sum action"
  shows "double_reverse_f5_offset
      (double_reverse_f5_action_power action copies) mod 5 =
    double_reverse_f5_weighted_phase_sum
      (double_reverse_f5_action_power action copies)"
proof (induction copies)
  case 0
  then show ?case
    by (simp add: double_reverse_f5_action_power.simps
        double_reverse_f5_identity_def
        double_reverse_f5_weighted_phase_sum_def
        double_reverse_f5_phase_count_def)
next
  case (Suc copies)
  let ?earlier = "double_reverse_f5_action_power action copies"
  have earlier_mod:
    "double_reverse_f5_offset ?earlier mod 5 =
      double_reverse_f5_weighted_phase_sum ?earlier mod 5"
    using Suc.IH by simp
  have later_mod:
    "double_reverse_f5_offset action mod 5 =
      double_reverse_f5_weighted_phase_sum action mod 5"
    using exact by simp
  have product:
    "(double_reverse_f5_multiplier action *
        double_reverse_f5_offset ?earlier) mod 5 =
      (double_reverse_f5_multiplier action *
        double_reverse_f5_weighted_phase_sum ?earlier) mod 5"
    by (rule mod_mult_cong[OF refl earlier_mod])
  have total:
    "(double_reverse_f5_multiplier action *
        double_reverse_f5_offset ?earlier +
        double_reverse_f5_offset action) mod 5 =
      (double_reverse_f5_multiplier action *
        double_reverse_f5_weighted_phase_sum ?earlier +
        double_reverse_f5_weighted_phase_sum action) mod 5"
    by (rule mod_add_cong[OF product later_mod])
  have offset_step:
    "double_reverse_f5_offset
        (double_reverse_f5_action_power action (Suc copies)) mod 5 =
      (double_reverse_f5_multiplier action *
        double_reverse_f5_offset ?earlier +
        double_reverse_f5_offset action) mod 5"
    by (simp add: double_reverse_f5_action_power.simps
        double_reverse_f5_then_def)
  have weight_step:
    "double_reverse_f5_weighted_phase_sum
        (double_reverse_f5_action_power action (Suc copies)) =
      (double_reverse_f5_multiplier action *
        double_reverse_f5_weighted_phase_sum ?earlier +
        double_reverse_f5_weighted_phase_sum action) mod 5"
    by (simp add: double_reverse_f5_action_power.simps
        double_reverse_f5_weighted_phase_sum_then)
  show ?case using offset_step weight_step total by simp
qed

lemma double_reverse_ring_lineage_segment_weighted_phase_exact:
  "double_reverse_f5_offset
      (double_reverse_ring_lineage_segment_action word output_position
        total_steps start span) mod 5 =
    double_reverse_f5_weighted_phase_sum
      (double_reverse_ring_lineage_segment_action word output_position
        total_steps start span)"
  unfolding double_reverse_ring_lineage_segment_action_def Let_def
  by (rule double_reverse_f5_open_trace_offset_weighted)

theorem double_reverse_ring_lineage_cycle_fold_weighted_phase_exact:
  fixes output_position :: nat
  assumes nonempty: "word \<noteq> []"
      and cycle:
        "double_reverse_ring_eventual_cycle cycle_start temporal_period word"
      and temporal: "temporal_period dvd joint_period"
      and spatial: "length word dvd joint_period"
      and joint_positive: "0 < joint_period"
      and extent: "cycle_start + copies * joint_period \<le> total_steps"
  defines "block_action \<equiv>
      double_reverse_ring_lineage_segment_action word output_position total_steps
        cycle_start joint_period"
  shows "double_reverse_f5_offset
      (double_reverse_ring_lineage_cycle_fold word output_position total_steps
        cycle_start joint_period copies) mod 5 =
    double_reverse_f5_weighted_phase_sum
      (double_reverse_ring_lineage_cycle_fold word output_position total_steps
        cycle_start joint_period copies)"
proof -
  have fold_power:
    "double_reverse_ring_lineage_cycle_fold word output_position total_steps
        cycle_start joint_period copies =
      double_reverse_f5_action_power block_action copies"
    unfolding block_action_def
    by (rule double_reverse_ring_lineage_cycle_fold_power
      [OF nonempty cycle temporal spatial joint_positive extent])
  have initial_weighted:
    "double_reverse_f5_offset block_action mod 5 =
      double_reverse_f5_weighted_phase_sum block_action"
    unfolding block_action_def
    by (rule double_reverse_ring_lineage_segment_weighted_phase_exact)
  have powered_weighted:
    "double_reverse_f5_offset
        (double_reverse_f5_action_power block_action copies) mod 5 =
      double_reverse_f5_weighted_phase_sum
        (double_reverse_f5_action_power block_action copies)"
    by (rule double_reverse_f5_action_power_weighted_phase_exact
      [OF initial_weighted])
  show ?thesis using fold_power powered_weighted by simp
qed

ML \<open>
  val checked = @{thms double_reverse_ring_inward_trace_exact
    double_reverse_f5_ring_lineage_action_exact
    double_reverse_ring_eventual_periodic
    double_reverse_ring_repeated_state_yields_eventual_cycle
    double_reverse_ring_eventual_shift_periodic
    double_reverse_ring_digit_shift_period
    double_reverse_ring_inward_ports_shift_period
    double_reverse_ring_lineage_segment_refines_endpoint
    double_reverse_ring_lineage_segment_joint_shift
    double_reverse_ring_lineage_cycle_fold_power
    double_reverse_f5_action_power_weighted_phase_exact
    double_reverse_ring_lineage_segment_weighted_phase_exact
    double_reverse_ring_lineage_cycle_fold_weighted_phase_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Double-reverse ring lineage action depends on an oracle";
  val _ = if Thm_Deps.has_skip_proof checked
    then error "Skipped double-reverse ring lineage action proof" else ();
\<close>

end
