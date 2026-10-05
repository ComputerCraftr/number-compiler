theory Comma_Semantic_B1_Table_Transform
  imports Comma_Semantic_B1_Publication Comma_CRT_Columns
begin

text \<open>
This theory starts the source-selected B1 publisher at the endpoint
recurrence.  Candidate construction reads one packet per local slot; it does
not construct `comma_source_continuation_id`, its complete action list, or a
proof object per source row.  Clock occurrences are represented by finite
intersections of CRT cylinders and are normalized by the publisher.
\<close>

type_synonym comma_semantic_b1_crt_scope = "nat \<times> nat"
definition comma_semantic_b1_crt_scope_admitted ::
    "comma_semantic_b1_crt_scope \<Rightarrow> bool" where
  "comma_semantic_b1_crt_scope_admitted scope \<longleftrightarrow>
    comma_semantic_b1_scope_admitted (fst scope) (snd scope)"

definition comma_semantic_b1_crt_scope_holds ::
    "comma_semantic_b1_crt_scope \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_semantic_b1_crt_scope_holds scope phase \<longleftrightarrow>
    phase mod fst scope = snd scope"

definition comma_semantic_b1_source_slot_scope ::
    "nat \<Rightarrow> nat \<Rightarrow> comma_semantic_b1_crt_scope" where
  "comma_semantic_b1_source_slot_scope period slot = (period,slot)"

definition comma_semantic_b1_source_slot_action ::
    "comma_finite_position \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action" where
  "comma_semantic_b1_source_slot_action source slot =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet slot
        (comma_source_continuation_base source))"

definition comma_semantic_b1_source_slot_action_width ::
    "comma_finite_position \<Rightarrow> nat \<Rightarrow>
      comma_source_continuation_action" where
  "comma_semantic_b1_source_slot_action_width source slot =
    (let target = comma_decisive_sector_target slot
        (comma_source_continuation_base source)
     in case target of
       Comma_Near f delta h \<Rightarrow>
         (case comma_near_terminal_width_j f h of
            Some j \<Rightarrow>
              (if j = 8 then Comma_Continuation_Landmine delta
               else Comma_Continuation_Fork (j + 2) delta)
          | None \<Rightarrow> comma_source_continuation_action_of_packet
              (target, comma_fast_step (slot mod 924) target))
     | _ \<Rightarrow> comma_source_continuation_action_of_packet
         (target, comma_fast_step (slot mod 924) target))"

definition comma_semantic_b1_source_slot_actions ::
    "comma_finite_position \<Rightarrow> comma_source_continuation_action list" where
  "comma_semantic_b1_source_slot_actions source =
    map (comma_semantic_b1_source_slot_action_width source)
      [0..<comma_decisive_sector_period (comma_source_continuation_base source)]"

lemma comma_semantic_b1_source_slot_action_width_refines:
  assumes admitted: "comma_round_admitted source"
  shows "comma_semantic_b1_source_slot_action_width source slot =
    comma_semantic_b1_source_slot_action source slot"
proof -
  let ?base = "comma_source_continuation_base source"
  let ?target = "comma_decisive_sector_target slot ?base"
  have base_admitted: "comma_round_admitted ?base"
    by (rule comma_source_continuation_base_admitted[OF admitted])
  obtain f delta h where target:
      "?target = Comma_Near f delta h"
    using comma_decisive_sector_target_near[OF base_admitted, of slot] by blast
  have target_admitted: "comma_round_admitted ?target"
    using comma_decisive_packet_target_admitted[OF base_admitted, of slot]
    by (simp add: comma_decisive_endpoint_packet_def Let_def)
  have bounds: "1 \<le> f" "f \<le> 9" "1 \<le> h" "h \<le> 540"
    using target_admitted target by simp_all
  have classifier:
      "comma_near_terminal_width_j f h =
        comma_terminal_width_j_of_move
          (comma_fast_step (slot mod 924) ?target)"
    using comma_near_terminal_width_j_refines[OF bounds]
      target by (simp only: comma_fast_step_correct)
  show ?thesis
  proof (cases "comma_fast_step (slot mod 924) ?target")
    case (Comma_Fork a shift)
    have finite_shift:
        "comma_finite_step (slot mod 924) (Comma_Near f delta h) =
          Comma_Fork a shift"
      using Comma_Fork target by (simp only: comma_fast_step_correct)
    have normal:
        "1 \<le> f \<and> f < 9 \<and> h = 91 - 9 * f \<and>
          a = f + 1 \<and> shift = delta"
      using comma_near_fork_headroom_normal_form[OF finite_shift] by blast
    have shift_eq: "shift=delta" using normal by blast
    have position: "comma_near_terminal_width_j f h = Some (a - 2)"
      using classifier Comma_Fork by simp
    have a_bounds: "2 \<le> a" "a \<le> 9"
      using normal bounds by auto
    have not_landmine_position: "a - 2 \<noteq> 8"
      using a_bounds by arith
    have reconstruct: "a - 2 + 2 = a"
      using a_bounds by arith
    have projected_action:
        "(if a - 2 = 8 then Comma_Continuation_Landmine delta
         else Comma_Continuation_Fork (a - 2 + 2) delta) =
          Comma_Continuation_Fork a delta"
      using not_landmine_position reconstruct by simp
    show ?thesis
      using target Comma_Fork position shift_eq projected_action
      by (simp only: comma_semantic_b1_source_slot_action_width_def
          comma_semantic_b1_source_slot_action_def
          comma_decisive_endpoint_packet_def Let_def
          comma_source_continuation_action_of_packet.simps
          comma_finite_position.case option.case prod.case
          target Comma_Fork position shift_eq projected_action)
  next
    case (Comma_Landmine shift)
    have finite_shift:
        "comma_finite_step (slot mod 924) (Comma_Near f delta h) =
          Comma_Landmine shift"
      using Comma_Landmine target by (simp only: comma_fast_step_correct)
    have shift_eq: "shift=delta"
      using finite_shift bounds
      by (auto simp: comma_near_control_formula Let_def split: if_splits)
    have position: "comma_near_terminal_width_j f h = Some 8"
      using classifier Comma_Landmine by simp
    show ?thesis
      using target Comma_Landmine position shift_eq
      by (simp add: comma_semantic_b1_source_slot_action_width_def
          comma_semantic_b1_source_slot_action_def
          comma_decisive_endpoint_packet_def Let_def
          comma_source_continuation_action_of_packet.simps)
  next
    case (Comma_Next successor)
    have no_terminal: "comma_near_terminal_width_j f h = None"
      using classifier Comma_Next by simp
    show ?thesis
      using target Comma_Next no_terminal
      by (simp add: comma_semantic_b1_source_slot_action_width_def
          comma_semantic_b1_source_slot_action_def
          comma_decisive_endpoint_packet_def Let_def
          comma_source_continuation_action_of_packet.simps)
  next
    case Comma_Invalid
    have no_terminal: "comma_near_terminal_width_j f h = None"
      using classifier Comma_Invalid by simp
    show ?thesis
      using target Comma_Invalid no_terminal
      by (simp add: comma_semantic_b1_source_slot_action_width_def
          comma_semantic_b1_source_slot_action_def
          comma_decisive_endpoint_packet_def Let_def
          comma_source_continuation_action_of_packet.simps)
  qed
qed

lemma comma_semantic_b1_source_slot_action_code:
  "comma_semantic_b1_source_slot_action source slot =
    (if comma_round_admitted source then
       comma_semantic_b1_source_slot_action_width source slot
     else comma_source_continuation_action_of_packet
       (comma_decisive_endpoint_packet slot
         (comma_source_continuation_base source)))"
proof (cases "comma_round_admitted source")
  case True
  then show ?thesis
    using comma_semantic_b1_source_slot_action_width_refines[OF True]
    by simp
next
  case False
  then show ?thesis
    using False
    by (simp only: comma_semantic_b1_source_slot_action_def if_False)
qed

declare comma_semantic_b1_source_slot_action_def[code del]
declare comma_semantic_b1_source_slot_action_code[code]

lemma comma_semantic_b1_source_slot_actions_refines:
  assumes admitted: "comma_round_admitted source"
  shows "comma_semantic_b1_source_slot_actions source =
    map (comma_semantic_b1_source_slot_action source)
      [0..<comma_decisive_sector_period
        (comma_source_continuation_base source)]"
proof -
  show ?thesis
    unfolding comma_semantic_b1_source_slot_actions_def
    by (rule map_cong[OF refl])
      (rule comma_semantic_b1_source_slot_action_width_refines[OF admitted])
qed

lemma comma_semantic_b1_source_slot_action_refines:
  assumes admitted: "comma_round_admitted source"
  shows "comma_semantic_b1_source_slot_action source slot =
    comma_source_continuation_action_at source slot"
  using comma_source_continuation_signature_slot[OF admitted, of slot]
  by (simp only: comma_semantic_b1_source_slot_action_def)

lemma comma_semantic_b1_noncrossing_successor_shift_zero:
  assumes target: "comma_source_continuation_shift target = 0"
    and transition: "comma_finite_step (residue mod 924) target =
      Comma_Next successor"
    and internal: "\<not> comma_round_crossing target successor"
  shows "comma_source_continuation_shift successor = 0"
  using target transition internal
  by (cases target; cases successor)
    (auto simp: comma_source_continuation_shift.simps comma_round_crossing_def
      comma_finite_step_def comma_weighted_step_def
      comma_weighted_step_with_headroom_def comma_finite_headroom_def Let_def
      split: if_splits)

lemma comma_semantic_b1_source_slot_action_shape:
  assumes admitted: "comma_round_admitted source"
    and normalized: "source = comma_source_continuation_base source"
  shows "comma_semantic_b1_local_action_shape
    (comma_semantic_b1_source_slot_action source slot)"
proof -
  let ?packet = "comma_decisive_endpoint_packet slot source"
  obtain target move where packet: "?packet = (target,move)"
    by (cases ?packet) auto
  have packet_base:
      "comma_decisive_endpoint_packet slot
        (comma_source_continuation_base source)=(target,move)"
    using packet normalized by simp
  have target_admitted: "comma_round_admitted target"
    using comma_decisive_packet_target_admitted[OF admitted, of slot] packet
    by simp
  have target_shift: "comma_source_continuation_shift target = 0"
    using comma_semantic_b1_base_packet_target_shift_zero
        [OF normalized, of slot] packet
    by simp
  have finite_move:
      "comma_finite_step (slot mod 924) target = move"
  proof -
    have fast_move:
        "comma_fast_step (slot mod 924) target = move"
      using packet by (auto simp: comma_decisive_endpoint_packet_def Let_def)
    show ?thesis using fast_move by (simp only: comma_fast_step_correct)
  qed
  show ?thesis
    using packet finite_move target_shift
  proof (cases move)
    case (Comma_Next successor)
    show ?thesis
    proof (cases "comma_round_crossing target successor")
      case True
      have crossing:
        "\<exists>delta headroom offset.
          target = Comma_Near 9 delta headroom \<and>
          successor = Comma_Entry 1 (Suc delta) offset \<and> offset \<le> 90"
        by (rule comma_round_crossing_offset_bound[OF _ True])
          (use finite_move Comma_Next in simp)
      then obtain delta headroom offset where
        target_shape: "target = Comma_Near 9 delta headroom" and
        successor_shape: "successor = Comma_Entry 1 (Suc delta) offset" and
        offset_bound: "offset \<le> 90"
        by blast
      have delta_zero: "delta=0"
        using target_shape target_shift by simp
      show ?thesis
        using packet_base Comma_Next True target_shape successor_shape
          delta_zero offset_bound
        by (simp add: comma_semantic_b1_source_slot_action_def
          comma_source_continuation_action_of_packet.simps
          comma_semantic_b1_local_action_shape.simps
          comma_round_crossing_def)
    next
      case False
      have shift_zero: "comma_source_continuation_shift successor=0"
        by (rule comma_semantic_b1_noncrossing_successor_shift_zero
          [OF target_shift _ False])
          (use finite_move Comma_Next in simp)
      show ?thesis
        using packet_base shift_zero False Comma_Next
        by (simp add: comma_semantic_b1_source_slot_action_def
          comma_source_continuation_action_of_packet.simps
          comma_semantic_b1_local_action_shape.simps)
    qed
  next
    case (Comma_Fork a delta)
    have delta_zero: "delta=0"
      using target_shift finite_move Comma_Fork
      by (cases target)
        (auto simp: comma_finite_step_def comma_weighted_step_def
          comma_weighted_step_with_headroom_def comma_finite_headroom_def Let_def
          split: if_splits)
    show ?thesis using packet_base Comma_Fork delta_zero
      by (simp add: comma_semantic_b1_source_slot_action_def
        comma_source_continuation_action_of_packet.simps
        comma_semantic_b1_local_action_shape.simps)
  next
    case (Comma_Landmine delta)
    have delta_zero: "delta=0"
      using target_shift finite_move Comma_Landmine
      by (cases target)
        (auto simp: comma_finite_step_def comma_weighted_step_def
          comma_weighted_step_with_headroom_def comma_finite_headroom_def Let_def
          split: if_splits)
    show ?thesis using packet_base Comma_Landmine delta_zero
      by (simp add: comma_semantic_b1_source_slot_action_def
        comma_source_continuation_action_of_packet.simps
        comma_semantic_b1_local_action_shape.simps)
  next
    case Comma_Invalid
    then show ?thesis using packet_base
      by (simp add: comma_semantic_b1_source_slot_action_def
        comma_semantic_b1_local_action_shape.simps)
  qed
qed

lemma comma_semantic_b1_source_period_admitted:
  assumes admitted: "comma_round_admitted source"
    and slot: "slot < comma_decisive_sector_period
      (comma_source_continuation_base source)"
  shows "comma_semantic_b1_crt_scope_admitted
    (comma_semantic_b1_source_slot_scope
      (comma_decisive_sector_period
        (comma_source_continuation_base source)) slot)"
proof -
  have base_admitted:
      "comma_round_admitted (comma_source_continuation_base source)"
    by (rule comma_source_continuation_base_admitted[OF admitted])
  have positive:
      "0 < comma_decisive_sector_period
        (comma_source_continuation_base source)"
    by (rule comma_decisive_sector_period_admitted(1)[OF base_admitted])
  have divides:
      "comma_decisive_sector_period
        (comma_source_continuation_base source) dvd 924"
    by (rule comma_decisive_sector_period_admitted(2)[OF base_admitted])
  show ?thesis
    using positive divides slot
    by (simp add: comma_semantic_b1_crt_scope_admitted_def
      comma_semantic_b1_scope_admitted_def
      comma_semantic_b1_source_slot_scope_def)
qed

lemma comma_semantic_b1_round_output_root_exact:
  assumes clock: "clock < 924" and root: "root < 46"
  shows "comma_semantic_b1_round_output clock
      (Comma_Entry 1 0 (comma_offset_representatives ! root)) =
    comma_semantic_b1 clock root"
  using clock root
  by (simp add: comma_semantic_b1_round_output_def
      comma_semantic_b1_def comma_decisive_B1_def
      comma_decisive_B1_source_def)

text \<open>
The recursive provider follows normalized Goto children under strict sector
decrease. A Goto intersects the current slot cylinder with its completed
child's rows. Terminal actions publish their exact result directly; no
discovered source-order list is required to establish this refinement.
\<close>

fun comma_semantic_b1_terminal_action_result ::
    "comma_source_continuation_action \<Rightarrow>
      comma_semantic_b1_result option" where
  "comma_semantic_b1_terminal_action_result
      (Comma_Continuation_Goto source shift) = None"
| "comma_semantic_b1_terminal_action_result
      (Comma_Continuation_Exit (Comma_Entry f delta offset) shift) =
    Some (if f=1 \<and> delta=0 \<and> offset\<le>90
      then Comma_Semantic_B1_Live (comma_offset_orbit offset)
      else Comma_Semantic_B1_Invalid)"
| "comma_semantic_b1_terminal_action_result
      (Comma_Continuation_Exit (Comma_Near f delta headroom) shift) =
    Some Comma_Semantic_B1_Invalid"
| "comma_semantic_b1_terminal_action_result
      (Comma_Continuation_Fork a shift) =
    Some (if 2\<le>a \<and> a\<le>9 then Comma_Semantic_B1_Stop (a-2)
      else Comma_Semantic_B1_Invalid)"
| "comma_semantic_b1_terminal_action_result
      (Comma_Continuation_Landmine shift) =
    Some (Comma_Semantic_B1_Stop 8)"
| "comma_semantic_b1_terminal_action_result
      Comma_Continuation_Invalid = Some Comma_Semantic_B1_Invalid"

definition comma_semantic_b1_source_slot_output ::
    "nat \<Rightarrow> comma_source_continuation_action \<Rightarrow>
      comma_semantic_b1_result" where
  "comma_semantic_b1_source_slot_output phase action =
    (case action of
       Comma_Continuation_Goto child shift \<Rightarrow>
         comma_semantic_b1_round_output phase child
     | action \<Rightarrow>
         (case comma_semantic_b1_terminal_action_result action of
            None \<Rightarrow> Comma_Semantic_B1_Invalid
          | Some result \<Rightarrow> result))"

lemma comma_semantic_b1_source_slot_round_output:
  assumes normalized:
      "source=comma_source_continuation_base source"
    and admitted: "comma_round_admitted source"
    and slot: "slot < comma_decisive_sector_period source"
    and phase: "phase<924"
    and selected: "phase mod comma_decisive_sector_period source=slot"
  shows "comma_semantic_b1_source_slot_output phase
      (comma_semantic_b1_source_slot_action source slot) =
    comma_semantic_b1_round_output phase source"
proof -
  let ?packet = "comma_decisive_endpoint_packet phase source"
  let ?action = "comma_semantic_b1_source_slot_action source slot"
  obtain target move where packet: "?packet=(target,move)"
    by (cases ?packet) auto
  have base_shift: "comma_source_continuation_shift source=0"
    using normalized by (cases source) simp_all
  have transport_zero:
      "comma_source_continuation_transport 0
        (comma_source_continuation_action_at source phase) =
        comma_source_continuation_action_at source phase"
    by (cases "comma_source_continuation_action_at source phase") simp_all
  have apply_exact:
    "comma_source_continuation_action_at source phase =
        comma_source_continuation_action_of_packet ?packet"
    using comma_source_continuation_apply_exact[OF admitted, of phase]
      normalized base_shift phase transport_zero
    by simp
  have action_periodic:
    "comma_source_continuation_action_at source slot =
        comma_source_continuation_action_at source phase"
    using selected slot normalized
    by (simp add: comma_source_continuation_action_at_def
      comma_source_continuation_id_def Let_def)
  have action_slot:
      "?action=comma_source_continuation_action_at source slot"
    using comma_semantic_b1_source_slot_action_refines[OF admitted, of slot]
    by simp
  have action_packet:
      "?action=comma_source_continuation_action_of_packet ?packet"
    using action_slot action_periodic apply_exact by simp
  have action_move:
      "?action=comma_source_continuation_action_of_packet (target,move)"
    using action_packet packet by simp
  have target_admitted: "comma_round_admitted target"
    using comma_decisive_packet_target_admitted[OF admitted, of phase] packet
    by simp
  have target_shift: "comma_source_continuation_shift target=0"
    using comma_semantic_b1_base_packet_target_shift_zero[OF normalized, of phase]
      packet by simp
  have packet_target: "comma_decisive_sector_target phase source=target"
    using packet
    by (simp add: comma_decisive_endpoint_packet_def Let_def)
  have fast_move: "comma_fast_step (phase mod 924) target=move"
    using packet packet_target
    by (auto simp: comma_decisive_endpoint_packet_def Let_def)
  have finite_move: "comma_finite_step (phase mod 924) target=move"
    using fast_move by (simp only: comma_fast_step_correct)
  have action_shape:
      "comma_semantic_b1_local_action_shape ?action"
    by (rule comma_semantic_b1_source_slot_action_shape[OF admitted normalized])
  have round_packet:
      "comma_decisive_endpoint_round phase source =
        (case move of
           Comma_Next successor \<Rightarrow>
             if comma_round_crossing target successor then
               Comma_Round_Cross successor
             else comma_decisive_endpoint_round phase successor
         | Comma_Fork a delta \<Rightarrow> Comma_Round_Fork a delta
         | Comma_Landmine delta \<Rightarrow> Comma_Round_Landmine delta
         | Comma_Invalid \<Rightarrow> Comma_Round_Invalid)"
    using comma_decisive_endpoint_round_packet[OF admitted] packet by simp
  show ?thesis
  proof (cases move)
    case (Comma_Next successor)
    show ?thesis
    proof (cases "comma_round_crossing target successor")
      case True
      have finite_next:
          "comma_finite_step (phase mod 924) target=Comma_Next successor"
        using finite_move Comma_Next by simp
      obtain delta headroom offset where target_shape:
          "target=Comma_Near 9 delta headroom"
        and successor_shape: "successor=Comma_Entry 1 (Suc delta) offset"
        and offset_bound: "offset\<le>90"
        using comma_round_crossing_offset_bound[OF finite_next True] by blast
      have delta_zero: "delta=0"
        using target_shape target_shift by simp
      have action_value:
          "?action=Comma_Continuation_Exit (Comma_Entry 1 0 offset) 1"
        using action_move Comma_Next True target_shape successor_shape delta_zero
        by (simp add: comma_source_continuation_action_of_packet.simps)
      show ?thesis
        using action_value round_packet Comma_Next True successor_shape
          delta_zero offset_bound
        by (simp add: comma_semantic_b1_source_slot_output_def
          comma_semantic_b1_terminal_action_result.simps
          comma_semantic_b1_round_output_def comma_semantic_b1_of_word.simps
          comma_sector_base_project.simps comma_decade_root_admitted_def
          comma_terminal_weight_encode_def)
    next
      case False
      have shift_zero: "comma_source_continuation_shift successor=0"
        using action_move action_shape Comma_Next False
        by (simp add: comma_semantic_b1_local_action_shape.simps
          comma_source_continuation_action_of_packet.simps)
      have successor_base:
          "comma_source_continuation_base successor=successor"
        using shift_zero by (cases successor) simp_all
      have action_value:
          "?action=Comma_Continuation_Goto successor 0"
        using action_move Comma_Next False shift_zero successor_base
        by (simp add: comma_source_continuation_action_of_packet.simps)
      show ?thesis
        using action_value round_packet Comma_Next False
        by (simp add: comma_semantic_b1_source_slot_output_def
          comma_semantic_b1_round_output_def)
    qed
  next
    case (Comma_Fork a delta)
    have finite_fork:
        "comma_finite_step (phase mod 924) target=Comma_Fork a delta"
      using finite_move Comma_Fork by simp
    have fork_bounds: "2\<le>a \<and> a\<le>9"
      by (rule comma_finite_fork_digit_bounds[OF finite_fork])
    have delta_zero: "delta=0"
      using action_move action_shape Comma_Fork
      by (simp add: comma_semantic_b1_local_action_shape.simps
        comma_source_continuation_action_of_packet.simps)
    show ?thesis
      using action_move round_packet Comma_Fork delta_zero fork_bounds
      by (simp add: comma_semantic_b1_source_slot_output_def
        comma_source_continuation_action_of_packet.simps
        comma_semantic_b1_terminal_action_result.simps
        comma_semantic_b1_round_output_def comma_semantic_b1_of_word.simps
        comma_sector_base_project.simps comma_terminal_weight_encode_def)
  next
    case (Comma_Landmine delta)
    have delta_zero: "delta=0"
      using action_move action_shape Comma_Landmine
      by (simp add: comma_semantic_b1_local_action_shape.simps
        comma_source_continuation_action_of_packet.simps)
    show ?thesis
      using action_move round_packet Comma_Landmine delta_zero
      by (simp add: comma_semantic_b1_source_slot_output_def
        comma_source_continuation_action_of_packet.simps
        comma_semantic_b1_terminal_action_result.simps
        comma_semantic_b1_round_output_def comma_semantic_b1_of_word.simps
        comma_sector_base_project.simps comma_terminal_weight_encode_def)
  next
    case Comma_Invalid
    show ?thesis
      using action_move round_packet Comma_Invalid
      by (simp add: comma_semantic_b1_source_slot_output_def
        comma_source_continuation_action_of_packet.simps
        comma_semantic_b1_terminal_action_result.simps
        comma_semantic_b1_round_output_def comma_semantic_b1_of_word.simps
        comma_sector_base_project.simps)
  qed
qed

lemma comma_semantic_b1_terminal_action_result_present:
  assumes non_goto: "\<not>(\<exists>child shift.
    action=Comma_Continuation_Goto child shift)"
  shows "\<exists>terminal_result.
    comma_semantic_b1_terminal_action_result action=Some terminal_result"
proof (cases action)
  case (Comma_Continuation_Goto child shift)
  then show ?thesis using non_goto by blast
next
  case (Comma_Continuation_Exit target shift)
  then show ?thesis
    by (cases target)
      (auto simp: comma_semantic_b1_terminal_action_result.simps)
next
  case (Comma_Continuation_Fork a shift)
  then show ?thesis
    by (simp add: comma_semantic_b1_terminal_action_result.simps)
next
  case (Comma_Continuation_Landmine shift)
  then show ?thesis
    by (simp add: comma_semantic_b1_terminal_action_result.simps)
next
  case Comma_Continuation_Invalid
  then show ?thesis
    by (simp add: comma_semantic_b1_terminal_action_result.simps)
qed

lemma comma_semantic_b1_terminal_action_output:
  assumes terminal:
    "comma_semantic_b1_terminal_action_result action=Some terminal_result"
  shows "comma_semantic_b1_source_slot_output phase action=terminal_result"
proof (cases action)
  case (Comma_Continuation_Goto child shift)
  then show ?thesis using terminal
    by (simp add: comma_semantic_b1_terminal_action_result.simps)
next
  case (Comma_Continuation_Exit target shift)
  then show ?thesis using terminal
    by (cases target)
      (auto simp: comma_semantic_b1_terminal_action_result.simps
        comma_semantic_b1_source_slot_output_def)
next
  case (Comma_Continuation_Fork a shift)
  then show ?thesis using terminal
    by (simp add: comma_semantic_b1_terminal_action_result.simps
      comma_semantic_b1_source_slot_output_def)
next
  case (Comma_Continuation_Landmine shift)
  then show ?thesis using terminal
    by (simp add: comma_semantic_b1_terminal_action_result.simps
      comma_semantic_b1_source_slot_output_def)
next
  case Comma_Continuation_Invalid
  then show ?thesis using terminal
    by (simp add: comma_semantic_b1_terminal_action_result.simps
      comma_semantic_b1_source_slot_output_def)
qed

ML \<open>
  val checked = @{thms comma_semantic_b1_source_slot_action_refines
    comma_semantic_b1_source_slot_action_width_refines
    comma_semantic_b1_source_slot_action_code
    comma_semantic_b1_source_slot_actions_refines
    comma_semantic_b1_source_slot_action_shape
    comma_semantic_b1_source_period_admitted
    comma_semantic_b1_round_output_root_exact};
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "B1 table-transform foundations" checked;
\<close>

end
