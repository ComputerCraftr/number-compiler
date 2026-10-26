theory Comma_C1_B1_Source_Action
  imports Comma_Semantic_B1_Table_Transform
    Comma_Semantic_B1_Guarded_Port_Action
    Comma_C1_Occurrence.Comma_C1_Entry_Chart_Refinement
    Comma_C1_Occurrence.Comma_C1_Normalization_Morphism
begin

text \<open>
This bridge is upstream of the concrete B1 occurrence instance.  It relates
an admitted Entry source to the B1 source-slot action at the transported
exponent phase, while the C1 theorem supplies the exact weighted physical
Entry transition.  The two clocks remain distinct: the selector uses modulo
924 and the C1 return uses its physical step count.
\<close>

text \<open>
The source-selected clock is normalized independently of the physical C1
prefix. The resulting action retains the packet's guarded transition kind:
a crossing is an Exit, not a continuing Goto.
\<close>

definition comma_semantic_future_initial_sources :: "comma_finite_position list" where
  "comma_semantic_future_initial_sources =
    map (\<lambda>f. Comma_Near f 0 1) [1..<9] @
    map (\<lambda>a. Comma_Entry a 0 0) [2..<10]"

lemma comma_c1_b1_source_slot_action_transport:
  fixes source base :: comma_finite_position
    and r shift phase period slot :: nat
  assumes admitted: "comma_round_admitted source"
  defines "shift \<equiv> comma_source_continuation_shift source"
    and "base \<equiv> comma_source_continuation_base source"
    and "phase \<equiv> (r + shift) mod 924"
    and "period \<equiv> comma_decisive_sector_period base"
    and "slot \<equiv> phase mod period"
  shows "comma_source_continuation_transport shift
      (comma_semantic_b1_source_slot_action base slot) =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet (r mod 924) source)"
proof -
  have base_admitted: "comma_round_admitted base"
    using comma_source_continuation_base_admitted[OF admitted]
    by (simp add: base_def)
  have period_positive: "0 < period"
    using comma_decisive_sector_period_admitted(1)[OF base_admitted]
    by (simp add: period_def)
  have packet_period:
    "comma_decisive_endpoint_packet phase base =
      comma_decisive_endpoint_packet slot base"
    using comma_decisive_endpoint_packet_period[OF base_admitted,
        of phase slot]
    by (simp add: slot_def period_def period_positive)
  have slot_action:
    "comma_semantic_b1_source_slot_action base slot =
      comma_source_continuation_action_at base phase"
    using packet_period
      comma_source_continuation_signature_slot[OF base_admitted, of phase]
    by (simp only: comma_semantic_b1_source_slot_action_def base_def
        comma_source_continuation_base_idempotent)
  have transported:
    "comma_source_continuation_transport shift
        (comma_source_continuation_action_at base phase) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet (r mod 924) source)"
    using comma_source_continuation_apply_exact[OF admitted, of "r mod 924"]
    by (simp add: shift_def base_def phase_def mod_add_left_eq)
  show ?thesis using slot_action transported by simp
qed

definition comma_python_entry_b1_slot_matches ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_finite_position \<Rightarrow> bool" where
  "comma_python_entry_b1_slot_matches p f delta offset successor \<longleftrightarrow>
    (let source=Comma_Entry f delta offset;
         base=comma_source_continuation_base source;
         phase=(p+delta) mod 924;
         period=comma_decisive_sector_period base;
         slot=phase mod period;
         headroom=comma_finite_headroom f (p mod 924) delta offset
     in successor=Comma_Near f delta headroom \<and>
        comma_source_continuation_transport delta
          (comma_semantic_b1_source_slot_action base slot) =
          comma_source_continuation_action_of_packet
            (comma_decisive_endpoint_packet (p mod 924) source) \<and>
        comma_decisive_sector_target (p mod 924) source =
          Comma_Near f delta
            (snd (comma_near_closed_germ f headroom)))"

lemma comma_c1_entry_b1_slot_bridge:
  fixes f p delta offset h P L :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
  shows "comma_python_entry_b1_slot_matches p f delta offset
    (Comma_Near f delta h)"
proof -
  let ?source = "Comma_Entry f delta offset"
  let ?base = "Comma_Entry f 0 offset"
  let ?phase = "(p + delta) mod 924"
  let ?period = "comma_decisive_sector_period ?base"
  let ?slot = "?phase mod ?period"
  have weighted:
    "comma_weighted_step (p mod 924) ?source =
      Comma_WNext (Comma_Near f delta h)
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    using comma_c1_powered_entry_chart_bridge(6)[OF f exponent offset,
        where delta=delta]
    by (simp add: h_def P_def L_def)
  have finite_move:
    "comma_finite_step (p mod 924) ?source =
      Comma_Next (Comma_Near f delta h)"
    using comma_finite_step_is_erasure[of "p mod 924" ?source] weighted
    by simp
  have source_admitted: "comma_round_admitted ?source"
    using f offset by simp
  have fast_move:
    "comma_fast_step (p mod 924) ?source =
      Comma_Next (Comma_Near f delta h)"
    using finite_move by (simp only: comma_fast_step_correct)
  have fast_sector:
    "comma_fast_sector_target (p mod 924) ?source =
      Comma_Near f delta (snd (comma_near_closed_germ f h))"
    using fast_move by simp
  have decisive_sector:
    "comma_decisive_sector_target (p mod 924) ?source =
      Comma_Near f delta (snd (comma_near_closed_germ f h))"
    by (rule trans[OF comma_decisive_sector_target_refines_fast
          [OF source_admitted] fast_sector])
  have phase_transport:
    "((p mod 924 + delta) mod 924) = ?phase"
    by (simp add: mod_add_left_eq)
  have action_matches:
    "comma_source_continuation_transport delta
        (comma_semantic_b1_source_slot_action ?base ?slot) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet (p mod 924) ?source)"
    using comma_c1_b1_source_slot_action_transport[OF source_admitted,
        where r="p mod 924"]
    by (simp add: comma_source_continuation_shift.simps
        comma_source_continuation_base.simps phase_transport)
  show ?thesis
    using action_matches decisive_sector
    by (simp add: comma_python_entry_b1_slot_matches_def Let_def
        comma_source_continuation_base.simps h_def)
qed

text \<open>
The source-class producer evaluates an Entry port from the nine-core/CRT
selector and the admitted weighted port locator.  It is independent of a
published graph and returns the typed action, including the ordered target
source and the exact Goto/Exit distinction.  The occurrence's C1 weight and
headroom remain separate payload; neither the spatial carry ring nor the
selector clock is used as a substitute for the other.
\<close>

definition comma_c1_b1_entry_core_port_action ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> comma_source_continuation_action" where
  "comma_c1_b1_entry_core_port_action f offset slot =
    (let key = comma_decisive_entry_clock_key
        (comma_cyclotomic_clock_of (slot mod 924)) f offset
     in case comma_entry_port_refined_locator f (fst key) (snd key) of
       Some (active,residual,h) \<Rightarrow>
         comma_semantic_b1_near_control_port_action f 0 h
     | None \<Rightarrow> Comma_Continuation_Invalid)"

lemma comma_c1_b1_entry_core_port_action_source_exact:
  fixes f offset slot :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and offset: "offset \<le> 98"
  shows "comma_c1_b1_entry_core_port_action f offset slot =
    comma_semantic_b1_source_port_action (Comma_Entry f 0 offset) slot"
proof -
  have admitted: "comma_round_admitted (Comma_Entry f 0 offset)"
    using sector offset by simp
  have selected_exists:
    "\<exists>d eta active residual h.
      comma_decisive_entry_clock_key
        (comma_cyclotomic_clock_of (slot mod 924)) f offset = (d,eta) \<and>
      comma_entry_port_refined_locator f d eta = Some (active,residual,h) \<and>
      1 \<le> active \<and> active \<le> 9 \<and>
      residual < comma_port_dwell f active \<and>
      comma_fast_sector_target slot (Comma_Entry f 0 offset) =
        Comma_Near f 0 h"
    using comma_decisive_entry_core_clock_refines
      [OF sector(1) sector(2) offset, where r=slot and delta=0]
    by simp
  obtain d eta active residual h where selected:
    "comma_decisive_entry_clock_key
        (comma_cyclotomic_clock_of (slot mod 924)) f offset=(d,eta)"
    "comma_entry_port_refined_locator f d eta=Some (active,residual,h)"
    "1 \<le> active" "active \<le> 9"
    "residual < comma_port_dwell f active"
    "comma_fast_sector_target slot (Comma_Entry f 0 offset)=
      Comma_Near f 0 h"
    using selected_exists by blast
  show ?thesis
    using selected
    by (simp add: comma_c1_b1_entry_core_port_action_def
      comma_semantic_b1_source_port_action_def
      comma_decisive_sector_target.simps Let_def)
qed

lemma comma_c1_b1_entry_core_port_action_exact:
  fixes f offset slot :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and offset: "offset \<le> 98"
  shows "comma_c1_b1_entry_core_port_action f offset slot =
    comma_source_continuation_action_of_packet
      (comma_decisive_endpoint_packet slot (Comma_Entry f 0 offset))"
proof -
  have admitted: "comma_round_admitted (Comma_Entry f 0 offset)"
    using sector offset by simp
  have source_action:
    "comma_c1_b1_entry_core_port_action f offset slot =
      comma_semantic_b1_source_port_action (Comma_Entry f 0 offset) slot"
    by (rule comma_c1_b1_entry_core_port_action_source_exact[OF sector offset])
  have packet:
    "comma_semantic_b1_source_port_action (Comma_Entry f 0 offset) slot =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet slot (Comma_Entry f 0 offset))"
    using comma_semantic_b1_source_port_action_packet[OF admitted]
    by (simp add: comma_source_continuation_base.simps)
  show ?thesis using source_action packet by simp
qed

text \<open>
The typed control action is a representative-level object.  Its weighted
chart application remains source-bound and is certified independently below;
source-class transport must never identify distinct C1 occurrence weights.
\<close>

lemma comma_c1_b1_entry_occurrence_weight_exact:
  fixes f p delta offset h P L cycles steps width :: nat
    and C :: comma_c1_phase
    and source near :: comma_finite_position
    and z w :: "'a::comm_ring_1"
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and source_offset: "offset \<le> 98"
    and characteristic: "(32::'a)=0"
    and inverse_root: "z*w=1"
  defines "C \<equiv> comma_c1_phase_of f offset"
    and "source \<equiv> Comma_Entry f delta offset"
    and "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "near \<equiv> Comma_Near f delta h"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "cycles \<equiv> (10 ^ (p + delta) - offset - h) div P"
    and "steps \<equiv> cycles * L"
  shows "comma_weighted_step (p mod 924) source =
      Comma_WNext near
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    and "comma_c1_source_admitted C (f * 10 ^ (p + delta - 2))
      (p + delta) steps"
    and "(\<Sum>j<width. of_nat (comma_c1_source_carry_coefficient
          j C (f * 10 ^ (p + delta - 2)) steps)*z^j) =
      decimal_base_z_inverse_kernel w *
        ((\<Sum>j<width. of_nat (comma_c1_source_raw_coefficient
             j C (f * 10 ^ (p + delta - 2)) steps)*z^j) -
         (\<Sum>j<width. of_nat (comma_c1_source_normalized_coefficient
             j C (f * 10 ^ (p + delta - 2)) steps)*z^j) -
         (if width=0 then 0 else
           of_nat (comma_c1_source_carry_coefficient
             (width-1) C (f * 10 ^ (p + delta - 2)) steps)*z^width))"
proof -
  note bridge = comma_c1_powered_entry_chart_bridge
    [OF sector(1) sector(2) exponent source_offset,
      where delta=delta]
  show "comma_weighted_step (p mod 924) source =
      Comma_WNext near
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    using bridge(6)
    by (simp add: source_def near_def h_def L_def P_def)
  have admitted_c1:
    "comma_c1_source_admitted C (f * 10 ^ (p + delta - 2))
      (p + delta) steps"
    using bridge(1)
    by (simp add: C_def P_def L_def h_def cycles_def steps_def)
  show "comma_c1_source_admitted C (f * 10 ^ (p + delta - 2))
      (p + delta) steps"
    by (rule admitted_c1)
  show "(\<Sum>j<width. of_nat (comma_c1_source_carry_coefficient
          j C (f * 10 ^ (p + delta - 2)) steps)*z^j) =
      decimal_base_z_inverse_kernel w *
        ((\<Sum>j<width. of_nat (comma_c1_source_raw_coefficient
             j C (f * 10 ^ (p + delta - 2)) steps)*z^j) -
         (\<Sum>j<width. of_nat (comma_c1_source_normalized_coefficient
             j C (f * 10 ^ (p + delta - 2)) steps)*z^j) -
         (if width=0 then 0 else
           of_nat (comma_c1_source_carry_coefficient
             (width-1) C (f * 10 ^ (p + delta - 2)) steps)*z^width))"
    by (rule comma_c1_source_mod32_carry_morphism
      [OF admitted_c1 characteristic inverse_root])
qed

ML \<open>
  val checked = @{thms comma_c1_entry_b1_slot_bridge
    comma_c1_b1_entry_core_port_action_source_exact
    comma_c1_b1_entry_core_port_action_exact
    comma_c1_b1_entry_occurrence_weight_exact};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1/B1 Entry source-action bridge depends on an oracle";
\<close>

end
