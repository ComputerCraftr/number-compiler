theory Comma_Semantic_Producer_Record_Refinement
  imports Comma_Semantic_Fragment_Refinement
    Comma_C1_Occurrence.Comma_C1_Entry_Chart_Refinement
    Comma_Semantic_B1_Table_Transform
begin

text \<open>
An Entry record ends at the C1 Near headroom supplied by its weighted
transition.  B1's normalized source slot then applies the complete Near
sector germ.  The phase used to select that slot is the transported residue
`(p + delta) mod 924`; the C1 physical path length remains separate.
\<close>

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
  let ?packet = "comma_decisive_endpoint_packet ?phase ?base"
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
  have base_admitted: "comma_round_admitted ?base"
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
    using comma_decisive_sector_target_refines_fast[OF source_admitted]
      fast_sector by simp
  have phase_transport:
    "((p mod 924 + delta) mod 924) = ?phase"
    by (simp add: mod_add_left_eq)
  have period_positive: "0 < ?period"
    by (rule comma_decisive_sector_period_admitted(1)[OF base_admitted])
  have packet_period:
    "comma_decisive_endpoint_packet ?phase ?base =
      comma_decisive_endpoint_packet ?slot ?base"
    by (rule comma_decisive_endpoint_packet_period[OF base_admitted])
      (simp add: period_positive)
  have slot_action:
    "comma_semantic_b1_source_slot_action ?base ?slot =
      comma_source_continuation_action_at ?base ?phase"
    using packet_period
    by (simp add: comma_semantic_b1_source_slot_action_def
        comma_source_continuation_signature_slot[OF base_admitted])
  have transported_action:
    "comma_source_continuation_transport delta
        (comma_source_continuation_action_at ?base ?phase) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet (p mod 924) ?source)"
    using comma_source_continuation_apply_exact[OF source_admitted,
        where r="p mod 924"]
    by (simp add: comma_source_continuation_shift.simps
        comma_source_continuation_base.simps phase_transport)
  have action_matches:
    "comma_source_continuation_transport delta
        (comma_semantic_b1_source_slot_action ?base ?slot) =
      comma_source_continuation_action_of_packet
        (comma_decisive_endpoint_packet (p mod 924) ?source)"
    using slot_action transported_action by simp
  show ?thesis
    using action_matches decisive_sector
    by (simp add: comma_python_entry_b1_slot_matches_def Let_def
        comma_source_continuation_base.simps)
qed

definition comma_python_fragment_record_matches ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_finite_position \<Rightarrow> comma_chart_weight \<Rightarrow>
    comma_python_sector_fragment \<Rightarrow> bool" where
  "comma_python_fragment_record_matches p source successor weight fragment \<longleftrightarrow>
    comma_weighted_step (p mod 924) source =
      Comma_WNext successor weight \<and>
    (case source of
      Comma_Entry f delta offset \<Rightarrow>
        fragment = comma_python_entry_sector_fragment f delta offset
          (comma_finite_headroom f (p mod 924) delta offset) \<and>
        comma_python_entry_b1_slot_matches p f delta offset successor
    | Comma_Near f delta headroom \<Rightarrow>
        (\<exists>increment. comma_chart_value p successor =
            comma_chart_value p source + increment \<and>
          fragment = comma_python_literal_fragment f
            (comma_chart_value p source mod 10) 1 increment)) \<and>
    comma_python_fragment_weight_at_scale fragment (10 ^ p) =
      int (comma_chart_weight_value p weight) \<and>
    comma_python_fragment_displacement_at_scale fragment (10 ^ p) =
      int (comma_chart_value p successor) - int (comma_chart_value p source)"

text \<open>The relation above makes the local record payload explicit: a
Near increment is a natural number witnessed by the endpoint equation, so the
producer refinement does not cast a possibly negative displacement to
\<^typ>\<open>nat\<close>.\<close>



text \<open>The Entry record's affine displacement is tied to the exact endpoint
selected by the powered C1 occurrence path. The source-chart arithmetic
justifies the physical duration and seam guard; it does not identify the
physical C1 clock with the exponent-phase clock.\<close>

lemma comma_python_entry_record_matches:
  fixes f p delta offset h P L c :: nat
    and source successor :: comma_finite_position
    and weight :: comma_chart_weight
    and fragment :: comma_python_sector_fragment
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "c \<equiv> (10 ^ (p + delta) - offset - h) div P"
    and "source \<equiv> Comma_Entry f delta offset"
    and "successor \<equiv> Comma_Near f delta h"
    and "weight \<equiv> Comma_Chart_Weight L delta
      (- int (L * (offset + h))) P"
    and "fragment \<equiv> comma_python_entry_sector_fragment f delta offset h"
  shows "comma_python_fragment_record_matches p source successor weight fragment"
proof -
  note fields = comma_python_entry_fragment_refines_chart_move
    [OF f exponent offset, of delta]
  let ?C = "comma_c1_phase_of f offset"
  let ?prefix = "f * 10 ^ (p + delta - 2)"
  let ?steps = "c * L"
  have powered_endpoint:
    "comma_chart_value p successor =
      100 * (?prefix +
        c1_count (comma_c1_powered_return ?C ?steps)) +
      comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_powered_return ?C ?steps)))
        (c1_mod25 (c1_target (comma_c1_powered_return ?C ?steps)))"
    using comma_c1_powered_entry_chart_bridge(2)[OF f exponent offset,
      where delta=delta]
    by (simp add: h_def P_def L_def c_def source_def successor_def)
  have endpoint:
    "comma_chart_value p successor =
      comma_chart_value p source + c * P"
    using comma_c1_powered_entry_chart_bridge(3)[OF f exponent offset,
      where delta=delta]
    by (simp add: h_def P_def L_def c_def source_def successor_def)
  have powered_increment:
    "int (100 * (?prefix +
        c1_count (comma_c1_powered_return ?C ?steps)) +
      comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_powered_return ?C ?steps)))
        (c1_mod25 (c1_target (comma_c1_powered_return ?C ?steps)))) -
      int (comma_chart_value p source) = int (c * P)"
    using powered_endpoint endpoint by simp
  have row_displacement:
    "comma_python_fragment_displacement_at_scale fragment (10 ^ p) =
      int (comma_chart_value p successor) - int (comma_chart_value p source)"
    using fields(6) powered_increment powered_endpoint
    by (simp add: fragment_def P_def)
  have b1_slot_matches:
    "comma_python_entry_b1_slot_matches p f delta offset successor"
    using comma_c1_entry_b1_slot_bridge[OF f exponent offset,
        where delta=delta]
    by (simp add: h_def successor_def)
  show ?thesis
    using fields(1,5) row_displacement b1_slot_matches
    by (simp add: comma_python_fragment_record_matches_def source_def
        successor_def weight_def fragment_def h_def P_def L_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms comma_python_entry_record_matches
        comma_c1_entry_b1_slot_bridge}) then ()
    else error "Comma producer record refinement depends on an oracle";
\<close>

end
