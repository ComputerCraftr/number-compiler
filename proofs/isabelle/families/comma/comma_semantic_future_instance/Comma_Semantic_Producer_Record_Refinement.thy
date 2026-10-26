theory Comma_Semantic_Producer_Record_Refinement
  imports Comma_Semantic_Fragment_Refinement
    Comma_C1_Occurrence.Comma_C1_Entry_Chart_Refinement
    Comma_Semantic_B1.Comma_C1_B1_Source_Action
    Comma_Semantic_B1_Table_Transform
begin

text \<open>
An Entry record ends at the C1 Near headroom supplied by its weighted
transition.  B1's normalized source slot then applies the complete Near
sector germ.  The phase used to select that slot is the transported residue
`(p + delta) mod 924`; the C1 physical path length remains separate.
\<close>

definition comma_python_entry_c1_wire_tower_matches ::
    "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
      comma_finite_position \<Rightarrow> bool" where
  "comma_python_entry_c1_wire_tower_matches p f delta offset successor \<longleftrightarrow>
    (let q=p+delta;
         C=comma_c1_phase_of f offset;
         prefix=f*10^(q-2);
         h=comma_finite_headroom f (p mod 924) delta offset;
         P=comma_finite_period f (offset mod 10);
         cycles=(10^q-offset-h) div P;
         steps=cycles*comma_cycle_length f
     in successor=Comma_Near f delta h \<and>
        c1_count (comma_c1_powered_return C steps) =
          10^(q-2) - ((h+99) div 100) \<and>
        (\<forall>j. 2 \<le> j \<longrightarrow>
          comma_c1_carry_wire_total j C prefix steps =
            (prefix mod 10^(j-1) +
              c1_count (comma_c1_powered_return C steps)) div 10^(j-1)) \<and>
        (\<forall>j. 2 \<le> j \<and> j < q \<longrightarrow>
          comma_c1_carry_wire_total j C prefix steps = 10^(q-j-1)-1) \<and>
        (\<forall>j. q \<le> j \<longrightarrow>
          comma_c1_carry_wire_total j C prefix steps = 0))"

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
        comma_python_entry_c1_wire_tower_matches
          p f delta offset successor \<and>
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
  have c1_wire_tower_matches:
    "comma_python_entry_c1_wire_tower_matches p f delta offset successor"
    using comma_c1_powered_entry_chart_wire_tower
      [OF f exponent offset, where delta=delta]
      comma_c1_powered_entry_count_closed
        [OF f exponent offset, where delta=delta]
      comma_c1_powered_entry_higher_wire_closed
        [OF f exponent offset, where delta=delta]
    by (simp add: comma_python_entry_c1_wire_tower_matches_def
        h_def P_def L_def c_def source_def successor_def)
  show ?thesis
    using fields(1,5) row_displacement b1_slot_matches c1_wire_tower_matches
    by (simp add: comma_python_fragment_record_matches_def source_def
        successor_def weight_def fragment_def h_def P_def L_def)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms comma_python_entry_record_matches
        comma_c1_entry_b1_slot_bridge
        comma_c1_powered_entry_chart_wire_tower
        comma_c1_powered_entry_count_closed
        comma_c1_powered_entry_higher_wire_closed}) then ()
    else error "Comma producer record refinement depends on an oracle";
\<close>

end
