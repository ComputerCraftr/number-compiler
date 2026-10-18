theory Comma_C1_Entry_Chart_Refinement
  imports Comma_C1_Occurrence Comma_Chart_Bridge.Comma_Chart_Refinement
begin

text \<open>
An Entry chart macro is a guarded fixed-sector C1 segment.  The chart
clock remains the independent B1 exponent modulo 924; the physical number
of child steps is the macro cycle count times the decimal digit cycle.
The high prefix is retained explicitly so the powered cocycle returns the
same natural-number endpoint as the chart row.
\<close>

theorem comma_c1_powered_entry_chart_bridge:
  fixes f p delta offset q prefix h P L cycles steps :: nat
    and C :: comma_c1_phase
    and source near :: comma_finite_position
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and source_offset: "offset \<le> 98"
  defines "q \<equiv> p + delta"
    and "C \<equiv> comma_c1_phase_of f offset"
    and "prefix \<equiv> f * 10 ^ (q - 2)"
    and "source \<equiv> Comma_Entry f delta offset"
    and "near \<equiv> Comma_Near f delta
      (comma_finite_headroom f (p mod 924) delta offset)"
    and "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "cycles \<equiv> (10 ^ q - offset - h) div P"
    and "steps \<equiv> cycles * L"
  shows "comma_c1_source_admitted C prefix q steps"
    and "comma_chart_value p near =
      100 * (prefix + c1_count (comma_c1_powered_return C steps)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_powered_return C steps)))
          (c1_mod25 (c1_target (comma_c1_powered_return C steps)))"
    and "comma_chart_value p near =
      comma_chart_value p source + cycles * P"
    and "comma_literal_path steps
      (comma_chart_value p source) (comma_chart_value p near)"
    and "comma_c1_physical_occurrence
      (c1_target (comma_c1_powered_return C steps))
      (prefix + c1_count (comma_c1_powered_return C steps)) q
      (comma_chart_value p near)"
    and "comma_weighted_step (p mod 924) source =
      Comma_WNext near
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
proof -
  have q_bound: "5 \<le> q"
    using exponent by (simp add: q_def)
  have q_large: "2 \<le> q"
    using q_bound by arith
  have q_split: "q - 2 + 2 = q"
    using q_large by arith
  have power_split: "(10::nat) ^ q = 100 * 10 ^ (q - 2)"
  proof -
    have q_repr: "q = (q - 2) + 2"
      using q_split by arith
    have "(10::nat) ^ q = 10 ^ ((q - 2) + 2)"
      by (rule arg_cong[OF q_repr])
    also have "... = 10 ^ (q - 2) * 10 ^ 2"
      by (simp add: power_add)
    also have "... = 100 * 10 ^ (q - 2)"
      by (simp add: mult.commute)
    finally show ?thesis .
  qed
  have q_scale: "100000 \<le> (10::nat) ^ q"
  proof -
    have "(10::nat) ^ 5 \<le> 10 ^ q"
      by (rule power_increasing) (use q_bound in auto)
    then show ?thesis by simp
  qed
  have offset_below_scale: "offset \<le> 10 ^ q"
    using source_offset q_scale by arith
  have phase: "comma_c1_phase_admitted C"
    using comma_c1_phase_of_admitted[OF sector]
    by (simp add: C_def)
  have phase_sector: "c1_sector C = f"
    by (simp add: C_def comma_c1_phase_of_def)
  have decoded: "comma_c1_decode (c1_mod4 C) (c1_mod25 C) = offset"
    using source_offset by (simp add: C_def comma_c1_phase_of_def
      comma_c1_decode_residue)
  have start: "comma_chart_value p source =
      100 * prefix + comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
    using power_split decoded
    by (simp add: source_def prefix_def q_def comma_chart_value_def
        algebra_simps)
  have canonical_sector: "comma_sector f q (comma_chart_value p source)"
    using comma_entry_chart_checked_sector[OF sector exponent source_offset,
      of delta]
    by (simp add: source_def q_def)
  have headroom: "comma_headroom f q (comma_chart_value p source) =
      10 ^ q - offset"
    using offset_below_scale
    by (simp add: source_def prefix_def q_def comma_chart_value_def
        comma_headroom_def algebra_simps; arith)
  have cycle_closes: "10 dvd L * f"
    using comma_cycle_length_admitted(2)[OF sector]
    by (simp add: L_def)
  have period_refines:
    "P = comma_period_displacement f (offset mod 10) L"
    using comma_finite_period_refines[OF sector, of "offset mod 10"]
    by (simp add: P_def L_def)
  have positive_period: "0 < P"
    using comma_finite_period_in_catalog[rule_format,
        of f "offset mod 10"] sector
    by (auto simp: P_def comma_cycle_displacements_def)
  have selected_weighted_move:
    "comma_weighted_step (p mod 924) source =
      Comma_WNext near
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    using sector source_offset positive_period
    by (simp add: comma_weighted_step_def
        comma_weighted_step_with_headroom_def source_def near_def h_def
        P_def L_def Let_def)
  have reduced_headroom:
    "h = 1 + comma_finite_guard_extra f +
      (10 ^ q - offset - (1 + comma_finite_guard_extra f)) mod P"
    using comma_finite_headroom_reduced[OF sector exponent source_offset,
        of delta]
    by (simp add: h_def P_def q_def Let_def)
  have period_divides_gap: "P dvd 10 ^ q - offset - h"
    using comma_entry_chart_exact_literal_path(8)
      [OF sector exponent source_offset, of delta]
    by (simp add: h_def P_def q_def Let_def)
  have euclidean_gap:
    "10 ^ q - offset - h =
      ((10 ^ q - offset - h) div P) * P +
        (10 ^ q - offset - h) mod P"
    by (simp add: div_mult_mod_eq)
  have gap_remainder: "(10 ^ q - offset - h) mod P = 0"
    using period_divides_gap by (simp add: dvd_eq_mod_eq_0)
  have headroom_gap:
    "10 ^ q - offset - h = ((10 ^ q - offset - h) div P) * P"
    using euclidean_gap by (simp only: gap_remainder add_0)
  have chart_displacement:
    "cycles * P = 10 ^ q - offset - h"
    using headroom_gap by (simp add: cycles_def mult.commute)
  have chart_endpoint:
    "comma_chart_value p near =
      comma_chart_value p source + cycles * P"
    using comma_entry_chart_exact_literal_path(3)
      [OF sector exponent source_offset, of delta]
    by (simp add: source_def near_def h_def P_def q_def cycles_def)
  have zero_displacement: "comma_period_displacement f (offset mod 10) 0 = 0"
    by (simp add: comma_period_displacement_def)
  have repeated_displacement:
    "comma_period_displacement f (offset mod 10) steps = cycles * P"
    using comma_period_displacement_repeated[OF cycle_closes,
        of "offset mod 10" cycles 0]
    by (simp add: steps_def period_refines zero_displacement)
  have displacement:
    "comma_c1_displacement_prefix C steps = cycles * P"
    using comma_c1_displacement_prefix_refines[OF phase, of steps]
      decoded phase_sector repeated_displacement
    by simp
  have seam_reserve: "comma_finite_guard_extra f < h"
    using reduced_headroom by arith
  have h_bound: "h \<le> 540"
    using comma_finite_entry_headroom_admitted(2)
      [OF sector exponent source_offset, of delta]
    by (simp add: h_def)
  have h_below_gap: "h \<le> 10 ^ q - offset"
    using h_bound q_scale source_offset by arith
  have guard_extra:
    "(if f < 9 then 1 else 0) = comma_finite_guard_extra f"
    by (simp add: comma_finite_guard_extra_def)
  have guard_numeric:
    "10 ^ q - offset - h + (if f < 9 then 1 else 0) <
      10 ^ q - offset"
    using h_below_gap seam_reserve guard_extra by arith
  have guard:
    "comma_c1_displacement_prefix C steps +
      (if f < 9 then 1 else 0) <
        comma_headroom f q (comma_chart_value p source)"
    using guard_numeric
    by (simp only: displacement chart_displacement headroom)
  have admitted: "comma_c1_source_admitted C prefix q steps"
    unfolding comma_c1_source_admitted_def
    using phase q_large canonical_sector start guard phase_sector
    by simp
  have iter_physical:
    "comma_fixed_iter f steps (comma_chart_value p source) =
      100 * (prefix + comma_c1_count C steps) +
        comma_c1_decode
          (c1_mod4 (comma_c1_iter steps C))
          (c1_mod25 (comma_c1_iter steps C))"
    using comma_c1_iter_physical[OF phase, where H=prefix and n=steps]
      start phase_sector by simp
  have source_digit:
    "comma_chart_value p source mod 10 = offset mod 10"
    using comma_entry_chart_digit[of p f delta offset] exponent
    by (simp add: source_def)
  have iter_displacement_prefix:
    "comma_fixed_iter f steps (comma_chart_value p source) =
      comma_chart_value p source +
        comma_c1_displacement_prefix C steps"
    using comma_fixed_iter_displacement[of f steps
      "comma_chart_value p source"]
      comma_c1_displacement_prefix_refines[OF phase, of steps]
      source_digit phase_sector decoded
    by simp
  have powered_exact:
    "comma_c1_powered_return C steps = comma_c1_return C steps"
    by (rule comma_c1_powered_return_exact[OF phase])
  have powered_endpoint:
    "100 * (prefix + c1_count (comma_c1_powered_return C steps)) +
      comma_c1_decode
        (c1_mod4 (c1_target (comma_c1_powered_return C steps)))
        (c1_mod25 (c1_target (comma_c1_powered_return C steps))) =
      comma_chart_value p near"
    using iter_physical iter_displacement_prefix powered_exact
      chart_endpoint displacement
    by (simp add: comma_c1_return_def)
  have chart_c1_displacement:
    "comma_chart_value p near =
      comma_chart_value p source +
        comma_c1_displacement_prefix C steps"
    using powered_endpoint iter_physical iter_displacement_prefix
      powered_exact
    by (simp add: comma_c1_return_def)
  have powered_path:
    "comma_literal_path steps (comma_chart_value p source)
      (100 * (prefix + c1_count (comma_c1_powered_return C steps)) +
       comma_c1_decode
         (c1_mod4 (c1_target (comma_c1_powered_return C steps)))
         (c1_mod25 (c1_target (comma_c1_powered_return C steps))))"
    using comma_c1_fixed_sector_powered_occurrence_path(1)[OF admitted] start
      powered_endpoint
    by (simp add: C_def)
  have powered_occurrence:
    "comma_c1_physical_occurrence
      (c1_target (comma_c1_powered_return C steps))
      (prefix + c1_count (comma_c1_powered_return C steps)) q
      (100 * (prefix + c1_count (comma_c1_powered_return C steps)) +
       comma_c1_decode
         (c1_mod4 (c1_target (comma_c1_powered_return C steps)))
         (c1_mod25 (c1_target (comma_c1_powered_return C steps))))"
    using comma_c1_fixed_sector_powered_occurrence_path(2)[OF admitted]
    by simp
  show admitted: "comma_c1_source_admitted C prefix q steps"
    by (rule admitted)
  show endpoint_chart: "comma_chart_value p near =
      100 * (prefix + c1_count (comma_c1_powered_return C steps)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_powered_return C steps)))
          (c1_mod25 (c1_target (comma_c1_powered_return C steps)))"
    by (rule sym[OF powered_endpoint])
  show "comma_chart_value p near =
      comma_chart_value p source + cycles * P"
    using chart_c1_displacement displacement by simp
  show "comma_literal_path steps
      (comma_chart_value p source) (comma_chart_value p near)"
    using powered_path endpoint_chart by simp
  show "comma_c1_physical_occurrence
      (c1_target (comma_c1_powered_return C steps))
      (prefix + c1_count (comma_c1_powered_return C steps)) q
      (comma_chart_value p near)"
    using powered_occurrence endpoint_chart by simp
  show "comma_weighted_step (p mod 924) source =
      Comma_WNext near
        (Comma_Chart_Weight L delta (- int (L * (offset + h))) P)"
    by (rule selected_weighted_move)
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms comma_c1_powered_entry_chart_bridge}) then ()
    else error "C1 Entry chart refinement depends on an oracle";
\<close>

end
