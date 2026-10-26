theory Comma_C1_Entry_Chart_Refinement
  imports Comma_C1_Source_Coefficients
    Comma_Chart_Bridge.Comma_Chart_Refinement
begin

text \<open>
An Entry chart macro is a guarded fixed-sector C1 segment.  The chart
clock remains the independent B1 exponent modulo 924; the physical number
of child steps is the macro cycle count times the decimal digit cycle.
The high prefix is retained explicitly so the powered cocycle returns the
same natural-number endpoint as the chart row.
\<close>

text \<open>The source-bound coefficient carrier uses the authenticated fixed-
sector integer action. The temporal phase is still the C1 source phase; the
independent exponent selector modulo 924 remains an admission argument and
is not used as the spatial digit variable.
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

lemma comma_c1_powered_entry_chart_wire_tower:
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
  shows "comma_chart_value p near =
      100 * (prefix + c1_count (comma_c1_powered_return C steps)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_powered_return C steps)))
          (c1_mod25 (c1_target (comma_c1_powered_return C steps))) \<and>
    (\<forall>j. 2 \<le> j \<longrightarrow>
      comma_c1_carry_wire_total j C prefix steps =
        (prefix mod 10^(j-1) +
          c1_count (comma_c1_powered_return C steps)) div 10^(j-1))"
proof -
  have endpoint:
    "comma_chart_value p near =
      100 * (prefix + c1_count (comma_c1_powered_return C steps)) +
        comma_c1_decode
          (c1_mod4 (c1_target (comma_c1_powered_return C steps)))
          (c1_mod25 (c1_target (comma_c1_powered_return C steps)))"
    using comma_c1_powered_entry_chart_bridge(2)
      [OF sector exponent source_offset, where delta=delta]
    by (simp add: q_def C_def prefix_def source_def near_def h_def P_def
        L_def cycles_def steps_def)
  have phase: "comma_c1_phase_admitted C"
    using comma_c1_phase_of_admitted[OF sector]
    by (simp add: C_def)
  have powered_exact:
    "comma_c1_powered_return C steps = comma_c1_return C steps"
    by (rule comma_c1_powered_return_exact[OF phase])
  have wire_total:
    "\<forall>j. 2 \<le> j \<longrightarrow>
      comma_c1_carry_wire_total j C prefix steps =
        (prefix mod 10^(j-1) +
          c1_count (comma_c1_powered_return C steps)) div 10^(j-1)"
  proof (intro allI impI)
    fix j :: nat
    assume wire: "2 \<le> j"
    have exact:
      "comma_c1_carry_wire_total j C prefix steps =
        (prefix mod 10^(j-1) + comma_c1_count C steps) div 10^(j-1)"
      by (rule comma_c1_carry_wire_total_exact[OF wire])
    show "comma_c1_carry_wire_total j C prefix steps =
        (prefix mod 10^(j-1) +
          c1_count (comma_c1_powered_return C steps)) div 10^(j-1)"
      using exact powered_exact by (simp add: comma_c1_return_def)
  qed
  show ?thesis using endpoint wire_total by blast
qed

lemma comma_entry_ceil_arithmetic:
  fixes x h t k :: nat
  assumes balance: "100 * x = 100 * k + t + h"
    and digit: "t < 100"
  shows "k = x - ((h + 99) div 100)"
proof -
  have k_le_x: "k \<le> x" using balance by arith
  let ?e = "x - k"
  have quotient_balance: "100 * ?e = t + h"
    using balance k_le_x by arith
  have digit_upper: "t \<le> 99" using digit by arith
  have quotient_lower: "?e * 100 \<le> h + 99"
    using quotient_balance digit_upper by arith
  have h_le: "h \<le> 100 * ?e"
  proof -
    have "h \<le> t + h" by simp
    also have "... = 100 * ?e" by (rule quotient_balance[symmetric])
    finally show ?thesis .
  qed
  have h_shift: "h + 99 \<le> 100 * ?e + 99"
    using h_le by simp
  have next_shift: "100 * ?e + 99 < 100 * ?e + 100" by simp
  have quotient_upper: "h + 99 < (?e + 1) * 100"
    using le_less_trans[OF h_shift next_shift]
    by (simp only: distrib_right mult_1_left mult.commute)
  have ceil_lower: "?e \<le> (h + 99) div 100"
    using quotient_lower by (simp add: less_eq_div_iff_mult_less_eq)
  have ceil_upper: "(h + 99) div 100 < ?e + 1"
    using quotient_upper by (simp add: div_less_iff_less_mult)
  have ceil_exact: "(h + 99) div 100 = ?e"
    using ceil_lower ceil_upper by arith
  show ?thesis using ceil_exact k_le_x by arith
qed

text \<open>The Entry driver below is a fixed-sector arithmetic operator.
Its quotient is selected before physical path admission. The bounded border
packet is an output, not a semantic key or an input headroom certificate.\<close>

theorem comma_c1_entry_euclidean_packet:
  fixes f x q P L g A Q R n K t beta :: nat
    and C :: comma_c1_phase
  assumes sector: "1 \<le> f" "f \<le> 9"
    and width: "5 \<le> q" and suffix: "x \<le> 98"
  defines "C \<equiv> comma_c1_phase_of f x"
    and "P \<equiv> comma_finite_period f (x mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "g \<equiv> 1 + comma_finite_guard_extra f"
    and "A \<equiv> 10 ^ q - x - g"
    and "Q \<equiv> A div P"
    and "R \<equiv> A mod P"
    and "n \<equiv> Q * L"
    and "K \<equiv> comma_c1_count C n"
    and "t \<equiv> comma_c1_decode
      (c1_mod4 (comma_c1_iter n C)) (c1_mod25 (comma_c1_iter n C))"
    and "beta \<equiv> 10 ^ (q - 2) - K"
  shows "P * Q + R = A"
    and "R < P"
    and "1 \<le> g + R \<and> g + R \<le> 540"
    and "1 \<le> beta \<and> beta \<le> 6"
    and "K + beta = 10 ^ (q - 2)"
    and "100 * beta - t = g + R"
proof -
  have phase: "comma_c1_phase_admitted C"
    using comma_c1_phase_of_admitted[OF sector, of x]
    by (simp add: C_def)
  have period: "0 < P"
    using comma_finite_period_in_catalog[rule_format, of f "x mod 10"] sector
    by (auto simp: P_def comma_cycle_displacements_def)
  have period_guard: "P + comma_finite_guard_extra f \<le> 540"
    using comma_finite_period_guard_bound[OF sector, of "x mod 10"]
    by (simp add: P_def)
  have g_bounds: "1 \<le> g" "g \<le> 2"
    by (simp_all add: g_def comma_finite_guard_extra_def)
  have scale_lower: "100000 \<le> (10::nat) ^ q"
    using power_increasing[OF width, of "10::nat"] by simp
  have fits: "x + g \<le> 10 ^ q"
    using suffix g_bounds scale_lower by arith
  have division: "P * Q + R = A"
    by (simp add: Q_def R_def mult.commute)
  have remainder: "R < P"
    using period by (simp add: R_def)
  have packet_bounds: "1 \<le> g + R" "g + R \<le> 540"
    using g_bounds period_guard remainder by (auto simp: g_def)
  have euclidean_balance: "x + Q * P + g + R = 10 ^ q"
    using division fits by (simp add: A_def mult.commute; arith)
  have closes: "10 dvd L * f"
    using comma_cycle_length_admitted(2)[OF sector] by (simp add: L_def)
  have period_exact: "comma_period_displacement f (x mod 10) L = P"
    using comma_finite_period_refines[OF sector, of "x mod 10"]
    by (simp add: P_def L_def)
  have zero_displacement: "comma_period_displacement f (x mod 10) 0 = 0"
    by (simp add: comma_period_displacement_def)
  have displacement: "comma_period_displacement f (x mod 10) n = Q * P"
    using comma_period_displacement_repeated[OF closes,
      of "x mod 10" Q 0]
    by (simp add: n_def period_exact zero_displacement)
  have decode: "comma_c1_decode (c1_mod4 C) (c1_mod25 C) = x"
    using suffix by (simp add: C_def comma_c1_phase_of_def
      comma_c1_decode_residue)
  have sector_exact: "c1_sector C = f"
    by (simp add: C_def comma_c1_phase_of_def)
  have physical: "comma_fixed_iter f n x = 100 * K + t"
    using comma_c1_iter_physical[OF phase, where H=0 and n=n]
    by (simp add: decode sector_exact K_def t_def)
  have endpoint: "x + Q * P = 100 * K + t"
    using comma_fixed_iter_displacement[of f n x] physical displacement by simp
  have t_bound: "t < 100"
    by (simp add: t_def comma_c1_decode_def)
  have power_split: "(10::nat) ^ q = 100 * 10 ^ (q - 2)"
  proof -
    have split: "q = (q - 2) + 2" using width by arith
    show ?thesis by (subst split) (simp add: power_add mult.commute)
  qed
  have carry_balance:
    "100 * 10 ^ (q - 2) = 100 * K + t + (g + R)"
    using euclidean_balance endpoint power_split by arith
  have count_bound: "K \<le> 10 ^ (q - 2)"
    using carry_balance by arith
  have beta_balance: "100 * beta = t + (g + R)"
    using carry_balance count_bound by (simp add: beta_def; arith)
  have beta_bounds: "1 \<le> beta" "beta \<le> 6"
    using beta_balance packet_bounds t_bound by arith+
  show "P * Q + R = A" by (rule division)
  show "R < P" by (rule remainder)
  show "1 \<le> g + R \<and> g + R \<le> 540"
    using packet_bounds by blast
  show "1 \<le> beta \<and> beta \<le> 6" using beta_bounds by blast
  show "K + beta = 10 ^ (q - 2)"
    using count_bound by (simp add: beta_def)
  show "100 * beta - t = g + R" using beta_balance by arith
qed

theorem comma_c1_powered_entry_count_closed:
  fixes f p delta offset q h P L cycles steps :: nat
    and C :: comma_c1_phase
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and source_offset: "offset \<le> 98"
  defines "q \<equiv> p + delta"
    and "C \<equiv> comma_c1_phase_of f offset"
    and "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "cycles \<equiv> (10 ^ q - offset - h) div P"
    and "steps \<equiv> cycles * L"
  shows "c1_count (comma_c1_powered_return C steps) =
    10 ^ (q - 2) - ((h + 99) div 100)"
proof -
  have q_bound: "5 \<le> q" using exponent by (simp add: q_def)
  let ?g = "1 + comma_finite_guard_extra f"
  let ?A = "10 ^ q - offset - ?g"
  let ?Q = "?A div P"
  let ?R = "?A mod P"
  let ?K = "comma_c1_count C (?Q * L)"
  let ?t = "comma_c1_decode
      (c1_mod4 (comma_c1_iter (?Q * L) C))
      (c1_mod25 (comma_c1_iter (?Q * L) C))"
  let ?beta = "10 ^ (q - 2) - ?K"

  have packet_division:
    "P * ?Q + ?R = ?A"
    using comma_c1_entry_euclidean_packet(1)
      [OF sector q_bound source_offset]
    by (simp add: P_def)
  have packet_count:
    "?K + ?beta = 10 ^ (q - 2)"
    using comma_c1_entry_euclidean_packet(5)
      [OF sector q_bound source_offset]
    by (simp add: C_def P_def L_def)
  have packet_carry:
    "100 * ?beta - ?t = ?g + ?R"
    using comma_c1_entry_euclidean_packet(6)
      [OF sector q_bound source_offset]
    by (simp add: C_def P_def L_def)
  have packet_beta:
    "1 \<le> ?beta"
    using comma_c1_entry_euclidean_packet(4)
      [OF sector q_bound source_offset]
    by (simp add: C_def P_def L_def)

  have reduced_headroom: "h = ?g + ?R"
    using comma_finite_headroom_reduced
      [OF sector exponent source_offset, of delta]
    by (simp add: h_def q_def P_def Let_def)
  have positive_period: "0 < P"
    using comma_finite_period_in_catalog[rule_format,
        of f "offset mod 10"] sector
    by (auto simp: P_def comma_cycle_displacements_def)
  have gap: "10 ^ q - offset - h = P * ?Q"
  proof -
    have cancelled: "?A - ?R = P * ?Q"
      using arg_cong[OF packet_division, of "\<lambda>u::nat. u - ?R"]
      by (simp only: add_diff_cancel_right')
    have rebased: "10 ^ q - offset - h = ?A - ?R"
      by (simp only: reduced_headroom diff_diff_left add.assoc)
    show ?thesis by (rule trans[OF rebased cancelled])
  qed
  have cycles_eq: "cycles = ?Q"
    using gap positive_period
    by (simp add: cycles_def mult.commute)
  have steps_eq: "steps = ?Q * L"
    by (simp add: steps_def cycles_eq)

  have phase: "comma_c1_phase_admitted C"
    using comma_c1_phase_of_admitted[OF sector]
    by (simp add: C_def)
  have powered_exact:
    "comma_c1_powered_return C steps = comma_c1_return C steps"
    by (rule comma_c1_powered_return_exact[OF phase])
  have count_eq:
    "c1_count (comma_c1_powered_return C steps) = ?K"
    using powered_exact by (simp add: comma_c1_return_def steps_eq)

  have digit_bound: "?t < 100"
    by (simp add: comma_c1_decode_def)
  have carry_balance: "100 * ?beta = ?t + h"
    using packet_carry reduced_headroom packet_beta digit_bound by arith
  have balance: "100 * 10 ^ (q - 2) = 100 * ?K + ?t + h"
    using packet_count carry_balance by arith
  have ceiling: "?K = 10 ^ (q - 2) - ((h + 99) div 100)"
    by (rule comma_entry_ceil_arithmetic[OF balance digit_bound])
  show ?thesis using count_eq ceiling by simp
qed


lemma comma_nat_power_borrow_quotient:
  fixes m u beta :: nat
  assumes m_positive: "0 < m"
    and u_positive: "0 < u"
    and beta_positive: "0 < beta"
    and beta_small: "beta < m"
  shows "(m * u - beta) div m = u - 1"
proof -
  have u_split: "u = (u - 1) + 1" using u_positive by arith
  have product_split: "m * u = m * (u - 1) + m"
  proof -
    have "m * u = m * ((u - 1) + 1)"
      by (rule arg_cong[OF u_split])
    also have "... = m * (u - 1) + m"
      by (simp add: distrib_left)
    finally show ?thesis .
  qed
  have difference_split:
    "m * u - beta = m * (u - 1) + (m - beta)"
    using product_split beta_small by arith
  have remainder_bound: "m - beta < m"
    using beta_positive m_positive by arith
  have product_div: "(m * (u - 1)) div m = u - 1"
    using m_positive by (simp add: mult.commute)
  have product_mod: "(m * (u - 1)) mod m = 0"
    by (simp add: mult.commute)
  have remainder_div: "(m - beta) div m = 0"
    using remainder_bound by simp
  have remainder_mod: "(m - beta) mod m = m - beta"
    using remainder_bound by simp
  have sum_div:
    "(m * (u - 1) + (m - beta)) div m =
      (m * (u - 1)) div m + (m - beta) div m +
        ((m * (u - 1)) mod m + (m - beta) mod m) div m"
    by (rule div_add1_eq)
  have reduced_sum: "(m * (u - 1) + (m - beta)) div m = u - 1"
    using sum_div product_div product_mod remainder_div remainder_mod
      remainder_bound by simp
  show ?thesis using difference_split reduced_sum by simp
qed

lemma comma_entry_ceil_bounds:
  fixes h :: nat
  assumes lower: "1 \<le> h" and upper: "h \<le> 540"
  shows "1 \<le> (h + 99) div 100" "(h + 99) div 100 \<le> 6"
proof -
  have quotient_lower: "100 \<le> h + 99" using lower by arith
  have beta_lower: "1 \<le> (h + 99) div 100"
    using quotient_lower by (simp add: less_eq_div_iff_mult_less_eq)
  have quotient_upper: "h + 99 < 7 * 100" using upper by arith
  have beta_upper: "(h + 99) div 100 < 7"
    using quotient_upper by (simp add: div_less_iff_less_mult)
  show "1 \<le> (h + 99) div 100" by (rule beta_lower)
  show "(h + 99) div 100 \<le> 6" using beta_upper by arith
qed

theorem comma_c1_powered_entry_higher_wire_closed:
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
  shows "(\<forall>j. 2 \<le> j \<and> j < q \<longrightarrow>
      comma_c1_carry_wire_total j C prefix steps =
        10 ^ (q - j - 1) - 1) \<and>
    (\<forall>j. q \<le> j \<longrightarrow>
      comma_c1_carry_wire_total j C prefix steps = 0)"
proof -
  have q_bound: "5 \<le> q" using exponent by (simp add: q_def)
  have h_positive:
    "1 \<le> comma_finite_headroom f (p mod 924) delta offset"
    using comma_finite_entry_headroom_admitted(1)
      [OF sector exponent source_offset, of delta] by simp
  have h_bound:
    "comma_finite_headroom f (p mod 924) delta offset \<le> 540"
    using comma_finite_entry_headroom_admitted(2)
      [OF sector exponent source_offset, of delta] by simp
  have h_numeric: "1 \<le> h" "h \<le> 540"
    using h_positive h_bound by (simp_all add: h_def)
  have beta_bounds:
    "1 \<le> (h + 99) div 100" "(h + 99) div 100 \<le> 6"
    using comma_entry_ceil_bounds[OF h_numeric] by blast+
  have q_large: "2 \<le> q" using q_bound by arith
  have phase: "comma_c1_phase_admitted C"
    using comma_c1_phase_of_admitted[OF sector] by (simp add: C_def)
  have powered_exact:
    "comma_c1_powered_return C steps = comma_c1_return C steps"
    by (rule comma_c1_powered_return_exact[OF phase])
  have count_closed:
    "c1_count (comma_c1_powered_return C steps) =
      10 ^ (q - 2) - ((h + 99) div 100)"
    using comma_c1_powered_entry_count_closed
      [OF sector exponent source_offset, where delta=delta]
    by (simp add: q_def C_def prefix_def source_def near_def h_def P_def
        L_def cycles_def steps_def)
  have prefix_shape: "prefix = f * 10 ^ (q - 2)"
    by (simp add: prefix_def)
  have generic_total:
    "comma_c1_carry_wire_total j C prefix steps =
      (prefix mod 10^(j-1) +
        c1_count (comma_c1_powered_return C steps)) div 10^(j-1)"
    if "2 \<le> j" for j
  proof -
    have base:
      "comma_c1_carry_wire_total j C prefix steps =
        (prefix mod 10^(j-1) + comma_c1_count C steps) div 10^(j-1)"
      by (rule comma_c1_carry_wire_total_exact[OF that])
    show ?thesis using base powered_exact
      by (simp add: comma_c1_return_def)
  qed
  have lower_wires:
    "comma_c1_carry_wire_total j C prefix steps =
      10 ^ (q - j - 1) - 1"
    if j_bound: "2 \<le> j" "j < q" for j
  proof -
    let ?m = "(10::nat)^(j-1)"
    let ?u = "(10::nat)^(q-j-1)"
    have exp_split: "q - 2 = (j - 1) + (q - j - 1)"
      using j_bound by arith
    have power_split: "(10::nat)^(q-2) = ?m * ?u"
      using exp_split by (simp only: power_add)
    have m_positive: "0 < ?m" by simp
    have m_at_least_ten: "10 \<le> ?m"
    proof -
      have "(10::nat)^1 \<le> 10^(j-1)"
        by (rule power_increasing) (use j_bound(1) in auto)
      then show ?thesis by simp
    qed
    have beta_small: "(h + 99) div 100 < ?m"
      using beta_bounds(2) m_at_least_ten by arith
    have u_positive: "0 < ?u" by simp
    have beta_positive: "0 < (h + 99) div 100"
      using beta_bounds(1) by simp
    have prefix_mod: "prefix mod ?m = 0"
      using comma_c1_boundary_high_zero[where a=f and p=q and j=j] j_bound
      by (simp add: prefix_shape)
    have quotient:
      "(?m * ?u - (h + 99) div 100) div ?m = ?u - 1"
      by (rule comma_nat_power_borrow_quotient
        [OF m_positive u_positive beta_positive beta_small])
    have total:
      "comma_c1_carry_wire_total j C prefix steps =
        (prefix mod ?m +
          c1_count (comma_c1_powered_return C steps)) div ?m"
      by (rule generic_total[OF j_bound(1)])
    show ?thesis
      using total prefix_mod count_closed power_split quotient
      by simp
  qed
  have upper_wires:
    "comma_c1_carry_wire_total j C prefix steps = 0"
    if j_bound: "q \<le> j" for j
  proof -
    let ?m = "(10::nat)^(j-1)"
    let ?x = "(10::nat)^(q-2)"
    have j_large: "2 \<le> j" using q_bound j_bound by arith
    have x_positive: "0 < ?x" by simp
    have exponent_split: "q - 1 = Suc (q - 2)"
      using q_bound by arith
    have scale_split: "10 * ?x = (10::nat)^(q-1)"
      using exponent_split by (simp add: power_Suc mult.commute)
    have exponent_order: "q - 1 \<le> j - 1"
      using j_bound by arith
    have modulus_order: "(10::nat)^(q-1) \<le> ?m"
      by (rule power_increasing) (use exponent_order in auto)
    have m_positive: "0 < ?m" by simp
    have prefix_bound: "prefix \<le> 9 * ?x"
    proof -
      have factor: "f * ?x \<le> 9 * ?x"
        using sector(2) by (rule mult_right_mono) simp
      show ?thesis using prefix_shape factor by simp
    qed
    have beta_positive: "0 < (h + 99) div 100"
      using beta_bounds(1) by simp
    have count_bound:
      "c1_count (comma_c1_powered_return C steps) \<le> ?x - 1"
      using count_closed beta_bounds x_positive by arith
    have prefix_small: "prefix < ?m"
      using prefix_bound scale_split modulus_order x_positive by arith
    have sum_small:
      "prefix + c1_count (comma_c1_powered_return C steps) < ?m"
      using prefix_bound count_bound scale_split modulus_order x_positive
      by arith
    have total:
      "comma_c1_carry_wire_total j C prefix steps =
        (prefix mod ?m +
          c1_count (comma_c1_powered_return C steps)) div ?m"
      by (rule generic_total[OF j_large])
    have numerator_small:
      "prefix mod ?m +
        c1_count (comma_c1_powered_return C steps) < ?m"
      using prefix_small sum_small by simp
    have quotient_lt_one:
      "(prefix mod ?m +
        c1_count (comma_c1_powered_return C steps)) div ?m < 1"
      using numerator_small m_positive
      by (simp add: div_less_iff_less_mult)
    show ?thesis using total quotient_lt_one by simp
  qed
  show ?thesis using lower_wires upper_wires by blast
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
      @{thms comma_c1_powered_entry_chart_bridge
        comma_entry_ceil_arithmetic comma_c1_powered_entry_count_closed
        comma_nat_power_borrow_quotient comma_entry_ceil_bounds
        comma_c1_entry_euclidean_packet
        comma_c1_powered_entry_higher_wire_closed}) then ()
    else error "C1 Entry chart refinement depends on an oracle";
\<close>

end
