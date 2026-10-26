theory Comma_C1_Near_Chart_Refinement
  imports Comma_C1_Entry_Chart_Refinement
    Comma_Near_Period.Comma_Near_Period
begin

text \<open>A strict Near prefix is a fixed-sector C1 source segment.  The
prefix relation supplies both the exact headroom displacement and the
reserved boundary margin; source admission therefore certifies every
physical step, while the 924-phase selector remains an independent input
to the finite chart state.  A prefix ending at a fork, landmine, or sector
crossing is deliberately outside this theorem.\<close>

lemma comma_near_prefix_endpoint_reserve:
  fixes n f h t :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and initial: "1 \<le> h" "h \<le> 540"
    and positive: "0 < n"
    and path: "comma_near_prefix n f h t"
  shows "(if f < 9 then 2 else 1) \<le> t"
  using path sector initial positive
proof (induction n arbitrary: h)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have h_bounds: "1 \<le> h" "h \<le> 540" using Suc.prems by auto
  obtain j where step:
      "comma_finite_step 0 (Comma_Near f 0 h) =
        Comma_Next (Comma_Near f 0 j)"
    and tail: "comma_near_prefix n f j t"
    using Suc.prems by auto
  let ?d = "(10 - h mod 10) mod 10"
  have step_formula:
      "10 * ?d + f + (if f < 9 then 1 else 0) < h"
      "j = h - (10 * ?d + f)"
    using step sector h_bounds
    by (auto simp: comma_near_internal_iff
      [OF sector(1) sector(2) h_bounds(1) h_bounds(2)])
  have margin: "(if f < 9 then 1 else 0) < j"
    using step_formula by (simp only: less_diff_conv add.commute)
  have j_reserve: "(if f < 9 then 2 else 1) \<le> j"
    using margin by (cases "f < 9") simp_all
  have j_bounds: "1 \<le> j" "j \<le> 540"
  proof -
    show "1 \<le> j" using j_reserve by (cases "f < 9") simp_all
    have "j \<le> h" using step_formula(2) by simp
    then show "j \<le> 540" by (rule order_trans[OF _ h_bounds(2)])
  qed
  show ?case
  proof (cases "n = 0")
    case True
    then have "t = j" using tail by simp
    then show ?thesis using j_reserve by simp
  next
    case False
    have tail_positive: "0 < n" using False by simp
    have tail_reserve:
      "(if f < 9 then 2 else 1) \<le> t"
      by (rule Suc.IH[OF tail sector j_bounds tail_positive])
    show ?thesis by (rule tail_reserve)
  qed
qed

theorem comma_c1_near_chart_prefix_refinement:
  fixes f p delta h t n q prefix k low :: nat
    and C :: comma_c1_phase
    and source target :: comma_finite_position
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and headroom: "1 \<le> h" "h \<le> 540"
    and prefix_path: "comma_near_prefix n f h t"
  defines "q \<equiv> p + delta"
    and "source \<equiv> Comma_Near f delta h"
    and "target \<equiv> Comma_Near f delta t"
    and "k \<equiv> comma_chart_value p source"
    and "prefix \<equiv> k div 100"
    and "low \<equiv> k mod 100"
    and "C \<equiv> comma_c1_phase_of f low"
  shows admitted: "comma_c1_source_admitted C prefix q n"
    and endpoint:
      "comma_chart_value p target =
        100 * (prefix + c1_count (comma_c1_powered_return C n)) +
          comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_powered_return C n)))
            (c1_mod25 (c1_target (comma_c1_powered_return C n)))"
    and path:
      "comma_literal_path n (comma_chart_value p source)
        (comma_chart_value p target)"
    and occurrence:
      "comma_c1_physical_occurrence
        (c1_target (comma_c1_powered_return C n))
        (prefix + c1_count (comma_c1_powered_return C n)) q
        (comma_chart_value p target)"
    and wires:
      "\<forall>j. 2 \<le> j \<longrightarrow>
        comma_c1_carry_wire_total j C prefix n =
          (prefix mod 10^(j-1) +
            c1_count (comma_c1_powered_return C n)) div 10^(j-1)"
proof -
  have source_chart:
      "k = comma_chart_value p (Comma_Near f delta h)"
    by (simp add: k_def source_def)
  have target_chart:
      "comma_chart_value p target =
        (f + 1) * 10^q - t"
    by (simp add: target_def q_def comma_chart_value_def)
  have source_shape:
      "k = (f + 1) * 10^q - h"
    by (simp add: source_chart q_def comma_chart_value_def)
  have chart_sector: "comma_sector f q k"
    using comma_near_chart_checked_sector[OF sector exponent headroom, of delta]
    by (simp add: k_def source_def q_def)
  have q_index: "q = p + delta"
    by (simp add: q_def)
  have q_positive: "0 < q"
    using exponent by (simp add: q_def)
  have chart_headroom: "comma_headroom f q k = h"
    by (rule comma_near_chart_headroom[OF chart_sector source_chart q_index])
  have low_bound: "low < 100"
    by (simp add: low_def)
  have decode_low:
      "comma_c1_decode (c1_mod4 C) (c1_mod25 C) = low"
    by (simp add: C_def comma_c1_phase_of_def
      comma_c1_decode_residue low_bound)
  have phase: "comma_c1_phase_admitted C"
    using comma_c1_phase_of_admitted[OF sector] by (simp add: C_def)
  have phase_sector: "c1_sector C = f"
    by (simp add: C_def comma_c1_phase_of_def)
  have start_decomposition: "k = 100 * prefix + low"
  proof -
    have "k = (k div 100) * 100 + k mod 100"
      by (simp add: div_mult_mod_eq mult.commute)
    then show ?thesis by (simp add: prefix_def low_def mult.commute)
  qed
  have start_c1:
      "k = 100 * prefix +
        comma_c1_decode (c1_mod4 C) (c1_mod25 C)"
    using start_decomposition decode_low by simp
  have chart_sum: "k + h = (f + 1) * 10^q"
    using comma_sector_headroom[OF chart_sector] chart_headroom by simp
  have near_digit:
      "k mod 10 = (10 - h mod 10) mod 10"
    by (rule comma_near_chart_digit[OF chart_sum q_positive])
  have near_displacement:
      "h = t + comma_period_displacement f (k mod 10) n"
  proof -
    have digit:
      "(10 - h mod 10) mod 10 = (10 - h mod 10) mod 10"
      by simp
    have exact:
      "h = t + comma_period_displacement f
        ((10 - h mod 10) mod 10) n"
      by (rule comma_near_prefix_displacement_refines
        [OF sector headroom digit prefix_path])
    show ?thesis using exact near_digit by simp
  qed
  have chart_displacement:
      "comma_chart_value p target = k +
        comma_period_displacement f (k mod 10) n"
    using near_displacement chart_sum target_chart
    by arith
  have c1_displacement:
      "comma_c1_displacement_prefix C n =
        comma_period_displacement f (k mod 10) n"
  proof -
    have decoded_digit:
      "comma_c1_decode (c1_mod4 C) (c1_mod25 C) mod 10 = k mod 10"
      using decode_low start_decomposition by simp
    show ?thesis
      using comma_c1_displacement_prefix_refines[OF phase, of n]
        decoded_digit phase_sector by simp
  qed
  have guard_or:
      "n = 0 \<or>
        comma_c1_displacement_prefix C n + (if f < 9 then 1 else 0) < h"
  proof (cases "n = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have positive: "0 < n" using False by simp
    have reserve:
      "(if f < 9 then 2 else 1) \<le> t"
      by (rule comma_near_prefix_endpoint_reserve
        [OF sector headroom positive prefix_path])
    have strict:
      "comma_period_displacement f (k mod 10) n +
        (if f < 9 then 1 else 0) < h"
      using near_displacement reserve by (cases "f < 9") arith+
    show ?thesis using strict c1_displacement by simp
  qed
  have admitted_source:
      "comma_c1_source_admitted C prefix q n"
    unfolding comma_c1_source_admitted_def
    using phase chart_sector start_c1 exponent guard_or phase_sector
      chart_headroom
    by (simp add: q_def)
  have powered_exact:
      "comma_c1_powered_return C n = comma_c1_return C n"
    by (rule comma_c1_powered_return_exact[OF phase])
  have iter_physical:
      "comma_fixed_iter f n k =
        100 * (prefix + c1_count (comma_c1_return C n)) +
          comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return C n)))
            (c1_mod25 (c1_target (comma_c1_return C n)))"
    using comma_c1_iter_physical[OF phase, where H=prefix and n=n]
      start_c1 phase_sector
    by (simp add: comma_c1_return_def)
  have iter_displacement:
      "comma_fixed_iter f n k = k +
        comma_period_displacement f (k mod 10) n"
    by (rule comma_fixed_iter_displacement)
  have returned_endpoint:
      "comma_chart_value p target =
        100 * (prefix + c1_count (comma_c1_return C n)) +
          comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return C n)))
            (c1_mod25 (c1_target (comma_c1_return C n)))"
    using iter_physical iter_displacement chart_displacement by simp
  have returned_path:
      "comma_literal_path n k
        (100 * (prefix + c1_count (comma_c1_return C n)) +
          comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return C n)))
            (c1_mod25 (c1_target (comma_c1_return C n))))"
    using comma_c1_fixed_sector_occurrence_path(1)[OF admitted_source]
      start_c1 phase_sector by simp
  have returned_occurrence:
      "comma_c1_physical_occurrence
        (c1_target (comma_c1_return C n))
        (prefix + c1_count (comma_c1_return C n)) q
        (100 * (prefix + c1_count (comma_c1_return C n)) +
          comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_return C n)))
            (c1_mod25 (c1_target (comma_c1_return C n))))"
    using comma_c1_fixed_sector_occurrence_path(2)[OF admitted_source]
    by (simp add: q_def)
  have wire_totals:
      "\<forall>j. 2 \<le> j \<longrightarrow>
        comma_c1_carry_wire_total j C prefix n =
          (prefix mod 10^(j-1) +
            c1_count (comma_c1_return C n)) div 10^(j-1)"
  proof (intro allI impI)
    fix j :: nat
    assume wire: "2 \<le> j"
    show "comma_c1_carry_wire_total j C prefix n =
        (prefix mod 10^(j-1) +
          c1_count (comma_c1_return C n)) div 10^(j-1)"
      using comma_c1_carry_wire_total_exact[OF wire]
      by (simp add: comma_c1_return_def)
  qed
  show admitted: "comma_c1_source_admitted C prefix q n"
    by (rule admitted_source)
  show endpoint:
      "comma_chart_value p target =
        100 * (prefix + c1_count (comma_c1_powered_return C n)) +
          comma_c1_decode
            (c1_mod4 (c1_target (comma_c1_powered_return C n)))
            (c1_mod25 (c1_target (comma_c1_powered_return C n)))"
    using returned_endpoint by (simp only: powered_exact)
  show path:
      "comma_literal_path n (comma_chart_value p source)
        (comma_chart_value p target)"
    using returned_path returned_endpoint
    by (simp only: k_def)
  show occurrence:
      "comma_c1_physical_occurrence
        (c1_target (comma_c1_powered_return C n))
        (prefix + c1_count (comma_c1_powered_return C n)) q
        (comma_chart_value p target)"
    using returned_occurrence returned_endpoint by (simp only: powered_exact)
  show wires:
      "\<forall>j. 2 \<le> j \<longrightarrow>
        comma_c1_carry_wire_total j C prefix n =
          (prefix mod 10^(j-1) +
            c1_count (comma_c1_powered_return C n)) div 10^(j-1)"
    using wire_totals by (simp only: powered_exact)
qed

text \<open>The C1 certificate ends at the admitted strict Near prefix.  The
remaining round is evaluated explicitly from that endpoint: its terminal
fork, landmine, invalid result, or decade crossing is retained verbatim, and
only its elapsed prefix length is added to the certified Near length.  This
does not identify the physical C1 clock with the independent 924-phase
selector used by the round action.\<close>

definition comma_c1_near_terminal_round_close ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<times> comma_finite_position \<times> comma_round_result" where
  "comma_c1_near_terminal_round_close p f delta t n =
    (case comma_round_close (p mod 924) (Comma_Near f delta t) of
      (suffix_steps, terminal, event) \<Rightarrow>
        (n + suffix_steps, terminal, event))"

lemma comma_c1_near_prefix_round_close_exact:
  assumes prefix: "comma_near_prefix n f h t"
  shows "comma_round_close (p mod 924) (Comma_Near f delta h) =
    comma_c1_near_terminal_round_close p f delta t n"
proof -
  obtain suffix_steps terminal event where suffix:
    "comma_round_close (p mod 924) (Comma_Near f delta t) =
      (suffix_steps, terminal, event)"
    by (cases "comma_round_close (p mod 924) (Comma_Near f delta t)") auto
  have full:
    "comma_round_close (p mod 924) (Comma_Near f delta h) =
      (n + suffix_steps, terminal, event)"
    by (rule comma_near_prefix_round_close[OF prefix suffix])
  show ?thesis using full suffix
    by (simp add: comma_c1_near_terminal_round_close_def)
qed

lemma comma_c1_near_prefix_round_close_composition:
  assumes prefix: "comma_near_prefix n f h t"
  shows "\<exists>suffix_steps terminal event suffix_weight.
    comma_round_close (p mod 924) (Comma_Near f delta t) =
      (suffix_steps, terminal, event) \<and>
    comma_c1_near_terminal_round_close p f delta t n =
      (n + suffix_steps, terminal, event) \<and>
    comma_round_close (p mod 924) (Comma_Near f delta h) =
      (n + suffix_steps, terminal, event) \<and>
    comma_round_weighted_prefix p (p mod 924) suffix_steps
      (Comma_Near f delta t) terminal suffix_weight \<and>
    comma_round_weighted_prefix p (p mod 924) (n + suffix_steps)
      (Comma_Near f delta h) terminal (n + suffix_weight)"
proof -
  obtain suffix_steps terminal event where suffix:
    "comma_round_close (p mod 924) (Comma_Near f delta t) =
      (suffix_steps, terminal, event)"
    by (cases "comma_round_close (p mod 924) (Comma_Near f delta t)") auto
  obtain suffix_weight where suffix_weight:
    "comma_round_weighted_prefix p (p mod 924) suffix_steps
      (Comma_Near f delta t) terminal suffix_weight"
    using comma_round_close_has_weighted_prefix[OF suffix] by blast
  have prefix_weight:
    "comma_round_weighted_prefix p (p mod 924) n
      (Comma_Near f delta h) (Comma_Near f delta t) n"
    by (rule comma_near_prefix_weighted[OF prefix])
  have whole_weight:
    "comma_round_weighted_prefix p (p mod 924) (n + suffix_steps)
      (Comma_Near f delta h) terminal (n + suffix_weight)"
    by (rule comma_round_weighted_prefix_concat[OF prefix_weight suffix_weight])
  have named:
    "comma_c1_near_terminal_round_close p f delta t n =
      (n + suffix_steps, terminal, event)"
    using comma_c1_near_prefix_round_close_exact[OF prefix] suffix
    by (simp add: comma_c1_near_terminal_round_close_def)
  have full:
    "comma_round_close (p mod 924) (Comma_Near f delta h) =
      (n + suffix_steps, terminal, event)"
    by (rule comma_near_prefix_round_close[OF prefix suffix])
  show ?thesis
    using suffix named full suffix_weight whole_weight
    by blast
qed

ML \<open>
  val checked = @{thms comma_near_prefix_endpoint_reserve
    comma_c1_near_chart_prefix_refinement
    comma_c1_near_prefix_round_close_exact
    comma_c1_near_prefix_round_close_composition};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "C1 Near chart refinement depends on an oracle";
\<close>

end
