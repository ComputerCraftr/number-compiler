theory Comma_C1_Fused_Entry_Refinement
  imports Comma_C1_Near_Chart_Refinement
begin

text \<open>The source-bound Entry prefix and closed Near descent are
chronologically composed before any terminal seam is selected. The exponent
and selector clock remain independent; this packet does not decide a Fork or
transport an occurrence weight between sources.\<close>

theorem comma_fused_entry_prefix_consumer:
  fixes f p delta offset h P L steps :: nat
    and near :: "nat \<times> nat"
    and w :: comma_chart_weight
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and source_offset: "offset \<le> 98"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "steps \<equiv> ((10 ^ (p + delta) - offset - h) div P) * L"
    and "near \<equiv> comma_near_germ f h"
    and "w \<equiv> Comma_Chart_Weight L delta (- int (L * (offset + h))) P"
  shows "comma_round_weighted_prefix p p (Suc (fst near))
      (Comma_Entry f delta offset) (Comma_Near f delta (snd near))
      (comma_chart_weight_value p w + fst near)"
    and "comma_chart_weight_value p w = steps"
    and "comma_literal_path steps (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta h))"
    and "c1_count (comma_c1_powered_return (comma_c1_phase_of f offset) steps) =
      10 ^ (p + delta - 2) - ((h + 99) div 100)"
    and "comma_literal_path (steps + fst near)
      (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta (snd near)))"
proof -
  have entry: "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta h) w"
    using comma_c1_powered_entry_chart_bridge(6)[OF sector exponent source_offset, where delta=delta]
    by (simp add: h_def P_def L_def w_def)
  have shape: "comma_sector_germ p (Comma_Entry f delta offset) =
      (Suc (fst near), Comma_Near f delta (snd near), Some w, fst near)"
    using entry by (cases near) (simp add: comma_sector_germ_def near_def[symmetric])
  show prefix: "comma_round_weighted_prefix p p (Suc (fst near))
      (Comma_Entry f delta offset) (Comma_Near f delta (snd near))
      (comma_chart_weight_value p w + fst near)"
    using comma_sector_germ_weighted[OF shape, of p]
    by (simp add: comma_sector_weight_def)
  have exact_weight: "comma_finite_next_weight p (Comma_Entry f delta offset) = steps"
    using comma_entry_chart_exact_literal_path(2)[OF sector exponent source_offset, where delta=delta]
    by (simp add: steps_def h_def P_def L_def)
  show weight: "comma_chart_weight_value p w = steps"
    using exact_weight entry by (simp add: comma_finite_next_weight_def)
  show "comma_literal_path steps (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta h))"
    using comma_c1_powered_entry_chart_bridge(4)[OF sector exponent source_offset, where delta=delta]
    by (simp add: steps_def h_def P_def L_def)
  show "c1_count (comma_c1_powered_return (comma_c1_phase_of f offset) steps) =
      10 ^ (p + delta - 2) - ((h + 99) div 100)"
    using comma_c1_powered_entry_count_closed[OF sector exponent source_offset, where delta=delta]
    by (simp add: steps_def h_def P_def L_def)
  have admitted: "comma_round_admitted (Comma_Entry f delta offset)"
    using sector source_offset by simp
  show "comma_literal_path (steps + fst near)
      (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta (snd near)))"
    using comma_round_weighted_prefix_literal[OF prefix refl exponent admitted]
    by (simp only: weight)
qed

theorem comma_fused_entry_clocked_endpoint:
  fixes f p delta offset k h extra steps :: nat
    and A :: "nat \<Rightarrow> nat"
    and terminal :: comma_finite_position
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and source_offset: "offset \<le> 98"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "A \<equiv> comma_period_displacement f ((10 - h mod 10) mod 10)"
    and "extra \<equiv> if f < 9 then 1 else 0"
    and "steps \<equiv> ((10 ^ (p + delta) - offset - h) div
      comma_finite_period f (offset mod 10)) * comma_cycle_length f"
    and "terminal \<equiv> Comma_Near f delta (h - A k)"
  assumes safe: "A k + extra < h"
    and first_crossing: "h \<le> A (Suc k) + extra"
  shows "comma_literal_path (steps + k)
      (comma_chart_value p (Comma_Entry f delta offset)) (comma_chart_value p terminal)"
    and "comma_finite_step (p mod 924) terminal = Comma_Next next \<Longrightarrow>
      comma_literal_path (steps + Suc k)
        (comma_chart_value p (Comma_Entry f delta offset)) (comma_chart_value p next)"
proof -
  have h: "1 \<le> h" "h \<le> 540"
    using comma_finite_entry_headroom_admitted[OF sector exponent source_offset, of delta]
    by (simp_all add: h_def)
  let ?d = "(10 - h mod 10) mod 10"
  have digit: "?d < 10" by simp
  have aligned: "(h+?d) mod 10 = 0" by (rule comma_near_initial_digit_aligned)
  have near: "comma_near_germ f h = (k,h - A k)"
    using comma_near_germ_from_maximal_displacement
      [OF sector h(2) digit aligned, of k] safe first_crossing
    by (simp add: A_def extra_def)
  show prefix: "comma_literal_path (steps + k)
      (comma_chart_value p (Comma_Entry f delta offset)) (comma_chart_value p terminal)"
    using comma_fused_entry_prefix_consumer(5)[OF sector exponent source_offset,
      where delta=delta]
    by (simp add: steps_def terminal_def h_def[symmetric] near)
  assume advance: "comma_finite_step (p mod 924) terminal = Comma_Next next"
  have t: "1 \<le> h - A k" "h - A k \<le> 540"
    using h safe by arith+
  have next_step: "comma_finite_step (p mod 924) (Comma_Near f delta (h - A k)) =
      Comma_Next next"
    using advance by (simp only: terminal_def)
  have tail: "comma_literal_path 1 (comma_chart_value p terminal)
      (comma_chart_value p next)"
    using comma_near_chart_next_literal(1)[OF sector exponent t next_step]
    by (simp only: terminal_def)
  show "comma_literal_path (steps + Suc k)
      (comma_chart_value p (Comma_Entry f delta offset)) (comma_chart_value p next)"
    using comma_literal_path_append[OF prefix tail] by simp
qed

lemma comma_fused_entry_decimal_split:
  fixes q :: nat
  assumes "2 \<le> q"
  shows "(10::nat)^q = 100 * 10^(q-2)"
proof -
  have split: "q = (q - 2) + 2" using assms by arith
  show ?thesis using arg_cong[OF split, of "\<lambda>k. (10::nat)^k"]
    by (simp add: power_add mult.commute)
qed

lemma comma_fused_entry_advance_quotient:
  fixes f q x y :: nat
  assumes "2 \<le> q" "x < 100" "y < 100"
  shows "((f+1) * 10^q + y) div 100 - (f * 10^q + x) div 100 =
    10^(q-2)"
proof -
  let ?u = "(10::nat)^(q-2)"
  have before: "(f * 10^q + x) div 100 = f * ?u"
    using assms(2)
    by (simp add: comma_fused_entry_decimal_split[OF assms(1)]
      div_add1_eq mult.left_commute)
  have after: "((f+1) * 10^q + y) div 100 = (f+1) * ?u"
    using assms(3)
    by (simp add: comma_fused_entry_decimal_split[OF assms(1)]
      div_add1_eq mult.left_commute)
  show ?thesis unfolding before after
    by (simp only: add_mult_distrib mult_1_left; arith)
qed

lemma comma_fused_entry_terminal_quotient:
  fixes f q x H T :: nat
  assumes exponent: "2 \<le> q"
    and offset: "x < 100"
    and bound: "H \<le> 10^q"
  defines "T \<equiv> (f+1) * 10^q - H"
  shows "T div 100 - (f * 10^q + x) div 100 =
    10^(q-2) - ((H+99) div 100)"
proof -
  let ?u = "(10::nat)^(q-2)"
  let ?v = "(H+99) div 100"
  have decimal: "(10::nat)^q = 100 * ?u"
    by (rule comma_fused_entry_decimal_split[OF exponent])
  have before: "(f * 10^q + x) div 100 = f * ?u"
    using offset by (simp add: decimal div_add1_eq mult.left_commute)
  have sum: "T + H = 100 * ((f+1) * ?u)"
  proof -
    have "H \<le> (f+1) * 10^q" using bound by simp
    then show ?thesis by (simp add: T_def decimal mult.left_commute)
  qed
  have qr: "100 * (T div 100) + T mod 100 = T"
    using div_mult_mod_eq[of T 100] by (simp add: mult.commute)
  have balance: "100 * ((f+1) * ?u) = 100 * (T div 100) + T mod 100 + H"
    by (simp only: qr sum)
  have after: "T div 100 = (f+1) * ?u - ?v"
    by (rule comma_entry_ceil_arithmetic[OF balance]) simp
  show ?thesis unfolding before after
    by (simp only: add_mult_distrib mult_1_left; arith)
qed

ML \<open>
  val checked = @{thms comma_fused_entry_prefix_consumer
    comma_fused_entry_clocked_endpoint comma_fused_entry_advance_quotient
    comma_fused_entry_terminal_quotient};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Fused Entry refinement depends on an oracle";
\<close>

end
