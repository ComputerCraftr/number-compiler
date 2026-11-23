theory Comma_C1_First_Sector
  imports Comma_C1_Fused_Entry_Refinement
    Comma_Closed_Near.Comma_Closed_Near
begin

text \<open>
The bounded residual selector chooses the first sector event directly from the
source clock and headroom.  The returned physical clock counts only edges
already traversed.  The decisive edge is consumed only when the returned
action is Next.  The selector phase and the physical clock have different
units.
\<close>


definition comma_first_crossing_cycles ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_first_crossing_cycles f d P threshold j =
    (let gap = threshold - comma_period_displacement f d j
     in if gap = 0 then 0 else Suc ((gap - 1) div P))"

definition comma_first_crossing_time ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_first_crossing_time f d L P threshold =
    Min ((\<lambda>j. comma_first_crossing_cycles f d P threshold j * L + j) ` {1..L})"

lemma comma_first_crossing_ceiling:
  fixes N P q :: nat
  assumes positive: "0 < P"
  defines "c \<equiv> (if N = 0 then 0 else Suc ((N - 1) div P))"
  shows "N \<le> c * P"
    and "N \<le> q * P \<Longrightarrow> c \<le> q"
proof -
  show "N \<le> c * P"
  proof (cases "N = 0")
    case True
    then show ?thesis by simp
  next
    case False
    have "(N-1) div P < c" using False by (simp add: c_def)
    then have "N-1 < c * P" by (simp only: div_less_iff_less_mult[OF positive])
    then show ?thesis using False by arith
  qed
  assume bound: "N \<le> q * P"
  show "c \<le> q"
  proof (cases "N = 0")
    case True
    then show ?thesis by (simp add: c_def)
  next
    case False
    have "N-1 < q * P" using bound False by arith
    then have "(N-1) div P < q" by (simp only: div_less_iff_less_mult[OF positive])
    then show ?thesis using False by (simp add: c_def)
  qed
qed

theorem comma_first_crossing_minimum:
  fixes f d L P threshold :: nat
  assumes length: "0 < L" and period: "0 < P"
    and closed: "10 dvd L * f"
    and displacement: "P = comma_period_displacement f d L"
  defines "first \<equiv> comma_first_crossing_time f d L P threshold"
  shows "0 < first"
    and "threshold \<le> comma_period_displacement f d first"
    and "\<And>t. \<lbrakk>0 < t; threshold \<le> comma_period_displacement f d t\<rbrakk>
      \<Longrightarrow> first \<le> t"
proof -
  let ?candidate = "\<lambda>j. comma_first_crossing_cycles f d P threshold j * L + j"
  let ?set = "?candidate ` {1..L}"
  have finite: "finite ?set" by simp
  have nonempty: "?set \<noteq> {}" using length by auto
  have member: "first \<in> ?set"
    using Min_in[OF finite nonempty] by (simp add: first_def comma_first_crossing_time_def)
  then obtain j where j: "1 \<le> j" "j \<le> L" and first: "first = ?candidate j" by auto
  have positive: "0 < first" using j first by simp
  show "0 < first" by (rule positive)
  have crossing: "threshold \<le> comma_period_displacement f d (?candidate j)" for j
  proof -
    let ?gap = "threshold - comma_period_displacement f d j"
    have gap: "?gap \<le> comma_first_crossing_cycles f d P threshold j * P"
      using comma_first_crossing_ceiling(1)[OF period, of ?gap]
      by (simp add: comma_first_crossing_cycles_def Let_def)
    show ?thesis
      using gap comma_period_displacement_repeated[OF closed, of d
          "comma_first_crossing_cycles f d P threshold j" j]
      by (simp only: displacement[symmetric]; arith)
  qed
  show "threshold \<le> comma_period_displacement f d first"
    using crossing[of j] first by simp
  fix t
  assume t: "0 < t" "threshold \<le> comma_period_displacement f d t"
  let ?q = "(t - 1) div L"
  let ?r = "(t - 1) mod L + 1"
  have r: "1 \<le> ?r" "?r \<le> L"
    using mod_less_divisor[OF length, of "t - 1"] by simp_all
  have split: "t = ?q * L + ?r"
    using div_mult_mod_eq[of "t - 1" L] t by arith
  have split_displacement: "comma_period_displacement f d t =
      comma_period_displacement f d (?q * L + ?r)"
    using arg_cong[OF split, of "comma_period_displacement f d"] .
  have crossing: "threshold - comma_period_displacement f d ?r \<le> ?q * P"
    using t(2) comma_period_displacement_repeated[OF closed, of d ?q ?r]
    by (simp only: split_displacement displacement[symmetric]; arith)
  have count: "comma_first_crossing_cycles f d P threshold ?r \<le> ?q"
    unfolding comma_first_crossing_cycles_def Let_def
    by (rule comma_first_crossing_ceiling(2)[OF period crossing])
  have slot: "?r \<in> {1..L}" using r by simp
  have candidate: "?candidate ?r \<in> ?set" by (rule imageI[OF slot])
  have min: "first \<le> ?candidate ?r"
    unfolding first_def comma_first_crossing_time_def
    by (rule Min_le[OF finite candidate])
  have bounded: "?candidate ?r \<le> ?q * L + ?r"
    by (rule add_le_mono1[OF mult_le_mono1[OF count]])
  show "first \<le> t" using order_trans[OF min bounded] split by simp
qed



text \<open>Draft bridge: the least positive crossing selects the existing
Near germ. The zero threshold is an immediate decisive case.\<close>

theorem comma_first_crossing_near_germ:
  fixes f h d first :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and headroom: "1 \<le> h" "h \<le> 540"
  defines "d \<equiv> (10 - h mod 10) mod 10"
    and "first \<equiv> comma_first_crossing_time f d (comma_cycle_length f)
      (comma_finite_period f d) (h - (if f < 9 then 1 else 0))"
  shows "comma_near_germ f h =
      (first - 1, h - comma_period_displacement f d (first - 1))"
proof -
  let ?extra = "if f < 9 then 1 else 0"
  let ?threshold = "h - ?extra"
  let ?A = "comma_period_displacement f d"
  have digit: "d < 10" by (simp add: d_def)
  have aligned: "(h+d) mod 10 = 0"
    using comma_near_initial_digit_aligned[of h] by (simp add: d_def)
  have length: "0 < comma_cycle_length f"
    and closes: "10 dvd comma_cycle_length f * f"
    using comma_cycle_length_admitted[OF sector] by auto
  have period: "0 < comma_finite_period f d"
    using comma_near_fast_period_positive_decimal(1)[OF sector digit]
      comma_finite_period_fast_correct[OF sector digit] by simp
  have displacement: "comma_finite_period f d = ?A (comma_cycle_length f)"
    by (rule comma_finite_period_refines[OF sector digit])
  note minimum = comma_first_crossing_minimum[OF length period closes displacement,
      where threshold="?threshold"]
  have positive: "0 < first" using minimum(1) by (simp only: first_def)
  have crossing: "?threshold \<le> ?A first"
    using minimum(2) by (simp only: first_def)
  show ?thesis
  proof (cases "?threshold = 0")
    case True
    have one: "first = 1"
      using minimum(3)[of 1] positive True by (simp only: first_def; arith)
    have immediate: "comma_near_decisive f h"
      using True headroom sector
      by (simp add: comma_near_decisive_iff; arith)
    have germ: "comma_near_germ f h = (0,h)"
      by (rule comma_near_prefix_decisive_germ[OF _ immediate]) simp
    show ?thesis using germ one by (simp add: comma_period_displacement_def)
  next
    case False
    have previous: "?A (first - 1) < ?threshold"
    proof (cases "first = 1")
      case True
      then show ?thesis using False by (simp add: comma_period_displacement_def)
    next
      case False
      have earlier: "0 < first - 1" "first - 1 < first"
        using positive False by arith+
      have "\<not> ?threshold \<le> ?A (first - 1)"
      proof
        assume reached: "?threshold \<le> ?A (first - 1)"
        have lower: "first \<le> first - 1"
          using minimum(3)[OF earlier(1) reached] by (simp only: first_def)
        show False using lower earlier(2) by arith
      qed
      then show ?thesis by arith
    qed
    have safe: "?A (first - 1) + ?extra < h"
      using previous headroom by (cases "f < 9") simp_all
    have maximal: "h \<le> ?A (Suc (first - 1)) + ?extra"
      using crossing positive headroom by (cases "f < 9") simp_all
    show ?thesis
      by (rule comma_near_germ_from_maximal_displacement
        [OF sector headroom(2) digit aligned safe maximal])
  qed
qed

theorem comma_first_crossing_source_threshold:
  fixes f d q offset first :: nat
  assumes sector: "1 \<le> f" "f \<le> 9" and digit: "d < 10"
  defines "first \<equiv> comma_first_crossing_time f d
      (comma_cycle_length f) (comma_finite_period f d)
      (10 ^ q - (if f < 9 then 1 else 0) - offset)"
  shows "0 < first"
    and "10 ^ q - (if f < 9 then 1 else 0) - offset
      \<le> comma_period_displacement f d first"
    and "\<And>t. \<lbrakk>0 < t; t < first\<rbrakk> \<Longrightarrow>
      comma_period_displacement f d t <
        10 ^ q - (if f < 9 then 1 else 0) - offset"
proof -
  have length: "0 < comma_cycle_length f"
    and closed: "10 dvd comma_cycle_length f * f"
    using comma_cycle_length_admitted[OF sector] by auto
  have period: "0 < comma_finite_period f d"
    using comma_near_fast_period_positive_decimal(1)[OF sector digit]
      comma_finite_period_fast_correct[OF sector digit] by simp
  have displacement: "comma_finite_period f d =
      comma_period_displacement f d (comma_cycle_length f)"
    by (rule comma_finite_period_refines[OF sector digit])
  note result = comma_first_crossing_minimum[OF length period closed displacement,
      where threshold="10 ^ q - (if f < 9 then 1 else 0) - offset"]
  show "0 < first" using result(1) by (simp add: first_def)
  show "10 ^ q - (if f < 9 then 1 else 0) - offset
      \<le> comma_period_displacement f d first"
    using result(2) by (simp add: first_def)
  fix t
  assume t: "0 < t" "t < first"
  show "comma_period_displacement f d t <
      10 ^ q - (if f < 9 then 1 else 0) - offset"
    using result(3)[of t] t unfolding first_def by arith
qed


text \<open>The common quotient of the decimal scale is an additive physical
clock term.  It cancels from comparisons of two positions in the same
cycle, including when their residual ceiling terms are negative.\<close>

lemma comma_signed_ceiling_period_translate:
  fixes k r c P :: int
  assumes "P \<noteq> 0"
  shows "- ((- (k * P + r - c)) div P) =
    k - ((c - r) div P)"
proof -
  have rewrite: "- (k * P + r - c) = (c-r) + (-k) * P"
    by (simp add: algebra_simps)
  have quotient: "((c-r) + (-k) * P) div P = -k + (c-r) div P"
    using assms by (rule div_mult_self1)
  show ?thesis by (simp only: rewrite quotient; arith)
qed

lemma comma_first_crossing_quotient_order:
  fixes k u v L a b :: int
  shows "(k+u)*L+a \<le> (k+v)*L+b \<longleftrightarrow> u*L+a \<le> v*L+b"
  by (simp add: algebra_simps)


lemma comma_first_crossing_admitted_positive_gap:
  fixes f d p delta offset j :: nat
  assumes sector: "1 \<le> f" "f \<le> 9" and digit: "d < 10"
    and exponent: "5 \<le> p" and offset: "offset < 100"
    and phase: "j \<le> comma_cycle_length f"
  shows "comma_period_displacement f d j <
    10 ^ (p + delta) - (if f < 9 then 1 else 0) - offset"
proof -
  have catalog: "comma_finite_period f d \<in> comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f d] sector digit by auto
  have period: "comma_finite_period f d \<le> 540"
    using catalog by (auto simp: comma_cycle_displacements_def)
  have displacement:
      "comma_period_displacement f d j \<le> comma_finite_period f d"
    using comma_period_displacement_mono[OF phase, of f d]
      comma_finite_period_refines[OF sector digit] by simp
  have scale: "(100000::nat) \<le> 10 ^ (p + delta)"
    using power_increasing[of 5 "p + delta" "10::nat"] exponent by simp
  show ?thesis using period displacement scale offset by (cases "f < 9") arith+
qed

lemma comma_first_crossing_phase_period:
  assumes sector: "1 \<le> f" "f \<le> 9" and digit: "d < 10" and exponent: "5 \<le> p"
  shows "(10::nat) ^ (p + 924) mod comma_finite_period f d =
    10 ^ p mod comma_finite_period f d"
proof -
  have catalog: "comma_finite_period f d \<in> comma_cycle_displacements"
    using comma_finite_period_in_catalog[rule_format, of f d] sector digit by auto
  show ?thesis by (rule comma_power_period_924[OF catalog exponent])
qed

lemma comma_cycle_catalog_common_modulus:
  assumes "P \<in> comma_cycle_displacements"
  shows "P dvd (14421607200::nat)"
  using assms by (auto simp: comma_cycle_displacements_def)

lemma comma_common_modulus_924_period:
  "(10::nat)^5 mod 14421607200 = 10^(5 + 924) mod 14421607200"
proof -
  have "mod_exp (10::nat) 5 14421607200 =
      mod_exp 10 (5 + 924) 14421607200"
    by (simp add: power2_eq_square)
  then show ?thesis unfolding mod_exp_def .
qed

definition comma_c1_first_sector ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<times> nat \<times> comma_finite_move" where
  "comma_c1_first_sector f p delta offset =
    (let h = comma_finite_headroom f (p mod 924) delta offset;
         P = comma_finite_period f (offset mod 10);
         L = comma_cycle_length f;
         steps = ((10 ^ (p + delta) - offset - h) div P) * L;
         (n,t) = comma_near_closed_germ f h
     in (steps + n,t,comma_finite_step (p mod 924) (Comma_Near f delta t)))"

theorem comma_c1_first_sector_source:
  fixes f p delta offset elapsed t h steps n :: nat
    and event :: comma_finite_move
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset = (elapsed,t,event)"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "steps \<equiv> ((10 ^ (p + delta) - offset - h) div
      comma_finite_period f (offset mod 10)) * comma_cycle_length f"
    and "n \<equiv> fst (comma_near_closed_germ f h)"
  shows "elapsed = steps + n"
    and "comma_literal_path elapsed (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta t))"
    and "comma_near_prefix n f h t"
    and "1 \<le> t" "t \<le> 540"
    and "comma_near_decisive f t"
    and "event = comma_finite_step (p mod 924) (Comma_Near f delta t)"
    and "c1_count (comma_c1_powered_return (comma_c1_phase_of f offset) steps) =
      10 ^ (p + delta - 2) - ((h + 99) div 100)"
proof -
  have h_bounds: "1 \<le> h" "h \<le> 540"
    using comma_finite_entry_headroom_admitted[OF sector exponent offset, of delta]
    by (simp_all add: h_def)
  obtain k u where closed: "comma_near_closed_germ f h = (k,u)"
    by (cases "comma_near_closed_germ f h") auto
  have germ: "comma_near_germ f h = (k,u)"
    using comma_near_closed_germ_correct[OF sector h_bounds] closed by simp
  have checked: "comma_c1_first_sector f p delta offset =
      (steps + k,u,comma_finite_step (p mod 924) (Comma_Near f delta u))"
    by (simp only: comma_c1_first_sector_def Let_def h_def[symmetric]
      steps_def[symmetric] closed prod.case)
  have fields: "n = k" "t = u" "elapsed = steps + k"
    "event = comma_finite_step (p mod 924) (Comma_Near f delta u)"
    using packet checked closed by (auto simp: n_def)
  have prefix: "comma_near_prefix k f h u" and decisive: "comma_near_decisive f u"
    using comma_near_germ_refines[OF germ] by blast+
  have displacement: "h = u + comma_period_displacement f
      ((10 - h mod 10) mod 10) k"
    by (rule comma_near_prefix_displacement_refines[OF sector h_bounds refl prefix])
  have upper: "u \<le> 540" using h_bounds displacement by arith
  have lower: "1 \<le> u"
  proof (cases "k=0")
    case True
    then show ?thesis using prefix h_bounds by simp
  next
    case False
    have "0 < k" using False by simp
    then have "(if f < 9 then 2 else 1) \<le> u"
      by (rule comma_near_prefix_endpoint_reserve[OF sector h_bounds _ prefix])
    then show ?thesis by (cases "f < 9") simp_all
  qed
  show "elapsed = steps + n" using fields by simp
  show "comma_literal_path elapsed (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta t))"
    using comma_fused_entry_prefix_consumer(5)[OF sector exponent offset, where delta=delta]
      germ fields by (simp add: h_def steps_def)
  show "comma_near_prefix n f h t" using prefix fields by simp
  show "1 \<le> t" "t \<le> 540" using lower upper fields by simp_all
  show "comma_near_decisive f t" using decisive fields by simp
  show "event = comma_finite_step (p mod 924) (Comma_Near f delta t)" using fields by simp
  show "c1_count (comma_c1_powered_return (comma_c1_phase_of f offset) steps) =
      10 ^ (p + delta - 2) - ((h + 99) div 100)"
    using comma_fused_entry_prefix_consumer(4)[OF sector exponent offset, where delta=delta]
    by (simp add: h_def steps_def)
qed

text \<open>The minimum-derived terminal is the one carried by the existing
source-bound packet; this is not a global termination certificate.\<close>

lemma comma_c1_first_sector_minimum_projection:
  fixes f p delta offset elapsed t h d first steps :: nat and event :: comma_finite_move
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset = (elapsed,t,event)"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "d \<equiv> (10 - h mod 10) mod 10"
    and "first \<equiv> comma_first_crossing_time f d (comma_cycle_length f)
      (comma_finite_period f d) (h - (if f < 9 then 1 else 0))"
    and "steps \<equiv> ((10 ^ (p + delta) - offset - h) div
      comma_finite_period f (offset mod 10)) * comma_cycle_length f"
  shows "t = h - comma_period_displacement f d (first - 1)"
    and "elapsed = steps + (first - 1)"
proof -
  have bounds: "1 \<le> h" "h \<le> 540"
    using comma_finite_entry_headroom_admitted[OF sector exponent offset, of delta]
    by (simp_all add: h_def)
  have germ: "comma_near_germ f h =
      (first - 1, h - comma_period_displacement f d (first - 1))"
    using comma_first_crossing_near_germ[OF sector bounds]
    by (simp only: d_def first_def)
  have closed: "comma_near_closed_germ f h = comma_near_germ f h"
    by (rule comma_near_closed_germ_correct[OF sector bounds])
  show "t = h - comma_period_displacement f d (first - 1)"
    and "elapsed = steps + (first - 1)"
    using packet germ closed
    by (simp_all add: comma_c1_first_sector_def Let_def h_def[symmetric] steps_def)
qed

theorem comma_c1_first_sector_next:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset =
      (elapsed,t,Comma_Next target)"
  shows "comma_literal_path (Suc elapsed)
      (comma_chart_value p (Comma_Entry f delta offset)) (comma_chart_value p target)"
    and "comma_large_children f (p + delta)
      (comma_chart_value p (Comma_Near f delta t)) = [comma_chart_value p target]"
proof -
  have prefix: "comma_literal_path elapsed
      (comma_chart_value p (Comma_Entry f delta offset))
      (comma_chart_value p (Comma_Near f delta t))"
    and t: "1 \<le> t" "t \<le> 540"
    and outcome: "Comma_Next target =
      comma_finite_step (p mod 924) (Comma_Near f delta t)"
    using comma_c1_first_sector_source[OF sector exponent offset packet] by blast+
  have step: "comma_finite_step (p mod 924) (Comma_Near f delta t) = Comma_Next target"
    using outcome by simp
  note result = comma_near_chart_next_literal[OF sector exponent t step]
  show "comma_literal_path (Suc elapsed)
      (comma_chart_value p (Comma_Entry f delta offset)) (comma_chart_value p target)"
    using comma_literal_path_append[OF prefix result(1)] by simp
  show "comma_large_children f (p + delta)
      (comma_chart_value p (Comma_Near f delta t)) = [comma_chart_value p target]"
    using result(3) .
qed

theorem comma_c1_first_sector_fork:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset =
      (elapsed,t,Comma_Fork a delta)"
  shows "a = f + 1" "f < 9"
    "comma_large_children f (p + delta) (comma_chart_value p (Comma_Near f delta t)) =
      [comma_near_boundary a (p + delta), comma_zero_boundary a (p + delta)]"
proof -
  have t: "1 \<le> t" "t \<le> 540"
    and event: "Comma_Fork a delta =
      comma_finite_step (p mod 924) (Comma_Near f delta t)"
    using comma_c1_first_sector_source[OF sector exponent offset packet] by blast+
  have source: "comma_sector f (p + delta) (comma_chart_value p (Comma_Near f delta t))"
    by (rule comma_near_chart_checked_sector[OF sector exponent t])
  have step: "comma_finite_step (p mod 924) (Comma_Near f delta t) = Comma_Fork a delta"
    using event by simp
  show "a = f + 1" "f < 9"
    "comma_large_children f (p + delta) (comma_chart_value p (Comma_Near f delta t)) =
      [comma_near_boundary a (p + delta), comma_zero_boundary a (p + delta)]"
    using comma_near_chart_fork[OF source _ refl refl step] exponent by auto
qed

theorem comma_c1_first_sector_landmine:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset =
      (elapsed,t,Comma_Landmine delta)"
  shows "comma_large_children f (p + delta) (comma_chart_value p (Comma_Near f delta t)) = []"
    and "\<nexists>target. comma_child (comma_chart_value p (Comma_Near f delta t)) target"
proof -
  have t: "1 \<le> t" "t \<le> 540"
    and event: "Comma_Landmine delta =
      comma_finite_step (p mod 924) (Comma_Near f delta t)"
    using comma_c1_first_sector_source[OF sector exponent offset packet] by blast+
  have source: "comma_sector f (p + delta) (comma_chart_value p (Comma_Near f delta t))"
    by (rule comma_near_chart_checked_sector[OF sector exponent t])
  have step: "comma_finite_step (p mod 924) (Comma_Near f delta t) = Comma_Landmine delta"
    using event by simp
  show "comma_large_children f (p + delta) (comma_chart_value p (Comma_Near f delta t)) = []"
    "\<nexists>target. comma_child (comma_chart_value p (Comma_Near f delta t)) target"
    using comma_near_chart_landmine[OF source _ refl refl step] exponent by auto
qed


corollary comma_c1_first_sector_fork_order:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p" and offset: "offset \<le> 98"
    and packet: "comma_c1_first_sector f p delta offset =
      (elapsed,t,Comma_Fork a delta)"
  shows "comma_large_children f (p + delta) (comma_chart_value p (Comma_Near f delta t))
    \<noteq> [comma_zero_boundary a (p + delta), comma_near_boundary a (p + delta)]"
proof -
  have a: "a = f+1"
    and children: "comma_large_children f (p + delta)
        (comma_chart_value p (Comma_Near f delta t)) =
      [comma_near_boundary a (p + delta), comma_zero_boundary a (p + delta)]"
    using comma_c1_first_sector_fork[OF sector exponent offset packet] by blast+
  have positive: "0 < a * 10 ^ (p + delta)" using sector a by simp
  have unequal: "a * 10 ^ (p + delta) - 1 \<noteq> a * 10 ^ (p + delta)"
    using positive by arith
  show ?thesis using children unequal
    by (simp add: comma_near_boundary_def comma_zero_boundary_def)
qed

lemma comma_c1_first_sector_terminal_disjoint:
  assumes "comma_c1_first_sector f p delta offset = (elapsed,t,Comma_Fork a delta)"
  shows "comma_c1_first_sector f p delta offset \<noteq> (elapsed,t,Comma_Landmine delta)"
  using assms by simp

ML \<open>
  val checked = @{thms comma_first_crossing_minimum comma_first_crossing_near_germ
    comma_first_crossing_source_threshold comma_c1_first_sector_minimum_projection
    comma_first_crossing_phase_period comma_signed_ceiling_period_translate
    comma_first_crossing_quotient_order comma_first_crossing_admitted_positive_gap
    comma_cycle_catalog_common_modulus comma_common_modulus_924_period comma_c1_first_sector_source comma_c1_first_sector_next
    comma_c1_first_sector_fork comma_c1_first_sector_landmine
    comma_c1_first_sector_fork_order comma_c1_first_sector_terminal_disjoint};
  val _ = if null (Thm_Deps.all_oracles checked) then ()
    else error "Source first-sector certificate depends on an oracle";
\<close>

end
