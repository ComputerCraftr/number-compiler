theory Comma_Python_Grouped_Near_Refinement
  imports Comma_Python_Chart_Refinement
    Comma_Semantic_Producer_Cut_Refinement
begin

text \<open>
The grouped Near classifier uses one quotient by the complete phase
displacement, followed by the same lower-endpoint binary search as
`classify_near_port`.  Its selected endpoint is not a separate jump rule:
it is an exact prefix of the existing scalar Near transition.
\<close>

fun comma_python_near_prefix_search_fuel ::
  "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_python_near_prefix_search_fuel f d r 0 lower upper = lower"
| "comma_python_near_prefix_search_fuel f d r (Suc fuel) lower upper =
    (if lower + 1 < upper then
       (let middle = (lower + upper) div 2
        in if comma_period_displacement f d middle \<le> r
           then comma_python_near_prefix_search_fuel
             f d r fuel middle upper
           else comma_python_near_prefix_search_fuel
             f d r fuel lower middle)
     else lower)"

lemma comma_period_displacement_strict:
  assumes positive: "0 < f" and order: "i < j"
  shows "comma_period_displacement f d i < comma_period_displacement f d j"
proof -
  have next: "comma_period_displacement f d i <
      comma_period_displacement f d (Suc i)"
    using positive
    by (simp add: comma_period_displacement_succ comma_phase_digit_def)
  have "Suc i \<le> j" using order by arith
  then have "comma_period_displacement f d (Suc i) \<le>
      comma_period_displacement f d j"
    by (rule comma_period_displacement_mono)
  then show ?thesis using next by arith
qed

lemma comma_python_near_phase_periods:
  assumes closes: "10 dvd period * f"
  shows "comma_phase_digit f d (cycles * period + index) =
    comma_phase_digit f d index"
proof (induction cycles)
  case 0
  then show ?case by simp
next
  case (Suc cycles)
  have rearrange:
    "Suc cycles * period + index =
      period + (cycles * period + index)"
    by (simp add: algebra_simps)
  have phase:
    "comma_phase_digit f d (period + (cycles * period + index)) =
      comma_phase_digit f d (cycles * period + index)"
    by (rule comma_phase_digit_periodic[OF closes])
  show ?case using rearrange phase Suc.IH by simp
qed

lemma comma_python_near_binary_search_correct:
  assumes positive: "0 < f"
    and interval: "lower < upper"
    and lower_ok: "comma_period_displacement f d lower \<le> r"
    and upper_ok: "r < comma_period_displacement f d upper"
    and fuel_ok: "upper - lower \<le> Suc fuel"
  shows "let j = comma_python_near_prefix_search_fuel
      f d r fuel lower upper
    in lower \<le> j \<and> j < upper \<and>
       comma_period_displacement f d j \<le> r \<and>
       r < comma_period_displacement f d (Suc j)"
  using interval lower_ok upper_ok fuel_ok
proof (induction fuel arbitrary: lower upper)
  case 0
  then have adjacent: "upper = lower + 1" by arith
  show ?case by (simp add: adjacent)
next
  case (Suc fuel)
  show ?case
  proof (cases "lower + 1 < upper")
    case False
    then have adjacent: "upper = lower + 1"
      using Suc.prems(1) by arith
    show ?thesis by (simp add: False adjacent)
  next
    case True
    note search_branch = True
    let ?middle = "(lower + upper) div 2"
    have midpoint_sum:
      "lower + upper = 2 * ?middle + (lower + upper) mod 2"
      by (metis div_mult_mod_eq mult.commute)
    have midpoint_remainder: "(lower + upper) mod 2 < 2" by simp
    have midpoint_bounds: "lower < ?middle" "?middle < upper"
      using True midpoint_sum midpoint_remainder by arith+
    have left_width: "upper - ?middle \<le> Suc fuel"
      using midpoint_bounds Suc.prems(4) by arith
    show ?thesis
    proof (cases "comma_period_displacement f d ?middle \<le> r")
      case True
      have result:
        "let j = comma_python_near_prefix_search_fuel
            f d r fuel ?middle upper
         in ?middle \<le> j \<and> j < upper \<and>
           comma_period_displacement f d j \<le> r \<and>
           r < comma_period_displacement f d (Suc j)"
        using Suc.IH[of ?middle upper]
          midpoint_bounds(2) True Suc.prems(3) left_width by blast
      show ?thesis using result search_branch True by (simp add: Let_def)
    next
      case False
      have right_width: "?middle - lower \<le> Suc fuel"
        using midpoint_bounds Suc.prems(4) by arith
      have result:
        "let j = comma_python_near_prefix_search_fuel
            f d r fuel lower ?middle
         in lower \<le> j \<and> j < ?middle \<and>
           comma_period_displacement f d j \<le> r \<and>
           r < comma_period_displacement f d (Suc j)"
        using Suc.IH[of lower ?middle]
          midpoint_bounds(1) Suc.prems(2) False right_width by blast
      show ?thesis using result search_branch False by (simp add: Let_def)
    qed
  qed
qed

record comma_python_near_port_summary =
  comma_python_near_port_steps :: nat
  comma_python_near_port_terminal :: nat
  comma_python_near_port_active :: nat
  comma_python_near_port_point :: nat
  comma_python_near_port_dwell :: nat
  comma_python_near_port_row_numerator :: nat
  comma_python_near_port_row :: nat
  comma_python_near_port_cycles :: nat
  comma_python_near_port_prefix_index :: nat
  comma_python_near_port_remainder :: nat
  comma_python_near_port_prefix_displacement :: nat

definition comma_python_classify_near_port_summary ::
  "nat \<Rightarrow> nat \<Rightarrow> comma_python_near_port_summary" where
  "comma_python_classify_near_port_summary f h =
    (let extra = if f < 9 then 1 else 0;
         digit = (10 - h mod 10) mod 10;
         period = comma_cycle_length f;
         cycle = comma_finite_period f digit;
         cycles = (h - 1 - extra) div cycle;
         remainder = (h - 1 - extra) mod cycle;
         index = comma_python_near_prefix_search_fuel
           f digit remainder period 0 period;
         displacement = comma_period_displacement f digit index;
         active = comma_phase_digit f digit index;
         terminal = 1 + extra + remainder - displacement;
         point = (active + f + extra) mod 10;
         dwell = comma_port_dwell f active;
         row_numerator = 10 * active + f + extra - point - terminal;
         row = row_numerator div 10
     in \<lparr>
       comma_python_near_port_steps = cycles * period + index,
       comma_python_near_port_terminal = terminal,
       comma_python_near_port_active = active,
       comma_python_near_port_point = point,
       comma_python_near_port_dwell = dwell,
       comma_python_near_port_row_numerator = row_numerator,
       comma_python_near_port_row = row,
       comma_python_near_port_cycles = cycles,
       comma_python_near_port_prefix_index = index,
       comma_python_near_port_remainder = remainder,
       comma_python_near_port_prefix_displacement = displacement
     \<rparr>)"

text \<open>The runtime constructs exactly one punctured port after selecting
the active phase, then checks that the selected terminal lies on an admitted
row of that port.  This arithmetic lemma proves those checks from the phase
and terminal guards; it does not identify dwell rows with physical time.\<close>

lemma comma_python_punctured_port_row_guards:
  fixes f active terminal :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and digit: "1 \<le> active" "active \<le> 9"
    and extra_lt: "(if f < 9 then 1 else 0) < terminal"
    and terminal_bound:
      "terminal \<le> 10 * active + f + (if f < 9 then 1 else 0)"
    and phase:
      "(10 - terminal mod 10) mod 10 = active"
  shows "((active + f + (if f < 9 then 1 else 0)) mod 10) + terminal
        \<le> 10 * active + f + (if f < 9 then 1 else 0)"
    "(10 * active + f + (if f < 9 then 1 else 0) -
        ((active + f + (if f < 9 then 1 else 0)) mod 10 + terminal)) mod 10 = 0"
    "(10 * active + f + (if f < 9 then 1 else 0) -
        ((active + f + (if f < 9 then 1 else 0)) mod 10 + terminal)) div 10
      < comma_port_dwell f active"
proof -
  let ?extra = "if f < 9 then 1 else 0"
  let ?point = "(active + f + ?extra) mod 10"
  let ?total = "10 * active + f + ?extra"
  have aligned: "(terminal + active) mod 10 = 0"
    using phase digit by presburger
  have residues: "(?point + terminal) mod 10 = ?total mod 10"
    using aligned by presburger
  have point_bound: "?point < 10" by simp
  have point_terminal_bound: "?point + terminal \<le> ?total"
    using terminal_bound residues point_bound by presburger
  have row_mod:
    "(?total - (?point + terminal)) mod 10 = 0"
    using point_terminal_bound residues by presburger
  show "?point + terminal \<le> ?total" by fact
  show "(?total - (?point + terminal)) mod 10 = 0" by fact
  have row_bound:
    "?total - (?point + terminal) < 10 * comma_port_dwell f active"
  proof (cases "f < 9")
    case True
    show ?thesis
    proof (cases "active = 9")
      case True
      then show ?thesis
        using extra_lt sector terminal_bound digit
        by (simp add: comma_port_dwell_def; presburger)
    next
      case False
      then have active_lt: "active < 9" using digit by arith
      show ?thesis
      proof (cases "9 - f \<le> active")
        case True
        then show ?thesis
          using point_terminal_bound sector active_lt False
          by (simp add: comma_port_dwell_def; presburger)
      next
        case False
        then show ?thesis
          using point_terminal_bound extra_lt sector active_lt
          by (simp add: comma_port_dwell_def; presburger)
      qed
    qed
  next
    case False
    then have f_nine: "f = 9" using sector by arith
    show ?thesis
      using point_terminal_bound sector digit f_nine
      by (simp add: comma_port_dwell_def; presburger)
  qed
  have quotient_bound:
    "(?total - (?point + terminal)) div 10 < comma_port_dwell f active"
    using row_bound by (simp add: div_less_iff_less_mult mult.commute)
  show "(?total - (?point + terminal)) div 10 < comma_port_dwell f active"
    by fact
qed

lemma comma_python_classify_near_port_summary_arithmetic:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and interior: "10 * ((10 - h mod 10) mod 10) + f +
      (if f < 9 then 1 else 0) < h"
    and initial: "h \<le> 540"
  defines "result \<equiv> comma_python_classify_near_port_summary f h"
  shows "comma_python_near_port_cycles result * comma_cycle_length f +
      comma_python_near_port_prefix_index result =
        comma_python_near_port_steps result"
    "comma_python_cycle_displacement f ((10 - h mod 10) mod 10) =
      comma_period_displacement f ((10 - h mod 10) mod 10)
        (comma_cycle_length f)"
    "comma_python_near_port_cycles result =
      (h - 1 - (if f < 9 then 1 else 0)) div
        (comma_python_cycle_displacement f
          ((10 - h mod 10) mod 10))"
    "comma_python_near_port_remainder result =
      (h - 1 - (if f < 9 then 1 else 0)) mod
        (comma_python_cycle_displacement f
          ((10 - h mod 10) mod 10))"
    "comma_python_near_port_remainder result <
      comma_python_cycle_displacement f ((10 - h mod 10) mod 10)"
    "comma_python_near_port_prefix_index result < comma_cycle_length f"
    "comma_period_displacement f ((10 - h mod 10) mod 10)
        (comma_python_near_port_prefix_index result) \<le>
      comma_python_near_port_remainder result"
    "comma_python_near_port_remainder result <
      comma_period_displacement f ((10 - h mod 10) mod 10)
        (Suc (comma_python_near_port_prefix_index result))"
    "\<forall>k\<le>comma_python_near_port_prefix_index result.
      comma_period_displacement f ((10 - h mod 10) mod 10) k \<le>
        comma_python_near_port_remainder result"
    "\<forall>k. comma_python_near_port_prefix_index result < k \<longrightarrow>
      comma_python_near_port_remainder result <
        comma_period_displacement f ((10 - h mod 10) mod 10) k"
    "comma_python_near_port_active result =
      comma_phase_digit f ((10 - h mod 10) mod 10)
        (comma_python_near_port_prefix_index result)"
    "h = comma_python_near_port_terminal result +
      comma_period_displacement f ((10 - h mod 10) mod 10)
        (comma_python_near_port_steps result)"
    "h - comma_python_near_port_terminal result =
      comma_period_displacement f ((10 - h mod 10) mod 10)
        (comma_python_near_port_steps result)"
proof -
  let ?extra = "if f < 9 then 1 else 0"
  let ?digit = "(10 - h mod 10) mod 10"
  let ?period = "comma_cycle_length f"
  let ?cycle = "comma_finite_period f ?digit"
  let ?cycles = "(h - 1 - ?extra) div ?cycle"
  let ?remainder = "(h - 1 - ?extra) mod ?cycle"
  let ?index = "comma_python_near_prefix_search_fuel
    f ?digit ?remainder ?period 0 ?period"
  let ?displacement = "comma_period_displacement f ?digit ?index"
  let ?active = "comma_phase_digit f ?digit ?index"
  let ?terminal = "1 + ?extra + ?remainder - ?displacement"
  have digit: "?digit < 10" by simp
  have period_positive: "0 < ?period"
    using comma_cycle_length_admitted(1)[OF sector] .
  have closes: "10 dvd ?period * f"
    using comma_cycle_length_admitted(2)[OF sector] .
  have cycle_exact:
    "?cycle = comma_period_displacement f ?digit ?period"
    using comma_finite_period_catalog sector digit by auto
  have python_cycle_exact:
    "comma_python_cycle_displacement f ?digit =
      comma_period_displacement f ?digit ?period"
    using comma_python_cycle_displacement_eq_finite_period[of f ?digit]
      cycle_exact by simp
  have cycle_positive: "0 < ?cycle"
    using comma_period_displacement_admitted[OF sector(1) period_positive]
      cycle_exact by simp
  have divmod:
    "h - 1 - ?extra = ?cycles * ?cycle + ?remainder"
    by (metis div_mult_mod_eq mult.commute)
  have remainder_bound: "?remainder < ?cycle"
    using cycle_positive by simp
  have search:
    "let j = comma_python_near_prefix_search_fuel
        f ?digit ?remainder ?period 0 ?period
     in 0 \<le> j \<and> j < ?period \<and>
       comma_period_displacement f ?digit j \<le> ?remainder \<and>
       ?remainder < comma_period_displacement f ?digit (Suc j)"
  proof (rule comma_python_near_binary_search_correct
      [where f=f and d="?digit" and r="?remainder" and fuel="?period"
        and lower=0 and upper="?period"])
    show "0 < f" using sector by arith
    show "0 < ?period" by fact
    show "comma_period_displacement f ?digit 0 \<le> ?remainder" by simp
    show "?remainder < comma_period_displacement f ?digit ?period"
      using remainder_bound cycle_exact by simp
    show "?period - 0 \<le> Suc ?period" by simp
  qed
  have selected:
    "?index < ?period"
    "?displacement \<le> ?remainder"
    "?remainder < comma_period_displacement f ?digit (Suc ?index)"
    using search by (simp_all only: Let_def)
  have all_before:
    "\<forall>k\<le>?index.
      comma_period_displacement f ?digit k \<le> ?remainder"
    using selected(2) comma_period_displacement_mono by blast
  have all_after:
    "\<forall>k. ?index < k \<longrightarrow>
      ?remainder < comma_period_displacement f ?digit k"
  proof (intro allI impI)
    fix k assume index: "?index < k"
    have "Suc ?index \<le> k" using index by arith
    then have "comma_period_displacement f ?digit (Suc ?index) \<le>
        comma_period_displacement f ?digit k"
      by (rule comma_period_displacement_mono)
    then show "?remainder < comma_period_displacement f ?digit k"
      using selected(3) by arith
  qed
  have selected_fields:
    "comma_python_near_port_cycles result = ?cycles"
    "comma_python_near_port_prefix_index result = ?index"
    "comma_python_near_port_remainder result = ?remainder"
    "comma_python_near_port_prefix_displacement result = ?displacement"
    "comma_python_near_port_active result = ?active"
    "comma_python_near_port_terminal result = ?terminal"
    "comma_python_near_port_steps result = ?cycles * ?period + ?index"
    by (simp_all add: result_def comma_python_classify_near_port_summary_def
        Let_def)
  show "comma_python_near_port_cycles result * comma_cycle_length f +
      comma_python_near_port_prefix_index result =
        comma_python_near_port_steps result"
    using selected_fields by simp
  show "comma_python_cycle_displacement f ?digit =
      comma_period_displacement f ?digit ?period"
    using python_cycle_exact .
  show "comma_python_near_port_cycles result =
      (h - 1 - ?extra) div
        comma_python_cycle_displacement f ?digit"
    using python_cycle_exact
    by (simp add: result_def comma_python_classify_near_port_summary_def
        Let_def)
  show "comma_python_near_port_remainder result =
      (h - 1 - ?extra) mod
        comma_python_cycle_displacement f ?digit"
    using python_cycle_exact
    by (simp add: result_def comma_python_classify_near_port_summary_def
        Let_def)
  show "comma_python_near_port_remainder result <
      comma_python_cycle_displacement f ?digit"
    using remainder_bound python_cycle_exact by simp
  show "comma_python_near_port_prefix_index result < comma_cycle_length f"
    using selected(1) selected_fields by simp
  show "comma_period_displacement f ?digit
        (comma_python_near_port_prefix_index result) \<le>
      comma_python_near_port_remainder result"
    using selected(2) selected_fields by simp
  show "comma_python_near_port_remainder result <
      comma_period_displacement f ?digit
        (Suc (comma_python_near_port_prefix_index result))"
    using selected(3) selected_fields by simp
  show "\<forall>k\<le>comma_python_near_port_prefix_index result.
      comma_period_displacement f ?digit k \<le>
        comma_python_near_port_remainder result"
    using all_before selected_fields by simp
  show "\<forall>k. comma_python_near_port_prefix_index result < k \<longrightarrow>
      comma_python_near_port_remainder result <
        comma_period_displacement f ?digit k"
    using all_after selected_fields by simp
  show "comma_python_near_port_active result =
      comma_phase_digit f ?digit
        (comma_python_near_port_prefix_index result)"
    using selected_fields by simp
  have repeated:
    "comma_period_displacement f ?digit (?cycles * ?period + ?index) =
      ?cycles * comma_period_displacement f ?digit ?period + ?displacement"
    using comma_period_displacement_repeated[OF closes, of ?digit ?cycles ?index]
    by (simp add: mult.commute)
  have balance:
    "h = ?terminal +
      comma_period_displacement f ?digit (?cycles * ?period + ?index)"
    using divmod cycle_exact repeated selected(2)
    by (simp add: algebra_simps; arith)
  show "h = comma_python_near_port_terminal result +
      comma_period_displacement f ?digit
        (comma_python_near_port_steps result)"
    using balance selected_fields by simp
  show "h - comma_python_near_port_terminal result =
      comma_period_displacement f ?digit
        (comma_python_near_port_steps result)"
    using balance selected_fields by arith
qed

theorem comma_python_grouped_near_classifier_prefix:
  assumes sector: "1 \<le> f" "f \<le> 9"
    and interior: "10 * ((10 - h mod 10) mod 10) + f +
      (if f < 9 then 1 else 0) < h"
    and initial: "h \<le> 540"
  defines "result \<equiv> comma_python_classify_near_port_summary f h"
  shows "0 < comma_python_near_port_steps result"
    "comma_near_prefix (comma_python_near_port_steps result) f h
      (comma_python_near_port_terminal result)"
    "h = comma_python_near_port_terminal result +
      comma_period_displacement f ((10 - h mod 10) mod 10)
        (comma_python_near_port_steps result)"
    "h - comma_python_near_port_terminal result =
      comma_period_displacement f ((10 - h mod 10) mod 10)
        (comma_python_near_port_steps result)"
    "comma_near_decisive f (comma_python_near_port_terminal result)"
    "comma_near_germ f h =
      (comma_python_near_port_steps result,
       comma_python_near_port_terminal result)"
    "(if f < 9 then 1 else 0) <
      comma_python_near_port_terminal result"
    "comma_python_near_port_terminal result \<le>
      10 * comma_python_near_port_active result + f +
        (if f < 9 then 1 else 0)"
    "1 \<le> comma_python_near_port_active result"
    "comma_python_near_port_active result \<le> 9"
    "comma_python_near_port_point result =
      comma_port_low f (comma_python_near_port_active result)"
    "comma_python_near_port_dwell result =
      comma_port_dwell f (comma_python_near_port_active result)"
    "comma_python_near_port_row_numerator result =
      10 * comma_python_near_port_active result + f +
        (if f < 9 then 1 else 0) -
          comma_python_near_port_point result -
          comma_python_near_port_terminal result"
    "comma_python_near_port_row result =
      comma_python_near_port_row_numerator result div 10"
    "comma_python_near_port_point result +
        comma_python_near_port_terminal result \<le>
      10 * comma_python_near_port_active result + f +
        (if f < 9 then 1 else 0)"
    "comma_python_near_port_row_numerator result mod 10 = 0"
    "comma_python_near_port_row result <
      comma_python_near_port_dwell result"
proof -
  let ?extra = "if f < 9 then 1 else 0"
  let ?digit = "(10 - h mod 10) mod 10"
  let ?index = "comma_python_near_port_prefix_index result"
  let ?cycles = "comma_python_near_port_cycles result"
  let ?steps = "comma_python_near_port_steps result"
  let ?terminal = "comma_python_near_port_terminal result"
  let ?active = "comma_python_near_port_active result"
  let ?point = "(?active + f + ?extra) mod 10"
  let ?D = "comma_period_displacement f ?digit ?steps"
  note arithmetic = comma_python_classify_near_port_summary_arithmetic
    [OF sector interior initial, folded result_def]
  have digit: "?digit < 10" by simp
  have aligned: "(h + ?digit) mod 10 = 0"
    by (rule comma_near_initial_digit_aligned)
  have selected:
    "?index < comma_cycle_length f"
    "comma_period_displacement f ?digit ?index \<le>
      comma_python_near_port_remainder result"
    "comma_python_near_port_remainder result <
      comma_period_displacement f ?digit (Suc ?index)"
    "h = ?terminal + ?D"
    using arithmetic(6,7,8,12) by simp_all
  have positive_period: "0 < comma_cycle_length f"
    using comma_cycle_length_admitted(1)[OF sector] .
  have closes: "10 dvd comma_cycle_length f * f"
    using comma_cycle_length_admitted(2)[OF sector] .
  have extra_lt: "?extra < h" using interior by arith
  have divmod_balance:
    "h = 1 + ?extra +
      comma_python_near_port_cycles result *
        comma_finite_period f ?digit +
      comma_python_near_port_remainder result"
  proof -
    let ?cycle = "comma_python_cycle_displacement f ?digit"
    have quotient:
      "h - 1 - ?extra =
        (h - 1 - ?extra) div ?cycle * ?cycle +
          (h - 1 - ?extra) mod ?cycle"
      by (metis div_mult_mod_eq mult.commute)
    show ?thesis
      using quotient arithmetic(2,3,4) interior by arith
  qed
  have cycle_exact:
    "comma_finite_period f ?digit =
      comma_period_displacement f ?digit (comma_cycle_length f)"
    using comma_finite_period_catalog sector digit by auto
  have repeated:
    "?D = comma_python_near_port_cycles result *
        comma_period_displacement f ?digit (comma_cycle_length f) +
      comma_period_displacement f ?digit ?index"
    using comma_period_displacement_repeated[OF closes, of ?digit ?cycles ?index]
      arithmetic(1) cycle_exact
    by (simp add: algebra_simps)
  have safe: "?D + ?extra < h"
  proof -
    have displacement_le:
      "comma_period_displacement f ?digit ?index \<le>
        comma_python_near_port_remainder result"
      using selected(2) .
    show ?thesis using divmod_balance repeated displacement_le by arith
  qed
  have prefix:
    "comma_near_prefix ?steps f h (h - ?D)"
    by (rule comma_near_prefix_from_displacement
      [OF sector initial digit aligned safe])
  have terminal_eq: "?terminal = h - ?D"
    using selected(4) by arith
  have steps_positive: "0 < ?steps"
  proof (cases "?cycles = 0")
    case False
    then show ?thesis using positive_period arithmetic(1) by simp
  next
    case True
    have small_decomposition:
      "h = 1 + ?extra + comma_python_near_port_remainder result"
      using divmod_balance True by simp
    have first_disp:
      "comma_period_displacement f ?digit (Suc 0) = 10 * ?digit + f"
      by (simp add: comma_period_displacement_succ comma_phase_digit_def
          comma_period_displacement_def)
    have first_fits:
      "comma_period_displacement f ?digit (Suc 0) \<le>
        comma_python_near_port_remainder result"
      using interior small_decomposition first_disp by arith
    have not_zero: "?index \<noteq> 0"
    proof
      assume zero: "?index = 0"
      have "comma_python_near_port_remainder result <
          comma_period_displacement f ?digit (Suc 0)"
        using selected(3) zero by simp
      then show False using first_fits by simp
    qed
    show ?thesis using True not_zero arithmetic(1) by arith
  qed
  show "0 < comma_python_near_port_steps result" using steps_positive .
  show "comma_near_prefix ?steps f h ?terminal"
    using prefix terminal_eq by simp
  show "h = ?terminal + ?D" using selected(4) .
  show "h - ?terminal = ?D" using selected(4) by arith
  have terminal_range: "?extra < ?terminal" "?terminal \<le> 540"
  proof -
    show "?extra < ?terminal"
      using interior selected(2) by (simp add: result_def
        comma_python_classify_near_port_summary_def Let_def; arith)
    have "?terminal \<le> h" using selected(4) by arith
    then show "?terminal \<le> 540" using initial by arith
  qed
  have phase:
    "(10 - ?terminal mod 10) mod 10 =
      comma_python_near_port_active result"
  proof -
    have fits: "?D \<le> h" using selected(4) by arith
    have at_steps:
      "(10 - ?terminal mod 10) mod 10 = comma_phase_digit f ?digit ?steps"
      using comma_near_phase_headroom_digit[OF digit aligned fits] .
    have periodic:
      "comma_phase_digit f ?digit
          (comma_python_near_port_cycles result * comma_cycle_length f + ?index) =
        comma_phase_digit f ?digit ?index"
      by (rule comma_python_near_phase_periods[OF closes])
    have step_count:
      "?steps = comma_python_near_port_cycles result *
        comma_cycle_length f + ?index"
      using arithmetic(1) by simp
    have active:
      "comma_python_near_port_active result =
        comma_phase_digit f ?digit ?index"
      using arithmetic(11) by simp
    show ?thesis using at_steps periodic step_count active by simp
  qed
  have next_gap:
    "comma_period_displacement f ?digit (Suc ?index) =
      comma_period_displacement f ?digit ?index +
        10 * comma_python_near_port_active result + f"
    using comma_period_displacement_succ arithmetic(11) by simp
  have terminal_guard:
    "?terminal \<le> 10 * comma_python_near_port_active result + f + ?extra"
  proof -
    have rem_tail:
      "comma_python_near_port_remainder result -
          comma_period_displacement f ?digit ?index <
        10 * comma_python_near_port_active result + f"
      using selected(3) next_gap by arith
    show ?thesis
      using interior rem_tail
      by (simp add: result_def comma_python_classify_near_port_summary_def
          Let_def; arith)
  qed
  have active_bounds:
    "1 \<le> comma_python_near_port_active result"
    "comma_python_near_port_active result \<le> 9"
    using phase terminal_range terminal_guard sector by presburger+
  have row_guards: "?point + ?terminal \<le>
      10 * comma_python_near_port_active result + f + ?extra"
    "(10 * comma_python_near_port_active result + f + ?extra -
      (?point + ?terminal)) mod 10 = 0"
    "(10 * comma_python_near_port_active result + f + ?extra -
      (?point + ?terminal)) div 10 <
      comma_port_dwell f (comma_python_near_port_active result)"
    using comma_python_punctured_port_row_guards
      [OF sector active_bounds terminal_range(1) terminal_guard phase] .
  have point_field:
    "comma_python_near_port_point result = ?point"
    by (simp add: result_def comma_python_classify_near_port_summary_def Let_def)
  have dwell_field:
    "comma_python_near_port_dwell result =
      comma_port_dwell f (comma_python_near_port_active result)"
    by (simp add: result_def comma_python_classify_near_port_summary_def Let_def)
  have row_numerator_field:
    "comma_python_near_port_row_numerator result =
      10 * comma_python_near_port_active result + f + ?extra -
        (?point + ?terminal)"
    using row_guards(1)
    by (simp add: result_def comma_python_classify_near_port_summary_def Let_def;
        presburger)
  have row_field:
    "comma_python_near_port_row result =
      comma_python_near_port_row_numerator result div 10"
    by (simp add: result_def comma_python_classify_near_port_summary_def Let_def)
  have decisive:
    "comma_near_decisive f ?terminal"
    using comma_near_decisive_iff[OF sector terminal_range] phase
      terminal_guard by simp
  show "comma_near_decisive f ?terminal" using decisive .
  show "comma_near_germ f h = (?steps, ?terminal)"
    using comma_near_prefix_decisive_germ[OF prefix decisive] by simp
  show "?extra < comma_python_near_port_terminal result"
    using terminal_range(1) .
  show "comma_python_near_port_terminal result \<le>
      10 * comma_python_near_port_active result + f + ?extra"
    using terminal_guard .
  show "1 \<le> comma_python_near_port_active result"
    using active_bounds(1) .
  show "comma_python_near_port_active result \<le> 9"
    using active_bounds(2) .
  show "comma_python_near_port_point result =
      comma_port_low f (comma_python_near_port_active result)"
  proof -
    have "?point = comma_port_low f ?active"
      by (simp add: comma_port_low_def)
    then show ?thesis using point_field by simp
  qed
  show "comma_python_near_port_dwell result =
      comma_port_dwell f (comma_python_near_port_active result)"
    using dwell_field .
  show "comma_python_near_port_row_numerator result =
      10 * comma_python_near_port_active result + f + ?extra -
        comma_python_near_port_point result -
        comma_python_near_port_terminal result"
    using row_numerator_field point_field by simp
  show "comma_python_near_port_row result =
      comma_python_near_port_row_numerator result div 10"
    using row_field .
  show "comma_python_near_port_point result +
        comma_python_near_port_terminal result \<le>
      10 * comma_python_near_port_active result + f + ?extra"
    using row_guards(1) point_field by simp
  show "comma_python_near_port_row_numerator result mod 10 = 0"
    using row_guards(2) row_numerator_field by simp
  show "comma_python_near_port_row result <
      comma_python_near_port_dwell result"
    using row_guards(3) row_numerator_field row_field dwell_field
    by simp
qed

text \<open>This is the chart-move contract: the grouped result denotes a
positive, unit-weight scalar Near prefix ending at the first decisive
terminal.  Its literal increment is the exact endpoint displacement; it is
not the port dwell or the physical step count.\<close>

theorem comma_python_grouped_near_chart_contract:
  fixes f h delta p residue :: nat
  assumes sector: "1 \<le> f" "f \<le> 9"
    and interior: "10 * ((10 - h mod 10) mod 10) + f +
      (if f < 9 then 1 else 0) < h"
    and initial: "h \<le> 540"
  defines "result \<equiv> comma_python_classify_near_port_summary f h"
  shows "0 < comma_python_near_port_steps result"
    "comma_near_prefix (comma_python_near_port_steps result) f h
      (comma_python_near_port_terminal result)"
    "comma_near_decisive f (comma_python_near_port_terminal result)"
    "comma_round_weighted_prefix p residue
        (comma_python_near_port_steps result)
        (Comma_Near f delta h)
        (Comma_Near f delta (comma_python_near_port_terminal result))
        (comma_python_near_port_steps result)"
    "h - comma_python_near_port_terminal result =
      comma_period_displacement f ((10 - h mod 10) mod 10)
        (comma_python_near_port_steps result)"
proof -
  note contract = comma_python_grouped_near_classifier_prefix
    [OF sector interior initial, folded result_def]
  show "0 < comma_python_near_port_steps result"
    using contract(1) .
  show "comma_near_prefix (comma_python_near_port_steps result) f h
      (comma_python_near_port_terminal result)"
    using contract(2) .
  show "comma_near_decisive f (comma_python_near_port_terminal result)"
    using contract(5) .
  show "comma_round_weighted_prefix p residue
      (comma_python_near_port_steps result)
      (Comma_Near f delta h)
      (Comma_Near f delta (comma_python_near_port_terminal result))
      (comma_python_near_port_steps result)"
    by (rule comma_near_prefix_weighted[OF contract(2)])
  show "h - comma_python_near_port_terminal result =
      comma_period_displacement f ((10 - h mod 10) mod 10)
        (comma_python_near_port_steps result)"
    using contract(4) .
qed

ML \<open>
  val grouped_near_classifier_theorems =
    @{thms comma_python_classify_near_port_summary_arithmetic
      comma_python_grouped_near_classifier_prefix
      comma_python_grouped_near_chart_contract
      comma_python_punctured_port_row_guards}
  val _ = if null (Thm_Deps.all_oracles grouped_near_classifier_theorems)
    then () else error "grouped Near classifier refinement uses an oracle"
\<close>

end
