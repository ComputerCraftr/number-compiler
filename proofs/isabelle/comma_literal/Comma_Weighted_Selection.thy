theory Comma_Weighted_Selection
  imports Comma_Chart_Bridge.Comma_Chart_Refinement
begin

text \<open>Partial selection within an admitted Entry block.  A selected
literal index is split into complete cyclic phases and a remainder smaller
than one phase; the latter is at most nine edges.\<close>

lemma comma_partial_cycle_arithmetic:
  fixes j L f k P :: nat
  assumes positive: "0 < L"
    and closes: "10 dvd L * f"
    and displacement:
      "P = comma_period_displacement f (k mod 10) L"
  shows "comma_fixed_iter f j k =
    k + (j div L) * P +
      comma_period_displacement f (k mod 10) (j mod L)"
proof -
  have split: "j = (j div L) * L + j mod L"
    using positive by (simp add: div_mult_mod_eq)
  have repeated: "comma_period_displacement f (k mod 10)
      ((j div L) * L + j mod L) =
      (j div L) * P +
        comma_period_displacement f (k mod 10) (j mod L)"
    using comma_period_displacement_repeated
      [OF closes, of "k mod 10" "j div L" "j mod L"]
    by (simp only: displacement)
  show ?thesis using comma_fixed_iter_displacement[of f j k]
    repeated split by simp
qed

lemma comma_cycle_length_at_most_ten:
  assumes "1 \<le> f" "f \<le> 9"
  shows "comma_cycle_length f \<le> 10"
  using assms by (auto simp: comma_cycle_length_def)

lemma comma_admitted_entry_has_positive_cycles:
  fixes f p delta offset H P h c :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
  defines "H \<equiv> 10 ^ (p + delta) - offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "c \<equiv> (H - h) div P"
  shows "0 < c"
proof -
  have catalog: "P \<in> comma_cycle_displacements"
    using comma_finite_period_in_catalog f
    by (auto simp: P_def)
  have Pbound: "0 < P" "P \<le> 540"
    using catalog by (auto simp: comma_cycle_displacements_def)
  let ?e = "comma_finite_guard_extra f"
  have e_bound: "?e \<le> 1"
    by (simp add: comma_finite_guard_extra_def)
  have scale: "100000 \<le> (10::nat) ^ (p + delta)"
  proof -
    have "(10::nat) ^ 5 \<le> 10 ^ (p + delta)"
      by (rule power_increasing) (use exponent in auto)
    then show ?thesis by simp
  qed
  have Hbound: "99902 \<le> H"
    using scale offset by (simp add: H_def; arith)
  have hformula: "h = 1 + ?e + (H - (1 + ?e)) mod P"
    using comma_finite_headroom_reduced[OF f exponent offset,
      of delta]
    by (simp add: h_def H_def P_def Let_def)
  have remainder: "(H - (1 + ?e)) mod P < P"
    using Pbound by simp
  have hbound: "h \<le> P + 2"
    using hformula remainder e_bound by arith
  have enough: "P \<le> H - h"
    using Hbound hbound Pbound by arith
  have "P div P \<le> (H - h) div P"
    using enough by (rule div_le_mono)
  then show ?thesis using Pbound by (simp add: c_def)
qed

theorem comma_admitted_entry_partial_selection:
  fixes f p delta offset k H P h L c j :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
    and j: "j \<le> ((10 ^ (p + delta) - offset -
      comma_finite_headroom f (p mod 924) delta offset) div
      comma_finite_period f (offset mod 10)) * comma_cycle_length f"
  defines "k \<equiv> comma_chart_value p (Comma_Entry f delta offset)"
    and "H \<equiv> 10 ^ (p + delta) - offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "L \<equiv> comma_cycle_length f"
    and "c \<equiv> (H - h) div P"
  shows "j mod L < L"
    "j mod L < 10"
    "j div L \<le> c"
    "0 < c"
    "comma_finite_next_weight p (Comma_Entry f delta offset) = c * L"
    "comma_fixed_iter f j k =
      k + (j div L) * P +
        comma_period_displacement f (offset mod 10) (j mod L)"
    "comma_literal_path j k (comma_fixed_iter f j k)"
proof -
  have bound: "j \<le> c * L"
    using j by (simp add: H_def P_def h_def L_def c_def)
  have length: "0 < L" and closes: "10 dvd L * f"
    using comma_cycle_length_admitted[OF f]
    by (simp_all add: L_def)
  have length_bound: "L \<le> 10"
    using comma_cycle_length_at_most_ten[OF f] by (simp add: L_def)
  have remainder: "j mod L < L" using length by simp
  then show "j mod L < L" .
  show "j mod L < 10" using remainder length_bound by arith
  have quotient: "j div L \<le> c"
  proof -
    have "j div L \<le> (c * L) div L"
      using bound by (rule div_le_mono)
    then show ?thesis using length by simp
  qed
  then show "j div L \<le> c" .
  show "0 < c"
    using comma_admitted_entry_has_positive_cycles[OF f exponent offset,
      of delta]
    by (simp add: H_def P_def h_def c_def)
  show "comma_finite_next_weight p (Comma_Entry f delta offset) = c * L"
    using comma_entry_chart_exact_literal_path(2)
      [OF f exponent offset, of delta]
    by (simp add: k_def H_def P_def h_def L_def c_def)
  have digit: "k mod 10 = offset mod 10"
    using comma_entry_chart_digit[of p f delta offset] exponent
    by (simp add: k_def)
  have displacement: "P = comma_period_displacement f (k mod 10) L"
    using comma_finite_period_refines[OF f, of "offset mod 10"] digit
    by (simp add: P_def L_def)
  show "comma_fixed_iter f j k =
      k + (j div L) * P +
        comma_period_displacement f (offset mod 10) (j mod L)"
    using comma_partial_cycle_arithmetic[OF length closes displacement,
      of j] digit by simp
  have edges: "\<forall>n<c * L. comma_child (comma_fixed_iter f n k)
      (comma_fixed_iter f (Suc n) k)"
    using comma_entry_chart_exact_literal_path(5)
      [OF f exponent offset, of delta]
    by (simp add: k_def H_def P_def h_def L_def c_def)
  show "comma_literal_path j k (comma_fixed_iter f j k)"
    using comma_fixed_iter_literal_path[OF edges] bound by blast
qed

text \<open>These are the exact construction rows consumed by the indexed
point observer.  A row is emitted by the canonical weighted chart move; its
first component is that move's weight at the receiving exponent, and its
second component is the signed change in the interpreted source value.
The terminal branch has no row and no physical tick.  The Python
``SectorFragment`` encoding and resource charging still require a separate
production refinement check; this chart theorem does not infer them from
generic list algebra.\<close>

inductive comma_indexed_trace ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> (nat \<times> int) list
    \<Rightarrow> comma_finite_outcome \<Rightarrow>
    comma_finite_position \<Rightarrow> bool" where
  fork: "comma_weighted_step (p mod 924) position =
      Comma_WFork position a delta \<Longrightarrow>
    comma_indexed_trace p position [] (Comma_Fork_At a delta) position"
| landmine: "comma_weighted_step (p mod 924) position =
      Comma_WLandmine position delta \<Longrightarrow>
    comma_indexed_trace p position [] (Comma_Landmine_At delta) position"
| advance: "comma_weighted_step (p mod 924) position =
      Comma_WNext successor weight \<Longrightarrow>
    comma_indexed_trace p successor rows outcome terminal \<Longrightarrow>
    comma_indexed_trace p position
      ((comma_chart_weight_value p weight,
        int (comma_chart_value p successor) -
          int (comma_chart_value p position)) # rows)
      outcome terminal"

lemma comma_control_trace_indexed:
  assumes trace: "comma_finite_trace_ok (p mod 924) positions outcome"
  shows "\<exists>rows. comma_indexed_trace p (hd positions) rows outcome
      (last positions) \<and>
    sum_list (map fst rows) =
      sum_list (map (comma_finite_next_weight p) (butlast positions))"
  using trace
proof (induction positions arbitrary: outcome)
  case Nil
  then show ?case by simp
next
  case (Cons position tail)
  show ?case
  proof (cases tail)
    case Nil
    show ?thesis
    proof (cases "comma_weighted_step (p mod 924) position")
      case (Comma_WNext successor weight)
      then show ?thesis using Cons.prems Nil
        by (simp add: comma_finite_step_def del: comma_weighted_step_def)
    next
      case (Comma_WFork terminal a delta)
      have owner: "terminal = position"
        by (rule comma_weighted_terminal_is_source,
            rule disjI1, rule Comma_WFork)
      have local_trace: "comma_indexed_trace p position []
          (Comma_Fork_At a delta) position"
        using comma_indexed_trace.fork Comma_WFork owner by blast
      show ?thesis using Cons.prems Nil Comma_WFork owner local_trace
        by (auto simp: comma_finite_step_def del: comma_weighted_step_def)
    next
      case (Comma_WLandmine terminal delta)
      have owner: "terminal = position"
        by (rule comma_weighted_terminal_is_source[where a=0],
            rule disjI2, rule Comma_WLandmine)
      have local_trace: "comma_indexed_trace p position []
          (Comma_Landmine_At delta) position"
        using comma_indexed_trace.landmine Comma_WLandmine owner by blast
      show ?thesis using Cons.prems Nil Comma_WLandmine owner local_trace
        by (auto simp: comma_finite_step_def del: comma_weighted_step_def)
    next
      case Comma_WInvalid
      then show ?thesis using Cons.prems Nil
        by (simp add: comma_finite_step_def del: comma_weighted_step_def)
    qed
  next
    case (Cons successor rest)
    have step: "comma_finite_step (p mod 924) position = Comma_Next successor"
      using Cons.prems Cons by simp
    obtain local_weight where weighted:
      "comma_weighted_step (p mod 924) position =
        Comma_WNext successor local_weight"
      using step by (cases "comma_weighted_step (p mod 924) position")
        (auto simp: comma_finite_step_def del: comma_weighted_step_def)
    have tail_trace: "comma_finite_trace_ok (p mod 924) tail outcome"
      using Cons.prems Cons by simp
    obtain rows where ih:
      "comma_indexed_trace p (hd tail) rows outcome (last tail)"
      "sum_list (map fst rows) =
        sum_list (map (comma_finite_next_weight p) (butlast tail))"
      using Cons.IH[OF tail_trace] by blast
    have suffix:
      "comma_indexed_trace p successor rows outcome (last (successor # rest))"
      "sum_list (map fst rows) =
        sum_list (map (comma_finite_next_weight p) (butlast (successor # rest)))"
      using ih Cons by simp_all
    have amount: "comma_finite_next_weight p position =
        comma_chart_weight_value p local_weight"
      by (simp only: comma_finite_next_weight_def weighted comma_weighted_move.case)
    show ?thesis
      using comma_indexed_trace.advance[OF weighted suffix(1)] suffix(2) Cons amount
      by (auto simp del: comma_weighted_step_def)
  qed
qed

lemma comma_indexed_trace_weighted_run:
  assumes trace: "comma_indexed_trace p position rows outcome terminal"
  shows "comma_finite_weighted_run (Suc (length rows)) p position =
    Some (outcome, sum_list (map fst rows), terminal)"
  using trace
proof (induction rule: comma_indexed_trace.induct)
  case (fork p position a delta)
  then show ?case by (simp del: comma_weighted_step_def)
next
  case (landmine p position delta)
  then show ?case by (simp del: comma_weighted_step_def)
next
  case (advance p position successor weight rows outcome terminal)
  then show ?case by (simp del: comma_weighted_step_def)
qed

text \<open>Conversely, a successful canonical weighted run produces its
own indexed trace.  This extracts the existing constructor transitions;
it does not posit a supplied event word or an independent evaluator.\<close>

lemma comma_weighted_run_indexed_trace:
  assumes run: "comma_finite_weighted_run fuel p position =
    Some (outcome,weight,terminal)"
  shows "\<exists>rows. comma_indexed_trace p position rows outcome terminal
    \<and> sum_list (map fst rows) = weight"
  using run
proof (induction fuel arbitrary: position outcome weight terminal)
  case 0
  then show ?case by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "comma_weighted_step (p mod 924) position")
    case (Comma_WNext successor local_weight)
    then obtain tail_weight where tail:
      "comma_finite_weighted_run fuel p successor =
        Some (outcome,tail_weight,terminal)"
      using Suc.prems
      by (cases "comma_finite_weighted_run fuel p successor")
        (auto simp del: comma_weighted_step_def split: prod.splits)
    obtain rows where rows:
      "comma_indexed_trace p successor rows outcome terminal"
      "sum_list (map fst rows) = tail_weight"
      using Suc.IH[OF tail] by blast
    have trace: "comma_indexed_trace p position
      ((comma_chart_weight_value p local_weight,
        int (comma_chart_value p successor) -
          int (comma_chart_value p position)) # rows)
      outcome terminal"
      using comma_indexed_trace.advance[OF Comma_WNext rows(1)] .
    have "weight = comma_chart_weight_value p local_weight + tail_weight"
      using Suc.prems Comma_WNext tail
      by (simp del: comma_weighted_step_def)
    then show ?thesis using trace rows(2) by auto
  next
    case (Comma_WFork stop a delta)
    have stop: "stop = position"
      using comma_weighted_terminal_is_source Comma_WFork by blast
    have result_fields: "outcome = Comma_Fork_At a delta"
      "weight = 0" "terminal = position"
      using Suc.prems Comma_WFork stop
      by (simp_all del: comma_weighted_step_def)
    have "comma_indexed_trace p position []
      (Comma_Fork_At a delta) position"
      using comma_indexed_trace.fork[OF Comma_WFork[unfolded stop]] .
    then show ?thesis using result_fields by auto
  next
    case (Comma_WLandmine stop delta)
    have stop: "stop = position"
      using comma_weighted_terminal_is_source Comma_WLandmine by blast
    have result_fields: "outcome = Comma_Landmine_At delta"
      "weight = 0" "terminal = position"
      using Suc.prems Comma_WLandmine stop
      by (simp_all del: comma_weighted_step_def)
    have "comma_indexed_trace p position []
      (Comma_Landmine_At delta) position"
      using comma_indexed_trace.landmine
        [OF Comma_WLandmine[unfolded stop]] .
    then show ?thesis using result_fields by auto
  next
    case Comma_WInvalid
    then show ?thesis using Suc.prems
      by (simp del: comma_weighted_step_def)
  qed
qed

lemma comma_boundary_indexed_trace_admitted:
  fixes q :: comma_boundary_state
  assumes valid: "comma_boundary_valid q"
    and exponent: "5 \<le> p"
    and residue: "p mod 924 = snd (snd q)"
    and trace: "comma_indexed_trace p (comma_finite_initial q)
      rows outcome terminal"
  shows "comma_finite_weighted_macro (Suc (length rows)) p q =
    Some (outcome, sum_list (map fst rows), terminal)"
  using comma_indexed_trace_weighted_run[OF trace]
    valid exponent residue
  by (simp add: comma_finite_weighted_macro_def)

lemma comma_indexed_trace_displacement:
  assumes trace: "comma_indexed_trace p position rows outcome terminal"
  shows "sum_list (map snd rows) =
    int (comma_chart_value p terminal) -
      int (comma_chart_value p position)"
  using trace
proof (induction rule: comma_indexed_trace.induct)
  case (fork p position a delta)
  then show ?case by simp
next
  case (landmine p position delta)
  then show ?case by simp
next
  case (advance p position successor weight rows outcome terminal)
  then show ?case by simp
qed

inductive comma_indexed_prefix ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> nat \<Rightarrow>
    comma_finite_position \<Rightarrow> nat \<Rightarrow> bool" where
  empty: "comma_indexed_prefix p position 0 position 0"
| advance: "comma_weighted_step (p mod 924) position =
      Comma_WNext successor local_weight \<Longrightarrow>
    comma_indexed_prefix p successor i middle tail_weight \<Longrightarrow>
    comma_indexed_prefix p position (Suc i) middle
      (comma_chart_weight_value p local_weight + tail_weight)"

lemma comma_indexed_trace_prefix_occurrence:
  assumes trace: "comma_indexed_trace p position rows outcome terminal"
    and index: "i \<le> length rows"
  shows "\<exists>middle.
    comma_indexed_prefix p position i middle
      (sum_list (map fst (take i rows))) \<and>
    sum_list (map snd (take i rows)) =
      int (comma_chart_value p middle) -
        int (comma_chart_value p position)"
  using trace index
proof (induction arbitrary: i rule: comma_indexed_trace.induct)
  case (fork p position a delta)
  then show ?case by (auto intro: comma_indexed_prefix.empty)
next
  case (landmine p position delta)
  then show ?case by (auto intro: comma_indexed_prefix.empty)
next
  case (advance p position successor weight rows outcome terminal)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by (auto intro: comma_indexed_prefix.empty)
  next
    case (Suc j)
    have j: "j \<le> length rows" using advance.prems Suc by simp
    obtain middle where middle:
        "comma_indexed_prefix p successor j middle
          (sum_list (map fst (take j rows)))"
        "sum_list (map snd (take j rows)) =
          int (comma_chart_value p middle) -
            int (comma_chart_value p successor)"
      using advance.IH[OF j] by blast
    have prefix: "comma_indexed_prefix p position (Suc j) middle
      (comma_chart_weight_value p weight +
        sum_list (map fst (take j rows)))"
      using comma_indexed_prefix.advance[OF advance.hyps(1) middle(1)]
      .
    show ?thesis using prefix middle(2) Suc
      by (auto simp: algebra_simps)
  qed
qed

fun comma_scan_left ::
  "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list" where
  "comma_scan_left update initial [] = [initial]"
| "comma_scan_left update initial (row # rows) =
    initial # comma_scan_left update (update initial row) rows"

lemma comma_scan_left_length [simp]:
  "length (comma_scan_left update initial rows) = Suc (length rows)"
  by (induction rows arbitrary: initial) simp_all

lemma comma_scan_left_head [simp]:
  "comma_scan_left update initial rows ! 0 = initial"
  by (cases rows) simp_all

lemma comma_scan_left_nonempty [simp]:
  "comma_scan_left update initial rows \<noteq> []"
  by (cases rows) simp_all

definition comma_indexed_prefixes ::
  "(nat \<times> int) list \<Rightarrow> (nat \<times> int) list" where
  "comma_indexed_prefixes rows =
    comma_scan_left (\<lambda>total row.
      (fst total + fst row, snd total + snd row)) (0,0) rows"

lemma comma_indexed_prefixes_length [simp]:
  "length (comma_indexed_prefixes rows) = Suc (length rows)"
  by (simp add: comma_indexed_prefixes_def)

lemma comma_indexed_prefixes_initial [simp]:
  "comma_indexed_prefixes rows ! 0 = (0,0)"
  by (simp add: comma_indexed_prefixes_def)

lemma comma_indexed_scanl_final:
  "last (comma_scan_left (\<lambda>total row.
      (fst total + fst row, snd total + snd row)) initial rows) =
    (fst initial + sum_list (map fst rows),
      snd initial + sum_list (map snd rows))"
proof (induction rows arbitrary: initial)
  case Nil
  then show ?case by simp
next
  case (Cons row rows)
  show ?case using Cons.IH[of
      "(fst initial + fst row, snd initial + snd row)"]
    by (simp add: algebra_simps)
qed

lemma comma_indexed_prefixes_final:
  "last (comma_indexed_prefixes rows) =
    (sum_list (map fst rows), sum_list (map snd rows))"
  using comma_indexed_scanl_final[of "(0,0)" rows]
  by (simp add: comma_indexed_prefixes_def)

lemma comma_indexed_scanl_nth:
  assumes "i \<le> length rows"
  shows "comma_scan_left (\<lambda>total row.
      (fst total + fst row, snd total + snd row)) initial rows ! i =
    (fst initial + sum_list (map fst (take i rows)),
      snd initial + sum_list (map snd (take i rows)))"
  using assms
proof (induction rows arbitrary: i initial)
  case Nil
  then show ?case by simp
next
  case (Cons row rows)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis by simp
  next
    case (Suc j)
    have j: "j \<le> length rows" using Cons.prems Suc by simp
    show ?thesis
      using Cons.IH[OF j, of
        "(fst initial + fst row, snd initial + snd row)"]
      by (simp add: Suc algebra_simps)
  qed
qed

lemma comma_indexed_prefixes_nth:
  assumes "i \<le> length rows"
  shows "comma_indexed_prefixes rows ! i =
    (sum_list (map fst (take i rows)),
      sum_list (map snd (take i rows)))"
  using comma_indexed_scanl_nth[OF assms, of "(0,0)"]
  by (simp add: comma_indexed_prefixes_def)

lemma comma_indexed_prefix_counts_mono:
  assumes "i \<le> j" "j \<le> length rows"
  shows "fst (comma_indexed_prefixes rows ! i) \<le>
    fst (comma_indexed_prefixes rows ! j)"
proof -
  have i: "i \<le> length rows" using assms by arith
  have ji: "j = i + (j - i)" using assms by arith
  have split: "take j rows = take i rows @
      take (j - i) (drop i rows)"
  proof -
    have "take j rows = take (i + (j - i)) rows"
      using ji by (rule arg_cong)
    also have "... = take i rows @ take (j - i) (drop i rows)"
      by (rule take_add)
    finally show ?thesis .
  qed
  show ?thesis
    using comma_indexed_prefixes_nth[OF i]
      comma_indexed_prefixes_nth[OF assms(2)]
    by (simp add: split)
qed

text \<open>This is the exact interval update used by the production
``MacroTemplate.point`` binary search.  The prefix-array theorem below is
deliberately separate from the chart arithmetic: a proof of a block weight
does not by itself justify selection inside that block.\<close>

fun comma_prefix_lower_bound ::
  "nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_prefix_lower_bound 0 xs target low high = low"
| "comma_prefix_lower_bound (Suc fuel) xs target low high =
    (if high \<le> low then low else
      (let middle = (low + high) div 2 in
        if target \<le> xs ! middle then
          comma_prefix_lower_bound fuel xs target low middle
        else comma_prefix_lower_bound fuel xs target (Suc middle) high))"

lemma comma_binary_midpoint_bounds:
  fixes low high :: nat
  assumes "low < high"
  shows "low \<le> (low + high) div 2"
    "(low + high) div 2 < high"
proof -
  let ?mid = "(low + high) div 2"
  have decomp: "low + high = 2 * ?mid + (low + high) mod 2"
    by (simp add: div_mult_mod_eq)
  have rem: "(low + high) mod 2 < 2" by simp
  show "low \<le> ?mid" using assms decomp rem by arith
  show "?mid < high" using assms decomp rem by arith
qed

lemma comma_prefix_lower_bound_correct:
  fixes xs :: "nat list"
  assumes budget: "high - low \<le> fuel"
    and interval: "low \<le> first" "first \<le> high"
    and length: "high < length xs"
    and before: "\<And>i. low \<le> i \<Longrightarrow> i < first \<Longrightarrow> xs ! i < target"
    and after: "\<And>i. first \<le> i \<Longrightarrow> i \<le> high \<Longrightarrow> target \<le> xs ! i"
  shows "comma_prefix_lower_bound fuel xs target low high = first"
  using assms
proof (induction fuel arbitrary: low high)
  case 0
  then have "low = high" by arith
  then show ?case using 0 by simp
next
  case (Suc fuel)
  show ?case
  proof (cases "high \<le> low")
    case True
    then have "low = first" using Suc.prems by arith
    then show ?thesis using True by simp
  next
    case False
    then have strict: "low < high" by simp
    let ?middle = "(low + high) div 2"
    have mid: "low \<le> ?middle" "?middle < high"
      using comma_binary_midpoint_bounds[OF strict] by simp_all
    show ?thesis
    proof (cases "target \<le> xs ! ?middle")
      case True
      have first: "first \<le> ?middle"
      proof (rule ccontr)
        assume "\<not> first \<le> ?middle"
        then have "xs ! ?middle < target"
          using Suc.prems(5)[OF mid(1)] by simp
        then show False using True by simp
      qed
      have budget: "?middle - low \<le> fuel"
        using Suc.prems(1) mid strict by arith
      have before: "\<And>i. low \<le> i \<Longrightarrow> i < first
          \<Longrightarrow> xs ! i < target"
        using Suc.prems(5) by blast
      have after: "\<And>i. first \<le> i \<Longrightarrow> i \<le> ?middle
          \<Longrightarrow> target \<le> xs ! i"
      proof -
        fix i assume first_i: "first \<le> i" and i_mid: "i \<le> ?middle"
        have i_high: "i \<le> high" using i_mid mid by arith
        show "target \<le> xs ! i"
          by (rule Suc.prems(6)[OF first_i i_high])
      qed
      have correct: "comma_prefix_lower_bound fuel xs target low ?middle = first"
        using Suc.IH[OF budget Suc.prems(2) first _ before after]
          Suc.prems(4) mid by auto
      have notle: "\<not> high \<le> low" using strict by simp
      have step_eq: "comma_prefix_lower_bound (Suc fuel) xs target
          low high = comma_prefix_lower_bound fuel xs target low ?middle"
        by (simp only: comma_prefix_lower_bound.simps(2) Let_def
          notle if_False True if_True)
      show ?thesis using step_eq correct by simp
    next
      case False
      have first: "Suc ?middle \<le> first"
      proof (rule ccontr)
        assume "\<not> Suc ?middle \<le> first"
        then have "target \<le> xs ! ?middle"
          using Suc.prems(6) Suc.prems(3) mid by auto
        then show False using False by simp
      qed
      have budget: "high - Suc ?middle \<le> fuel"
        using Suc.prems(1) mid strict by arith
      have before: "\<And>i. Suc ?middle \<le> i \<Longrightarrow> i < first
          \<Longrightarrow> xs ! i < target"
      proof -
        fix i assume middle_i: "Suc ?middle \<le> i"
          and i_first: "i < first"
        have low_i: "low \<le> i" using middle_i mid by arith
        show "xs ! i < target"
          by (rule Suc.prems(5)[OF low_i i_first])
      qed
      have after: "\<And>i. first \<le> i \<Longrightarrow> i \<le> high
          \<Longrightarrow> target \<le> xs ! i"
        using Suc.prems(6) by blast
      have correct: "comma_prefix_lower_bound fuel xs target
          (Suc ?middle) high = first"
        using Suc.IH[OF budget first Suc.prems(3) Suc.prems(4)
          before after] .
      have notle: "\<not> high \<le> low" using strict by simp
      have step_eq: "comma_prefix_lower_bound (Suc fuel) xs target
          low high = comma_prefix_lower_bound fuel xs target
            (Suc ?middle) high"
        by (simp only: comma_prefix_lower_bound.simps(2) Let_def
          notle if_False False if_True)
      show ?thesis using step_eq correct by simp
    qed
  qed
qed

theorem comma_prefix_search_first_crossing:
  fixes xs :: "nat list"
  assumes length: "1 < length xs"
    and positive: "0 < target"
    and initial: "xs ! 0 = 0"
    and final: "target \<le> xs ! (length xs - 1)"
    and monotone: "\<And>i j. 1 \<le> i \<Longrightarrow> i \<le> j
      \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i \<le> xs ! j"
  defines "first \<equiv> Min {i. 1 \<le> i \<and> i < length xs
    \<and> target \<le> xs ! i}"
  shows "comma_prefix_lower_bound (length xs - 2) xs target 1
      (length xs - 1) = first"
    "1 \<le> first" "first < length xs"
    "target \<le> xs ! first"
    "xs ! (first - 1) < target"
    "\<forall>i. 1 \<le> i \<and> i < first \<longrightarrow> xs ! i < target"
proof -
  let ?S = "{i. 1 \<le> i \<and> i < length xs \<and> target \<le> xs ! i}"
  have finite: "finite ?S"
    by (rule finite_subset[of ?S "{..<length xs}"]) auto
  have last: "length xs - 1 \<in> ?S"
    using length final by auto
  have nonempty: "?S \<noteq> {}" using last by blast
  have in_set: "first \<in> ?S"
    using Min_in[OF finite nonempty] by (simp add: first_def)
  then have bounds: "1 \<le> first" "first < length xs"
    "target \<le> xs ! first" by auto
  show "1 \<le> first" "first < length xs"
    "target \<le> xs ! first" using bounds by simp_all
  show "xs ! (first - 1) < target"
  proof (cases "first = 1")
    case True
    then show ?thesis using initial positive by simp
  next
    case False
    then have one: "1 \<le> first - 1" using bounds by arith
    have less: "first - 1 < first" using bounds by arith
    have below: "first - 1 < length xs" using less bounds by arith
    have "first - 1 \<notin> ?S"
    proof
      assume member: "first - 1 \<in> ?S"
      have "first \<le> first - 1"
        using Min_le[OF finite member] by (simp add: first_def)
      then show False using less by simp
    qed
    then show ?thesis using one below by auto
  qed
  have first_le_last: "first \<le> length xs - 1"
    using Min_le[OF finite last] by (simp add: first_def)
  have before: "\<And>i. 1 \<le> i \<Longrightarrow> i < first
      \<Longrightarrow> xs ! i < target"
  proof -
    fix i assume one: "1 \<le> i" and less: "i < first"
    have below: "i < length xs" using less bounds by arith
    have "i \<notin> ?S"
    proof
      assume member: "i \<in> ?S"
      have "first \<le> i"
        using Min_le[OF finite member] by (simp add: first_def)
      then show False using less by simp
    qed
    then show "xs ! i < target" using one below by auto
  qed
  show "\<forall>i. 1 \<le> i \<and> i < first \<longrightarrow> xs ! i < target"
    using before by blast
  have after: "\<And>i. first \<le> i \<Longrightarrow> i \<le> length xs - 1
      \<Longrightarrow> target \<le> xs ! i"
  proof -
    fix i assume first_i: "first \<le> i"
      and i_last: "i \<le> length xs - 1"
    have i_length: "i < length xs" using i_last length by arith
    have ordered: "xs ! first \<le> xs ! i"
      by (rule monotone[OF bounds(1) first_i i_length])
    show "target \<le> xs ! i" using bounds(3) ordered by arith
  qed
  have budget: "(length xs - 1) - 1 \<le> length xs - 2"
    using length by arith
  show "comma_prefix_lower_bound (length xs - 2) xs target 1
      (length xs - 1) = first"
    using comma_prefix_lower_bound_correct[OF budget bounds(1)
      first_le_last _ before after]
      length by auto
qed

theorem comma_indexed_trace_point_selection:
  assumes trace: "comma_indexed_trace p position rows outcome terminal"
    and requested: "0 < requested"
      "requested < sum_list (map fst rows)"
  defines "prefixes \<equiv> map fst (comma_indexed_prefixes rows)"
    and "first \<equiv> Min {i. 1 \<le> i \<and>
      i < length (map fst (comma_indexed_prefixes rows)) \<and>
      requested \<le> map fst (comma_indexed_prefixes rows) ! i}"
  shows "comma_finite_weighted_run (Suc (length rows)) p position =
      Some (outcome, sum_list (map fst rows), terminal)"
    "last (comma_indexed_prefixes rows) =
      (sum_list (map fst rows),
        int (comma_chart_value p terminal) -
          int (comma_chart_value p position))"
    "comma_prefix_lower_bound (length prefixes - 2) prefixes
      requested 1 (length prefixes - 1) = first"
    "first - 1 < length rows"
    "prefixes ! (first - 1) < requested"
    "requested \<le> prefixes ! first"
    "\<exists>middle. comma_indexed_prefix p position (first - 1) middle
      (prefixes ! (first - 1)) \<and>
      snd (comma_indexed_prefixes rows ! (first - 1)) =
        int (comma_chart_value p middle) -
          int (comma_chart_value p position)"
    "1 \<le> first"
proof -
  show "comma_finite_weighted_run (Suc (length rows)) p position =
      Some (outcome, sum_list (map fst rows), terminal)"
    using comma_indexed_trace_weighted_run[OF trace] .
  show "last (comma_indexed_prefixes rows) =
      (sum_list (map fst rows),
        int (comma_chart_value p terminal) -
          int (comma_chart_value p position))"
    using comma_indexed_prefixes_final
      comma_indexed_trace_displacement[OF trace] by simp
  have rows: "rows \<noteq> []"
    using requested by (cases rows) simp_all
  have length: "1 < length prefixes"
    using rows by (simp add: prefixes_def)
  have initial: "prefixes ! 0 = 0"
    by (simp add: prefixes_def)
  have final: "requested \<le> prefixes ! (length prefixes - 1)"
  proof -
    have "prefixes ! (length prefixes - 1) =
        sum_list (map fst rows)"
      using comma_indexed_prefixes_nth[of "length rows" rows]
      by (simp add: prefixes_def)
    then show ?thesis using requested by simp
  qed
  have monotone: "\<And>i j. 1 \<le> i \<Longrightarrow> i \<le> j
      \<Longrightarrow> j < length prefixes \<Longrightarrow>
      prefixes ! i \<le> prefixes ! j"
    using comma_indexed_prefix_counts_mono[of _ _ rows]
    by (simp add: prefixes_def)
  have first_eq: "first = Min {i. 1 \<le> i \<and> i < length prefixes
      \<and> requested \<le> prefixes ! i}"
    by (simp only: first_def prefixes_def)
  have selected:
      "comma_prefix_lower_bound (length prefixes - 2) prefixes
        requested 1 (length prefixes - 1) = first"
      "1 \<le> first" "first < length prefixes"
      "requested \<le> prefixes ! first"
      "prefixes ! (first - 1) < requested"
    using comma_prefix_search_first_crossing
      [OF length requested(1) initial final monotone]
      first_eq
    by (simp_all only: first_eq)
  show "1 \<le> first" using selected(2) .
  show "comma_prefix_lower_bound (length prefixes - 2) prefixes
      requested 1 (length prefixes - 1) = first"
    "prefixes ! (first - 1) < requested"
    "requested \<le> prefixes ! first"
    using selected by simp_all
  have fragment: "first - 1 < length rows"
    using selected(2,3) by (simp add: prefixes_def; arith)
  then show "first - 1 < length rows" .
  have prefix_bound: "first - 1 \<le> length rows"
    using fragment by arith
  obtain middle where middle:
      "comma_indexed_prefix p position (first - 1) middle
        (sum_list (map fst (take (first - 1) rows)))"
      "sum_list (map snd (take (first - 1) rows)) =
        int (comma_chart_value p middle) -
          int (comma_chart_value p position)"
    using comma_indexed_trace_prefix_occurrence[OF trace prefix_bound]
    by blast
  have index_valid: "first - 1 < length (comma_indexed_prefixes rows)"
    using prefix_bound by simp
  have nth: "comma_indexed_prefixes rows ! (first - 1) =
      (sum_list (map fst (take (first - 1) rows)),
        sum_list (map snd (take (first - 1) rows)))"
    by (rule comma_indexed_prefixes_nth[OF prefix_bound])
  have prefix_value: "prefixes ! (first - 1) =
      sum_list (map fst (take (first - 1) rows))"
    using nth index_valid by (simp add: prefixes_def)
  show "\<exists>middle. comma_indexed_prefix p position (first - 1) middle
      (prefixes ! (first - 1)) \<and>
      snd (comma_indexed_prefixes rows ! (first - 1)) =
        int (comma_chart_value p middle) -
          int (comma_chart_value p position)"
  proof (rule exI[where x=middle])
    show "comma_indexed_prefix p position (first - 1) middle
        (prefixes ! (first - 1)) \<and>
        snd (comma_indexed_prefixes rows ! (first - 1)) =
          int (comma_chart_value p middle) -
            int (comma_chart_value p position)"
      using middle nth prefix_value by simp
  qed
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_partial_cycle_arithmetic
      comma_cycle_length_at_most_ten
      comma_admitted_entry_has_positive_cycles
      comma_admitted_entry_partial_selection
      comma_scan_left_length
      comma_scan_left_head
      comma_scan_left_nonempty
      comma_indexed_trace_weighted_run
      comma_weighted_run_indexed_trace
      comma_boundary_indexed_trace_admitted
      comma_indexed_trace_displacement
      comma_indexed_trace_prefix_occurrence
      comma_indexed_prefixes_final
      comma_indexed_prefixes_nth
      comma_indexed_prefix_counts_mono
      comma_binary_midpoint_bounds
      comma_prefix_lower_bound_correct
      comma_prefix_search_first_crossing
      comma_indexed_trace_point_selection})
    then () else error "Comma weighted selection depends on an oracle";
\<close>

end
