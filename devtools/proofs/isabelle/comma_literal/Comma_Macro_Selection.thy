theory Comma_Macro_Selection
  imports Comma_Weighted_Selection
begin

text \<open>A chart fragment has an exact literal point at every position in
its emitted weight.  The Entry case uses the proved phase-cycle formula;
the Near case has at most one physical edge.  This predicate records the
local refinement obligation, not another executable transition system.\<close>

fun comma_chart_fragment_point ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position
    \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_chart_fragment_point p (Comma_Entry f delta offset) next j =
    comma_fixed_iter f j
      (comma_chart_value p (Comma_Entry f delta offset))"
| "comma_chart_fragment_point p (Comma_Near f delta H) next j =
    (if j = 0 then comma_chart_value p (Comma_Near f delta H)
     else comma_chart_value p next)"

text \<open>This is the selected-value arithmetic used by the production
fragment consumer: complete cycles contribute their displacement and the
remaining phase contributes fewer than ten local edges.  The affine
encoding of Python's prefix arrays is a separate executable-refinement
obligation; this equation concerns the admitted chart semantics.\<close>

fun comma_chart_fragment_closed ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position
    \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_chart_fragment_closed p (Comma_Entry f delta offset) next j =
    (let L = comma_cycle_length f;
         P = comma_finite_period f (offset mod 10)
     in comma_chart_value p (Comma_Entry f delta offset) +
       (j div L) * P +
       comma_period_displacement f (offset mod 10) (j mod L))"
| "comma_chart_fragment_closed p (Comma_Near f delta H) next j =
    (if j = 0 then comma_chart_value p (Comma_Near f delta H)
     else comma_chart_value p next)"

lemma comma_admitted_entry_fragment_closed:
  fixes f p delta offset j :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
    and in_block: "j \<le> ((10 ^ (p + delta) - offset -
      comma_finite_headroom f (p mod 924) delta offset) div
      comma_finite_period f (offset mod 10)) * comma_cycle_length f"
  shows "comma_chart_fragment_point p (Comma_Entry f delta offset)
      next j =
    comma_chart_fragment_closed p (Comma_Entry f delta offset)
      next j"
    "j mod comma_cycle_length f < 10"
  using comma_admitted_entry_partial_selection(2,6)
    [OF f exponent offset in_block]
  by (simp_all add: Let_def)

definition comma_chart_step_refined ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_finite_position \<Rightarrow> comma_chart_weight \<Rightarrow> bool" where
  "comma_chart_step_refined p source next weight \<longleftrightarrow>
    (let W = comma_chart_weight_value p weight in
      comma_chart_fragment_point p source next 0 =
        comma_chart_value p source \<and>
      comma_chart_fragment_point p source next W =
        comma_chart_value p next \<and>
      (\<forall>j\<le>W. comma_literal_path j (comma_chart_value p source)
        (comma_chart_fragment_point p source next j)))"

lemma comma_admitted_entry_step_refined:
  fixes f p delta offset h :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
  shows "comma_chart_step_refined p (Comma_Entry f delta offset)
    (Comma_Near f delta h)
    (Comma_Chart_Weight (comma_cycle_length f) delta
      (- int (comma_cycle_length f * (offset + h)))
      (comma_finite_period f (offset mod 10)))"
proof -
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?H = "10 ^ (p + delta) - offset"
  let ?L = "comma_cycle_length f"
  let ?c = "(?H - h) div ?P"
  let ?weight = "Comma_Chart_Weight ?L delta
      (- int (?L * (offset + h))) ?P"
  have emission: "comma_chart_weight_value p ?weight = ?c * ?L"
    using comma_entry_chart_exact_literal_path(2,7)
      [OF f exponent offset]
    by (simp add: h_def comma_finite_next_weight_def)
  have endpoint: "comma_fixed_iter f (?c * ?L)
      (comma_chart_value p (Comma_Entry f delta offset)) =
      comma_chart_value p (Comma_Near f delta h)"
  proof -
    have input_bound: "?c * ?L \<le> ((10 ^ (p + delta) - offset -
        comma_finite_headroom f (p mod 924) delta offset) div
        comma_finite_period f (offset mod 10)) * comma_cycle_length f"
      by (simp add: h_def)
    have arithmetic: "comma_fixed_iter f (?c * ?L)
        (comma_chart_value p (Comma_Entry f delta offset)) =
        comma_chart_value p (Comma_Entry f delta offset) + ?c * ?P"
      using comma_admitted_entry_partial_selection(6)
        [OF f exponent offset input_bound]
        comma_cycle_length_admitted[OF f]
      by (simp add: h_def comma_period_displacement_def)
    show ?thesis
      using arithmetic comma_entry_chart_exact_literal_path(3)
        [OF f exponent offset]
      by (simp add: h_def)
  qed
  have partial: "\<forall>j\<le>?c * ?L.
      comma_literal_path j
        (comma_chart_value p (Comma_Entry f delta offset))
        (comma_fixed_iter f j
          (comma_chart_value p (Comma_Entry f delta offset)))"
  proof -
    have edges: "\<forall>j<?c * ?L.
        comma_child
          (comma_fixed_iter f j
            (comma_chart_value p (Comma_Entry f delta offset)))
          (comma_fixed_iter f (Suc j)
            (comma_chart_value p (Comma_Entry f delta offset)))"
      using comma_entry_chart_exact_literal_path(5)
        [OF f exponent offset]
      by (simp add: h_def)
    show ?thesis using comma_fixed_iter_literal_path[OF edges]
      by blast
  qed
  show ?thesis using emission endpoint partial
    by (auto simp: comma_chart_step_refined_def Let_def
      intro: comma_literal_path.zero)
qed

lemma comma_admitted_near_step_refined:
  fixes f p delta H :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and headroom: "1 \<le> H" "H \<le> 540"
    and step: "comma_weighted_step (p mod 924)
      (Comma_Near f delta H) = Comma_WNext next weight"
  shows "comma_chart_step_refined p (Comma_Near f delta H)
    next weight"
proof -
  have finite: "comma_finite_step (p mod 924)
      (Comma_Near f delta H) = Comma_Next next"
    using step by (simp add: comma_finite_step_def)
  have unit: "comma_chart_weight_value p weight = 1"
    using comma_near_chart_next_literal(2)
      [OF f exponent headroom finite]
      step by (simp add: comma_finite_next_weight_def)
  have edge: "comma_literal_path 1
      (comma_chart_value p (Comma_Near f delta H))
      (comma_chart_value p next)"
    using comma_near_chart_next_literal(1)
      [OF f exponent headroom finite] by simp
  have partial: "\<forall>j\<le>1. comma_literal_path j
      (comma_chart_value p (Comma_Near f delta H))
      (comma_chart_fragment_point p (Comma_Near f delta H) next j)"
  proof (intro allI impI)
    fix j :: nat assume bound: "j \<le> 1"
    show "comma_literal_path j
        (comma_chart_value p (Comma_Near f delta H))
        (comma_chart_fragment_point p (Comma_Near f delta H) next j)"
    proof (cases "j = 0")
      case True
      then show ?thesis by (simp add: comma_literal_path.zero)
    next
      case False
      then have one: "j = 1" using bound by arith
      show ?thesis using edge by (simp add: one)
    qed
  qed
  show ?thesis using unit partial
    by (simp add: comma_chart_step_refined_def Let_def)
qed

lemma comma_admitted_weighted_step_refined:
  assumes exponent: "5 \<le> p"
    and step: "comma_weighted_step (p mod 924) source =
      Comma_WNext next weight"
  shows "comma_chart_step_refined p source next weight"
proof (cases source)
  case (Comma_Entry f delta offset)
  have valid: "1 \<le> f" "f \<le> 9" "offset \<le> 98"
    using step by (auto simp: Comma_Entry comma_weighted_step_def
      Let_def split: if_splits)
  let ?h = "comma_finite_headroom f (p mod 924) delta offset"
  let ?L = "comma_cycle_length f"
  let ?P = "comma_finite_period f (offset mod 10)"
  have shape: "next = Comma_Near f delta ?h"
    "weight = Comma_Chart_Weight ?L delta
      (- int (?L * (offset + ?h))) ?P"
    using step valid
    by (auto simp: Comma_Entry comma_weighted_step_def Let_def
      split: if_splits)
  show ?thesis
    using comma_admitted_entry_step_refined
      [OF valid(1,2) exponent valid(3)]
      shape by (simp add: Comma_Entry)
next
  case (Comma_Near f delta H)
  have finite: "comma_finite_step (p mod 924)
      (Comma_Near f delta H) = Comma_Next next"
    using step by (simp add: Comma_Near comma_finite_step_def)
  have valid: "1 \<le> f" "f \<le> 9" "1 \<le> H" "H \<le> 540"
    using comma_near_success_admissible[of "p mod 924" f delta H]
      finite by auto
  show ?thesis
    using comma_admitted_near_step_refined
      [OF valid(1,2) exponent valid(3,4)] step
    by (simp add: Comma_Near)
qed

lemma comma_admitted_step_fragment_closed:
  assumes exponent: "5 \<le> p"
    and step: "comma_weighted_step (p mod 924) source =
      Comma_WNext next weight"
    and index: "j \<le> comma_chart_weight_value p weight"
  shows "comma_chart_fragment_point p source next j =
    comma_chart_fragment_closed p source next j"
proof (cases source)
  case (Comma_Entry f delta offset)
  have valid: "1 \<le> f" "f \<le> 9" "offset \<le> 98"
    using step by (auto simp: Comma_Entry comma_weighted_step_def
      Let_def split: if_splits)
  let ?h = "comma_finite_headroom f (p mod 924) delta offset"
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?L = "comma_cycle_length f"
  let ?c = "((10 ^ (p + delta) - offset - ?h) div ?P)"
  have shape: "weight = Comma_Chart_Weight ?L delta
      (- int (?L * (offset + ?h))) ?P"
    using step valid
    by (auto simp: Comma_Entry comma_weighted_step_def Let_def
      split: if_splits)
  have amount: "comma_chart_weight_value p weight = ?c * ?L"
    using comma_entry_chart_exact_literal_path(2,7)
      [OF valid(1,2) exponent valid(3)]
      shape by (simp add: comma_finite_next_weight_def)
  show ?thesis
    using comma_admitted_entry_fragment_closed(1)
      [OF valid(1,2) exponent valid(3)]
      index amount by (simp add: Comma_Entry)
next
  case (Comma_Near f delta H)
  then show ?thesis by simp
qed

inductive comma_refined_indexed_trace ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    (nat \<times> int) list \<Rightarrow> comma_finite_outcome \<Rightarrow>
    comma_finite_position \<Rightarrow> bool" where
  fork: "comma_weighted_step (p mod 924) position =
      Comma_WFork position a delta \<Longrightarrow>
    comma_refined_indexed_trace p position []
      (Comma_Fork_At a delta) position"
| landmine: "comma_weighted_step (p mod 924) position =
      Comma_WLandmine position delta \<Longrightarrow>
    comma_refined_indexed_trace p position []
      (Comma_Landmine_At delta) position"
| advance: "comma_weighted_step (p mod 924) position =
      Comma_WNext successor weight \<Longrightarrow>
    comma_chart_step_refined p position successor weight \<Longrightarrow>
    comma_refined_indexed_trace p successor rows outcome terminal \<Longrightarrow>
    comma_refined_indexed_trace p position
      ((comma_chart_weight_value p weight,
        int (comma_chart_value p successor) -
          int (comma_chart_value p position)) # rows)
      outcome terminal"

lemma comma_refined_indexed_trace_erases:
  assumes "comma_refined_indexed_trace p position rows outcome terminal"
  shows "comma_indexed_trace p position rows outcome terminal"
  using assms by (induction rule: comma_refined_indexed_trace.induct)
    (auto intro: comma_indexed_trace.intros)

lemma comma_indexed_trace_is_refined:
  assumes exponent: "5 \<le> p"
    and trace: "comma_indexed_trace p position rows outcome terminal"
  shows "comma_refined_indexed_trace p position rows outcome terminal"
  using trace exponent
proof (induction rule: comma_indexed_trace.induct)
  case (fork p position a delta)
  then show ?case by (auto intro: comma_refined_indexed_trace.fork)
next
  case (landmine p position delta)
  then show ?case by (auto intro: comma_refined_indexed_trace.landmine)
next
  case (advance p position successor weight rows outcome terminal)
  have local: "comma_chart_step_refined p position successor weight"
    using comma_admitted_weighted_step_refined[OF advance.prems
      advance.hyps(1)] .
  show ?case using advance.hyps(1) local
      advance.IH[OF advance.prems]
    by (rule comma_refined_indexed_trace.advance)
qed

lemma comma_refined_indexed_trace_row:
  assumes trace:
      "comma_refined_indexed_trace p position rows outcome terminal"
    and index: "i < length rows"
  shows "\<exists>middle successor weight.
    comma_indexed_prefix p position i middle
      (sum_list (map fst (take i rows))) \<and>
    comma_weighted_step (p mod 924) middle =
      Comma_WNext successor weight \<and>
    comma_chart_step_refined p middle successor weight \<and>
    rows ! i =
      (comma_chart_weight_value p weight,
        int (comma_chart_value p successor) -
          int (comma_chart_value p middle))"
  using trace index
proof (induction arbitrary: i rule: comma_refined_indexed_trace.induct)
  case (fork p position a delta)
  then show ?case by simp
next
  case (landmine p position delta)
  then show ?case by simp
next
  case (advance p position successor weight rows outcome terminal)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis using advance.hyps(1,2)
      by (auto intro: comma_indexed_prefix.empty)
  next
    case (Suc j)
    have j: "j < length rows" using advance.prems Suc by simp
    obtain middle successor' local_weight where tail:
        "comma_indexed_prefix p successor j middle
          (sum_list (map fst (take j rows)))"
        "comma_weighted_step (p mod 924) middle =
          Comma_WNext successor' local_weight"
        "comma_chart_step_refined p middle successor' local_weight"
        "rows ! j =
          (comma_chart_weight_value p local_weight,
            int (comma_chart_value p successor') -
              int (comma_chart_value p middle))"
      using advance.IH[OF j] by blast
    have prefix: "comma_indexed_prefix p position (Suc j) middle
      (comma_chart_weight_value p weight +
        sum_list (map fst (take j rows)))"
      using comma_indexed_prefix.advance[OF advance.hyps(1) tail(1)]
      .
    show ?thesis using prefix tail Suc by auto
  qed
qed

lemma comma_refined_indexed_trace_prefix_path:
  assumes trace:
      "comma_refined_indexed_trace p position rows outcome terminal"
    and index: "i \<le> length rows"
  shows "\<exists>middle.
    comma_indexed_prefix p position i middle
      (sum_list (map fst (take i rows))) \<and>
    comma_literal_path (sum_list (map fst (take i rows)))
      (comma_chart_value p position) (comma_chart_value p middle)"
  using trace index
proof (induction arbitrary: i rule: comma_refined_indexed_trace.induct)
  case (fork p position a delta)
  then show ?case
    by (auto intro: comma_indexed_prefix.empty comma_literal_path.zero)
next
  case (landmine p position delta)
  then show ?case
    by (auto intro: comma_indexed_prefix.empty comma_literal_path.zero)
next
  case (advance p position successor weight rows outcome terminal)
  show ?case
  proof (cases i)
    case 0
    then show ?thesis
      by (auto intro: comma_indexed_prefix.empty comma_literal_path.zero)
  next
    case (Suc j)
    have j: "j \<le> length rows" using advance.prems Suc by simp
    obtain middle where middle:
        "comma_indexed_prefix p successor j middle
          (sum_list (map fst (take j rows)))"
        "comma_literal_path (sum_list (map fst (take j rows)))
          (comma_chart_value p successor) (comma_chart_value p middle)"
      using advance.IH[OF j] by blast
    let ?W = "comma_chart_weight_value p weight"
    have local_endpoint: "comma_chart_fragment_point p position
        successor ?W = comma_chart_value p successor"
      and local_prefixes: "\<forall>k\<le>?W. comma_literal_path k
        (comma_chart_value p position)
        (comma_chart_fragment_point p position successor k)"
      using advance.hyps(2)
      by (auto simp: comma_chart_step_refined_def Let_def)
    have at_W: "comma_literal_path ?W
        (comma_chart_value p position)
        (comma_chart_fragment_point p position successor ?W)"
      using local_prefixes[rule_format, of ?W] by simp
    have local_path: "comma_literal_path ?W
        (comma_chart_value p position) (comma_chart_value p successor)"
      using at_W by (simp only: local_endpoint)
    have joined: "comma_literal_path
        (?W + sum_list (map fst (take j rows)))
        (comma_chart_value p position) (comma_chart_value p middle)"
      using comma_literal_path_append[OF local_path middle(2)] .
    have prefix: "comma_indexed_prefix p position (Suc j) middle
      (?W + sum_list (map fst (take j rows)))"
      using comma_indexed_prefix.advance[OF advance.hyps(1) middle(1)] .
    let ?row = "(?W, int (comma_chart_value p successor) -
      int (comma_chart_value p position))"
    show ?thesis
    proof (rule exI[where x=middle])
      show "comma_indexed_prefix p position i middle
          (sum_list (map fst (take i (?row # rows)))) \<and>
        comma_literal_path (sum_list (map fst (take i (?row # rows))))
          (comma_chart_value p position) (comma_chart_value p middle)"
        using Suc prefix joined by simp
    qed
  qed
qed

lemma comma_indexed_prefix_zero_fields:
  assumes "comma_indexed_prefix p source 0 middle weight"
  shows "middle = source \<and> weight = 0"
  using assms by (cases rule: comma_indexed_prefix.cases) auto

lemma comma_indexed_prefix_suc_fields:
  assumes "comma_indexed_prefix p source (Suc i) middle weight"
  shows "\<exists>successor local_weight tail_weight.
    comma_weighted_step (p mod 924) source =
      Comma_WNext successor local_weight \<and>
    comma_indexed_prefix p successor i middle tail_weight \<and>
    weight = comma_chart_weight_value p local_weight + tail_weight"
  using assms by (cases rule: comma_indexed_prefix.cases) auto

lemma comma_indexed_prefix_unique:
  assumes first: "comma_indexed_prefix p source i middle weight"
    and second: "comma_indexed_prefix p source i other other_weight"
  shows "middle = other \<and> weight = other_weight"
  using first second
proof (induction arbitrary: other other_weight
    rule: comma_indexed_prefix.induct)
  case (empty p source)
  show ?case
    using comma_indexed_prefix_zero_fields[OF empty.prems] by simp
next
  case (advance p source successor local_weight i middle tail_weight)
  obtain other_successor other_local_weight other_tail_weight where other:
      "comma_weighted_step (p mod 924) source =
        Comma_WNext other_successor other_local_weight"
      "comma_indexed_prefix p other_successor i other other_tail_weight"
      "other_weight =
        comma_chart_weight_value p other_local_weight + other_tail_weight"
    using comma_indexed_prefix_suc_fields[OF advance.prems] by blast
  have same_step: "other_successor = successor"
      "other_local_weight = local_weight"
    using advance.hyps(1) other(1) by simp_all
  have same_tail: "middle = other \<and>
      tail_weight = other_tail_weight"
    using advance.IH[OF other(2)[unfolded same_step(1)]] .
  show ?case using same_step same_tail other(3) by simp
qed

lemma comma_refined_indexed_trace_terminal_path:
  assumes trace:
    "comma_refined_indexed_trace p position rows outcome terminal"
  shows "comma_literal_path (sum_list (map fst rows))
    (comma_chart_value p position) (comma_chart_value p terminal)"
proof -
  have last: "comma_indexed_prefix p position (length rows) terminal
      (sum_list (map fst rows))"
    using trace
    by (induction rule: comma_refined_indexed_trace.induct)
      (auto intro: comma_indexed_prefix.intros)
  obtain middle where middle:
      "comma_indexed_prefix p position (length rows) middle
        (sum_list (map fst rows))"
      "comma_literal_path (sum_list (map fst rows))
        (comma_chart_value p position) (comma_chart_value p middle)"
    using comma_refined_indexed_trace_prefix_path[OF trace,
      of "length rows"] by auto
  have "middle = terminal"
    using comma_indexed_prefix_unique[OF middle(1) last] by simp
  then show ?thesis using middle(2) by simp
qed

text \<open>Literal point selection for a successful admitted chart run.
The first positive prefix crossing is the same binary-search index used
by the Python indexed macro.  The zero and final positions are treated
separately, so the terminal fork contributes no phantom physical edge.
This statement is conditional on a successful canonical trace; it does
not assert that every boundary state terminates within a supplied fuel.
\<close>

theorem comma_indexed_trace_whole_macro_point:
  assumes exponent: "5 \<le> p"
    and trace: "comma_indexed_trace p position rows outcome terminal"
  defines "W \<equiv> sum_list (map fst rows)"
    and "prefixes \<equiv> map fst (comma_indexed_prefixes rows)"
  shows "comma_literal_path 0 (comma_chart_value p position)
      (comma_chart_value p position)"
    "comma_literal_path W (comma_chart_value p position)
      (comma_chart_value p terminal)"
    "\<And>j. 0 < j \<Longrightarrow> j < W \<Longrightarrow>
      let first = comma_prefix_lower_bound (length prefixes - 2)
        prefixes j 1 (length prefixes - 1) in
      \<exists>middle successor weight.
        comma_indexed_prefix p position (first - 1) middle
          (prefixes ! (first - 1)) \<and>
        comma_weighted_step (p mod 924) middle =
          Comma_WNext successor weight \<and>
        (let r = j - prefixes ! (first - 1) in
          0 < r \<and> r \<le> comma_chart_weight_value p weight \<and>
          comma_literal_path j (comma_chart_value p position)
            (comma_chart_fragment_closed p middle successor r))"
proof -
  have refined:
    "comma_refined_indexed_trace p position rows outcome terminal"
    using comma_indexed_trace_is_refined[OF exponent trace] .
  show "comma_literal_path 0 (comma_chart_value p position)
      (comma_chart_value p position)"
    by (rule comma_literal_path.zero)
  show "comma_literal_path W (comma_chart_value p position)
      (comma_chart_value p terminal)"
    using comma_refined_indexed_trace_terminal_path[OF refined]
    by (simp add: W_def)
  fix j assume positive: "0 < j" and below: "j < W"
  define first where "first = comma_prefix_lower_bound
      (length prefixes - 2) prefixes j 1 (length prefixes - 1)"
  have below': "j < sum_list (map fst rows)"
    using below by (simp add: W_def)
  have selected: "first - 1 < length rows"
      "prefixes ! (first - 1) < j"
      "j \<le> prefixes ! first"
  proof -
    show "first - 1 < length rows"
      "prefixes ! (first - 1) < j"
      "j \<le> prefixes ! first"
    using comma_indexed_trace_point_selection(3-6)
      [OF trace positive below']
      by (simp_all add: prefixes_def first_def)
  qed
  have first_positive: "1 \<le> first"
    using comma_indexed_trace_point_selection(3,8)
      [OF trace positive below']
    by (simp add: prefixes_def first_def)
  have prefix_bound: "first - 1 \<le> length rows"
    using selected(1) by arith
  obtain middle successor weight where row:
      "comma_indexed_prefix p position (first - 1) middle
        (sum_list (map fst (take (first - 1) rows)))"
      "comma_weighted_step (p mod 924) middle =
        Comma_WNext successor weight"
      "comma_chart_step_refined p middle successor weight"
      "rows ! (first - 1) =
        (comma_chart_weight_value p weight,
          int (comma_chart_value p successor) -
            int (comma_chart_value p middle))"
    using comma_refined_indexed_trace_row[OF refined selected(1)]
    by blast
  have prefix_at: "prefixes ! (first - 1) =
      sum_list (map fst (take (first - 1) rows))"
  proof -
    have index_valid: "first - 1 < length (comma_indexed_prefixes rows)"
      using prefix_bound by simp
    have pair: "comma_indexed_prefixes rows ! (first - 1) =
        (sum_list (map fst (take (first - 1) rows)),
          sum_list (map snd (take (first - 1) rows)))"
      by (rule comma_indexed_prefixes_nth[OF prefix_bound])
    show ?thesis using pair index_valid
      by (simp add: prefixes_def)
  qed
  have next_at: "prefixes ! first =
      prefixes ! (first - 1) + comma_chart_weight_value p weight"
  proof -
    have first: "first \<le> length rows" using selected(1) by arith
    have take: "take first rows =
        take (first - 1) rows @ [rows ! (first - 1)]"
    proof -
      have first_suc: "first = Suc (first - 1)"
        using first_positive by arith
      have take_suc: "take (Suc (first - 1)) rows =
          take (first - 1) rows @ [rows ! (first - 1)]"
        using selected(1) by (simp add: take_Suc_conv_app_nth)
      show ?thesis using first_suc take_suc by simp
    qed
    have first_valid: "first < length (comma_indexed_prefixes rows)"
      using first by simp
    have first_pair: "comma_indexed_prefixes rows ! first =
        (sum_list (map fst (take first rows)),
          sum_list (map snd (take first rows)))"
      by (rule comma_indexed_prefixes_nth[OF first])
    have first_value: "prefixes ! first =
        sum_list (map fst (take first rows))"
      using first_pair first_valid by (simp add: prefixes_def)
    show ?thesis using first_value prefix_at take row(4) by simp
  qed
  let ?r = "j - prefixes ! (first - 1)"
  have r: "0 < ?r" "?r \<le> comma_chart_weight_value p weight"
    using selected(2,3) next_at by arith+
  obtain prefix_middle where prefix_middle:
      "comma_indexed_prefix p position (first - 1) prefix_middle
        (sum_list (map fst (take (first - 1) rows)))"
      "comma_literal_path
        (sum_list (map fst (take (first - 1) rows)))
        (comma_chart_value p position)
        (comma_chart_value p prefix_middle)"
    using comma_refined_indexed_trace_prefix_path
      [OF refined prefix_bound] by blast
  have same: "prefix_middle = middle"
    using comma_indexed_prefix_unique[OF prefix_middle(1) row(1)]
    by simp
  have local_path: "comma_literal_path ?r (comma_chart_value p middle)
      (comma_chart_fragment_point p middle successor ?r)"
  proof -
    have all: "\<forall>k\<le>comma_chart_weight_value p weight.
        comma_literal_path k (comma_chart_value p middle)
          (comma_chart_fragment_point p middle successor k)"
      using row(3)
      by (simp add: comma_chart_step_refined_def Let_def)
    show ?thesis using all[rule_format, of ?r] r(2) by simp
  qed
  have count_eq: "sum_list (map fst (take (first - 1) rows)) + ?r = j"
    using prefix_at selected(2) by arith
  have composed: "comma_literal_path j (comma_chart_value p position)
      (comma_chart_fragment_point p middle successor ?r)"
    using comma_literal_path_append
      [OF prefix_middle(2)[unfolded same] local_path] count_eq
    by simp
  have joined: "comma_literal_path j (comma_chart_value p position)
      (comma_chart_fragment_closed p middle successor ?r)"
    using composed
      comma_admitted_step_fragment_closed[OF exponent row(2) r(2)]
    by simp
  have interior: "\<exists>middle successor weight.
      comma_indexed_prefix p position (first - 1) middle
        (prefixes ! (first - 1)) \<and>
      comma_weighted_step (p mod 924) middle =
        Comma_WNext successor weight \<and>
      (let r = j - prefixes ! (first - 1) in
        0 < r \<and> r \<le> comma_chart_weight_value p weight \<and>
        comma_literal_path j (comma_chart_value p position)
          (comma_chart_fragment_closed p middle successor r))"
  proof (rule exI[where x=middle], rule exI[where x=successor],
      rule exI[where x=weight])
    show "comma_indexed_prefix p position (first - 1) middle
        (prefixes ! (first - 1)) \<and>
      comma_weighted_step (p mod 924) middle =
        Comma_WNext successor weight \<and>
      (let r = j - prefixes ! (first - 1) in
        0 < r \<and> r \<le> comma_chart_weight_value p weight \<and>
        comma_literal_path j (comma_chart_value p position)
          (comma_chart_fragment_closed p middle successor r))"
      using row(1,2) r joined prefix_at by (simp add: Let_def)
  qed
  show "let first = comma_prefix_lower_bound (length prefixes - 2)
      prefixes j 1 (length prefixes - 1) in
      \<exists>middle successor weight.
        comma_indexed_prefix p position (first - 1) middle
          (prefixes ! (first - 1)) \<and>
        comma_weighted_step (p mod 924) middle =
          Comma_WNext successor weight \<and>
        (let r = j - prefixes ! (first - 1) in
          0 < r \<and> r \<le> comma_chart_weight_value p weight \<and>
          comma_literal_path j (comma_chart_value p position)
            (comma_chart_fragment_closed p middle successor r))"
    using interior by (simp only: first_def Let_def)
qed


ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_admitted_entry_fragment_closed
      comma_admitted_entry_step_refined
      comma_admitted_near_step_refined
      comma_admitted_weighted_step_refined
      comma_admitted_step_fragment_closed
      comma_refined_indexed_trace_erases
      comma_indexed_trace_is_refined
      comma_refined_indexed_trace_row
      comma_refined_indexed_trace_prefix_path
      comma_indexed_prefix_zero_fields
      comma_indexed_prefix_suc_fields
      comma_indexed_prefix_unique
      comma_refined_indexed_trace_terminal_path
      comma_indexed_trace_whole_macro_point})
    then () else error "Comma macro selection depends on an oracle";
\<close>

end
