theory Comma_Semantic_Weighted_Selection
  imports Comma_Semantic_Future.Comma_Semantic_Boundary
    Comma_Literal_Bridge.Comma_Macro_Selection
begin

fun comma_shift_weighted_chart_weight ::
  "nat \<Rightarrow> comma_chart_weight \<Rightarrow> comma_chart_weight" where
  "comma_shift_weighted_chart_weight k (Comma_Chart_Weight scale delta offset denominator) =
    (if scale=0 then Comma_Chart_Weight scale delta offset denominator
     else Comma_Chart_Weight scale (delta+k) offset denominator)"

fun comma_shift_weighted_move ::
  "nat \<Rightarrow> comma_weighted_move \<Rightarrow> comma_weighted_move" where
  "comma_shift_weighted_move k (Comma_WNext position weight) =
    Comma_WNext (comma_shift_position k position)
      (comma_shift_weighted_chart_weight k weight)"
| "comma_shift_weighted_move k (Comma_WFork position a delta) =
    Comma_WFork (comma_shift_position k position) a (delta+k)"
| "comma_shift_weighted_move k (Comma_WLandmine position delta) =
    Comma_WLandmine (comma_shift_position k position) (delta+k)"
| "comma_shift_weighted_move k Comma_WInvalid = Comma_WInvalid"

fun comma_shift_weighted_outcome ::
  "nat \<Rightarrow> comma_finite_outcome \<Rightarrow> comma_finite_outcome" where
  "comma_shift_weighted_outcome k (Comma_Fork_At a delta) =
    Comma_Fork_At a (delta+k)"
| "comma_shift_weighted_outcome k (Comma_Landmine_At delta) =
    Comma_Landmine_At (delta+k)"

lemma comma_shift_weighted_chart_weight_value:
  "comma_chart_weight_value p (comma_shift_weighted_chart_weight k weight) =
    comma_chart_weight_value (p+k) weight"
proof (cases weight)
  case (Comma_Chart_Weight scale delta offset denominator)
  show ?thesis
  proof (cases "scale=0")
    case True
    then show ?thesis
      by (simp add: Comma_Chart_Weight comma_chart_weight_value_def)
  next
    case False
    have shifted:
      "comma_shift_weighted_chart_weight k weight =
        comma_weight_piece_shift k weight"
      using Comma_Chart_Weight False
      by (simp add: comma_shift_weighted_chart_weight.simps
        comma_weight_piece_shift.simps add.commute)
    show ?thesis
      by (simp only: shifted comma_weight_piece_shift_exact)
  qed
qed

lemma comma_chart_value_shift_position:
  "comma_chart_value p (comma_shift_position k position) =
    comma_chart_value (p+k) position"
  by (cases position)
    (simp_all add: comma_chart_value_def add.assoc add.commute add.left_commute)

lemma comma_weighted_step_shift_position:
  "comma_weighted_step residue (comma_shift_position k position) =
    comma_shift_weighted_move k
      (comma_weighted_step ((residue+k) mod 924) position)"
proof (cases position)
  case (Comma_Entry f delta offset)
  have phase:
    "(residue+(delta+k)) mod 924 =
      ((((residue+k) mod 924)+delta) mod 924)"
  proof -
    have "(((residue+k) mod 924)+delta) mod 924 =
        (residue+k+delta) mod 924"
      by (rule mod_add_left_eq)
    then show ?thesis by (simp add: add.assoc add.commute add.left_commute)
  qed
  have headroom:
    "comma_finite_headroom f residue (delta+k) offset =
      comma_finite_headroom f ((residue+k) mod 924) delta offset"
    by (rule comma_entry_headroom_phase[OF phase])
  show ?thesis
    using headroom
    by (simp add: Comma_Entry comma_weighted_step_def
      comma_weighted_step_with_headroom_def comma_shift_weighted_move.simps
      comma_shift_weighted_chart_weight.simps Let_def add.commute
      comma_cycle_length_admitted(1)
      split: if_splits)
next
  case (Comma_Near f delta headroom)
  show ?thesis
    by (simp add: Comma_Near comma_weighted_step_def
      comma_weighted_step_with_headroom_def comma_shift_weighted_move.simps
      comma_shift_weighted_chart_weight.simps Let_def add.assoc
      split: if_splits)
qed

text \<open>This bridge turns a semantic round-weighted prefix into the literal
indexed rows consumed by chart selection.  It uses the canonical weighted
step and terminal chart move directly; it does not use finite-run or
total-macro evaluator fuel.\<close>

lemma comma_round_weighted_prefix_indexed_trace:
  assumes phase: "r mod 924 = p mod 924"
    and prefix: "comma_round_weighted_prefix p r n source terminal weight"
    and stop:
      "comma_weighted_step (p mod 924) terminal =
          Comma_WFork terminal a delta \<or>
       comma_weighted_step (p mod 924) terminal =
          Comma_WLandmine terminal delta"
  shows "(\<exists>rows. comma_indexed_trace p source rows
      (Comma_Fork_At a delta) terminal \<and>
      sum_list (map fst rows) = weight) \<or>
    (\<exists>rows. comma_indexed_trace p source rows
      (Comma_Landmine_At delta) terminal \<and>
      sum_list (map fst rows) = weight)"
  using prefix
proof (induction n arbitrary: source weight)
  case "0"
  have source_eq: "source = terminal"
    and weight_eq: "weight = 0"
    using "0".prems by simp
  show ?case
  proof (rule disjE[OF stop])
    assume fork_stop:
      "comma_weighted_step (p mod 924) terminal =
        Comma_WFork terminal a delta"
    have trace: "comma_indexed_trace p terminal []
        (Comma_Fork_At a delta) terminal"
      by (rule comma_indexed_trace.fork[OF fork_stop])
    show ?thesis using trace source_eq weight_eq by blast
  next
    assume landmine_stop:
      "comma_weighted_step (p mod 924) terminal =
        Comma_WLandmine terminal delta"
    have trace: "comma_indexed_trace p terminal []
        (Comma_Landmine_At delta) terminal"
      by (rule comma_indexed_trace.landmine[OF landmine_stop])
    show ?thesis using trace source_eq weight_eq by blast
  qed
next
  case (Suc n)
  obtain successor local_weight rest where move:
      "comma_weighted_step (r mod 924) source =
        Comma_WNext successor local_weight"
    and tail: "comma_round_weighted_prefix p r n successor terminal rest"
    and weight_eq: "weight = comma_chart_weight_value p local_weight + rest"
    using Suc.prems
    by (simp only: comma_round_weighted_prefix_suc; blast)
  have move_p:
    "comma_weighted_step (p mod 924) source =
      Comma_WNext successor local_weight"
    using move phase by simp
  have ih:
    "(\<exists>rows. comma_indexed_trace p successor rows
        (Comma_Fork_At a delta) terminal \<and>
        sum_list (map fst rows) = rest) \<or>
     (\<exists>rows. comma_indexed_trace p successor rows
        (Comma_Landmine_At delta) terminal \<and>
        sum_list (map fst rows) = rest)"
    by (rule Suc.IH[OF tail])
  show ?case
  proof (rule disjE[OF ih])
    assume fork:
      "\<exists>rows. comma_indexed_trace p successor rows
          (Comma_Fork_At a delta) terminal \<and>
        sum_list (map fst rows) = rest"
    then obtain rows where trace:
        "comma_indexed_trace p successor rows
          (Comma_Fork_At a delta) terminal"
        and total: "sum_list (map fst rows) = rest"
      by blast
    let ?joined_rows =
      "(comma_chart_weight_value p local_weight,
        int (comma_chart_value p successor) -
          int (comma_chart_value p source)) # rows"
    have joined: "comma_indexed_trace p source ?joined_rows
        (Comma_Fork_At a delta) terminal"
      by (rule comma_indexed_trace.advance[OF move_p trace])
    have joined_weight: "sum_list (map fst ?joined_rows) = weight"
      using total weight_eq by simp
    show ?thesis using joined joined_weight by blast
  next
    assume landmine:
      "\<exists>rows. comma_indexed_trace p successor rows
          (Comma_Landmine_At delta) terminal \<and>
        sum_list (map fst rows) = rest"
    then obtain rows where trace:
        "comma_indexed_trace p successor rows
          (Comma_Landmine_At delta) terminal"
        and total: "sum_list (map fst rows) = rest"
      by blast
    let ?joined_rows =
      "(comma_chart_weight_value p local_weight,
        int (comma_chart_value p successor) -
          int (comma_chart_value p source)) # rows"
    have joined: "comma_indexed_trace p source ?joined_rows
        (Comma_Landmine_At delta) terminal"
      by (rule comma_indexed_trace.advance[OF move_p trace])
    have joined_weight: "sum_list (map fst ?joined_rows) = weight"
      using total weight_eq by simp
    show ?thesis using joined joined_weight by blast
  qed
qed

lemma comma_round_weighted_prefix_shift_position:
  assumes prefix:
    "comma_round_weighted_prefix (p+k) (p+k)
      n source terminal weight"
  shows "comma_round_weighted_prefix p p n
    (comma_shift_position k source) (comma_shift_position k terminal) weight"
  using prefix
proof (induction n arbitrary: source terminal weight)
  case "0"
  then show ?case by simp
next
  case (Suc n)
  obtain successor local_weight rest where move:
      "comma_weighted_step (((p+k) mod 924)) source =
        Comma_WNext successor local_weight"
    and tail: "comma_round_weighted_prefix (p+k) (p+k)
      n successor terminal rest"
    and weight_eq:
      "weight = comma_chart_weight_value (p+k) local_weight + rest"
    using Suc.prems
    by (simp only: comma_round_weighted_prefix_suc; blast)
  have shifted_move:
    "comma_weighted_step p (comma_shift_position k source) =
      Comma_WNext (comma_shift_position k successor)
        (comma_shift_weighted_chart_weight k local_weight)"
    using comma_weighted_step_shift_position[of p k source] move
    by simp
  have shifted_tail:
    "comma_round_weighted_prefix p p n
      (comma_shift_position k successor) (comma_shift_position k terminal) rest"
    by (rule Suc.IH[OF tail])
  have shifted_weight:
    "comma_chart_weight_value p
        (comma_shift_weighted_chart_weight k local_weight) =
      comma_chart_weight_value (p+k) local_weight"
    by (rule comma_shift_weighted_chart_weight_value)
  show ?case
    using shifted_move shifted_tail weight_eq shifted_weight
    by (simp only: comma_round_weighted_prefix_suc; blast)
qed

lemma comma_indexed_trace_shift_position_at:
  assumes index: "q=p+k"
    and trace: "comma_indexed_trace q position rows outcome terminal"
  shows "comma_indexed_trace p (comma_shift_position k position) rows
    (comma_shift_weighted_outcome k outcome) (comma_shift_position k terminal)"
  using trace index
proof (induction arbitrary: p k rule: comma_indexed_trace.induct)
  case (fork q position a delta)
  have phase: "((p mod 924+k) mod 924) = q mod 924"
    using fork.prems(1) by (simp add: mod_add_left_eq)
  have shifted_move:
    "comma_weighted_step (p mod 924) (comma_shift_position k position) =
      Comma_WFork (comma_shift_position k position) a (delta+k)"
    using comma_weighted_step_shift_position[of "p mod 924" k position]
      fork.hyps phase by simp
  show ?case
    by (rule comma_indexed_trace.fork[OF shifted_move])
next
  case (landmine q position delta)
  have phase: "((p mod 924+k) mod 924) = q mod 924"
    using landmine.prems(1) by (simp add: mod_add_left_eq)
  have shifted_move:
    "comma_weighted_step (p mod 924) (comma_shift_position k position) =
      Comma_WLandmine (comma_shift_position k position) (delta+k)"
    using comma_weighted_step_shift_position[of "p mod 924" k position]
      landmine.hyps phase by simp
  show ?case
    by (rule comma_indexed_trace.landmine[OF shifted_move])
next
  case (advance q position successor weight rows outcome terminal)
  have phase: "((p mod 924+k) mod 924) = q mod 924"
    using advance.prems(1) by (simp add: mod_add_left_eq)
  have shifted_move:
    "comma_weighted_step (p mod 924) (comma_shift_position k position) =
      Comma_WNext (comma_shift_position k successor)
        (comma_shift_weighted_chart_weight k weight)"
    using comma_weighted_step_shift_position[of "p mod 924" k position]
      advance.hyps(1) phase by simp
  have tail:
    "comma_indexed_trace p (comma_shift_position k successor) rows
      (comma_shift_weighted_outcome k outcome) (comma_shift_position k terminal)"
    using advance.IH[OF advance.prems(1) advance.hyps(2)] .
  have row:
    "(comma_chart_weight_value p (comma_shift_weighted_chart_weight k weight),
      int (comma_chart_value p (comma_shift_position k successor)) -
        int (comma_chart_value p (comma_shift_position k position))) =
     (comma_chart_weight_value (p+k) weight,
      int (comma_chart_value (p+k) successor) -
        int (comma_chart_value (p+k) position))"
    by (simp only: comma_shift_weighted_chart_weight_value
      comma_chart_value_shift_position)
  have shifted_trace:
    "comma_indexed_trace p (comma_shift_position k position)
      ((comma_chart_weight_value p
          (comma_shift_weighted_chart_weight k weight),
        int (comma_chart_value p (comma_shift_position k successor)) -
          int (comma_chart_value p (comma_shift_position k position))) # rows)
      (comma_shift_weighted_outcome k outcome)
      (comma_shift_position k terminal)"
    by (rule comma_indexed_trace.advance[OF shifted_move tail])
  show ?case using shifted_trace row
    by (simp only: row comma_shift_weighted_outcome.simps)
qed

lemma comma_indexed_trace_shift_position:
  assumes trace:
    "comma_indexed_trace (p+k) position rows outcome terminal"
  shows "comma_indexed_trace p (comma_shift_position k position) rows
    (comma_shift_weighted_outcome k outcome) (comma_shift_position k terminal)"
  by (rule comma_indexed_trace_shift_position_at[OF refl trace])

lemma comma_round_weighted_prefix_indexed_trace_continue:
  assumes phase: "r mod 924 = p mod 924"
    and prefix: "comma_round_weighted_prefix p r n source middle weight"
    and next: "comma_weighted_step (p mod 924) middle =
      Comma_WNext target local_weight"
    and tail: "comma_indexed_trace p target rows outcome terminal"
  shows "\<exists>all_rows. comma_indexed_trace p source all_rows outcome terminal \<and>
    sum_list (map fst all_rows) =
      weight + comma_chart_weight_value p local_weight +
        sum_list (map fst rows) \<and>
    (\<exists>prefix_rows.
      all_rows = prefix_rows @
        (comma_chart_weight_value p local_weight,
          int (comma_chart_value p target) -
            int (comma_chart_value p middle)) # rows \<and>
      sum_list (map fst prefix_rows) = weight)"
  using prefix
proof (induction n arbitrary: source weight)
  case "0"
  then have source: "source=middle" and zero: "weight=0" by simp_all
  have move_source:
    "comma_weighted_step (p mod 924) source =
      Comma_WNext target local_weight"
    using source next by simp
  have trace: "comma_indexed_trace p source
      [(comma_chart_weight_value p local_weight,
        int (comma_chart_value p target) -
          int (comma_chart_value p middle))] outcome terminal"
    by (rule comma_indexed_trace.advance[OF move_source tail])
  show ?case
  proof (intro exI[where x="[(comma_chart_weight_value p local_weight,
        int (comma_chart_value p target) - int (comma_chart_value p middle))] @ rows"]
      conjI)
    show "comma_indexed_trace p source
        ([(comma_chart_weight_value p local_weight,
          int (comma_chart_value p target) -
            int (comma_chart_value p middle))] @ rows) outcome terminal"
      using trace by simp
    show "sum_list (map fst
        ([(comma_chart_weight_value p local_weight,
          int (comma_chart_value p target) -
            int (comma_chart_value p middle))] @ rows)) =
        weight + comma_chart_weight_value p local_weight +
          sum_list (map fst rows)"
      using zero by simp
    show "\<exists>prefix_rows.
        [(comma_chart_weight_value p local_weight,
          int (comma_chart_value p target) -
            int (comma_chart_value p middle))] @ rows =
          prefix_rows @
            (comma_chart_weight_value p local_weight,
              int (comma_chart_value p target) -
                int (comma_chart_value p middle)) # rows \<and>
        sum_list (map fst prefix_rows) = weight"
      using zero by (intro exI[where x="[]"]) simp
  qed
next
  case (Suc n)
  obtain successor first_weight rest where move:
      "comma_weighted_step (r mod 924) source =
        Comma_WNext successor first_weight"
    and suffix: "comma_round_weighted_prefix p r n successor middle rest"
    and amount:
      "weight = comma_chart_weight_value p first_weight + rest"
    using Suc.prems by (simp only: comma_round_weighted_prefix_suc; blast)
  have move_p:
    "comma_weighted_step (p mod 924) source =
      Comma_WNext successor first_weight"
    using move phase by simp
  obtain prefix_rows where suffix_trace:
      "comma_indexed_trace p successor
        (prefix_rows @
          (comma_chart_weight_value p local_weight,
            int (comma_chart_value p target) -
              int (comma_chart_value p middle)) # rows)
        outcome terminal"
    and suffix_weight:
      "sum_list (map fst prefix_rows) = rest"
    using Suc.IH[OF suffix] by blast
  let ?connecting_row =
    "(comma_chart_weight_value p local_weight,
      int (comma_chart_value p target) -
        int (comma_chart_value p middle))"
  let ?prefix_rows =
    "(comma_chart_weight_value p first_weight,
      int (comma_chart_value p successor) -
        int (comma_chart_value p source)) # prefix_rows"
  let ?all_rows = "?prefix_rows @ ?connecting_row # rows"
  have trace:
    "comma_indexed_trace p source ?all_rows outcome terminal"
  proof -
    have "comma_indexed_trace p source
        ((comma_chart_weight_value p first_weight,
          int (comma_chart_value p successor) -
            int (comma_chart_value p source)) #
          (prefix_rows @ ?connecting_row # rows)) outcome terminal"
      by (rule comma_indexed_trace.advance[OF move_p suffix_trace])
    then show ?thesis by simp
  qed
  have prefix_weight: "sum_list (map fst ?prefix_rows) = weight"
    using amount suffix_weight by simp
  have weight:
    "sum_list (map fst ?all_rows) =
      weight + comma_chart_weight_value p local_weight +
        sum_list (map fst rows)"
    using prefix_weight by simp
  show ?case using trace weight prefix_weight by blast
qed

lemma comma_finite_terminal_weighted_shape:
  assumes step: "comma_finite_step residue position = Comma_Fork a delta"
  shows "comma_weighted_step residue position =
      Comma_WFork position a delta"
proof -
  obtain terminal where weighted:
      "comma_weighted_step residue position = Comma_WFork terminal a delta"
    using step
    by (cases "comma_weighted_step residue position")
      (auto simp: comma_finite_step_def simp del: comma_weighted_step_def)
  have "terminal=position"
    by (rule comma_weighted_terminal_is_source[where a=a and delta=delta])
      (rule disjI1[OF weighted])
  then show ?thesis using weighted by simp
qed

lemma comma_finite_landmine_weighted_shape:
  assumes step: "comma_finite_step residue position = Comma_Landmine delta"
  shows "comma_weighted_step residue position =
      Comma_WLandmine position delta"
proof -
  obtain terminal where weighted:
      "comma_weighted_step residue position = Comma_WLandmine terminal delta"
    using step
    by (cases "comma_weighted_step residue position")
      (auto simp: comma_finite_step_def simp del: comma_weighted_step_def)
  have "terminal=position"
    by (rule comma_weighted_terminal_is_source[where a=0 and delta=delta])
      (rule disjI2[OF weighted])
  then show ?thesis using weighted by simp
qed

lemma comma_indexed_trace_terminal_weighted_shape:
  assumes trace: "comma_indexed_trace p source rows outcome terminal"
  shows "(\<exists>a delta. outcome=Comma_Fork_At a delta \<and>
      comma_weighted_step (p mod 924) terminal =
        Comma_WFork terminal a delta) \<or>
    (\<exists>delta. outcome=Comma_Landmine_At delta \<and>
      comma_weighted_step (p mod 924) terminal =
        Comma_WLandmine terminal delta)"
  using trace
proof (induction rule: comma_indexed_trace.induct)
  case (fork p source a delta)
  then show ?case by blast
next
  case (landmine p source delta)
  then show ?case by blast
next
  case (advance p source successor weight rows outcome terminal)
  then show ?case by blast
qed

lemma comma_round_weighted_prefix_indexed_trace_fork:
  assumes phase: "r mod 924 = p mod 924"
    and prefix: "comma_round_weighted_prefix p r n source terminal weight"
    and stop: "comma_weighted_step (p mod 924) terminal =
      Comma_WFork terminal a delta"
  shows "\<exists>rows. comma_indexed_trace p source rows
      (Comma_Fork_At a delta) terminal \<and>
    sum_list (map fst rows) = weight"
proof -
  have either:
    "(\<exists>rows. comma_indexed_trace p source rows
        (Comma_Fork_At a delta) terminal \<and>
        sum_list (map fst rows)=weight) \<or>
     (\<exists>rows. comma_indexed_trace p source rows
        (Comma_Landmine_At d) terminal \<and>
        sum_list (map fst rows)=weight)"
    using comma_round_weighted_prefix_indexed_trace[OF phase prefix]
      stop by blast
  show ?thesis
  proof (rule disjE[OF either])
    assume good: "\<exists>rows. comma_indexed_trace p source rows
        (Comma_Fork_At a delta) terminal \<and>
        sum_list (map fst rows)=weight"
    then show ?thesis by blast
  next
    assume bad: "\<exists>rows. comma_indexed_trace p source rows
        (Comma_Landmine_At d) terminal \<and>
        sum_list (map fst rows)=weight"
    then obtain rows where trace:
        "comma_indexed_trace p source rows (Comma_Landmine_At d) terminal"
      by blast
    obtain d' where wrong:
        "comma_weighted_step (p mod 924) terminal =
          Comma_WLandmine terminal d'"
      using comma_indexed_trace_terminal_weighted_shape[OF trace] by blast
    show False using stop wrong by simp
  qed
qed

lemma comma_round_weighted_prefix_indexed_trace_landmine:
  assumes phase: "r mod 924 = p mod 924"
    and prefix: "comma_round_weighted_prefix p r n source terminal weight"
    and stop: "comma_weighted_step (p mod 924) terminal =
      Comma_WLandmine terminal delta"
  shows "\<exists>rows. comma_indexed_trace p source rows
      (Comma_Landmine_At delta) terminal \<and>
    sum_list (map fst rows) = weight"
proof -
  have either:
    "(\<exists>rows. comma_indexed_trace p source rows
        (Comma_Fork_At a d) terminal \<and>
        sum_list (map fst rows)=weight) \<or>
     (\<exists>rows. comma_indexed_trace p source rows
        (Comma_Landmine_At delta) terminal \<and>
        sum_list (map fst rows)=weight)"
    using comma_round_weighted_prefix_indexed_trace[OF phase prefix]
      stop by blast
  show ?thesis
  proof (rule disjE[OF either])
    assume bad: "\<exists>rows. comma_indexed_trace p source rows
        (Comma_Fork_At a d) terminal \<and>
        sum_list (map fst rows)=weight"
    then obtain rows where trace:
        "comma_indexed_trace p source rows (Comma_Fork_At a d) terminal"
      by blast
    obtain a' where wrong:
        "comma_weighted_step (p mod 924) terminal =
          Comma_WFork terminal a' d"
      using comma_indexed_trace_terminal_weighted_shape[OF trace] by blast
    show False using stop wrong by simp
  next
    assume good: "\<exists>rows. comma_indexed_trace p source rows
        (Comma_Landmine_At delta) terminal \<and>
        sum_list (map fst rows)=weight"
    then show ?thesis by blast
  qed
qed

lemma comma_decade_continue_close_details:
  assumes admitted: "comma_decade_admitted (Comma_Decade r x)"
    and control: "comma_decade_control (Comma_Decade r x) =
      Comma_Decade_Continue q"
  obtains n terminal y where
    "comma_round_close r (Comma_Entry 1 0 x) =
      (n,terminal,Comma_Round_Cross (Comma_Entry 1 1 y))"
    "y \<le> 90"
    "q=Comma_Decade ((r+1) mod 924) y"
proof -
  obtain n terminal event where close:
      "comma_round_close r (Comma_Entry 1 0 x)=(n,terminal,event)"
    by (cases "comma_round_close r (Comma_Entry 1 0 x)") auto
  have valid: "comma_round_admitted (Comma_Entry 1 0 x)"
    using admitted by simp
  have decoded: "comma_decade_decode r event = Comma_Decade_Continue q"
    using control by (simp only: comma_decade_control.simps close prod.case)
  obtain target where event:
      "event=Comma_Round_Cross target"
    using decoded by (cases event)
      (auto split: comma_finite_position.splits if_splits)
  obtain y where y_bound: "y\<le>90"
    and target: "target=Comma_Entry 1
        (Suc (comma_round_delta (Comma_Entry 1 0 x))) y"
    using comma_round_close_crossing_phase[OF close[unfolded event] valid]
    by blast
  have target': "target=Comma_Entry 1 1 y"
    using target by simp
  have q_eq: "q=Comma_Decade ((r+1) mod 924) y"
    using decoded event target' by simp
  have close': "comma_round_close r (Comma_Entry 1 0 x) =
      (n,terminal,Comma_Round_Cross (Comma_Entry 1 1 y))"
    using close event target' by simp
  show thesis using close' y_bound q_eq by (rule that)
qed

text \<open>The checked B32 summary is now lifted to the exact ordered weighted
chart trace consumed by selection.  Crossing summaries are composed at the
next exponent and shifted back to the original chart; no rank/fuel evaluator
or sampled exponent is involved.  This is the semantic trace producer.  The
separate Python SectorFragment serialization still needs its own fieldwise
refinement theorem.\<close>

theorem comma_decade_summary_weighted_indexed_trace:
  assumes summary: "comma_decade_exact_summary s h terminal"
    and admitted: "comma_decade_admitted s"
    and exponent: "5\<le>p"
    and binding: "s=Comma_Decade (p mod 924) x"
  shows "\<exists>rows final_position. comma_indexed_trace p
      (Comma_Entry 1 0 x) rows
      (comma_summary_outcome h terminal)
      (comma_shift_position h final_position)"
  using summary admitted exponent binding
proof (induction arbitrary: p x rule: comma_decade_exact_summary.induct)
  case (fork s a)
  have state: "s=Comma_Decade (p mod 924) x"
    using fork.prems(3) by simp
  have admitted_state: "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    using fork.prems(1) state by simp
  have control:
    "comma_decade_control (Comma_Decade (p mod 924) x) =
      Comma_Decade_Fork a 0"
    using fork.hyps state by simp
  obtain n terminal_position event where close:
      "comma_round_close (p mod 924) (Comma_Entry 1 0 x) =
        (n,terminal_position,event)"
    by (cases "comma_round_close (p mod 924) (Comma_Entry 1 0 x)") auto
  have decoded: "comma_decade_decode (p mod 924) event =
      Comma_Decade_Fork a 0"
    using control by (simp only: comma_decade_control.simps close prod.case)
  have event: "event=Comma_Round_Fork a 0"
    using decoded by (cases event)
      (auto split: comma_finite_position.splits if_splits)
  have finite:
    "comma_finite_step ((p mod 924) mod 924) terminal_position =
      Comma_Fork a 0"
    using comma_round_close_refines_trace[OF close] event by simp
  have prefix_exists:
    "\<exists>w. comma_round_weighted_prefix p (p mod 924) n
      (Comma_Entry 1 0 x) terminal_position w"
    using comma_round_close_has_weighted_prefix[OF close] .
  then obtain w where prefix:
      "comma_round_weighted_prefix p (p mod 924) n
        (Comma_Entry 1 0 x) terminal_position w" by blast
  have stop:
    "comma_weighted_step (p mod 924) terminal_position =
      Comma_WFork terminal_position a 0"
    using comma_finite_terminal_weighted_shape[OF finite] by simp
  have phase: "(p mod 924) mod 924=p mod 924" by simp
  obtain rows where trace:
      "comma_indexed_trace p (Comma_Entry 1 0 x) rows
        (Comma_Fork_At a 0) terminal_position"
    using comma_round_weighted_prefix_indexed_trace_fork
      [OF phase prefix stop] by blast
  show ?case using trace by simp
next
  case (landmine s)
  have state: "s=Comma_Decade (p mod 924) x"
    using landmine.prems(3) by simp
  have control:
    "comma_decade_control (Comma_Decade (p mod 924) x) =
      Comma_Decade_Landmine 0"
    using landmine.hyps state by simp
  obtain n terminal_position event where close:
      "comma_round_close (p mod 924) (Comma_Entry 1 0 x) =
        (n,terminal_position,event)"
    by (cases "comma_round_close (p mod 924) (Comma_Entry 1 0 x)") auto
  have decoded: "comma_decade_decode (p mod 924) event =
      Comma_Decade_Landmine 0"
    using control by (simp only: comma_decade_control.simps close prod.case)
  have event: "event=Comma_Round_Landmine 0"
    using decoded by (cases event)
      (auto split: comma_finite_position.splits if_splits)
  have finite:
    "comma_finite_step ((p mod 924) mod 924) terminal_position =
      Comma_Landmine 0"
    using comma_round_close_refines_trace[OF close] event by simp
  obtain w where prefix:
      "comma_round_weighted_prefix p (p mod 924) n
        (Comma_Entry 1 0 x) terminal_position w"
    using comma_round_close_has_weighted_prefix[OF close] by blast
  have stop:
    "comma_weighted_step (p mod 924) terminal_position =
      Comma_WLandmine terminal_position 0"
    using comma_finite_landmine_weighted_shape[OF finite] by simp
  have phase: "(p mod 924) mod 924=p mod 924" by simp
  obtain rows where trace:
      "comma_indexed_trace p (Comma_Entry 1 0 x) rows
        (Comma_Landmine_At 0) terminal_position"
    using comma_round_weighted_prefix_indexed_trace_landmine
      [OF phase prefix stop] by blast
  show ?case using trace by simp
next
  case (crossing s q h terminal)
  have state: "s=Comma_Decade (p mod 924) x"
    using crossing.prems(3) by simp
  have admitted_state:
    "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    using crossing.prems(1) state by simp
  have control:
    "comma_decade_control (Comma_Decade (p mod 924) x) =
      Comma_Decade_Continue q"
    using crossing.hyps(1) state by simp
  have child_admitted: "comma_decade_admitted q"
    using comma_decade_control_closed[OF admitted_state control] by auto
  obtain n terminal_position y where close:
      "comma_round_close (p mod 924) (Comma_Entry 1 0 x) =
        (n,terminal_position,
          Comma_Round_Cross (Comma_Entry 1 1 y))"
    and y_bound: "y\<le>90"
    and child_phase:
      "q=Comma_Decade (((p mod 924)+1) mod 924) y"
    using comma_decade_continue_close_details
      [OF admitted_state control] by blast
  have phase_next: "((p mod 924+1) mod 924)=(Suc p mod 924)"
    by (simp add: mod_add_left_eq)
  have child_binding: "q=Comma_Decade (Suc p mod 924) y"
    using child_phase phase_next by simp
  have next_exponent: "5\<le>Suc p" using crossing.prems(2) by simp
  obtain tail_rows final_position where tail:
      "comma_indexed_trace (Suc p) (Comma_Entry 1 0 y) tail_rows
        (comma_summary_outcome h terminal)
        (comma_shift_position h final_position)"
    using crossing.IH[OF child_admitted next_exponent child_binding]
    by blast
  have next_step:
    "comma_finite_step ((p mod 924) mod 924) terminal_position =
      Comma_Next (Comma_Entry 1 1 y)"
    and crossing_step:
      "comma_round_crossing terminal_position (Comma_Entry 1 1 y)"
    using comma_round_close_refines_trace[OF close] by simp_all
  have weighted_next:
    "comma_weighted_step (p mod 924) terminal_position =
      Comma_WNext (Comma_Entry 1 1 y) (Comma_Chart_Weight 0 0 1 1)"
  proof -
    have finite_next:
      "comma_finite_step (p mod 924) terminal_position =
        Comma_Next (Comma_Entry 1 1 y)"
      using next_step by simp
    show ?thesis
      by (rule comma_round_crossing_weight_unit[OF finite_next crossing_step])
  qed
  have shifted_tail:
    "comma_indexed_trace p (Comma_Entry 1 1 y) tail_rows
      (comma_shift_weighted_outcome 1 (comma_summary_outcome h terminal))
      (comma_shift_position 1 (comma_shift_position h final_position))"
    using comma_indexed_trace_shift_position[of p 1
      "Comma_Entry 1 0 y" tail_rows
      "comma_summary_outcome h terminal" final_position] tail by simp
  obtain local_weight where prefix:
      "comma_round_weighted_prefix p (p mod 924) n
        (Comma_Entry 1 0 x) terminal_position local_weight"
    using comma_round_close_has_weighted_prefix[OF close] by blast
  have phase: "(p mod 924) mod 924=p mod 924" by simp
  obtain prefix_rows where whole_prefix:
      "comma_indexed_trace p (Comma_Entry 1 0 x)
        (prefix_rows @
          (comma_chart_weight_value p (Comma_Chart_Weight 0 0 1 1),
            int (comma_chart_value p (Comma_Entry 1 1 y)) -
              int (comma_chart_value p terminal_position)) # tail_rows)
        (comma_shift_weighted_outcome 1 (comma_summary_outcome h terminal))
        (comma_shift_position 1 (comma_shift_position h final_position))"
    and prefix_weight: "sum_list (map fst prefix_rows) = local_weight"
    using comma_round_weighted_prefix_indexed_trace_continue
      [OF phase prefix weighted_next shifted_tail] by blast
  let ?rows = prefix_rows @
    (comma_chart_weight_value p (Comma_Chart_Weight 0 0 1 1),
      int (comma_chart_value p (Comma_Entry 1 1 y)) -
        int (comma_chart_value p terminal_position)) # tail_rows
  have whole:
    "comma_indexed_trace p (Comma_Entry 1 0 x) ?rows
      (comma_shift_weighted_outcome 1 (comma_summary_outcome h terminal))
      (comma_shift_position 1 (comma_shift_position h final_position))"
    using whole_prefix by simp
  have whole_weight:
    "sum_list (map fst ?rows) = local_weight +
      comma_chart_weight_value p (Comma_Chart_Weight 0 0 1 1) +
      sum_list (map fst tail_rows)"
    using prefix_weight by simp
  have outcome_shift:
    "comma_shift_weighted_outcome 1 (comma_summary_outcome h terminal) =
      comma_summary_outcome (Suc h) terminal"
    by (cases terminal) (simp_all add: comma_summary_outcome.simps)
  have position_shift:
    "comma_shift_position 1 (comma_shift_position h final_position) =
      comma_shift_position (Suc h) final_position"
    by (cases final_position) (simp_all add: add.assoc)
  show ?case using whole outcome_shift position_shift by simp
qed

ML \<open>
  val _ = if null (Thm_Deps.all_oracles
    @{thms comma_shift_weighted_chart_weight_value
      comma_chart_value_shift_position comma_weighted_step_shift_position
      comma_round_weighted_prefix_indexed_trace
      comma_round_weighted_prefix_indexed_trace_continue
      comma_finite_terminal_weighted_shape
      comma_finite_landmine_weighted_shape
      comma_indexed_trace_terminal_weighted_shape
      comma_round_weighted_prefix_indexed_trace_fork
      comma_round_weighted_prefix_indexed_trace_landmine
      comma_decade_continue_close_details
      comma_decade_summary_weighted_indexed_trace
      comma_round_weighted_prefix_shift_position
      comma_indexed_trace_shift_position})
    then () else error "Semantic weighted selection depends on an oracle";
\<close>

end
