theory Comma_Semantic_Producer_Refinement
  imports Comma_Semantic_Fragment_Refinement
begin

text \<open>This theory specifies the indexed producer's record writer over
the canonical first-terminal weighted trace.  Entry records carry reduced
affine cycle counts; successful Near edges carry literal increments.  A
pending Near run is flushed before an Entry record or a Near-to-Entry edge,
and once at the first Fork/Landmine.  There is no fuel result or artificial
total-step cutoff in this relation.\<close>

definition comma_python_constant_affine :: "nat \<Rightarrow> comma_python_affine_weight" where
  "comma_python_constant_affine n =
    comma_python_affine_normalize 0 (int n) 1"

definition comma_python_fragment_weight_affine ::
  "comma_python_sector_fragment \<Rightarrow> comma_python_affine_weight" where
  "comma_python_fragment_weight_affine g =
    comma_python_affine_add
      (comma_python_affine_times (comma_python_fragment_period g)
        (comma_python_fragment_complete_cycles g))
      (comma_python_constant_affine
        (comma_python_fragment_literal_steps g))"

definition comma_python_fragment_displacement_affine ::
  "comma_python_sector_fragment \<Rightarrow> comma_python_affine_weight" where
  "comma_python_fragment_displacement_affine g =
    comma_python_affine_add
      (comma_python_affine_times
        (comma_python_fragment_displacement g)
        (comma_python_fragment_complete_cycles g))
      (comma_python_constant_affine
        (comma_python_fragment_literal_increment g))"

lemma comma_python_literal_fragment_weight_affine_unit:
  "comma_python_fragment_weight_affine
      (comma_python_literal_fragment f digit 1 increment) =
    comma_python_chart_affine_weight 0 (Comma_Chart_Weight 0 0 1 1)"
  by (simp add: comma_python_fragment_weight_affine_def
      comma_python_constant_affine_def comma_python_affine_times_def
      comma_python_affine_add_def comma_python_affine_normalize_def
      comma_python_affine_zero_def comma_python_literal_fragment_def Let_def)

fun comma_python_affine_prefix_scan ::
  "comma_python_affine_weight list \<Rightarrow>
    comma_python_affine_weight \<Rightarrow> comma_python_affine_weight list" where
  "comma_python_affine_prefix_scan [] z = [z]"
| "comma_python_affine_prefix_scan (x # xs) z =
    z # comma_python_affine_prefix_scan xs
      (comma_python_affine_add z x)"

record comma_python_affine_prefix_arrays =
  comma_python_published_fragments :: "comma_python_sector_fragment list"
  comma_python_published_weights :: "comma_python_affine_weight list"
  comma_python_published_displacements :: "comma_python_affine_weight list"

definition comma_python_publish_fragments ::
  "comma_python_sector_fragment list \<Rightarrow>
    comma_python_affine_prefix_arrays" where
  "comma_python_publish_fragments fragments =
    \<lparr>comma_python_published_fragments = fragments,
     comma_python_published_weights = comma_python_affine_prefix_scan
       (map comma_python_fragment_weight_affine fragments)
       comma_python_affine_zero,
     comma_python_published_displacements = comma_python_affine_prefix_scan
       (map comma_python_fragment_displacement_affine fragments)
       comma_python_affine_zero\<rparr>"

lemma comma_python_affine_prefix_scan_length:
  "length (comma_python_affine_prefix_scan xs z) = Suc (length xs)"
  by (induction xs arbitrary: z) simp_all

lemma comma_python_affine_prefix_scan_nth:
  assumes index: "i \<le> length xs"
  shows "comma_python_affine_prefix_scan xs z ! i =
    foldl comma_python_affine_add z (take i xs)"
  using index
proof (induction xs arbitrary: i z)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases i)
    case "0"
    then show ?thesis by simp
  next
    case (Suc j)
    have j: "j \<le> length xs" using Cons.prems Suc by simp
    show ?thesis using Cons.IH[OF j, of "comma_python_affine_add z x"] Suc
      by (simp add: foldl_Cons)
  qed
qed

lemma comma_python_publish_fragments_lengths:
  "length (comma_python_published_weights
      (comma_python_publish_fragments fragments)) = Suc (length fragments)"
  "length (comma_python_published_displacements
      (comma_python_publish_fragments fragments)) = Suc (length fragments)"
  by (simp_all add: comma_python_publish_fragments_def
      comma_python_affine_prefix_scan_length)

lemma comma_python_publish_fragments_nth:
  assumes index: "i \<le> length fragments"
  shows "comma_python_published_weights
      (comma_python_publish_fragments fragments) ! i =
    foldl comma_python_affine_add comma_python_affine_zero
      (map comma_python_fragment_weight_affine (take i fragments))"
    "comma_python_published_displacements
      (comma_python_publish_fragments fragments) ! i =
    foldl comma_python_affine_add comma_python_affine_zero
      (map comma_python_fragment_displacement_affine (take i fragments))"
  using comma_python_affine_prefix_scan_nth[OF index]
  by (simp_all add: comma_python_publish_fragments_def)

definition comma_python_flush_near ::
  "comma_python_sector_fragment option \<Rightarrow>
    comma_python_sector_fragment list" where
  "comma_python_flush_near pending =
    (case pending of None \<Rightarrow> [] | Some fragment \<Rightarrow> [fragment])"

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
          (comma_finite_headroom f (p mod 924) delta offset)
    | Comma_Near f delta headroom \<Rightarrow>
        (\\<exists>increment. comma_chart_value p successor =
            comma_chart_value p source + increment \<and>
          fragment = comma_python_literal_fragment f
            (comma_chart_value p source mod 10) 1 increment)) \<and>
    comma_python_fragment_weight_at_scale fragment (10 ^ p) =
      int (comma_chart_weight_value p weight) \<and>
    comma_python_fragment_displacement_at_scale fragment (10 ^ p) =
      int (comma_chart_value p successor) - int (comma_chart_value p source)"

text \<open>The relation above makes the local record payload explicit: a
Near increment is a natural number witnessed by the endpoint equation, so
the producer refinement does not cast a possibly negative displacement to
`nat`.\<close>

lemma comma_python_entry_record_matches:
  fixes f p delta offset h :: nat
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
  have endpoint:
    "comma_chart_value p successor =
      comma_chart_value p source + c * P"
    using comma_entry_chart_exact_literal_path(3)[OF f exponent offset,
      of delta]
    by (simp add: h_def P_def L_def c_def source_def successor_def)
  have row_displacement:
    "comma_python_fragment_displacement_at_scale fragment (10 ^ p) =
      int (comma_chart_value p successor) - int (comma_chart_value p source)"
    using fields(6) endpoint by (simp add: fragment_def P_def)
  show ?thesis
    using fields(1,5) row_displacement
    by (simp add: comma_python_fragment_record_matches_def source_def
        successor_def weight_def fragment_def h_def P_def L_def)
qed

lemma comma_python_near_record_matches:
  fixes f p delta headroom :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and valid_headroom: "1 \<le> headroom" "headroom \<le> 540"
    and step: "comma_weighted_step (p mod 924)
      (Comma_Near f delta headroom) = Comma_WNext successor weight"
  obtains increment where
    "comma_chart_value p successor =
      comma_chart_value p (Comma_Near f delta headroom) + increment"
    "comma_python_fragment_record_matches p (Comma_Near f delta headroom)
      successor weight (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment)"
proof -
  have finite_next:
    "comma_finite_step (p mod 924) (Comma_Near f delta headroom) =
      Comma_Next successor"
    using step by (simp add: comma_finite_step_def)
  note near_edge = comma_near_chart_next_literal[OF f exponent
      valid_headroom finite_next]
  have child:
    "comma_child (comma_chart_value p (Comma_Near f delta headroom))
      (comma_chart_value p successor)"
    using near_edge(1)
    by (cases rule: comma_literal_path.cases) auto
  then obtain e n where target_sector:
      "comma_sector e n (comma_chart_value p successor)"
    and increment_eq:
      "comma_chart_value p successor =
        comma_chart_value p (Comma_Near f delta headroom) +
          10 * (comma_chart_value p (Comma_Near f delta headroom) mod 10) + e"
    by (auto simp: comma_child_def)
  let ?increment =
    "10 * (comma_chart_value p (Comma_Near f delta headroom) mod 10) + e"
  have weight_unit: "comma_chart_weight_value p weight = 1"
    using near_edge(2) step by (simp add: comma_finite_step_def)
  have weight_at_scale:
    "comma_python_fragment_weight_at_scale
       (comma_python_literal_fragment f
         (comma_chart_value p (Comma_Near f delta headroom) mod 10)
         1 ?increment) (10 ^ p) = int (comma_chart_weight_value p weight)"
    using weight_unit
    by (simp add: comma_python_fragment_weight_at_scale_def
        comma_python_literal_fragment_def comma_python_affine_zero_def
        comma_python_affine_normalize_def Let_def
        comma_python_affine_evaluate_def)
  have displacement:
    "comma_python_fragment_displacement_at_scale
       (comma_python_literal_fragment f
         (comma_chart_value p (Comma_Near f delta headroom) mod 10)
         1 ?increment) (10 ^ p) =
      int (comma_chart_value p successor) -
        int (comma_chart_value p (Comma_Near f delta headroom))"
    using increment_eq by (simp add: comma_python_fragment_displacement_at_scale_def
        comma_python_literal_fragment_def comma_python_affine_zero_def
        comma_python_affine_normalize_def Let_def
        comma_python_affine_evaluate_def)
  have record:
    "comma_python_fragment_record_matches p (Comma_Near f delta headroom)
      successor weight (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 ?increment)"
    using step increment_eq weight_at_scale displacement
    by (simp add: comma_python_fragment_record_matches_def)
  show thesis using record increment_eq by (rule that)
qed

lemma comma_python_near_internal_increment:
  fixes f p delta headroom next_headroom :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and valid_headroom: "1 \<le> headroom" "headroom \<le> 540"
    and step: "comma_weighted_step (p mod 924)
      (Comma_Near f delta headroom) =
        Comma_WNext (Comma_Near f delta next_headroom) weight"
  shows "comma_chart_value p (Comma_Near f delta next_headroom) =
      comma_chart_value p (Comma_Near f delta headroom) +
        comma_period_displacement f
          (comma_chart_value p (Comma_Near f delta headroom) mod 10) 1"
proof -
  let ?k = "comma_chart_value p (Comma_Near f delta headroom)"
  let ?n = "p + delta"
  let ?d = "(10 - headroom mod 10) mod 10"
  have finite_next:
    "comma_finite_step (p mod 924) (Comma_Near f delta headroom) =
      Comma_Next (Comma_Near f delta next_headroom)"
    using step by (simp add: comma_finite_step_def)
  have sector:
    "comma_sector f ?n ?k"
    using comma_near_chart_checked_sector[OF f exponent valid_headroom,
        of delta]
    by (simp add: comma_chart_value_def)
  have chart_sum: "?k + headroom = (f + 1) * 10 ^ ?n"
    using comma_sector_headroom[OF sector] .
  have n_positive: "0 < ?n" using exponent by simp
  have digit: "?k mod 10 = ?d"
    by (rule comma_near_chart_digit[OF chart_sum n_positive])
  have relation:
    "(f < 9 \<and> headroom > 10 * ?d + f + 1 \<and>
        next_headroom = headroom - (10 * ?d + f)) \<or>
     (f = 9 \<and> headroom > 10 * ?d + 9 \<and>
        next_headroom = headroom - (10 * ?d + 9))"
    using finite_next f
    by (auto simp: comma_near_control_formula Let_def
        split: if_splits)
  have value:
    "comma_chart_value p (Comma_Near f delta next_headroom) =
      ?k + 10 * ?d + f"
    using relation digit
    by (auto simp: comma_chart_value_def; arith)
  show ?thesis
    using value digit
    by (simp add: comma_period_displacement_def sum.lessThan_Suc
        comma_phase_digit_def)
qed

datatype comma_python_producer_event =
  Comma_Python_Advance comma_finite_position comma_finite_position
    comma_chart_weight

fun comma_python_event_row ::
  "nat \<Rightarrow> comma_python_producer_event \<Rightarrow> nat \<times> int" where
  "comma_python_event_row p (Comma_Python_Advance source successor weight) =
    (comma_chart_weight_value p weight,
      int (comma_chart_value p successor) - int (comma_chart_value p source))"

inductive comma_python_first_terminal_walk ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_producer_event list \<Rightarrow> comma_finite_outcome \<Rightarrow>
    comma_finite_position \<Rightarrow> bool" where
  fork: "comma_weighted_step (p mod 924) source =
      Comma_WFork source a delta \<Longrightarrow>
    comma_python_first_terminal_walk p source []
      (Comma_Fork_At a delta) source"
| landmine: "comma_weighted_step (p mod 924) source =
      Comma_WLandmine source delta \<Longrightarrow>
    comma_python_first_terminal_walk p source []
      (Comma_Landmine_At delta) source"
| advance: "comma_weighted_step (p mod 924) source =
      Comma_WNext successor weight \<Longrightarrow>
    comma_python_first_terminal_walk p successor events outcome terminal \<Longrightarrow>
    comma_python_first_terminal_walk p source
      (Comma_Python_Advance source successor weight # events)
      outcome terminal"

text \<open>This event walk is the source-position-bearing form of the indexed
trace. Its terminal constructors admit no successor event, so every walk
ends at the first terminal move. The exact-summary bridge below supplies the
finite walk without a fuel premise.\<close>

lemma comma_indexed_trace_to_python_first_terminal_walk:
  assumes trace: "comma_indexed_trace p source rows outcome terminal"
  obtains events where
    "comma_python_first_terminal_walk p source events outcome terminal"
    "rows = map (comma_python_event_row p) events"
  using trace
proof (induction rule: comma_indexed_trace.induct)
  case (fork p source a delta)
  then show thesis
    by (rule that[where events="[]"])
      (auto intro: comma_python_first_terminal_walk.fork)
next
  case (landmine p source delta)
  then show thesis
    by (rule that[where events="[]"])
      (auto intro: comma_python_first_terminal_walk.landmine)
next
  case (advance p source successor weight rows outcome terminal)
  then obtain events where walk:
      "comma_python_first_terminal_walk p successor events outcome terminal"
    and rows: "rows = map (comma_python_event_row p) events"
    by blast
  have walk': "comma_python_first_terminal_walk p source
      (Comma_Python_Advance source successor weight # events)
      outcome terminal"
    by (rule comma_python_first_terminal_walk.advance
      [OF advance.hyps(1) walk])
  show thesis
    by (rule advance.prems[where
        events="Comma_Python_Advance source successor weight # events"])
      (use rows in simp_all)
qed

lemma comma_python_first_terminal_walk_to_indexed_trace:
  assumes walk:
    "comma_python_first_terminal_walk p source events outcome terminal"
  shows "comma_indexed_trace p source
      (map (comma_python_event_row p) events) outcome terminal"
  using walk
proof (induction rule: comma_python_first_terminal_walk.induct)
  case (fork p source a delta)
  then show ?case by (rule comma_indexed_trace.fork)
next
  case (landmine p source delta)
  then show ?case by (rule comma_indexed_trace.landmine)
next
  case (advance p source successor weight events outcome terminal)
  then show ?case
    by (rule comma_indexed_trace.advance) simp_all
qed

theorem comma_decade_summary_python_first_terminal_walk:
  assumes summary: "comma_decade_exact_summary s h terminal"
    and admitted: "comma_decade_admitted s"
    and exponent: "5 \<le> p"
    and binding: "s=Comma_Decade (p mod 924) x"
  shows "\<exists>events final_position. comma_python_first_terminal_walk p
      (Comma_Entry 1 0 x) events (comma_summary_outcome h terminal)
      (comma_shift_position h final_position)"
proof -
  obtain rows final_position where trace:
      "comma_indexed_trace p (Comma_Entry 1 0 x) rows
        (comma_summary_outcome h terminal)
        (comma_shift_position h final_position)"
    using comma_decade_summary_weighted_indexed_trace
      [OF summary admitted exponent binding] by blast
  obtain events where walk:
      "comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
        (comma_summary_outcome h terminal)
        (comma_shift_position h final_position)"
    using comma_indexed_trace_to_python_first_terminal_walk[OF trace]
    by blast
  show ?thesis using walk by blast
qed

definition comma_python_pending_phase ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_sector_fragment option \<Rightarrow> bool" where
  "comma_python_pending_phase p position pending \<longleftrightarrow>
    (case pending of None \<Rightarrow> True
     | Some fragment \<Rightarrow>
        (case position of Comma_Near f delta headroom \<Rightarrow>
          comma_python_near_fragment_shape fragment \<and>
          comma_python_fragment_leading fragment = f \<and>
          comma_chart_value p position mod 10 =
            (comma_python_fragment_entering_digit fragment +
              comma_python_fragment_literal_steps fragment * f) mod 10
        | Comma_Entry f delta offset \<Rightarrow> False))"

inductive comma_python_writer_edge ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_chart_weight \<Rightarrow> comma_python_sector_fragment option \<Rightarrow>
    comma_python_sector_fragment list \<Rightarrow>
    comma_python_sector_fragment option \<Rightarrow> bool" where
  entry: "comma_python_fragment_record_matches p
      (Comma_Entry f delta offset) (Comma_Near f delta headroom) weight
      (comma_python_entry_sector_fragment f delta offset headroom) \<Longrightarrow>
    comma_python_writer_edge p (Comma_Entry f delta offset)
      (Comma_Near f delta headroom) weight pending
      (comma_python_flush_near pending @
        [comma_python_entry_sector_fragment f delta offset headroom]) None"
| near_start: "comma_python_fragment_record_matches p
      (Comma_Near f delta headroom) (Comma_Near f delta next_headroom) weight
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment) \<Longrightarrow>
    increment = comma_period_displacement f
      (comma_chart_value p (Comma_Near f delta headroom) mod 10) 1 \<Longrightarrow>
    comma_python_writer_edge p (Comma_Near f delta headroom)
      (Comma_Near f delta next_headroom) weight None []
      (Some (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment))"
| near_merge: "comma_python_near_fragments_compatible pending_fragment
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment) \<Longrightarrow>
    comma_python_fragment_record_matches p
      (Comma_Near f delta headroom) (Comma_Near f delta next_headroom) weight
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment) \<Longrightarrow>
    increment = comma_period_displacement f
      (comma_chart_value p (Comma_Near f delta headroom) mod 10) 1 \<Longrightarrow>
    comma_python_writer_edge p (Comma_Near f delta headroom)
      (Comma_Near f delta next_headroom) weight (Some pending_fragment) []
      (Some (comma_python_merge_near_fragments pending_fragment
        (comma_python_literal_fragment f
          (comma_chart_value p (Comma_Near f delta headroom) mod 10)
          1 increment)))"
| near_cross: "comma_python_fragment_record_matches p
      (Comma_Near f delta headroom) (Comma_Entry g next_delta offset) weight
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment) \<Longrightarrow>
    comma_python_writer_edge p (Comma_Near f delta headroom)
      (Comma_Entry g next_delta offset) weight pending
      (comma_python_flush_near pending @
        [comma_python_literal_fragment f
          (comma_chart_value p (Comma_Near f delta headroom) mod 10)
          1 increment]) None"

definition comma_python_fragment_list_weight_at_scale ::
  "comma_python_sector_fragment list \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_fragment_list_weight_at_scale fragments S =
    sum_list (map (\<lambda>g. comma_python_fragment_weight_at_scale g S) fragments)"

definition comma_python_fragment_list_displacement_at_scale ::
  "comma_python_sector_fragment list \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_fragment_list_displacement_at_scale fragments S =
    sum_list (map (\<lambda>g. comma_python_fragment_displacement_at_scale g S)
      fragments)"

definition comma_python_pending_weight_at_scale ::
  "comma_python_sector_fragment option \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_pending_weight_at_scale pending S =
    comma_python_fragment_list_weight_at_scale
      (comma_python_flush_near pending) S"

definition comma_python_pending_displacement_at_scale ::
  "comma_python_sector_fragment option \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_pending_displacement_at_scale pending S =
    comma_python_fragment_list_displacement_at_scale
      (comma_python_flush_near pending) S"

lemma comma_python_writer_edge_accounting:
  assumes edge: "comma_python_writer_edge p source successor weight
      pending emitted pending'"
  shows "comma_python_fragment_list_weight_at_scale emitted (10 ^ p) +
      comma_python_pending_weight_at_scale pending' (10 ^ p) =
    comma_python_pending_weight_at_scale pending (10 ^ p) +
      int (comma_chart_weight_value p weight)"
    and "comma_python_fragment_list_displacement_at_scale emitted (10 ^ p) +
      comma_python_pending_displacement_at_scale pending' (10 ^ p) =
    comma_python_pending_displacement_at_scale pending (10 ^ p) +
      int (comma_chart_value p successor) - int (comma_chart_value p source)"
  using edge
proof (induction rule: comma_python_writer_edge.induct)
  case (entry p f delta offset headroom weight pending)
  then show ?case
    by (simp add: comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def
        comma_python_flush_near_def
        comma_python_fragment_record_matches_def sum_list_append)
next
  case (near_start p f delta headroom next_headroom weight increment)
  then show ?case
    by (simp add: comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def
        comma_python_flush_near_def comma_python_fragment_record_matches_def
        comma_python_fragment_weight_at_scale_def
        comma_python_fragment_displacement_at_scale_def
        comma_python_literal_fragment_def sum_list_append)
next
  case near_merge
  then show ?case
    using comma_python_merge_near_preserves_weight
        [OF near_merge.hyps(1), of "10 ^ p"]
      comma_python_merge_near_preserves_displacement
        [OF near_merge.hyps(1), of "10 ^ p"]
    by (simp add: comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def
        comma_python_flush_near_def comma_python_fragment_record_matches_def
        comma_python_fragment_weight_at_scale_def
        comma_python_fragment_displacement_at_scale_def
        comma_python_literal_fragment_def sum_list_append)
next
  case (near_cross p f delta headroom g next_delta offset weight pending increment)
  then show ?case
    by (simp add: comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def
        comma_python_flush_near_def comma_python_fragment_record_matches_def
        comma_python_fragment_weight_at_scale_def
        comma_python_fragment_displacement_at_scale_def
        comma_python_literal_fragment_def sum_list_append)
qed

lemma comma_python_writer_edge_exists:
  assumes exponent: "5 \<le> p"
    and admitted: "comma_round_admitted source"
    and pending: "comma_python_pending_phase p source old_pending"
    and step: "comma_weighted_step (p mod 924) source =
      Comma_WNext successor weight"
  obtains emitted next_pending where
    "comma_python_writer_edge p source successor weight old_pending
      emitted next_pending"
    "comma_python_pending_phase p successor next_pending"
proof (cases source)
  case (Comma_Entry f delta offset)
  have f: "1 \<le> f" "f \<le> 9"
    and offset: "offset \<le> 98"
    using admitted by (simp_all add: Comma_Entry)
  let ?h = "comma_finite_headroom f (p mod 924) delta offset"
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?L = "comma_cycle_length f"
  have exact_step:
    "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta ?h)
        (Comma_Chart_Weight ?L delta (- int (?L * (offset + ?h))) ?P)"
    using comma_entry_chart_exact_literal_path(7)[OF f exponent offset,
      of delta]
    by (simp add: Comma_Entry)
  have target:
    "successor = Comma_Near f delta ?h"
    and weight:
    "weight = Comma_Chart_Weight ?L delta
      (- int (?L * (offset + ?h))) ?P"
    using step exact_step Comma_Entry by injection auto
  have record:
    "comma_python_fragment_record_matches p
      (Comma_Entry f delta offset) (Comma_Near f delta ?h)
      (Comma_Chart_Weight ?L delta (- int (?L * (offset + ?h))) ?P)
      (comma_python_entry_sector_fragment f delta offset ?h)"
    by (rule comma_python_entry_record_matches[OF f exponent offset])
  have edge: "comma_python_writer_edge p source successor weight old_pending
      (comma_python_flush_near old_pending @
        [comma_python_entry_sector_fragment f delta offset ?h]) None"
    using record target weight Comma_Entry
    by (intro comma_python_writer_edge.entry; simp)
  show thesis using edge Comma_Entry
    by (rule that[where emitted=
        "comma_python_flush_near old_pending @
          [comma_python_entry_sector_fragment f delta offset ?h]"
      and next_pending=None])
      (simp_all add: comma_python_pending_phase_def)
next
  case (Comma_Near f delta headroom)
  have f: "1 \<le> f" "f \<le> 9"
    and headroom: "1 \<le> headroom" "headroom \<le> 540"
    using admitted by (simp_all add: Comma_Near)
  have finite_next:
    "comma_finite_step (p mod 924) (Comma_Near f delta headroom) =
      Comma_Next successor"
    using step by (simp add: comma_finite_step_def)
  have step_shape:
    "successor = Comma_Near f delta next_headroom \<or>
     (\<exists>g next_delta offset.
       successor = Comma_Entry g next_delta offset)"
  proof (cases successor)
    case (Comma_Entry g next_delta offset)
    then show ?thesis by blast
  next
    case (Comma_Near g next_delta next_headroom)
    have eq: "g=f" "next_delta=delta"
      using finite_next Comma_Near f headroom
      by (auto simp: comma_finite_step_def comma_weighted_step_def
          comma_weighted_step_with_headroom_def Let_def split: if_splits)
    then show ?thesis using Comma_Near by blast
  qed
  obtain increment where endpoint:
      "comma_chart_value p successor =
        comma_chart_value p (Comma_Near f delta headroom) + increment"
    and record:
      "comma_python_fragment_record_matches p
        (Comma_Near f delta headroom) successor weight
        (comma_python_literal_fragment f
          (comma_chart_value p (Comma_Near f delta headroom) mod 10)
          1 increment)"
    using comma_python_near_record_matches[OF f exponent headroom step] .
  show thesis
  proof (cases "successor = Comma_Near f delta next_headroom")
    case True
    have internal:
      "comma_chart_value p (Comma_Near f delta next_headroom) =
        comma_chart_value p (Comma_Near f delta headroom) +
          comma_period_displacement f
            (comma_chart_value p (Comma_Near f delta headroom) mod 10) 1"
      using comma_python_near_internal_increment[OF f exponent headroom,
        of next_headroom weight] step True by simp
    have increment:
      "increment = comma_period_displacement f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10) 1"
      using endpoint internal True by arith
    let ?fragment = "comma_python_literal_fragment f
      (comma_chart_value p (Comma_Near f delta headroom) mod 10) 1 increment"
    have phase_step:
      "comma_chart_value p (Comma_Near f delta next_headroom) mod 10 =
        (comma_chart_value p (Comma_Near f delta headroom) mod 10 + f) mod 10"
      using internal increment
      by (simp add: comma_period_displacement_def sum.lessThan_Suc
          algebra_simps mod_add_eq)
    show ?thesis
    proof (cases old_pending)
      case None
      have edge:
        "comma_python_writer_edge p (Comma_Near f delta headroom)
          (Comma_Near f delta next_headroom) weight None [] (Some ?fragment)"
        using record increment True
        by (intro comma_python_writer_edge.near_start; simp)
      have bind:
        "comma_python_pending_phase p
          (Comma_Near f delta next_headroom) (Some ?fragment)"
        using phase_step f
        by (simp add: comma_python_pending_phase_def
            comma_python_literal_fragment_near_shape
            comma_python_literal_fragment_def
            comma_python_affine_zero_def comma_python_affine_normalize_def
            Let_def)
      show thesis using edge bind Comma_Near None
        by (rule that[where emitted="[]" and next_pending="Some ?fragment"])
          simp_all
    next
      case (Some previous)
      have old_binding:
        "comma_python_near_fragment_shape previous"
        and old_leading: "comma_python_fragment_leading previous = f"
        and old_phase:
          "comma_chart_value p (Comma_Near f delta headroom) mod 10 =
            (comma_python_fragment_entering_digit previous +
              comma_python_fragment_literal_steps previous * f) mod 10"
        using pending Some Comma_Near
        by (simp_all add: comma_python_pending_phase_def)
      have near_shape: "comma_python_near_fragment_shape ?fragment"
        using comma_python_literal_fragment_near_shape[OF f, of
          "comma_chart_value p (Comma_Near f delta headroom) mod 10" 1
          increment] .
      have compatible:
        "comma_python_near_fragments_compatible previous ?fragment"
        using old_binding old_leading old_phase near_shape
        by (simp add: comma_python_near_fragments_compatible_def
            comma_python_literal_fragment_def)
      have edge:
        "comma_python_writer_edge p (Comma_Near f delta headroom)
          (Comma_Near f delta next_headroom) weight (Some previous) []
          (Some (comma_python_merge_near_fragments previous ?fragment))"
        using compatible record increment True
        by (intro comma_python_writer_edge.near_merge; simp)
      have bind:
        "comma_python_pending_phase p
          (Comma_Near f delta next_headroom)
          (Some (comma_python_merge_near_fragments previous ?fragment))"
        using old_phase old_leading phase_step
          comma_python_merge_near_fields(1,2,3)[OF compatible]
          comma_python_merge_near_shape[OF compatible]
        by (simp add: comma_python_pending_phase_def
            comma_python_near_fragments_compatible_def
            comma_python_near_fragment_shape_def
            comma_python_merge_near_fragments_def)
      show thesis using edge bind Comma_Near Some
        by (rule that[where emitted="[]" and next_pending=
            "Some (comma_python_merge_near_fragments previous ?fragment)"])
          simp_all
    qed
  next
    case False
    then obtain g next_delta offset where
        target: "successor = Comma_Entry g next_delta offset"
      using step_shape by blast
    let ?fragment = "comma_python_literal_fragment f
      (comma_chart_value p (Comma_Near f delta headroom) mod 10) 1 increment"
    have edge:
      "comma_python_writer_edge p (Comma_Near f delta headroom)
        (Comma_Entry g next_delta offset) weight old_pending
        (comma_python_flush_near old_pending @ [?fragment]) None"
      using record target by (intro comma_python_writer_edge.near_cross; simp)
    show thesis using edge target Comma_Near
      by (rule that[where emitted=
          "comma_python_flush_near old_pending @ [?fragment]"
        and next_pending=None])
        (simp_all add: comma_python_pending_phase_def)
  qed
qed

inductive comma_python_writer_run ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_sector_fragment option \<Rightarrow>
    comma_python_producer_event list \<Rightarrow> comma_finite_outcome \<Rightarrow>
    comma_finite_position \<Rightarrow> comma_python_sector_fragment list \<Rightarrow> bool" where
  fork: "comma_weighted_step (p mod 924) source =
      Comma_WFork source a delta \<Longrightarrow>
    fragments = comma_python_flush_near pending \<Longrightarrow>
    comma_python_writer_run p source pending []
      (Comma_Fork_At a delta) source fragments"
| landmine: "comma_weighted_step (p mod 924) source =
      Comma_WLandmine source delta \<Longrightarrow>
    fragments = comma_python_flush_near pending \<Longrightarrow>
    comma_python_writer_run p source pending []
      (Comma_Landmine_At delta) source fragments"
| advance: "comma_weighted_step (p mod 924) source =
      Comma_WNext successor weight \<Longrightarrow>
    comma_python_writer_edge p source successor weight pending
      emitted pending' \<Longrightarrow>
    comma_python_writer_run p successor pending' events outcome terminal
      tail_fragments \<Longrightarrow>
    comma_python_writer_run p source pending
      (Comma_Python_Advance source successor weight # events)
      outcome terminal (emitted @ tail_fragments)"

theorem comma_python_first_terminal_walk_writer:
  fixes p source old_pending events outcome terminal
  assumes exponent: "5 \<le> p"
    and walk:
      "comma_python_first_terminal_walk p source events outcome terminal"
    and admitted: "comma_round_admitted source"
    and pending: "comma_python_pending_phase p source old_pending"
  shows "\<exists>fragments. comma_python_writer_run p source old_pending
      events outcome terminal fragments"
  using walk exponent admitted pending
proof (induction arbitrary: old_pending
    rule: comma_python_first_terminal_walk.induct)
  case (fork p source a delta)
  have run:
    "comma_python_writer_run p source old_pending []
      (Comma_Fork_At a delta) source
      (comma_python_flush_near old_pending)"
    by (rule comma_python_writer_run.fork[OF fork.hyps(1)]) simp
  show ?thesis using run by blast
next
  case (landmine p source delta)
  have run:
    "comma_python_writer_run p source old_pending []
      (Comma_Landmine_At delta) source
      (comma_python_flush_near old_pending)"
    by (rule comma_python_writer_run.landmine[OF landmine.hyps(1)]) simp
  show ?thesis using run by blast
next
  case (advance p source successor weight events outcome terminal)
  have finite_next:
    "comma_finite_step (p mod 924) source = Comma_Next successor"
    using advance.hyps(1) by (simp add: comma_finite_step_def)
  have successor_admitted: "comma_round_admitted successor"
    by (rule comma_round_next_admitted[OF advance.prems(2) finite_next])
  obtain emitted next_pending where edge:
      "comma_python_writer_edge p source successor weight old_pending
        emitted next_pending"
    and next_phase:
      "comma_python_pending_phase p successor next_pending"
    using comma_python_writer_edge_exists
      [OF advance.prems(1) advance.prems(2) advance.prems(3) advance.hyps(1)]
    by blast
  obtain tail_fragments where tail:
      "comma_python_writer_run p successor next_pending events outcome terminal
        tail_fragments"
    using advance.IH[OF advance.prems(1) successor_admitted next_phase] by blast
  have run:
    "comma_python_writer_run p source old_pending
      (Comma_Python_Advance source successor weight # events)
      outcome terminal (emitted @ tail_fragments)"
    by (rule comma_python_writer_run.advance
      [OF advance.hyps(1) edge tail])
  show ?thesis using run by blast
qed

lemma comma_python_writer_run_to_first_terminal_walk:
  assumes run:
    "comma_python_writer_run p source pending events outcome terminal fragments"
  shows "comma_python_first_terminal_walk p source events outcome terminal"
  using run
proof (induction rule: comma_python_writer_run.induct)
  case (fork p source a delta pending fragments)
  then show ?case by (rule comma_python_first_terminal_walk.fork)
next
  case (landmine p source delta pending fragments)
  then show ?case by (rule comma_python_first_terminal_walk.landmine)
next
  case (advance p source successor weight pending emitted pending' events outcome terminal tail_fragments)
  then show ?case
    by (rule comma_python_first_terminal_walk.advance)
qed

text \<open>The writer relation makes the runtime flush points explicit. An
Entry move publishes a pending Near run before its affine fragment; a
Near-to-Near move either starts the pending run or merges only a phase-
compatible fragment; a Near-to-Entry move publishes both the old pending run
and the crossing singleton. At a terminal event the final pending run is
flushed once. Its accounting invariant is the pair of equalities below.\<close>

lemma comma_python_writer_run_accounting:
  assumes run: "comma_python_writer_run p source pending events outcome
      terminal fragments"
  shows "comma_python_fragment_list_weight_at_scale fragments (10 ^ p) =
      comma_python_pending_weight_at_scale pending (10 ^ p) +
        sum_list (map (\<lambda>event. int (fst (comma_python_event_row p event))) events)"
    and "comma_python_fragment_list_displacement_at_scale fragments (10 ^ p) =
      comma_python_pending_displacement_at_scale pending (10 ^ p) +
        sum_list (map (snd \<circ> comma_python_event_row p) events)"
  using run
proof (induction rule: comma_python_writer_run.induct)
  case (fork p source a delta pending fragments)
  then show ?case
    by (simp add: comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def
        comma_python_flush_near_def)
next
  case (landmine p source delta pending fragments)
  then show ?case
    by (simp add: comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def
        comma_python_flush_near_def)
next
  case (advance p source successor weight pending emitted pending' events outcome terminal tail_fragments)
  note local = comma_python_writer_edge_accounting[OF advance.hyps(2)]
  note suffix = advance.IH
  show ?case using local suffix
    by (simp add: comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def
        sum_list_append)
qed

lemma comma_python_writer_run_published_prefix_fields:
  assumes run:
    "comma_python_writer_run p source pending events outcome terminal fragments"
    and index: "i \<le> length fragments"
  shows "length (comma_python_published_weights
      (comma_python_publish_fragments fragments)) = Suc (length fragments)"
    "length (comma_python_published_displacements
      (comma_python_publish_fragments fragments)) = Suc (length fragments)"
    "comma_python_published_weights
      (comma_python_publish_fragments fragments) ! i =
      foldl comma_python_affine_add comma_python_affine_zero
        (map comma_python_fragment_weight_affine (take i fragments))"
    "comma_python_published_displacements
      (comma_python_publish_fragments fragments) ! i =
      foldl comma_python_affine_add comma_python_affine_zero
        (map comma_python_fragment_displacement_affine (take i fragments))"
  using comma_python_publish_fragments_lengths[of fragments]
    comma_python_publish_fragments_nth[OF index]
  by simp_all

theorem comma_decade_summary_python_macro_writer_output:
  assumes summary: "comma_decade_exact_summary s h terminal"
    and admitted: "comma_decade_admitted s"
    and exponent: "5 \<le> p"
    and binding: "s=Comma_Decade (p mod 924) x"
  shows "\<exists>events final_position fragments.
    comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
      (comma_summary_outcome h terminal) (comma_shift_position h final_position) \<and>
    comma_python_writer_run p (Comma_Entry 1 0 x) None events
      (comma_summary_outcome h terminal) (comma_shift_position h final_position)
      fragments \<and>
    comma_python_fragment_list_weight_at_scale fragments (10 ^ p) =
      sum_list (map (\<lambda>event. int (fst (comma_python_event_row p event))) events) \<and>
    comma_python_fragment_list_displacement_at_scale fragments (10 ^ p) =
      sum_list (map (snd \<circ> comma_python_event_row p) events) \<and>
    length (comma_python_published_weights
      (comma_python_publish_fragments fragments)) = Suc (length fragments) \<and>
    length (comma_python_published_displacements
      (comma_python_publish_fragments fragments)) = Suc (length fragments) \<and>
    (\<forall>i\<le>length fragments.
      comma_python_published_weights
        (comma_python_publish_fragments fragments) ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_weight_affine (take i fragments)) \<and>
      comma_python_published_displacements
        (comma_python_publish_fragments fragments) ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_displacement_affine (take i fragments)))"
proof -
  obtain events final_position where walk:
      "comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
        (comma_summary_outcome h terminal)
        (comma_shift_position h final_position)"
    using comma_decade_summary_python_first_terminal_walk
      [OF summary admitted exponent binding] by blast
  have root_admitted: "comma_round_admitted (Comma_Entry 1 0 x)"
    using admitted binding by simp
  have empty_phase:
    "comma_python_pending_phase p (Comma_Entry 1 0 x) None"
    by (simp add: comma_python_pending_phase_def)
  obtain fragments where run:
      "comma_python_writer_run p (Comma_Entry 1 0 x) None events
        (comma_summary_outcome h terminal)
        (comma_shift_position h final_position) fragments"
    using comma_python_first_terminal_walk_writer
      [OF exponent walk root_admitted empty_phase] by blast
  have accounting:
      "comma_python_fragment_list_weight_at_scale fragments (10 ^ p) =
        sum_list (map
          (\<lambda>event. int (fst (comma_python_event_row p event))) events)"
      "comma_python_fragment_list_displacement_at_scale fragments (10 ^ p) =
        sum_list (map (snd \<circ> comma_python_event_row p) events)"
    using comma_python_writer_run_accounting[OF run]
    by (simp_all add: comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def
        comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_flush_near_def)
  show ?thesis
    using walk run accounting
      comma_python_publish_fragments_lengths[of fragments]
      comma_python_writer_run_published_prefix_fields[OF run]
    by (intro exI[of _ events] exI[of _ final_position]
        exI[of _ fragments]; auto)
qed

text \<open>The public prefix arrays are produced from the symbolic affine
contribution of each retained fragment. The existing nth theorem identifies
every published slot with the fold over exactly the preceding fragments;
the walk above identifies the physical edge sequence, while the writer run below carries the pending Near suffix and its
accounting through the first terminal event.\<close>

lemmas comma_python_producer_refinement_oracle_audit_bundle =
  comma_python_first_terminal_walk_writer
  comma_python_writer_edge_accounting
  comma_python_writer_run_accounting
  comma_python_writer_run_published_prefix_fields
  comma_decade_summary_python_macro_writer_output

ML \<open>
val _ = if null (Thm_Deps.all_oracles @{thms
  comma_python_producer_refinement_oracle_audit_bundle
}) then () else error "Comma_Semantic_Producer_Refinement local oracle audit failed"
\<close>

end
