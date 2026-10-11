theory Comma_Semantic_Producer_Trace_Bridge
  imports Comma_Semantic_Producer_Affine_Algebra
begin

text \<open>This owner connects the pending-fragment writer relation to the
ordered affine fold it publishes.  It accounts for a pending Near run before
the current event, including a coalescing step, and is stated for an arbitrary
affine accumulator so it composes through the recursive writer.  It proves
total-fold refinement.  The lower-bound search is formalized later under
published-prefix monotonicity; the full prefix-displacement bridge remains
open.\<close>

fun comma_python_event_weight_affine ::
  "comma_python_producer_event \<Rightarrow> comma_python_affine_weight" where
  "comma_python_event_weight_affine
      (Comma_Python_Advance (Comma_Entry f delta offset) successor weight) =
    comma_python_chart_affine_weight delta weight"
| "comma_python_event_weight_affine
      (Comma_Python_Advance (Comma_Near f delta headroom) successor weight) =
    comma_python_chart_affine_weight 0 weight"

lemma comma_python_merge_near_weight_affine:
  assumes compatible: "comma_python_near_fragments_compatible a b"
  shows "comma_python_fragment_weight_affine
      (comma_python_merge_near_fragments a b) =
    comma_python_affine_add (comma_python_fragment_weight_affine a)
      (comma_python_fragment_weight_affine b)"
  using compatible
  by (simp add: comma_python_fragment_weight_affine_def
      comma_python_constant_affine_def comma_python_affine_times_def
      comma_python_affine_add_def comma_python_affine_normalize_def
      comma_python_affine_zero_def comma_python_near_fragment_shape_def
      comma_python_near_fragments_compatible_def
      comma_python_merge_near_fragments_def Let_def)

lemma comma_python_pending_affine_weights_positive:
  assumes phase: "comma_python_pending_phase p position pending"
  shows "\<forall>x\<in>set (map comma_python_fragment_weight_affine
      (comma_python_flush_near pending)).
      0 < comma_python_affine_denominator x"
proof (cases pending)
  case None
  then show ?thesis by (simp add: comma_python_flush_near_def)
next
  case (Some fragment)
  have shape: "comma_python_near_fragment_shape fragment"
    using phase Some
    by (cases position)
      (auto simp: comma_python_pending_phase_def)
  then show ?thesis
    by (simp add: Some comma_python_flush_near_def
        comma_python_fragment_weight_affine_def
        comma_python_affine_times_def comma_python_constant_affine_def
        comma_python_affine_add_def comma_python_affine_normalize_def
        comma_python_affine_zero_def comma_python_near_fragment_shape_def
        Let_def)
qed

lemma comma_python_fragment_record_affine_bridge:
  assumes exponent: "5 \<le> p"
    and admitted: "comma_round_admitted source"
    and record: "comma_python_fragment_record_matches p source successor
      weight fragment"
  shows "comma_python_affine_equivalent
      (comma_python_fragment_weight_affine fragment)
      (comma_python_event_weight_affine
        (Comma_Python_Advance source successor weight))"
    and "0 < comma_python_affine_denominator
      (comma_python_fragment_weight_affine fragment)"
    and "0 < comma_python_affine_denominator
      (comma_python_event_weight_affine
        (Comma_Python_Advance source successor weight))"
proof (cases source)
  case (Comma_Entry f delta offset)
  have f: "1 \<le> f" "f \<le> 9"
    and offset: "offset \<le> 98"
    using admitted by (simp_all add: Comma_Entry)
  let ?h = "comma_finite_headroom f (p mod 924) delta offset"
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?L = "comma_cycle_length f"
  let ?weight = "Comma_Chart_Weight ?L delta
    (- int (?L * (offset + ?h))) ?P"
  have matched_step:
    "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext successor weight"
    and matched_fragment:
    "fragment = comma_python_entry_sector_fragment f delta offset ?h"
    using record by (simp_all add: comma_python_fragment_record_matches_def
      Comma_Entry)
  have exact_step:
    "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta ?h) ?weight"
    using comma_entry_chart_exact_literal_path(7)[OF f exponent offset,
      of delta]
    by simp
  have successor: "successor = Comma_Near f delta ?h"
    and weight: "weight = ?weight"
    using matched_step exact_step by injection auto
  have coefficient:
    "comma_python_affine_equivalent
      (comma_python_fragment_weight_affine
        (comma_python_entry_sector_fragment f delta offset ?h))
      (comma_python_chart_affine_weight delta ?weight)"
    using comma_python_entry_fragment_weight_affine_coefficient
      [of f delta offset ?h] f by simp
  show thesis
    using coefficient matched_fragment successor weight
    by (simp add: comma_python_event_weight_affine.simps
        comma_python_affine_equivalent_def)
next
  case (Comma_Near f delta headroom)
  have f: "1 \<le> f" "f \<le> 9"
    and headroom: "1 \<le> headroom" "headroom \<le> 540"
    using admitted by (simp_all add: Comma_Near)
  have matched_step:
    "comma_weighted_step (p mod 924) (Comma_Near f delta headroom) =
      Comma_WNext successor weight"
    and matched_increment:
    "\<exists>increment. comma_chart_value p successor =
        comma_chart_value p (Comma_Near f delta headroom) + increment \<and>
      fragment = comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment"
    using record by (simp_all add: comma_python_fragment_record_matches_def
      Comma_Near)
  obtain increment where endpoint:
      "comma_chart_value p successor =
        comma_chart_value p (Comma_Near f delta headroom) + increment"
    and fragment:
      "fragment = comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment"
    using matched_increment by blast
  obtain increment' where endpoint':
      "comma_chart_value p successor =
        comma_chart_value p (Comma_Near f delta headroom) + increment'"
    and coefficient:
      "comma_python_affine_equivalent
        (comma_python_fragment_weight_affine
          (comma_python_literal_fragment f
            (comma_chart_value p (Comma_Near f delta headroom) mod 10)
            1 increment'))
        (comma_python_chart_affine_weight 0 weight)"
    using comma_python_near_fragment_weight_affine_coefficient
      [OF f exponent headroom matched_step] by blast
  have same: "increment = increment'"
    using endpoint endpoint' by arith
  show thesis
    using coefficient fragment same
    by (simp add: comma_python_event_weight_affine.simps
        comma_python_affine_equivalent_def)
qed

lemma comma_python_writer_edge_affine_chunk:
  assumes exponent: "5 \<le> p"
    and admitted: "comma_round_admitted source"
    and phase: "comma_python_pending_phase p source pending"
    and edge: "comma_python_writer_edge p source successor weight
      pending emitted pending'"
    and initial: "0 < comma_python_affine_denominator z"
  shows "comma_python_affine_equivalent
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine
          (emitted @ comma_python_flush_near pending')))
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine
          (comma_python_flush_near pending) @
          [comma_python_event_weight_affine
            (Comma_Python_Advance source successor weight)]))"
    and "0 < comma_python_affine_denominator
      (comma_python_event_weight_affine
        (Comma_Python_Advance source successor weight))"
    and "\<forall>x\<in>set (map comma_python_fragment_weight_affine emitted).
      0 < comma_python_affine_denominator x"
  using edge exponent admitted phase initial
proof (induction rule: comma_python_writer_edge.induct)
  case (entry p f delta offset headroom weight pending)
  have admitted':
    "comma_round_admitted (Comma_Entry f delta offset)"
    using entry.prems(2) by simp
  have record:
    "comma_python_fragment_record_matches p
      (Comma_Entry f delta offset) (Comma_Near f delta headroom) weight
      (comma_python_entry_sector_fragment f delta offset headroom)"
    using entry.hyps(1) .
  note bridge = comma_python_fragment_record_affine_bridge
    [OF entry.prems(1) admitted' record]
  have pending_positive:
    "\<forall>x\<in>set (map comma_python_fragment_weight_affine
        (comma_python_flush_near pending)).
      0 < comma_python_affine_denominator x"
    by (rule comma_python_pending_affine_weights_positive[OF entry.prems(3)])
  have emitted_positive:
    "\<forall>x\<in>set (map comma_python_fragment_weight_affine
        (comma_python_flush_near pending @
          [comma_python_entry_sector_fragment f delta offset headroom])).
      0 < comma_python_affine_denominator x"
    using pending_positive bridge(2) by (auto simp: set_map)
  have fold_eq:
    "comma_python_affine_equivalent
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine
          (comma_python_flush_near pending @
            [comma_python_entry_sector_fragment f delta offset headroom])))
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine
          (comma_python_flush_near pending) @
          [comma_python_event_weight_affine
            (Comma_Python_Advance (Comma_Entry f delta offset)
              (Comma_Near f delta headroom) weight)]))"
    using comma_python_affine_fold_replace_last[OF entry.prems(4)
      pending_positive _ _ bridge(1)] bridge(2,3)
    by (simp add: comma_python_event_weight_affine.simps)
  show ?case using fold_eq bridge(3) emitted_positive
    by (simp add: comma_python_flush_near_def)
next
  case (near_start p f delta headroom next_headroom weight increment)
  have admitted':
    "comma_round_admitted (Comma_Near f delta headroom)"
    using near_start.prems(2) by simp
  have record:
    "comma_python_fragment_record_matches p
      (Comma_Near f delta headroom)
      (Comma_Near f delta next_headroom) weight
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment)"
    using near_start.hyps(1) .
  note bridge = comma_python_fragment_record_affine_bridge
    [OF near_start.prems(1) admitted' record]
  have fold_eq:
    "comma_python_affine_equivalent
      (comma_python_affine_add z
        (comma_python_fragment_weight_affine
          (comma_python_literal_fragment f
            (comma_chart_value p (Comma_Near f delta headroom) mod 10)
            1 increment)))
      (comma_python_affine_add z
        (comma_python_event_weight_affine
          (Comma_Python_Advance (Comma_Near f delta headroom)
            (Comma_Near f delta next_headroom) weight)))"
    proof -
      have z_refl: "comma_python_affine_equivalent z z"
        by (rule comma_python_affine_equivalent_refl[OF near_start.prems(4)])
      show ?thesis
        by (rule comma_python_affine_add_cong[OF z_refl bridge(1)])
    qed
  show ?case using fold_eq bridge(3)
    by (simp add: comma_python_flush_near_def)
next
  case (near_merge pending_fragment p f delta headroom next_headroom weight
      increment)
  have admitted':
    "comma_round_admitted (Comma_Near f delta headroom)"
    using near_merge.prems(2) by simp
  have record:
    "comma_python_fragment_record_matches p
      (Comma_Near f delta headroom)
      (Comma_Near f delta next_headroom) weight
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment)"
    using near_merge.hyps(2) .
  note bridge = comma_python_fragment_record_affine_bridge
    [OF near_merge.prems(1) admitted' record]
  have phase_pending:
    "comma_python_pending_phase p (Comma_Near f delta headroom)
      (Some pending_fragment)"
    using near_merge.prems(3) by simp
  have pending_positive:
    "0 < comma_python_affine_denominator
      (comma_python_fragment_weight_affine pending_fragment)"
    using comma_python_pending_affine_weights_positive[OF phase_pending]
    by (simp add: comma_python_flush_near_def)
  have z_refl: "comma_python_affine_equivalent z z"
    by (rule comma_python_affine_equivalent_refl[OF near_merge.prems(4)])
  have pending_refl:
    "comma_python_affine_equivalent
      (comma_python_fragment_weight_affine pending_fragment)
      (comma_python_fragment_weight_affine pending_fragment)"
    by (rule comma_python_affine_equivalent_refl[OF pending_positive])
  have merge_to_sum:
    "comma_python_affine_equivalent
      (comma_python_fragment_weight_affine
        (comma_python_merge_near_fragments pending_fragment
          (comma_python_literal_fragment f
            (comma_chart_value p (Comma_Near f delta headroom) mod 10)
            1 increment)))
      (comma_python_affine_add
        (comma_python_fragment_weight_affine pending_fragment)
        (comma_python_event_weight_affine
          (Comma_Python_Advance (Comma_Near f delta headroom)
            (Comma_Near f delta next_headroom) weight)))"
  proof -
    have merge:
      "comma_python_fragment_weight_affine
          (comma_python_merge_near_fragments pending_fragment
            (comma_python_literal_fragment f
              (comma_chart_value p (Comma_Near f delta headroom) mod 10)
              1 increment)) =
        comma_python_affine_add
          (comma_python_fragment_weight_affine pending_fragment)
          (comma_python_fragment_weight_affine
            (comma_python_literal_fragment f
              (comma_chart_value p (Comma_Near f delta headroom) mod 10)
              1 increment))"
      by (rule comma_python_merge_near_weight_affine[OF near_merge.hyps(1)])
    have add:
      "comma_python_affine_equivalent
        (comma_python_affine_add
          (comma_python_fragment_weight_affine pending_fragment)
          (comma_python_fragment_weight_affine
            (comma_python_literal_fragment f
              (comma_chart_value p (Comma_Near f delta headroom) mod 10)
              1 increment)))
        (comma_python_affine_add
          (comma_python_fragment_weight_affine pending_fragment)
          (comma_python_event_weight_affine
            (Comma_Python_Advance (Comma_Near f delta headroom)
              (Comma_Near f delta next_headroom) weight)))"
      by (rule comma_python_affine_add_cong[OF pending_refl bridge(1)])
    show ?thesis using merge add by simp
  qed
  have associate:
    "comma_python_affine_equivalent
      (comma_python_affine_add
        (comma_python_affine_add z
          (comma_python_fragment_weight_affine pending_fragment))
        (comma_python_event_weight_affine
          (Comma_Python_Advance (Comma_Near f delta headroom)
            (Comma_Near f delta next_headroom) weight)))
      (comma_python_affine_add z
        (comma_python_affine_add
          (comma_python_fragment_weight_affine pending_fragment)
          (comma_python_event_weight_affine
            (Comma_Python_Advance (Comma_Near f delta headroom)
              (Comma_Near f delta next_headroom) weight))))"
    by (rule comma_python_affine_add_assoc_equivalent
      [OF near_merge.prems(4) pending_positive bridge(3)])
  have fold_eq:
    "comma_python_affine_equivalent
      (comma_python_affine_add z
        (comma_python_fragment_weight_affine
          (comma_python_merge_near_fragments pending_fragment
            (comma_python_literal_fragment f
              (comma_chart_value p (Comma_Near f delta headroom) mod 10)
              1 increment)))
      (comma_python_affine_add z
        (comma_python_affine_add
          (comma_python_fragment_weight_affine pending_fragment)
          (comma_python_event_weight_affine
          (Comma_Python_Advance (Comma_Near f delta headroom)
            (Comma_Near f delta next_headroom) weight))))"
  proof -
    have merged_positive:
      "0 < comma_python_affine_denominator
        (comma_python_affine_add
          (comma_python_fragment_weight_affine pending_fragment)
          (comma_python_event_weight_affine
            (Comma_Python_Advance (Comma_Near f delta headroom)
              (Comma_Near f delta next_headroom) weight)))"
      by (rule comma_python_affine_add_positive[OF pending_positive bridge(3)])
    have left: "comma_python_affine_equivalent
        (comma_python_affine_add z
          (comma_python_fragment_weight_affine
            (comma_python_merge_near_fragments pending_fragment
              (comma_python_literal_fragment f
                (comma_chart_value p (Comma_Near f delta headroom) mod 10)
                1 increment)))
        (comma_python_affine_add z
          (comma_python_affine_add
            (comma_python_fragment_weight_affine pending_fragment)
            (comma_python_event_weight_affine
              (Comma_Python_Advance (Comma_Near f delta headroom)
                (Comma_Near f delta next_headroom) weight))))"
      using comma_python_affine_add_cong[OF z_refl merge_to_sum] .
    show ?thesis using left by simp
  qed
  have associate_sym:
    "comma_python_affine_equivalent
      (comma_python_affine_add z
        (comma_python_affine_add
          (comma_python_fragment_weight_affine pending_fragment)
          (comma_python_event_weight_affine
            (Comma_Python_Advance (Comma_Near f delta headroom)
              (Comma_Near f delta next_headroom) weight))))
      (comma_python_affine_add
        (comma_python_affine_add z
          (comma_python_fragment_weight_affine pending_fragment))
        (comma_python_event_weight_affine
          (Comma_Python_Advance (Comma_Near f delta headroom)
            (Comma_Near f delta next_headroom) weight)))"
    by (rule comma_python_affine_equivalent_sym[OF associate])
  have middle_positive:
    "0 < comma_python_affine_denominator
      (comma_python_affine_add z
        (comma_python_affine_add
          (comma_python_fragment_weight_affine pending_fragment)
          (comma_python_event_weight_affine
            (Comma_Python_Advance (Comma_Near f delta headroom)
              (Comma_Near f delta next_headroom) weight))))"
    using associate_sym by (simp add: comma_python_affine_equivalent_def)
  have result:
    "comma_python_affine_equivalent
      (comma_python_affine_add z
        (comma_python_fragment_weight_affine
          (comma_python_merge_near_fragments pending_fragment
            (comma_python_literal_fragment f
              (comma_chart_value p (Comma_Near f delta headroom) mod 10)
              1 increment)))
      (comma_python_affine_add
        (comma_python_affine_add z
          (comma_python_fragment_weight_affine pending_fragment))
        (comma_python_event_weight_affine
          (Comma_Python_Advance (Comma_Near f delta headroom)
            (Comma_Near f delta next_headroom) weight)))"
    by (rule comma_python_affine_equivalent_trans
      [OF fold_eq associate_sym middle_positive])
  show ?case using result bridge(3)
    by (simp add: comma_python_flush_near_def)
next
  case (near_cross p f delta headroom g next_delta offset weight pending
      increment)
  have admitted':
    "comma_round_admitted (Comma_Near f delta headroom)"
    using near_cross.prems(2) by simp
  have record:
    "comma_python_fragment_record_matches p
      (Comma_Near f delta headroom) (Comma_Entry g next_delta offset) weight
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment)"
    using near_cross.hyps(1) .
  note bridge = comma_python_fragment_record_affine_bridge
    [OF near_cross.prems(1) admitted' record]
  have pending_positive:
    "\<forall>x\<in>set (map comma_python_fragment_weight_affine
        (comma_python_flush_near pending)).
      0 < comma_python_affine_denominator x"
    by (rule comma_python_pending_affine_weights_positive[OF near_cross.prems(3)])
  have emitted_positive:
    "\<forall>x\<in>set (map comma_python_fragment_weight_affine
        (comma_python_flush_near pending @
          [comma_python_literal_fragment f
            (comma_chart_value p (Comma_Near f delta headroom) mod 10)
            1 increment])).
      0 < comma_python_affine_denominator x"
    using pending_positive bridge(2) by (auto simp: set_map)
  have fold_eq:
    "comma_python_affine_equivalent
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine
          (comma_python_flush_near pending @
            [comma_python_literal_fragment f
              (comma_chart_value p (Comma_Near f delta headroom) mod 10)
              1 increment])))
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine
          (comma_python_flush_near pending) @
          [comma_python_event_weight_affine
            (Comma_Python_Advance (Comma_Near f delta headroom)
              (Comma_Entry g next_delta offset) weight)]))"
    using comma_python_affine_fold_replace_last[OF near_cross.prems(4)
      pending_positive _ _ bridge(1)] bridge(2,3)
    by (simp add: comma_python_event_weight_affine.simps)
  show ?case using fold_eq bridge(3) emitted_positive
    by (simp add: comma_python_flush_near_def)
qed

theorem comma_python_first_terminal_walk_affine_writer:
  fixes p source events outcome terminal pending z
  assumes exponent: "5 \<le> p"
    and walk: "comma_python_first_terminal_walk p source events outcome terminal"
    and admitted: "comma_round_admitted source"
    and phase: "comma_python_pending_phase p source pending"
    and initial: "0 < comma_python_affine_denominator z"
  shows "\<exists>fragments. comma_python_writer_run p source pending events
      outcome terminal fragments \<and>
    comma_python_affine_equivalent
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine fragments))
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine
          (comma_python_flush_near pending) @
          map comma_python_event_weight_affine events)) \<and>
    (\<forall>x\<in>set (map comma_python_fragment_weight_affine fragments).
      0 < comma_python_affine_denominator x) \<and>
    (\<forall>x\<in>set (map comma_python_event_weight_affine events).
      0 < comma_python_affine_denominator x)"
  using walk exponent admitted phase initial
proof (induction arbitrary: pending z
    rule: comma_python_first_terminal_walk.induct)
  case (fork p source a delta)
  let ?fragments = "comma_python_flush_near pending"
  have run:
    "comma_python_writer_run p source pending []
      (Comma_Fork_At a delta) source ?fragments"
    by (rule comma_python_writer_run.fork[OF fork.hyps(1)]) simp
  have fragment_positive:
    "\<forall>x\<in>set (map comma_python_fragment_weight_affine ?fragments).
      0 < comma_python_affine_denominator x"
    by (rule comma_python_pending_affine_weights_positive[OF fork.prems(3)])
  have fold_positive:
    "0 < comma_python_affine_denominator
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine ?fragments))"
    by (rule comma_python_affine_fold_positive[OF fork.prems(4)
      fragment_positive])
  have equivalent:
    "comma_python_affine_equivalent
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine ?fragments))
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine ?fragments @ []))"
    by (rule comma_python_affine_equivalent_refl[OF fold_positive]) simp
  show ?case using run equivalent fragment_positive
    by (intro exI[of _ ?fragments] conjI; simp)
next
  case (landmine p source delta)
  let ?fragments = "comma_python_flush_near pending"
  have run:
    "comma_python_writer_run p source pending []
      (Comma_Landmine_At delta) source ?fragments"
    by (rule comma_python_writer_run.landmine[OF landmine.hyps(1)]) simp
  have fragment_positive:
    "\<forall>x\<in>set (map comma_python_fragment_weight_affine ?fragments).
      0 < comma_python_affine_denominator x"
    by (rule comma_python_pending_affine_weights_positive[OF landmine.prems(3)])
  have fold_positive:
    "0 < comma_python_affine_denominator
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine ?fragments))"
    by (rule comma_python_affine_fold_positive[OF landmine.prems(4)
      fragment_positive])
  have equivalent:
    "comma_python_affine_equivalent
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine ?fragments))
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine ?fragments @ []))"
    by (rule comma_python_affine_equivalent_refl[OF fold_positive]) simp
  show ?case using run equivalent fragment_positive
    by (intro exI[of _ ?fragments] conjI; simp)
next
  case (advance p source successor weight events outcome terminal)
  have finite_next:
    "comma_finite_step (p mod 924) source = Comma_Next successor"
    using advance.hyps(1) by (simp add: comma_finite_step_def)
  have successor_admitted: "comma_round_admitted successor"
    by (rule comma_round_next_admitted[OF advance.prems(2) finite_next])
  obtain emitted next_pending where edge:
      "comma_python_writer_edge p source successor weight pending
        emitted next_pending"
    and next_phase:
      "comma_python_pending_phase p successor next_pending"
    using comma_python_writer_edge_exists
      [OF advance.prems(1) advance.prems(2) advance.prems(3)
        advance.hyps(1)] by blast
  note chunk = comma_python_writer_edge_affine_chunk
    [OF advance.prems(1) advance.prems(2) advance.prems(3) edge
      advance.prems(4)]
  have emitted_positive:
    "\<forall>x\<in>set (map comma_python_fragment_weight_affine emitted).
      0 < comma_python_affine_denominator x"
    by (rule chunk(3))
  let ?z' = "foldl comma_python_affine_add z
    (map comma_python_fragment_weight_affine emitted)"
  have z'_positive:
    "0 < comma_python_affine_denominator ?z'"
    by (rule comma_python_affine_fold_positive[OF advance.prems(4)
      emitted_positive])
  obtain tail_fragments where tail_run:
      "comma_python_writer_run p successor next_pending events outcome terminal
        tail_fragments"
    and tail_equivalent:
      "comma_python_affine_equivalent
        (foldl comma_python_affine_add ?z'
          (map comma_python_fragment_weight_affine tail_fragments))
        (foldl comma_python_affine_add ?z'
          (map comma_python_fragment_weight_affine
            (comma_python_flush_near next_pending) @
            map comma_python_event_weight_affine events))"
    and tail_fragments_positive:
      "\<forall>x\<in>set (map comma_python_fragment_weight_affine tail_fragments).
        0 < comma_python_affine_denominator x"
    and tail_events_positive:
      "\<forall>x\<in>set (map comma_python_event_weight_affine events).
        0 < comma_python_affine_denominator x"
    using advance.IH[OF advance.prems(1) successor_admitted next_phase
      z'_positive] by blast
  have run:
    "comma_python_writer_run p source pending
      (Comma_Python_Advance source successor weight # events)
      outcome terminal (emitted @ tail_fragments)"
    by (rule comma_python_writer_run.advance
      [OF advance.hyps(1) edge tail_run])
  have full_tail:
    "comma_python_affine_equivalent
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine emitted @
          map comma_python_fragment_weight_affine tail_fragments))
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine emitted @
          map comma_python_fragment_weight_affine
            (comma_python_flush_near next_pending) @
          map comma_python_event_weight_affine events))"
    using tail_equivalent by (simp add: foldl_append)
  have chunk_with_tail:
    "comma_python_affine_equivalent
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine emitted @
          map comma_python_fragment_weight_affine
            (comma_python_flush_near next_pending) @
          map comma_python_event_weight_affine events))
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine
          (comma_python_flush_near pending) @
          [comma_python_event_weight_affine
            (Comma_Python_Advance source successor weight)] @
          map comma_python_event_weight_affine events))"
    using comma_python_affine_fold_equivalent_starts
      [OF chunk(1) tail_events_positive]
    by (simp add: foldl_append)
  have middle_positive:
    "0 < comma_python_affine_denominator
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine emitted @
          map comma_python_fragment_weight_affine
            (comma_python_flush_near next_pending) @
          map comma_python_event_weight_affine events))"
    using chunk_with_tail
    by (simp add: comma_python_affine_equivalent_def)
  have equivalent:
    "comma_python_affine_equivalent
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine emitted @
          map comma_python_fragment_weight_affine tail_fragments))
      (foldl comma_python_affine_add z
        (map comma_python_fragment_weight_affine
          (comma_python_flush_near pending) @
          map comma_python_event_weight_affine
            (Comma_Python_Advance source successor weight # events)))"
    by (rule comma_python_affine_equivalent_trans
      [OF full_tail chunk_with_tail middle_positive])
  have fragments_positive:
    "\<forall>x\<in>set (map comma_python_fragment_weight_affine
        (emitted @ tail_fragments)).
      0 < comma_python_affine_denominator x"
    using emitted_positive tail_fragments_positive by (auto simp: set_map)
  have events_positive:
    "\<forall>x\<in>set (map comma_python_event_weight_affine
        (Comma_Python_Advance source successor weight # events)).
      0 < comma_python_affine_denominator x"
    using chunk(2) tail_events_positive by (auto simp: set_map)
  show ?case using run equivalent fragments_positive events_positive
    by (intro exI[of _ "emitted @ tail_fragments"] conjI; simp)
qed

lemma comma_python_affine_equivalent_transfers_exact_division:
  fixes a b :: comma_python_affine_weight and S :: nat
  assumes equivalent: "comma_python_affine_equivalent a b"
    and exact: "comma_python_affine_divides b S"
  shows "comma_python_affine_divides a S"
    and "comma_python_affine_evaluate a S = comma_python_affine_evaluate b S"
proof -
  have da: "0 < comma_python_affine_denominator a"
    and db: "0 < comma_python_affine_denominator b"
    and slopes:
      "comma_python_affine_scale a *
          int (comma_python_affine_denominator b) =
       comma_python_affine_scale b *
          int (comma_python_affine_denominator a)"
    and offsets:
      "comma_python_affine_offset a *
          int (comma_python_affine_denominator b) =
       comma_python_affine_offset b *
          int (comma_python_affine_denominator a)"
    using equivalent by (simp_all add: comma_python_affine_equivalent_def)
  let ?na = "comma_python_affine_scale a * int S +
    comma_python_affine_offset a"
  let ?nb = "comma_python_affine_scale b * int S +
    comma_python_affine_offset b"
  have numerator_relation:
    "?na * int (comma_python_affine_denominator b) =
      ?nb * int (comma_python_affine_denominator a)"
    using slopes offsets by (simp add: algebra_simps)
  obtain k where nb_factor:
    "?nb = int (comma_python_affine_denominator b) * k"
    using exact unfolding comma_python_affine_divides_def dvd_def by blast
  have na_factor:
    "?na = int (comma_python_affine_denominator a) * k"
  proof -
    have cancel:
      "int (comma_python_affine_denominator b) * ?na =
       int (comma_python_affine_denominator b) *
         (int (comma_python_affine_denominator a) * k)"
      using numerator_relation nb_factor by (simp add: algebra_simps)
    have db_nonzero: "int (comma_python_affine_denominator b) \<noteq> 0"
      using db by simp
    show ?thesis using cancel db_nonzero by (metis mult_left_cancel)
  qed
  have exact_a: "int (comma_python_affine_denominator a) dvd ?na"
    using na_factor by (simp add: dvd_def)
  have eval_a:
    "comma_python_affine_evaluate a S *
       int (comma_python_affine_denominator a) = ?na"
    by (rule comma_python_affine_evaluate_integral[OF exact_a])
  have eval_b:
    "comma_python_affine_evaluate b S *
       int (comma_python_affine_denominator b) = ?nb"
    by (rule comma_python_affine_evaluate_integral[OF exact])
  have da_nonzero:
    "int (comma_python_affine_denominator a) \<noteq> 0"
    using da by simp
  have db_nonzero:
    "int (comma_python_affine_denominator b) \<noteq> 0"
    using db by simp
  have value_a: "comma_python_affine_evaluate a S = k"
    using eval_a na_factor da_nonzero
    by (metis mult_left_cancel mult.commute)
  have value_b: "comma_python_affine_evaluate b S = k"
    using eval_b nb_factor db_nonzero
    by (metis mult_left_cancel mult.commute)
  show "comma_python_affine_divides a S"
    using exact_a by (simp add: comma_python_affine_divides_def)
  show "comma_python_affine_evaluate a S =
      comma_python_affine_evaluate b S"
    using value_a value_b by simp
qed

text \<open>The next consumer step in Python's `MacroTemplate.point` is a
lower-bound lookup in the published prefix weights.  The lemmas here start
after that lookup has established its adjacent-prefix contract; they prove
the exact `remaining` bounds and the period-division guard used by the runtime.
The published-prefix theorem below separately proves that contract from
monotonicity of the evaluated prefix array.\<close>

lemma comma_python_point_selected_prefix_interval:
  fixes before after transitions :: int
    and fragment :: comma_python_sector_fragment
    and S :: nat
  assumes selected: "before < transitions" "transitions \<le> after"
    and adjacent: "after = before +
      comma_python_fragment_weight_at_scale fragment S"
  shows "0 < transitions - before"
    and "transitions - before \<le>
      comma_python_fragment_weight_at_scale fragment S"
  using selected adjacent by linarith+

lemma comma_python_point_entry_partial_divmod_guard:
  fixes fragment :: comma_python_sector_fragment
    and S :: nat and cycles remaining :: int
  assumes period: "0 < comma_python_fragment_period fragment"
    and literal: "comma_python_fragment_literal_steps fragment = 0"
    and cycle_value:
      "comma_python_affine_evaluate
        (comma_python_fragment_complete_cycles fragment) S = cycles"
    and cycles: "0 \<le> cycles"
    and selected: "0 < remaining"
    and within: "remaining \<le>
      comma_python_fragment_weight_at_scale fragment S"
  shows "remaining div int (comma_python_fragment_period fragment) \<le> cycles"
    and "0 \<le> remaining mod int (comma_python_fragment_period fragment)"
    and "remaining mod int (comma_python_fragment_period fragment) <
      int (comma_python_fragment_period fragment)"
proof -
  have positive: "0 < int (comma_python_fragment_period fragment)"
    using period by simp
  have bound:
    "remaining \<le>
      int (comma_python_fragment_period fragment) * cycles"
    using within literal cycle_value
    by (simp add: comma_python_fragment_weight_at_scale_def)
  have strict:
    "remaining < int (comma_python_fragment_period fragment) * (cycles + 1)"
    using bound cycles positive by linarith
  have quotient:
    "remaining div int (comma_python_fragment_period fragment) < cycles + 1"
    using strict
    by (simp only: div_less_iff_less_mult[OF positive])
  have remainder_nonnegative:
    "0 \<le> remaining mod int (comma_python_fragment_period fragment)"
    by (rule mod_nonneg) (use positive in simp)
  have remainder_below:
    "remaining mod int (comma_python_fragment_period fragment) <
      int (comma_python_fragment_period fragment)"
    by (rule mod_less_divisor[OF positive])
  show "remaining div int (comma_python_fragment_period fragment) \<le> cycles"
    using quotient by linarith
  show "0 \<le> remaining mod int (comma_python_fragment_period fragment)"
    by (rule remainder_nonnegative)
  show "remaining mod int (comma_python_fragment_period fragment) <
      int (comma_python_fragment_period fragment)"
    by (rule remainder_below)
qed

lemma comma_python_point_near_partial_literal_guard:
  fixes fragment :: comma_python_sector_fragment and S :: nat
    and remaining :: int
  assumes shape: "comma_python_near_fragment_shape fragment"
    and selected: "0 < remaining"
    and within: "remaining \<le>
      comma_python_fragment_weight_at_scale fragment S"
  shows "0 < remaining"
    and "remaining \<le> int (comma_python_fragment_literal_steps fragment)"
proof -
  show "0 < remaining" by (rule selected)
  show "remaining \<le> int (comma_python_fragment_literal_steps fragment)"
  using within shape
  by (simp add: comma_python_fragment_weight_at_scale_def
      comma_python_near_fragment_shape_def comma_python_affine_evaluate_def)
qed

text \<open>For an Entry fragment, the prefix-search postcondition is enough to
discharge the producer's partial-cycle bound and identify the exact chart
position returned by `MacroTemplate.point`.  The theorem is deliberately
local: prefix-array search correctness and the accumulated displacement
before this fragment remain separate obligations.\<close>

theorem comma_python_point_entry_partial_refines_chart_fragment:
  fixes f p delta offset :: nat
    and before after transitions :: int and base :: int
    and fragment :: comma_python_sector_fragment
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
    and lower: "before < transitions"
    and upper: "transitions \<le> after"
    and adjacent: "after = before +
      comma_python_fragment_weight_at_scale fragment (10 ^ p)"
    and base: "base = int (comma_chart_value p
      (Comma_Entry f delta offset))"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "c \<equiv> (10 ^ (p + delta) - offset - h) div P"
    and "fragment \<equiv> comma_python_entry_sector_fragment f delta offset h"
    and "j \<equiv> nat (transitions - before)"
  shows "base + comma_python_fragment_select fragment (10 ^ p) j =
    int (comma_chart_fragment_closed p (Comma_Entry f delta offset)
      (Comma_Near f delta h) j)"
proof -
  note fields = comma_python_entry_fragment_refines_chart_move
    [OF f exponent offset, of delta]
  have interval:
    "0 < transitions - before"
    "transitions - before <=
      comma_python_fragment_weight_at_scale fragment (10 ^ p)"
    using comma_python_point_selected_prefix_interval[OF lower upper]
      adjacent by simp_all
  have remaining_nat: "int j = transitions - before"
    using interval(1) by (simp add: j_def)
  have fragment_weight:
    "comma_python_fragment_weight_at_scale fragment (10 ^ p) =
      int (L * c)"
    using fields(4)
    by (simp add: comma_python_fragment_weight_at_scale_def fragment_def
        comma_python_entry_sector_fragment_def Let_def L_def)
  have j_bound: "j <= c * L"
  proof -
    have "int j <= int (c * L)"
      using interval(2) fragment_weight remaining_nat
      by (simp add: mult.commute)
    then show ?thesis by exact_mod_cast
  qed
  have selected:
    "comma_chart_fragment_closed p (Comma_Entry f delta offset)
        (Comma_Near f delta h) j =
      comma_chart_value p (Comma_Entry f delta offset) +
        comma_python_fragment_select fragment (10 ^ p) j"
    using comma_python_entry_fragment_selection
      [OF f exponent offset j_bound, of delta]
    by (simp add: h_def P_def L_def c_def fragment_def)
  show ?thesis using selected base by simp
qed

text \<open>This instantiates the shared lower-bound proof with the exact
published affine prefix-weight array read by `MacroTemplate.point`.  The
finite recursion fuel is derived from the loop's initial interval width;
the theorem has no runtime fuel premise.  Positivity/monotonicity and the
per-prefix exact-evaluation obligations are explicit inputs because the
writer theorem has not yet established them index by index.\<close>

theorem comma_python_published_prefix_binary_search_contract:
  fixes fragments :: "comma_python_sector_fragment list"
    and S target :: nat and weights :: "comma_python_affine_weight list"
    and prefixes :: "nat list" and first :: nat
  assumes nonempty: "fragments \<noteq> []"
    and evaluable: "\<And>i. i < length weights \<Longrightarrow>
      0 < comma_python_affine_denominator (weights ! i) \<and>
      comma_python_affine_divides (weights ! i) S"
    and nonnegative: "\<And>i. i < length weights \<Longrightarrow>
      0 \<le> comma_python_affine_evaluate (weights ! i) S"
    and monotone: "\<And>i j. i \<le> j \<Longrightarrow>
      j < length prefixes \<Longrightarrow> prefixes ! i \<le> prefixes ! j"
    and requested: "0 < target"
      "target < prefixes ! (length prefixes - 1)"
  defines "weights \<equiv> comma_python_published_weights
      (comma_python_publish_fragments fragments)"
    and "prefixes \<equiv> map
      (\<lambda>w. nat (comma_python_affine_evaluate w S)) weights"
    and "first \<equiv> Min {i. 1 \<le> i \<and> i < length prefixes \<and>
      target \<le> prefixes ! i}"
  shows "\<forall>i<length weights.
      0 < comma_python_affine_denominator (weights ! i) \<and>
      comma_python_affine_divides (weights ! i) S \<and>
      int (prefixes ! i) =
        comma_python_affine_evaluate (weights ! i) S"
    "comma_prefix_lower_bound (length prefixes - 2) prefixes target
      1 (length prefixes - 1) = first"
    "1 \<le> first"
    "prefixes ! (first - 1) < target"
    "target \<le> prefixes ! first"
    "first < length weights"
    "first - 1 < length fragments"
proof -
  have lengths:
    "length weights = Suc (length fragments)"
    "length prefixes = Suc (length fragments)"
    by (simp_all add: weights_def prefixes_def
        comma_python_publish_fragments_def
        comma_python_affine_prefix_scan_length)
  have initial_weight:
    "weights ! 0 = comma_python_affine_zero"
    by (simp add: weights_def comma_python_publish_fragments_def
        comma_python_affine_prefix_scan.simps)
  have initial: "prefixes ! 0 = 0"
    using initial_weight
    by (simp add: prefixes_def comma_python_affine_zero_def
        comma_python_affine_evaluate_def)
  have length: "1 < length prefixes"
    using nonempty lengths by (cases fragments) auto
  have final: "target \<le> prefixes ! (length prefixes - 1)"
    using requested(2) by arith
  have monotone_positive_index: "\<And>i j. 1 \<le> i \<Longrightarrow>
      i \<le> j \<Longrightarrow> j < length prefixes \<Longrightarrow>
      prefixes ! i \<le> prefixes ! j"
    using monotone by blast
  have first_eq: "first = Min {i. 1 \<le> i \<and> i < length prefixes \<and>
      target \<le> prefixes ! i}"
    by (simp add: first_def)
  have search:
    "comma_prefix_lower_bound (length prefixes - 2) prefixes target
      1 (length prefixes - 1) = first"
    "1 \<le> first"
    "first < length prefixes"
    "target \<le> prefixes ! first"
    "prefixes ! (first - 1) < target"
    using comma_prefix_search_first_crossing
      [OF length requested(1) initial final monotone_positive_index]
      first_eq
    by (simp_all only: first_eq)
  show evaluations:
    "\<forall>i<length weights.
      0 < comma_python_affine_denominator (weights ! i) \<and>
      comma_python_affine_divides (weights ! i) S \<and>
      int (prefixes ! i) =
        comma_python_affine_evaluate (weights ! i) S"
  proof (intro allI impI)
    fix i assume i: "i < length weights"
    have valid: "0 < comma_python_affine_denominator (weights ! i) \<and>
        comma_python_affine_divides (weights ! i) S"
      by (rule evaluable[OF i])
    have nonneg: "0 \<le> comma_python_affine_evaluate (weights ! i) S"
      by (rule nonnegative[OF i])
    show "0 < comma_python_affine_denominator (weights ! i) \<and>
        comma_python_affine_divides (weights ! i) S \<and>
        int (prefixes ! i) =
        comma_python_affine_evaluate (weights ! i) S"
      using valid nonneg by (simp add: prefixes_def)
  qed
  show "comma_prefix_lower_bound (length prefixes - 2) prefixes target
      1 (length prefixes - 1) = first"
    using search(1) .
  show "1 \<le> first" using search(2) .
  show "prefixes ! (first - 1) < target"
    using search(5) .
  show "target \<le> prefixes ! first"
    using search(4) .
  show "first < length weights"
    using search(3) lengths by simp
  show "first - 1 < length fragments"
    using search(2,3) lengths by arith
qed

lemmas comma_python_producer_trace_bridge_oracle_audit_bundle =
  comma_python_fragment_record_affine_bridge
  comma_python_writer_edge_affine_chunk
  comma_python_first_terminal_walk_affine_writer
  comma_python_point_selected_prefix_interval
  comma_python_point_entry_partial_divmod_guard
  comma_python_point_near_partial_literal_guard
  comma_python_point_entry_partial_refines_chart_fragment
  comma_python_published_prefix_binary_search_contract
  comma_python_affine_equivalent_transfers_exact_division
ML \<open>val _ = if null (Thm_Deps.all_oracles
  @{thms comma_python_producer_trace_bridge_oracle_audit_bundle}) then ()
  else error "Comma_Semantic_Producer_Trace_Bridge local oracle audit failed"\<close>

end
