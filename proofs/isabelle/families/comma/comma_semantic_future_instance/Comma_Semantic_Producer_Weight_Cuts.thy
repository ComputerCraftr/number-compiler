theory Comma_Semantic_Producer_Weight_Cuts
  imports Comma_Semantic_Producer_Cut_Refinement
begin

text \<open>Each published fragment prefix ends at an actual event cut in the
first-terminal walk.  A pending Near fragment accounts for the suffix of
events since the preceding published cut; when it is flushed, that cut becomes
visible in the published arrays.\<close>

fun comma_python_event_successor ::
  "comma_python_producer_event \<Rightarrow> comma_finite_position" where
  "comma_python_event_successor (Comma_Python_Advance source successor weight) =
    successor"

definition comma_python_event_prefix_endpoint ::
  "comma_finite_position \<Rightarrow> comma_python_producer_event list \<Rightarrow>
    nat \<Rightarrow> comma_finite_position" where
  "comma_python_event_prefix_endpoint origin events k =
    foldl (\<lambda>position event. comma_python_event_successor event)
      origin (take k events)"

definition comma_python_event_weight_prefix ::
  "nat \<Rightarrow> comma_python_producer_event list \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_event_weight_prefix p events k =
    sum_list (map (\<lambda>event. int (fst (comma_python_event_row p event)))
      (take k events))"

definition comma_python_event_displacement_prefix ::
  "nat \<Rightarrow> comma_python_producer_event list \<Rightarrow> nat \<Rightarrow> int" where
  "comma_python_event_displacement_prefix p events k =
    sum_list (map (snd \<circ> comma_python_event_row p) (take k events))"

definition comma_python_fragment_event_count ::
  "comma_python_sector_fragment \<Rightarrow> nat" where
  "comma_python_fragment_event_count fragment =
    (if comma_python_fragment_literal_steps fragment = 0 then 1
     else comma_python_fragment_literal_steps fragment)"

definition comma_python_fragment_event_cut ::
  "comma_python_sector_fragment list \<Rightarrow> nat \<Rightarrow> nat" where
  "comma_python_fragment_event_cut fragments i =
    sum_list (map comma_python_fragment_event_count (take i fragments))"

lemma comma_python_event_prefix_endpoint_append:
  assumes index: "i \<le> length events"
  shows "comma_python_event_prefix_endpoint origin (events @ [event]) i =
    comma_python_event_prefix_endpoint origin events i"
    and "comma_python_event_prefix_endpoint origin (events @ [event])
      (Suc (length events)) = comma_python_event_successor event"
  using index
  by (simp_all add: comma_python_event_prefix_endpoint_def)

lemma comma_python_event_weight_prefix_append:
  assumes index: "i \<le> length events"
  shows "comma_python_event_weight_prefix p (events @ [event]) i =
      comma_python_event_weight_prefix p events i"
    and "comma_python_event_weight_prefix p (events @ [event])
      (Suc (length events)) =
      comma_python_event_weight_prefix p events (length events) +
        int (fst (comma_python_event_row p event))"
  using index
  by (simp_all add: comma_python_event_weight_prefix_def)

lemma comma_python_event_displacement_prefix_append:
  assumes index: "i \<le> length events"
  shows "comma_python_event_displacement_prefix p (events @ [event]) i =
      comma_python_event_displacement_prefix p events i"
    and "comma_python_event_displacement_prefix p (events @ [event])
      (Suc (length events)) =
      comma_python_event_displacement_prefix p events (length events) +
        snd (comma_python_event_row p event)"
  using index
  by (simp_all add: comma_python_event_displacement_prefix_def)

lemma comma_python_event_prefix_endpoint_displacement:
  assumes path: "comma_python_first_terminal_walk p origin events outcome terminal"
    and index: "i \<le> length events"
  shows "comma_python_event_displacement_prefix p events i =
    int (comma_chart_value p
      (comma_python_event_prefix_endpoint origin events i)) -
    int (comma_chart_value p origin)"
using path index
proof (induction arbitrary: i rule: comma_python_first_terminal_walk.induct)
  case (fork p source a delta)
  then show ?case
    by (simp add: comma_python_event_displacement_prefix_def
        comma_python_event_prefix_endpoint_def)
next
  case (landmine p source delta)
  then show ?case
    by (simp add: comma_python_event_displacement_prefix_def
        comma_python_event_prefix_endpoint_def)
next
  case (advance p source successor weight events outcome terminal)
  then show ?case
  proof (cases i)
    case 0
    then show ?thesis
      by (simp add: comma_python_event_displacement_prefix_def
          comma_python_event_prefix_endpoint_def)
  next
    case (Suc j)
    have j: "j \<le> length events" using advance.prems Suc by simp
    have suffix:
      "comma_python_event_displacement_prefix p events j =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint successor events j)) -
        int (comma_chart_value p successor)"
      by (rule advance.IH[OF j])
    show ?thesis using suffix Suc
      by (simp add: comma_python_event_displacement_prefix_def
          comma_python_event_prefix_endpoint_def)
  qed
qed

definition comma_python_writer_weight_cut_state ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_producer_event list \<Rightarrow> comma_python_sector_fragment list \<Rightarrow>
    comma_python_sector_fragment option \<Rightarrow> bool"
where
  "comma_python_writer_weight_cut_state p origin source events fragments pending \<longleftrightarrow>
    comma_python_event_prefix_endpoint origin events (length events) = source \<and>
    (\<forall>i\<le>length fragments.
      let k = comma_python_fragment_event_cut fragments i in
      k \<le> length events \<and>
      sum_list (map (\<lambda>fragment.
          comma_python_fragment_weight_at_scale fragment (10 ^ p))
        (take i fragments)) =
        comma_python_event_weight_prefix p events k \<and>
      sum_list (map (\<lambda>fragment.
          comma_python_fragment_displacement_at_scale fragment (10 ^ p))
        (take i fragments)) =
        comma_python_event_displacement_prefix p events k) \<and>
    length events = comma_python_fragment_event_cut fragments (length fragments) +
      (case pending of None \<Rightarrow> 0
       | Some fragment \<Rightarrow> comma_python_fragment_event_count fragment) \<and>
    comma_python_pending_weight_at_scale pending (10 ^ p) =
      sum_list (map (\<lambda>event. int (fst (comma_python_event_row p event)))
        (drop (comma_python_fragment_event_cut fragments (length fragments)) events)) \<and>
    comma_python_pending_displacement_at_scale pending (10 ^ p) =
      sum_list (map (snd \<circ> comma_python_event_row p)
        (drop (comma_python_fragment_event_cut fragments (length fragments)) events))"

lemma comma_python_writer_weight_cut_state_edge:
  assumes state:
      "comma_python_writer_weight_cut_state p origin source events fragments pending"
    and phase: "comma_python_pending_phase p source pending"
    and step: "comma_weighted_step (p mod 924) source =
      Comma_WNext successor weight"
    and edge: "comma_python_writer_edge p source successor weight pending
      emitted pending'"
  shows "comma_python_writer_weight_cut_state p origin successor
      (events @ [Comma_Python_Advance source successor weight])
      (fragments @ emitted) pending'"
proof -
  note accounting = comma_python_writer_edge_accounting[OF edge]
  show ?thesis
  using state phase step edge accounting
proof (induction rule: comma_python_writer_edge.induct)
  case (entry p f delta offset headroom weight pending)
  then show ?case
    by (auto simp: comma_python_writer_weight_cut_state_def
        comma_python_fragment_event_cut_def comma_python_fragment_event_count_def
        comma_python_event_prefix_endpoint_def comma_python_event_weight_prefix_def
        comma_python_event_displacement_prefix_def comma_python_event_successor.simps
        comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def comma_python_flush_near_def
        accounting
        comma_python_fragment_record_matches_def
        comma_python_entry_sector_fragment_def Let_def
        comma_python_pending_phase_def split: option.splits if_splits)
next
  case (near_start p f delta headroom next_headroom weight increment)
  then show ?case
    by (auto simp: comma_python_writer_weight_cut_state_def
        comma_python_fragment_event_cut_def comma_python_fragment_event_count_def
        comma_python_event_prefix_endpoint_def comma_python_event_weight_prefix_def
        comma_python_event_displacement_prefix_def comma_python_event_successor.simps
        comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def comma_python_flush_near_def
        accounting
        comma_python_fragment_record_matches_def comma_python_literal_fragment_def
        comma_python_pending_phase_def sum_list_append split: option.splits if_splits)
next
  case (near_merge pending_fragment p f delta headroom next_headroom weight
      increment)
  then show ?case
    by (auto simp: comma_python_writer_weight_cut_state_def
        comma_python_fragment_event_cut_def comma_python_fragment_event_count_def
        comma_python_event_prefix_endpoint_def comma_python_event_weight_prefix_def
        comma_python_event_displacement_prefix_def comma_python_event_successor.simps
        comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def comma_python_flush_near_def
        accounting
        comma_python_fragment_record_matches_def comma_python_literal_fragment_def
        comma_python_merge_near_fragments_def comma_python_pending_phase_def
        comma_python_near_fragment_shape_def sum_list_append split: option.splits if_splits)
next
  case (near_cross p f delta headroom g next_delta offset weight pending increment)
  then show ?case
    by (auto simp: comma_python_writer_weight_cut_state_def
        comma_python_fragment_event_cut_def comma_python_fragment_event_count_def
        comma_python_event_prefix_endpoint_def comma_python_event_weight_prefix_def
        comma_python_event_displacement_prefix_def comma_python_event_successor.simps
        comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def comma_python_flush_near_def
        accounting
        comma_python_fragment_record_matches_def comma_python_literal_fragment_def
        comma_python_pending_phase_def sum_list_append split: option.splits if_splits)
qed
qed

lemma comma_python_writer_weight_cut_state_flush:
  assumes state:
    "comma_python_writer_weight_cut_state p origin source events fragments
      (Some pending)"
  shows "comma_python_writer_weight_cut_state p origin source events
      (fragments @ [pending]) None"
  using state
  by (auto simp: comma_python_writer_weight_cut_state_def
      comma_python_fragment_event_cut_def comma_python_fragment_event_count_def
      comma_python_event_weight_prefix_def comma_python_event_displacement_prefix_def
      comma_python_pending_weight_at_scale_def
      comma_python_pending_displacement_at_scale_def
      comma_python_fragment_list_weight_at_scale_def
      comma_python_fragment_list_displacement_at_scale_def
      comma_python_flush_near_def sum_list_append)

lemma comma_python_first_terminal_walk_writer_weight_cut_state:
  fixes p :: nat
  assumes exponent: "5 \<le> p"
    and walk:
      "comma_python_first_terminal_walk p source events outcome terminal"
    and admitted: "comma_round_admitted source"
    and phase: "comma_python_pending_phase p source pending"
    and state:
      "comma_python_writer_weight_cut_state p origin source past fragments pending"
    and link: "comma_python_writer_boundary_link p source pending boundary"
    and cuts: "comma_python_cut_boundaries p origin fragments boundaries"
    and boundary: "boundary = last boundaries"
  obtains suffix_fragments suffix_bounds where
    run: "comma_python_writer_run p source pending events outcome terminal
      suffix_fragments"
    and suffix_cuts:
      "comma_python_cut_boundaries p boundary suffix_fragments suffix_bounds"
    and guards: "\<forall>g\<in>set suffix_fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    and final_state:
      "comma_python_writer_weight_cut_state p origin terminal
        (past @ events) (fragments @ suffix_fragments) None"
    and combined_cuts:
      "comma_python_cut_boundaries p origin (fragments @ suffix_fragments)
        (boundaries @ tl suffix_bounds)"
  using walk exponent admitted phase state link cuts boundary
proof (induction arbitrary: origin past fragments boundaries pending boundary
    rule: comma_python_first_terminal_walk.induct)
  case (fork p source a delta)
  show thesis
  proof (cases pending)
    case None
    have boundary_source: "boundary = source"
      using fork.prems(5) None
      by (simp add: comma_python_writer_boundary_link_def)
    have run:
      "comma_python_writer_run p source None [] (Comma_Fork_At a delta)
        source []"
      by (rule comma_python_writer_run.fork[OF fork.hyps(1)]) simp
    have suffix_cuts:
      "comma_python_cut_boundaries p boundary [] [boundary]"
      by (simp add: comma_python_cut_boundaries_def)
    have final_state:
      "comma_python_writer_weight_cut_state p origin source past fragments None"
      using fork.prems(4) .
    have combined_cuts:
      "comma_python_cut_boundaries p origin fragments (boundaries @ tl [boundary])"
      using fork.prems(6) boundary_source boundary
      by simp
    show thesis using run suffix_cuts final_state combined_cuts
      by (rule fork.prems(8)[where suffix_fragments="[]"
          and suffix_bounds="[boundary]"]) simp_all
  next
    case (Some pending_fragment)
    have run:
      "comma_python_writer_run p source (Some pending_fragment) []
        (Comma_Fork_At a delta) source [pending_fragment]"
      by (rule comma_python_writer_run.fork[OF fork.hyps(1)])
        (simp add: comma_python_flush_near_def)
    have local_cuts:
      "comma_python_cut_boundaries p boundary [pending_fragment]
        [boundary, source]"
      using fork.prems(5) Some
      by (auto simp: comma_python_writer_boundary_link_def
          comma_python_cut_boundaries_def comma_python_fragment_near_cut_def)
    have final_state:
      "comma_python_writer_weight_cut_state p origin source past
        (fragments @ [pending_fragment]) None"
      by (rule comma_python_writer_weight_cut_state_flush[OF fork.prems(4)])
    have combined_cuts:
      "comma_python_cut_boundaries p origin (fragments @ [pending_fragment])
        (boundaries @ tl [boundary, source])"
      using comma_python_cut_boundaries_append[OF fork.prems(6) local_cuts]
        fork.prems(6) boundary by simp
    show thesis using run local_cuts final_state combined_cuts
      by (rule fork.prems(8)[where suffix_fragments="[pending_fragment]"
          and suffix_bounds="[boundary, source]"]) simp_all
  qed
next
  case (landmine p source delta)
  show thesis
  proof (cases pending)
    case None
    have boundary_source: "boundary = source"
      using landmine.prems(5) None
      by (simp add: comma_python_writer_boundary_link_def)
    have run:
      "comma_python_writer_run p source None [] (Comma_Landmine_At delta)
        source []"
      by (rule comma_python_writer_run.landmine[OF landmine.hyps(1)]) simp
    have suffix_cuts:
      "comma_python_cut_boundaries p boundary [] [boundary]"
      using boundary_source by (simp add: comma_python_cut_boundaries_def)
    have final_state:
      "comma_python_writer_weight_cut_state p origin source past fragments None"
      using landmine.prems(4) .
    have combined_cuts:
      "comma_python_cut_boundaries p origin fragments (boundaries @ tl [boundary])"
      using landmine.prems(6) boundary_source boundary by simp
    show thesis using run suffix_cuts final_state combined_cuts
      by (rule landmine.prems(8)[where suffix_fragments="[]"
          and suffix_bounds="[boundary]"]) simp_all
  next
    case (Some pending_fragment)
    have run:
      "comma_python_writer_run p source (Some pending_fragment) []
        (Comma_Landmine_At delta) source [pending_fragment]"
      by (rule comma_python_writer_run.landmine[OF landmine.hyps(1)])
        (simp add: comma_python_flush_near_def)
    have local_cuts:
      "comma_python_cut_boundaries p boundary [pending_fragment]
        [boundary, source]"
      using landmine.prems(5) Some
      by (auto simp: comma_python_writer_boundary_link_def
          comma_python_cut_boundaries_def comma_python_fragment_near_cut_def)
    have final_state:
      "comma_python_writer_weight_cut_state p origin source past
        (fragments @ [pending_fragment]) None"
      by (rule comma_python_writer_weight_cut_state_flush[OF landmine.prems(4)])
    have combined_cuts:
      "comma_python_cut_boundaries p origin (fragments @ [pending_fragment])
        (boundaries @ tl [boundary, source])"
      using comma_python_cut_boundaries_append[OF landmine.prems(6) local_cuts]
        landmine.prems(6) boundary by simp
    show thesis using run local_cuts final_state combined_cuts
      by (rule landmine.prems(8)[where suffix_fragments="[pending_fragment]"
          and suffix_bounds="[boundary, source]"]) simp_all
  qed
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
    and next_phase: "comma_python_pending_phase p successor next_pending"
    using comma_python_writer_edge_exists
      [OF advance.prems(1) advance.prems(2) advance.prems(3)
        advance.hyps(1)] by blast
  obtain next_boundary local_bounds where next_link:
      "comma_python_writer_boundary_link p successor next_pending next_boundary"
    and local_cuts:
      "comma_python_cut_boundaries p boundary emitted local_bounds"
    and next_eq: "next_boundary = last local_bounds"
    using comma_python_writer_edge_boundary_cuts
      [OF advance.prems(1) advance.prems(2) advance.prems(3)
        advance.prems(5) edge] by blast
  have state':
    "comma_python_writer_weight_cut_state p origin successor
      (past @ [Comma_Python_Advance source successor weight])
      (fragments @ emitted) next_pending"
    by (rule comma_python_writer_weight_cut_state_edge
      [OF advance.prems(4) advance.prems(3) advance.hyps(1) edge])
  have cuts':
    "comma_python_cut_boundaries p origin (fragments @ emitted)
      (boundaries @ tl local_bounds)"
    by (rule comma_python_cut_boundaries_append
      [OF advance.prems(6) local_cuts])
      (simp add: advance.prems(6) advance.prems(7))
  have next_boundary':
    "next_boundary = last (boundaries @ tl local_bounds)"
  proof -
    have local_length:
      "length local_bounds = Suc (length emitted)"
      by (rule comma_python_cut_boundaries_length[OF local_cuts])
    have bounds_nonempty: "boundaries \<noteq> []"
      using comma_python_cut_boundaries_length[OF advance.prems(6)]
      by (cases boundaries) auto
    show ?thesis using next_eq local_length bounds_nonempty
      by (simp add: boundary)
  qed
  obtain suffix_fragments suffix_bounds where tail_run:
      "comma_python_writer_run p successor next_pending events outcome terminal
        suffix_fragments"
    and tail_cuts:
      "comma_python_cut_boundaries p next_boundary suffix_fragments suffix_bounds"
    and tail_guards: "\<forall>g\<in>set suffix_fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    and tail_state:
      "comma_python_writer_weight_cut_state p origin terminal
        ((past @ [Comma_Python_Advance source successor weight]) @ events)
        ((fragments @ emitted) @ suffix_fragments) None"
    and tail_combined_cuts:
      "comma_python_cut_boundaries p origin
        ((fragments @ emitted) @ suffix_fragments)
        ((boundaries @ tl local_bounds) @ tl suffix_bounds)"
    using advance.IH[OF advance.prems(1) successor_admitted next_phase state'
      next_link cuts' next_boundary'] by blast
  have run:
    "comma_python_writer_run p source pending
      (Comma_Python_Advance source successor weight # events) outcome terminal
      (emitted @ suffix_fragments)"
    by (rule comma_python_writer_run.advance
      [OF advance.hyps(1) edge tail_run])
  have suffix_cuts:
    "comma_python_cut_boundaries p boundary (emitted @ suffix_fragments)
      (local_bounds @ tl suffix_bounds)"
    by (rule comma_python_cut_boundaries_append[OF local_cuts])
      (simp add: next_eq tail_cuts)
  have combined_cuts:
    "comma_python_cut_boundaries p origin
      (fragments @ (emitted @ suffix_fragments))
      (boundaries @ tl (local_bounds @ tl suffix_bounds))"
    using tail_combined_cuts by simp
  have final_state:
    "comma_python_writer_weight_cut_state p origin terminal
      (past @ (Comma_Python_Advance source successor weight # events))
      (fragments @ (emitted @ suffix_fragments)) None"
    using tail_state by simp
  have guards:
    "\<forall>g\<in>set (emitted @ suffix_fragments).
      comma_python_fragment_scale_guard g (10 ^ p)"
  proof -
    have emitted_guards:
      "\<forall>g\<in>set emitted.
        comma_python_fragment_scale_guard g (10 ^ p)"
      by (rule comma_python_writer_edge_emitted_scale_guards
        [OF advance.prems(1) advance.prems(2) advance.prems(3) edge])
    show ?thesis using emitted_guards tail_guards by auto
  qed
  show thesis using run suffix_cuts guards final_state combined_cuts
    by (rule advance.prems(8)[where suffix_fragments="emitted @ suffix_fragments"
        and suffix_bounds="local_bounds @ tl suffix_bounds"])
      (simp_all add: append.assoc)
qed

theorem comma_python_actual_writer_event_weight_prefix_cuts:
  fixes p :: nat
  assumes exponent: "5 \<le> p"
    and walk:
      "comma_python_first_terminal_walk p source events outcome terminal"
    and admitted: "comma_round_admitted source"
  obtains fragments boundaries where
    run: "comma_python_writer_run p source None events outcome terminal fragments"
    and aligned: "comma_python_cut_boundaries p source fragments boundaries"
    and guards: "\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    and published_weight_prefix:
      "\<forall>i\<le>length fragments.
        comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        comma_python_event_weight_prefix p events
          (comma_python_fragment_event_cut fragments i)"
    and actual_boundary_value:
      "\<forall>i\<le>length fragments.
        int (comma_chart_value p (boundaries ! i)) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events
            (comma_python_fragment_event_cut fragments i)))"
proof -
  have phase: "comma_python_pending_phase p source None"
    by (simp add: comma_python_pending_phase_def)
  have state:
    "comma_python_writer_weight_cut_state p source source [] [] None"
    by (simp add: comma_python_writer_weight_cut_state_def
        comma_python_event_prefix_endpoint_def
        comma_python_event_weight_prefix_def
        comma_python_event_displacement_prefix_def
        comma_python_fragment_event_cut_def
        comma_python_pending_weight_at_scale_def
        comma_python_pending_displacement_at_scale_def
        comma_python_fragment_list_weight_at_scale_def
        comma_python_fragment_list_displacement_at_scale_def
        comma_python_flush_near_def)
  have link: "comma_python_writer_boundary_link p source None source"
    by (simp add: comma_python_writer_boundary_link_def)
  have initial_cuts: "comma_python_cut_boundaries p source [] [source]"
    by (simp add: comma_python_cut_boundaries_def)
  obtain fragments raw_boundaries where run:
      "comma_python_writer_run p source None events outcome terminal fragments"
    and cuts:
      "comma_python_cut_boundaries p source fragments raw_boundaries"
    and guards: "\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    and state:
      "comma_python_writer_weight_cut_state p source terminal events
        fragments None"
    using comma_python_first_terminal_walk_writer_weight_cut_state
      [OF exponent walk admitted phase state link initial_cuts] by blast
  have output_cuts:
    "comma_python_cut_boundaries p source fragments raw_boundaries"
    by (rule cuts)
  have weight_prefix:
    "\<forall>i\<le>length fragments.
      comma_python_affine_evaluate
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
      comma_python_event_weight_prefix p events
        (comma_python_fragment_event_cut fragments i)"
  proof (intro allI impI)
    fix i assume index: "i \<le> length fragments"
    have prefix:
      "sum_list (map (\<lambda>fragment.
          comma_python_fragment_weight_at_scale fragment (10 ^ p))
        (take i fragments)) =
        comma_python_event_weight_prefix p events
          (comma_python_fragment_event_cut fragments i)"
      using state index
      by (simp add: comma_python_writer_weight_cut_state_def)
    have published:
      "comma_python_affine_evaluate
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
       sum_list (map (\<lambda>fragment.
          comma_python_fragment_weight_at_scale fragment (10 ^ p))
        (take i fragments))"
      by (rule comma_python_published_prefixes_at_scale(1)[OF guards index])
    show "comma_python_affine_evaluate
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
      comma_python_event_weight_prefix p events
        (comma_python_fragment_event_cut fragments i)"
      using published prefix by simp
  qed
  have boundary_value:
    "\<forall>i\<le>length fragments.
      int (comma_chart_value p (raw_boundaries ! i)) =
      int (comma_chart_value p
        (comma_python_event_prefix_endpoint source events
          (comma_python_fragment_event_cut fragments i)))"
  proof (intro allI impI)
    fix i assume index: "i \<le> length fragments"
    let ?k = "comma_python_fragment_event_cut fragments i"
    have cut_weight:
      "sum_list (map (\<lambda>fragment.
          comma_python_fragment_displacement_at_scale fragment (10 ^ p))
        (take i fragments)) =
        comma_python_event_displacement_prefix p events ?k"
      using state index
      by (simp add: comma_python_writer_weight_cut_state_def)
    have telescope:
      "sum_list (map (\<lambda>fragment.
          comma_python_fragment_displacement_at_scale fragment (10 ^ p))
        (take i fragments)) =
        int (comma_chart_value p (raw_boundaries ! i)) -
          int (comma_chart_value p source)"
      by (rule comma_python_cut_boundaries_telescope[OF cuts index])
    have endpoint:
      "comma_python_event_displacement_prefix p events ?k =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events ?k)) -
          int (comma_chart_value p source)"
      using comma_python_event_prefix_endpoint_displacement[OF walk]
        state index
      by (simp add: comma_python_writer_weight_cut_state_def)
    show "int (comma_chart_value p (raw_boundaries ! i)) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events ?k))"
      using cut_weight telescope endpoint by linarith
  qed
  show thesis using run output_cuts guards weight_prefix boundary_value
    by (rule that[where fragments=fragments and boundaries=raw_boundaries])
      simp_all
qed

lemmas comma_python_producer_weight_cuts_oracle_audit_bundle =
  comma_python_event_prefix_endpoint_displacement
  comma_python_writer_weight_cut_state_edge
  comma_python_writer_weight_cut_state_flush
  comma_python_first_terminal_walk_writer_weight_cut_state
  comma_python_actual_writer_event_weight_prefix_cuts

ML \<open>val _ = if null (Thm_Deps.all_oracles
  @{thms comma_python_producer_weight_cuts_oracle_audit_bundle}) then ()
  else error "Comma_Semantic_Producer_Weight_Cuts local oracle audit failed"\<close>

end
