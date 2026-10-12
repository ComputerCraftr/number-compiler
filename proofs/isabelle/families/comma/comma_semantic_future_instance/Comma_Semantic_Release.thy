theory Comma_Semantic_Release
  imports Comma_Semantic_Producer_Partial_Selection
    Comma_Python_Chart_Refinement
    Comma_Python_Grouped_Chart_Refinement
    Comma_Semantic_Global_Safety
    Comma_Semantic_B1_Instance.Comma_Semantic_Summary_Instance
begin

text \<open>
This is the concrete bridge from the checked B32 decade summary to the
producer record writer.  It selects the summary at the requested admitted
phase and then obtains one shared event walk and fragment list carrying the
writer relation, exact accounting, and every published prefix equation.
The existential outputs are deliberately kept together: downstream consumers
must not combine fragment witnesses from separate existential theorems.
\<close>

lemma comma_python_writer_edge_outputs_unique:
  assumes left:
      "comma_python_writer_edge p source successor weight pending
        emitted_left pending_left"
    and right:
      "comma_python_writer_edge p source successor weight pending
        emitted_right pending_right"
  shows "emitted_left = emitted_right \<and>
    pending_left = pending_right"
  using left right
  by (cases rule: comma_python_writer_edge.cases;
      cases rule: comma_python_writer_edge.cases;
      auto simp: comma_python_flush_near_def
        comma_python_near_fragments_compatible_def
        comma_python_merge_near_fragments_def
        comma_python_fragment_record_matches_def
        comma_python_literal_fragment_def
        split: option.splits comma_finite_position.splits)

lemma comma_python_first_terminal_walk_result_unique:
  assumes left:
      "comma_python_first_terminal_walk p source events_left outcome
        terminal_left"
    and right:
      "comma_python_first_terminal_walk p source events_right outcome
        terminal_right"
  shows "events_left = events_right \<and> terminal_left = terminal_right"
  using left right
proof (induction arbitrary: events_right terminal_right
    rule: comma_python_first_terminal_walk.induct)
  case (fork p source a delta)
  then show ?case
    by (cases rule: comma_python_first_terminal_walk.cases) auto
next
  case (landmine p source delta)
  then show ?case
    by (cases rule: comma_python_first_terminal_walk.cases) auto
next
  case (advance p source successor weight events outcome terminal)
  then obtain successor' weight' events' where step':
      "comma_weighted_step (p mod 924) source = Comma_WNext successor' weight'"
    and tail':
      "comma_python_first_terminal_walk p successor' events' outcome
        terminal_right"
    and right_events:
      "events_right =
        Comma_Python_Advance source successor' weight' # events'"
    by (cases rule: comma_python_first_terminal_walk.cases) auto
  have step_fields: "successor'=successor" "weight'=weight"
    using step' advance.hyps(1) by auto
  have tail:
      "comma_python_first_terminal_walk p successor events' outcome
        terminal_right"
    using tail' step_fields by simp
  have tail_eq: "events = events' \<and> terminal = terminal_right"
    by (rule advance.IH[OF tail])
  show ?case using right_events step_fields tail_eq by simp
qed

text \<open>The executable boundary chart starts at Near for an N move and
Entry for a Z move.  This bridge proves structural termination for those exact
ungrouped chart starts.  The first round handles every admitted leading digit;
if it crosses 9 to 1, the checked B32 summary supplies the remaining finite
walk.  This is a termination witness, not a numeric bound on the legacy fuel
cap.\<close>

definition comma_python_boundary_chart_initial ::
  "bool \<Rightarrow> nat \<Rightarrow> comma_finite_position" where
  "comma_python_boundary_chart_initial near a =
    (if near then Comma_Near (a - 1) 0 1 else Comma_Entry a 0 0)"

theorem comma_semantic_b32_boundary_chart_loop_structurally_terminates:
  fixes p a :: nat and near :: bool
  assumes exponent: "5 \<le> p"
    and leading_lower: "2 \<le> a"
    and leading_upper: "a \<le> 9"
  shows "\<exists>events outcome terminal.
    comma_python_first_terminal_walk p
      (comma_python_boundary_chart_initial near a) events outcome terminal \<and>
    (\<exists>rows. comma_indexed_trace p
        (comma_python_boundary_chart_initial near a) rows outcome terminal \<and>
      comma_refined_indexed_trace p
        (comma_python_boundary_chart_initial near a) rows outcome terminal) \<and>
    comma_semantic_boundary_step comma_semantic_decade_summary
      ((if near then Comma_N else Comma_Z), a, p mod 924) = Some outcome"
proof -
  let ?q = "((if near then Comma_N else Comma_Z), a, p mod 924)"
  have valid: "comma_boundary_valid ?q"
    using leading_lower leading_upper
    by (simp add: comma_boundary_valid_def)
  have phase: "p mod 924 = snd (snd ?q)" by simp
  have initial: "comma_finite_initial ?q =
      comma_python_boundary_chart_initial near a"
    by (cases near)
      (simp_all add: comma_finite_initial_def
        comma_python_boundary_chart_initial_def)
  obtain rows outcome terminal where trace:
      "comma_indexed_trace p (comma_finite_initial ?q) rows outcome terminal"
    and selected:
      "comma_semantic_boundary_step comma_semantic_decade_summary ?q =
        Some outcome"
    using comma_python_boundary_indexed_trace
      [OF comma_semantic_decade_summary_provider_exact valid exponent phase]
    by blast
  obtain events where walk:
      "comma_python_first_terminal_walk p (comma_finite_initial ?q)
        events outcome terminal"
    using comma_indexed_trace_to_python_first_terminal_walk[OF trace]
    by blast
  have refined:
      "comma_refined_indexed_trace p (comma_finite_initial ?q)
        rows outcome terminal"
    using comma_indexed_trace_is_refined[OF exponent trace] .
  show ?thesis using walk trace refined selected initial by blast
qed

theorem comma_semantic_b32_scalar_chart_terminates:
  fixes p a :: nat and near :: bool
  assumes exponent: "5 \<le> p"
    and lower: "2 \<le> a" and upper: "a \<le> 9"
  shows "\<exists>moves outcome terminal.
    comma_python_scalar_chart_walk p
      (comma_python_boundary_chart_initial near a) moves outcome terminal \<and>
    comma_semantic_boundary_step comma_semantic_decade_summary
      ((if near then Comma_N else Comma_Z), a, p mod 924) = Some outcome"
proof -
  obtain events outcome terminal where walk:
      "comma_python_first_terminal_walk p
        (comma_python_boundary_chart_initial near a) events outcome terminal"
    and selected:
      "comma_semantic_boundary_step comma_semantic_decade_summary
        ((if near then Comma_N else Comma_Z), a, p mod 924) = Some outcome"
    using comma_semantic_b32_boundary_chart_loop_structurally_terminates
      [OF exponent lower upper, of near] by blast
  have admitted: "comma_python_chart_position_admitted
      (comma_python_boundary_chart_initial near a)"
    using comma_python_chart_initial_position_admitted[OF lower upper, of near]
    by (simp only: comma_python_boundary_chart_initial_def)
  obtain moves where scalar:
      "comma_python_scalar_chart_walk p
        (comma_python_boundary_chart_initial near a) moves outcome terminal"
    using comma_python_first_terminal_walk_to_scalar_chart_walk[OF walk]
      exponent admitted by blast
  show ?thesis using scalar selected by blast
qed

theorem comma_semantic_b32_grouped_chart_terminates:
  fixes p a :: nat and near :: bool
  assumes exponent: "5 \<le> p"
    and lower: "2 \<le> a" and upper: "a \<le> 9"
  shows "\<exists>moves outcome terminal.
    comma_python_grouped_chart_walk p
      (comma_python_boundary_chart_initial near a) moves outcome terminal \<and>
    comma_semantic_boundary_step comma_semantic_decade_summary
      ((if near then Comma_N else Comma_Z), a, p mod 924) = Some outcome"
proof -
  obtain scalar_moves outcome terminal where scalar:
      "comma_python_scalar_chart_walk p
        (comma_python_boundary_chart_initial near a) scalar_moves outcome terminal"
    and selected:
      "comma_semantic_boundary_step comma_semantic_decade_summary
        ((if near then Comma_N else Comma_Z), a, p mod 924) = Some outcome"
    using comma_semantic_b32_scalar_chart_terminates
      [OF exponent lower upper, of near] by blast
  have admitted: "comma_python_chart_position_admitted
      (comma_python_boundary_chart_initial near a)"
    using comma_python_chart_initial_position_admitted[OF lower upper, of near]
    by (simp only: comma_python_boundary_chart_initial_def)
  obtain moves where grouped:
      "comma_python_grouped_chart_walk p
        (comma_python_boundary_chart_initial near a) moves outcome terminal"
    using comma_python_grouped_chart_walk_of_scalar[OF scalar exponent admitted]
    by blast
  show ?thesis using grouped selected by blast
qed

lemma comma_python_writer_run_fragments_unique:
  assumes left:
      "comma_python_writer_run p source pending events outcome terminal
        fragments_left"
    and right:
      "comma_python_writer_run p source pending events outcome terminal
        fragments_right"
  shows "fragments_left = fragments_right"
  using left right
proof (induction arbitrary: fragments_right
    rule: comma_python_writer_run.induct)
  case (fork p source a delta pending fragments)
  then show ?case
    by (cases rule: comma_python_writer_run.cases)
      (auto simp: comma_python_flush_near_def)
next
  case (landmine p source delta pending fragments)
  then show ?case
    by (cases rule: comma_python_writer_run.cases)
      (auto simp: comma_python_flush_near_def)
next
  case (advance p source successor weight pending emitted pending'
      events outcome terminal tail_fragments)
  obtain emitted_right pending_right tail_right where right_edge:
      "comma_python_writer_edge p source successor weight pending
        emitted_right pending_right"
    and right_tail:
      "comma_python_writer_run p successor pending_right events outcome terminal
        tail_right"
    and right_output: "fragments_right = emitted_right @ tail_right"
    using advance.prems
    by (cases rule: comma_python_writer_run.cases) auto
  have edge_outputs:
      "emitted = emitted_right \<and> pending' = pending_right"
    by (rule comma_python_writer_edge_outputs_unique
      [OF advance.hyps(2) right_edge])
  have right_tail_fixed:
      "comma_python_writer_run p successor pending' events outcome terminal
        tail_right"
    using right_tail edge_outputs by simp
  have tail_output: "tail_fragments = tail_right"
    by (rule advance.IH[OF right_tail_fixed])
  show ?case using edge_outputs tail_output right_output by simp
qed

definition comma_semantic_decade_writer_release_result where
  "comma_semantic_decade_writer_release_result p x h terminal events
      final_position fragments \<longleftrightarrow>
    comma_semantic_decade_summary (Comma_Decade (p mod 924) x) =
      Some (h, terminal) \<and>
    h \<le> 26 \<and>
    comma_decade_exact_summary (Comma_Decade (p mod 924) x) h terminal \<and>
    comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
      (comma_summary_outcome h terminal)
      (comma_shift_position h final_position) \<and>
    comma_python_writer_run p (Comma_Entry 1 0 x) None events
      (comma_summary_outcome h terminal)
      (comma_shift_position h final_position) fragments \<and>
    comma_python_fragment_list_weight_at_scale fragments (10 ^ p) =
      sum_list (map (\<lambda>event.
        int (fst (comma_python_event_row p event))) events) \<and>
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
          (map comma_python_fragment_displacement_affine
            (take i fragments)))"

definition comma_semantic_decade_partial_selection_result where
  "comma_semantic_decade_partial_selection_result p x target h terminal
      events final fragments boundaries weights prefixes i \<longleftrightarrow>
    comma_semantic_decade_writer_release_result p x h terminal events final
      fragments \<and>
    comma_python_cut_boundaries p (Comma_Entry 1 0 x) fragments boundaries \<and>
    weights = comma_python_published_weights
      (comma_python_publish_fragments fragments) \<and>
    length weights = Suc (length fragments) \<and>
    prefixes = map (\<lambda>w.
      nat (comma_python_affine_evaluate w (10 ^ p))) weights \<and>
    length prefixes = Suc (length fragments) \<and>
    length (comma_python_published_displacements
      (comma_python_publish_fragments fragments)) = Suc (length fragments) \<and>
    (\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)) \<and>
    (\<forall>j\<le>length fragments.
      0 < comma_python_affine_denominator (weights ! j) \<and>
      comma_python_affine_divides (weights ! j) (10 ^ p)) \<and>
    i < length fragments \<and>
    prefixes ! Suc i = prefixes ! i +
      nat (comma_python_fragment_weight_at_scale (fragments ! i) (10 ^ p)) \<and>
    comma_python_fragment_event_cut fragments (Suc i) =
      comma_python_fragment_event_cut fragments i +
        comma_python_fragment_event_count (fragments ! i) \<and>
    comma_prefix_lower_bound (length prefixes - 2) prefixes target
      1 (length prefixes - 1) = Suc i \<and>
    prefixes ! i < target \<and>
    target \<le> prefixes ! Suc i \<and>
    int (prefixes ! i) = comma_python_event_weight_prefix p events
      (comma_python_fragment_event_cut fragments i) \<and>
    int (prefixes ! Suc i) = comma_python_event_weight_prefix p events
      (comma_python_fragment_event_cut fragments (Suc i)) \<and>
    int (comma_chart_value p (boundaries ! i)) = int (comma_chart_value p
      (comma_python_event_prefix_endpoint (Comma_Entry 1 0 x) events
        (comma_python_fragment_event_cut fragments i))) \<and>
    int (comma_chart_value p (boundaries ! Suc i)) = int (comma_chart_value p
      (comma_python_event_prefix_endpoint (Comma_Entry 1 0 x) events
        (comma_python_fragment_event_cut fragments (Suc i))) \<and>
    (\<forall>j\<le>length fragments.
      0 < comma_python_affine_denominator
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! j) \<and>
      comma_python_affine_divides
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! j) (10 ^ p)) \<and>
    (\<forall>j\<le>length fragments.
      comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! j) (10 ^ p) =
      int (comma_chart_value p
        (comma_python_event_prefix_endpoint (Comma_Entry 1 0 x) events
          (comma_python_fragment_event_cut fragments j))) -
        int (comma_chart_value p (Comma_Entry 1 0 x)))"

theorem comma_semantic_decade_summary_writer_release:
  fixes p x :: nat
  assumes admitted:
      "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    and exponent: "5 \<le> p"
  shows "\<exists>h terminal events final_position fragments.
      comma_semantic_decade_writer_release_result p x h terminal events
        final_position fragments"
proof -
  let ?s = "Comma_Decade (p mod 924) x"
  obtain h terminal where summary:
      "comma_semantic_decade_summary ?s = Some (h, terminal)"
    and height: "h \<le> 26"
    and exact: "comma_decade_exact_summary ?s h terminal"
    using comma_semantic_decade_summary_total_exact[OF admitted] by blast
  have binding: "?s = Comma_Decade (p mod 924) x" by simp
  obtain events final_position fragments where producer:
      "comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
        (comma_summary_outcome h terminal)
        (comma_shift_position h final_position)"
      "comma_python_writer_run p (Comma_Entry 1 0 x) None events
        (comma_summary_outcome h terminal)
        (comma_shift_position h final_position) fragments"
      "comma_python_fragment_list_weight_at_scale fragments (10 ^ p) =
        sum_list (map (\<lambda>event.
          int (fst (comma_python_event_row p event))) events)"
      "comma_python_fragment_list_displacement_at_scale fragments (10 ^ p) =
        sum_list (map (snd \<circ> comma_python_event_row p) events)"
      "length (comma_python_published_weights
        (comma_python_publish_fragments fragments)) = Suc (length fragments)"
      "length (comma_python_published_displacements
        (comma_python_publish_fragments fragments)) = Suc (length fragments)"
      "\<forall>i\<le>length fragments.
        comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i =
          foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_weight_affine (take i fragments)) \<and>
        comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i =
          foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_displacement_affine
              (take i fragments))"
    using comma_decade_summary_python_macro_writer_output
      [OF exact admitted exponent binding] by blast
  show ?thesis
    using summary height exact producer
    unfolding comma_semantic_decade_writer_release_result_def
    by blast
qed

theorem comma_semantic_decade_summary_writer_release_closed:
  "\<forall>p x. comma_decade_admitted (Comma_Decade (p mod 924) x) \<longrightarrow>
    5 \<le> p \<longrightarrow>
    (\<exists>h terminal events final fragments.
      comma_semantic_decade_writer_release_result p x h terminal events
        final fragments)"
proof (intro allI impI)
  fix p x
  assume admitted:
      "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    and exponent: "5 \<le> p"
  show "\<exists>h terminal events final fragments.
      comma_semantic_decade_writer_release_result p x h terminal events final
        fragments"
    by (rule comma_semantic_decade_summary_writer_release[OF admitted exponent])
qed

theorem comma_semantic_decade_writer_partial_selection:
  fixes p x target :: nat
  assumes admitted:
      "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    and exponent: "5 \<le> p"
    and requested:
      "\<exists>h terminal events final.
        comma_semantic_decade_summary (Comma_Decade (p mod 924) x) =
          Some (h, terminal) \<and>
        comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
          (comma_summary_outcome h terminal) (comma_shift_position h final) \<and>
        0 < target \<and>
        int target < comma_python_event_weight_prefix p events (length events)"
  shows "\<exists>h terminal events final fragments boundaries weights prefixes i.
      comma_semantic_decade_partial_selection_result p x target h terminal
        events final fragments boundaries weights prefixes i"
proof -
  obtain h terminal events final fragments where release:
      "comma_semantic_decade_writer_release_result p x h terminal events final
        fragments"
    using comma_semantic_decade_summary_writer_release[OF admitted exponent]
    by blast
  have producer:
      "comma_semantic_decade_summary (Comma_Decade (p mod 924) x) =
        Some (h, terminal)"
    and exact: "comma_decade_exact_summary (Comma_Decade (p mod 924) x) h terminal"
    and walk:
      "comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
        (comma_summary_outcome h terminal) (comma_shift_position h final)"
    and writer:
      "comma_python_writer_run p (Comma_Entry 1 0 x) None events
        (comma_summary_outcome h terminal) (comma_shift_position h final)
        fragments"
    using release unfolding comma_semantic_decade_writer_release_result_def
    by blast
  obtain h' terminal' events' final' where selected_request:
      "comma_semantic_decade_summary (Comma_Decade (p mod 924) x) =
        Some (h', terminal')"
    and selected_walk:
      "comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events'
        (comma_summary_outcome h' terminal') (comma_shift_position h' final')"
    and positive: "0 < target"
    and before_terminal:
      "int target < comma_python_event_weight_prefix p events' (length events')"
    using requested by blast
  have selected_summary: "(h, terminal) = (h', terminal')"
    using producer selected_request by simp
  have h_eq: "h = h'" and terminal_eq: "terminal = terminal'"
    using selected_summary by simp_all
  have walk_eq: "events = events' \<and>
      comma_shift_position h final = comma_shift_position h' final'"
    by (rule comma_python_first_terminal_walk_result_unique[OF walk])
      (use selected_walk h_eq terminal_eq in simp)
  have event_eq: "events = events'" using walk_eq by simp
  have round_admitted: "comma_round_admitted (Comma_Entry 1 0 x)"
    using admitted by (simp add: comma_round_admitted.simps comma_decade_admitted.simps)
  have target_bound:
      "int target < comma_python_event_weight_prefix p events (length events)"
    using before_terminal event_eq by simp
  obtain selected_fragments boundaries weights prefixes i where cut:
      "comma_python_writer_run p (Comma_Entry 1 0 x) None events
        (comma_summary_outcome h terminal) (comma_shift_position h final)
        selected_fragments"
    and aligned:
      "comma_python_cut_boundaries p (Comma_Entry 1 0 x)
        selected_fragments boundaries"
    and weight_array:
      "weights = comma_python_published_weights
        (comma_python_publish_fragments selected_fragments)"
    and prefix_array:
      "prefixes = map (\<lambda>w.
        nat (comma_python_affine_evaluate w (10 ^ p))) weights"
    and guards:
      "\<forall>g\<in>set selected_fragments.
        comma_python_fragment_scale_guard g (10 ^ p)"
    and array_guards:
      "\<forall>j\<le>length selected_fragments.
        0 < comma_python_affine_denominator (weights ! j) \<and>
        comma_python_affine_divides (weights ! j) (10 ^ p)"
    and index: "i < length selected_fragments"
    and adjacent:
      "prefixes ! Suc i = prefixes ! i +
        nat (comma_python_fragment_weight_at_scale
          (selected_fragments ! i) (10 ^ p))"
    and event_cut_adjacent:
      "comma_python_fragment_event_cut selected_fragments (Suc i) =
        comma_python_fragment_event_cut selected_fragments i +
          comma_python_fragment_event_count (selected_fragments ! i)"
    and search:
      "comma_prefix_lower_bound (length prefixes - 2) prefixes target
        1 (length prefixes - 1) = Suc i"
    and before: "prefixes ! i < target"
    and after: "target \<le> prefixes ! Suc i"
    and before_weight:
      "int (prefixes ! i) = comma_python_event_weight_prefix p events
        (comma_python_fragment_event_cut selected_fragments i)"
    and after_weight:
      "int (prefixes ! Suc i) = comma_python_event_weight_prefix p events
        (comma_python_fragment_event_cut selected_fragments (Suc i))"
    and before_value:
      "int (comma_chart_value p (boundaries ! i)) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint (Comma_Entry 1 0 x) events
            (comma_python_fragment_event_cut selected_fragments i)))"
    and after_value:
      "int (comma_chart_value p (boundaries ! Suc i)) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint (Comma_Entry 1 0 x) events
            (comma_python_fragment_event_cut selected_fragments (Suc i)))"
    using comma_python_actual_writer_point_at_prefix_cut
      [OF exponent walk round_admitted positive target_bound] by blast
  obtain displacement_fragments where
      displacement_run:
        "comma_python_writer_run p (Comma_Entry 1 0 x) None events
          (comma_summary_outcome h terminal) (comma_shift_position h final)
          displacement_fragments"
    and displacement_array_guards:
      "\<forall>j\<le>length displacement_fragments.
        0 < comma_python_affine_denominator
          (comma_python_published_displacements
            (comma_python_publish_fragments displacement_fragments) ! j) \<and>
        comma_python_affine_divides
          (comma_python_published_displacements
            (comma_python_publish_fragments displacement_fragments) ! j)
          (10 ^ p)"
    and displacement_prefixes:
      "\<forall>j\<le>length displacement_fragments.
        comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments displacement_fragments) ! j)
          (10 ^ p) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint (Comma_Entry 1 0 x) events
            (comma_python_fragment_event_cut displacement_fragments j))) -
        int (comma_chart_value p (Comma_Entry 1 0 x))"
    using comma_python_actual_writer_published_displacement_prefixes
      [OF exponent walk round_admitted] .
  have same_fragments: "fragments = selected_fragments"
    by (rule comma_python_writer_run_fragments_unique[OF writer cut(1)])
  have displacement_same: "selected_fragments = displacement_fragments"
    by (rule comma_python_writer_run_fragments_unique[OF cut(1) displacement_run])
  have weights_length: "length weights = Suc (length selected_fragments)"
    using weight_array by (simp add: comma_python_publish_fragments_def
        comma_python_affine_prefix_scan_length)
  have prefixes_length: "length prefixes = Suc (length selected_fragments)"
    using prefix_array weights_length by simp
  have displacement_length:
      "length (comma_python_published_displacements
        (comma_python_publish_fragments selected_fragments)) =
          Suc (length selected_fragments)"
    by (simp add: comma_python_publish_fragments_def
        comma_python_affine_prefix_scan_length)
  show ?thesis
    unfolding comma_semantic_decade_partial_selection_result_def
    using release aligned weight_array weights_length prefix_array prefixes_length
      displacement_length guards array_guards index adjacent event_cut_adjacent
      search before after before_weight after_weight before_value after_value
      displacement_array_guards displacement_prefixes same_fragments
      displacement_same
    by blast
qed

theorem comma_semantic_decade_writer_partial_selection_closed:
  "\<forall>p x target. comma_decade_admitted (Comma_Decade (p mod 924) x) \<longrightarrow>
    5 \<le> p \<longrightarrow>
    (\<exists>h terminal events final.
      comma_semantic_decade_summary (Comma_Decade (p mod 924) x) =
        Some (h, terminal) \<and>
      comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
        (comma_summary_outcome h terminal) (comma_shift_position h final) \<and>
      0 < target \<and>
      int target < comma_python_event_weight_prefix p events (length events)) \<longrightarrow>
    (\<exists>h terminal events final fragments boundaries weights prefixes i.
      comma_semantic_decade_partial_selection_result p x target h terminal
        events final fragments boundaries weights prefixes i)"
proof (intro allI impI)
  fix p x target
  assume admitted:
      "comma_decade_admitted (Comma_Decade (p mod 924) x)"
    and exponent: "5 \<le> p"
    and requested:
      "\<exists>h terminal events final.
        comma_semantic_decade_summary (Comma_Decade (p mod 924) x) =
          Some (h, terminal) \<and>
        comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
          (comma_summary_outcome h terminal) (comma_shift_position h final) \<and>
        0 < target \<and>
        int target < comma_python_event_weight_prefix p events (length events)"
  show "\<exists>h terminal events final fragments boundaries weights prefixes i.
      comma_semantic_decade_partial_selection_result p x target h terminal
        events final fragments boundaries weights prefixes i"
    by (rule comma_semantic_decade_writer_partial_selection
      [OF admitted exponent requested])
qed

theorem comma_semantic_producer_global_release_contract:
  "(\<forall>p x. comma_decade_admitted (Comma_Decade (p mod 924) x) \<longrightarrow>
      5 \<le> p \<longrightarrow>
      (\<exists>h terminal events final fragments.
        comma_semantic_decade_writer_release_result p x h terminal events final
          fragments)) \<and>
   ((\<forall>p x target. comma_decade_admitted (Comma_Decade (p mod 924) x) \<longrightarrow>
       5 \<le> p \<longrightarrow>
       (\<exists>h terminal events final.
         comma_semantic_decade_summary (Comma_Decade (p mod 924) x) =
           Some (h, terminal) \<and>
         comma_python_first_terminal_walk p (Comma_Entry 1 0 x) events
           (comma_summary_outcome h terminal) (comma_shift_position h final) \<and>
         0 < target \<and>
         int target < comma_python_event_weight_prefix p events (length events)) \<longrightarrow>
       (\<exists>h terminal events final fragments boundaries weights prefixes i.
         comma_semantic_decade_partial_selection_result p x target h terminal
           events final fragments boundaries weights prefixes i)) \<and>
    ((\<forall>root\<in>comma_decimal_roots.
       ((\<exists>path :: nat \<Rightarrow> nat. path 0=root \<and>
         (\<forall>j. comma_child (path j) (path (Suc j)))) \<longleftrightarrow> root=20)) \<and>
     (\<forall>path :: nat \<Rightarrow> nat. path 0=20 \<longrightarrow>
       (\<forall>j. comma_child (path j) (path (Suc j))) \<longrightarrow>
       path 412987859=19999999999) \<and>
     (\<forall>left right :: nat \<Rightarrow> nat. left 0=20 \<longrightarrow>
       (\<forall>j. comma_child (left j) (left (Suc j))) \<longrightarrow>
       right 0=20 \<longrightarrow>
       (\<forall>j. comma_child (right j) (right (Suc j))) \<longrightarrow>
       (\<forall>n. left n=right n)) \<and>
     (\<forall>source. 0<source \<longrightarrow>
       (\<exists>path :: nat \<Rightarrow> nat. path 0=source \<and>
         (\<forall>j. comma_child (path j) (path (Suc j)))) \<longrightarrow>
       20 \<le> source)))"
  by (rule conjI[OF comma_semantic_decade_summary_writer_release_closed],
      rule conjI[OF comma_semantic_decade_writer_partial_selection_closed
        comma_semantic_global_release_safety])

ML \<open>
  val endpoints = @{thms comma_semantic_decade_summary_writer_release_closed
    comma_semantic_decade_writer_partial_selection_closed
    comma_semantic_producer_global_release_contract
    comma_semantic_global_release_safety}
  val _ = Comma_Proof_Dependency_Audit.require_native_closed_expected_paths
    @{context} "Concrete comma producer bridge and global release safety"
    ["comma_semantic_decade_summary_total_exact",
     "comma_decade_summary_python_macro_writer_output",
     "comma_python_actual_writer_point_at_prefix_cut",
     "comma_python_actual_writer_published_displacement_prefixes",
     "comma_python_writer_run_fragments_unique",
     "comma_python_first_terminal_walk_result_unique",
     "comma_semantic_future_candidate_provider_check_checked",
     "comma_semantic_concrete_future_rank_check",
     "comma_semantic_concrete_boundary_strong_occurrence_bridge",
     "comma_semantic_b1_crt_b32_stop242_checked",
     "comma_semantic_p5_entry_future_open_checked",
     "comma_semantic_p5_entry_infinite_imp_open",
     "comma_semantic_unique_infinite_decimal_root",
     "comma_semantic_concrete_source20_infinite_path",
     "comma_semantic_concrete_source20_z_no_infinite_path",
     "comma_semantic_concrete_future_paths_agree",
     "comma_every_positive_has_decimal_root",
     "comma_source20_to_fork_unique"] endpoints
\<close>

ML \<open>
  val _ = Comma_Proof_Dependency_Audit.require_native_clean @{context}
    "Concrete B32 summary to producer writer bridge"
    @{thms comma_python_writer_edge_outputs_unique
      comma_python_first_terminal_walk_result_unique
      comma_python_writer_run_fragments_unique
      comma_semantic_decade_summary_writer_release
      comma_semantic_b32_boundary_chart_loop_structurally_terminates
      comma_semantic_b32_scalar_chart_terminates
      comma_semantic_b32_grouped_chart_terminates
      comma_semantic_decade_writer_partial_selection}
\<close>

end
