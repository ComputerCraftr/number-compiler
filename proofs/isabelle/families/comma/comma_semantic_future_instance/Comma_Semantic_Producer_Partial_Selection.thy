theory Comma_Semantic_Producer_Partial_Selection
  imports Comma_Semantic_Producer_Weight_Cuts
begin

text \<open>This result connects one selected literal Near prefix to the chart
position at that cut, including pending Near records coalesced by the writer.\<close>

text \<open>A published Near chunk is the batched form of the runtime's physical
Near edges: its literal count is the exact transition weight, its displacement
is the endpoint difference, and its endpoint is either a same-sector prefix
or one checked crossing edge.  This is the local contract needed by both the
optional grouped chart walk and the ordinary coalesced writer run.\<close>

lemma comma_python_near_cut_chunk_refinement:
  fixes p i f delta h :: nat
  assumes cuts: "comma_python_cut_boundaries p origin fragments boundaries"
    and index: "i < length fragments"
    and left: "boundaries ! i = Comma_Near f delta h"
  shows "comma_python_near_fragment_shape (fragments ! i)"
    and "0 < comma_python_fragment_literal_steps (fragments ! i)"
    and "comma_python_fragment_leading (fragments ! i) = f"
    and "comma_python_fragment_entering_digit (fragments ! i) =
      comma_chart_value p (boundaries ! i) mod 10"
    and "1 \<le> h"
    and "h \<le> 540"
    and "(case boundaries ! Suc i of
        Comma_Near f' delta' t \<Rightarrow>
          f' = f \<and> delta' = delta \<and>
          comma_near_prefix
            (comma_python_fragment_literal_steps (fragments ! i)) f h t
      | Comma_Entry g delta' offset \<Rightarrow>
          comma_python_fragment_literal_steps (fragments ! i) = 1 \<and>
          comma_finite_step (p mod 924) (boundaries ! i) =
            Comma_Next (boundaries ! Suc i))"
    and "comma_python_fragment_displacement_at_scale
        (fragments ! i) (10 ^ p) =
      int (comma_chart_value p (boundaries ! Suc i)) -
        int (comma_chart_value p (boundaries ! i))"
    and "\<And>S. comma_python_fragment_weight_at_scale
        (fragments ! i) S =
      int (comma_python_fragment_literal_steps (fragments ! i))"
    and "comma_python_fragment_weight_affine (fragments ! i) =
      comma_python_chart_affine_weight 0
        (Comma_Chart_Weight 0 0
          (int (comma_python_fragment_literal_steps (fragments ! i))) 1)"
proof -
  let ?fragment = "fragments ! i"
  let ?left = "boundaries ! i"
  let ?right = "boundaries ! Suc i"
  have near_cut:
    "comma_python_fragment_near_cut p ?fragment ?left ?right"
    using cuts index by (auto simp: comma_python_cut_boundaries_def)
  have shape: "comma_python_near_fragment_shape ?fragment"
    and steps: "0 < comma_python_fragment_literal_steps ?fragment"
    and leading: "comma_python_fragment_leading ?fragment = f"
    and digit:
      "comma_python_fragment_entering_digit ?fragment =
        comma_chart_value p ?left mod 10"
    and h_lower: "1 \<le> h"
    and h_upper: "h \<le> 540"
    and right_shape:
      "(case ?right of
        Comma_Near f' delta' t \<Rightarrow>
          f' = f \<and> delta' = delta \<and>
          comma_near_prefix
            (comma_python_fragment_literal_steps ?fragment) f h t
      | Comma_Entry g delta' offset \<Rightarrow>
          comma_python_fragment_literal_steps ?fragment = 1 \<and>
          comma_finite_step (p mod 924) ?left = Comma_Next ?right)"
    using near_cut left by (auto simp: comma_python_fragment_near_cut_def)
  have displacement:
    "comma_python_fragment_displacement_at_scale ?fragment (10 ^ p) =
      int (comma_chart_value p ?right) - int (comma_chart_value p ?left)"
    using cuts index by (auto simp: comma_python_cut_boundaries_def)
  have weight_scale:
    "\<And>S. comma_python_fragment_weight_at_scale ?fragment S =
      int (comma_python_fragment_literal_steps ?fragment)"
    using shape by (simp add: comma_python_fragment_weight_at_scale_def
      comma_python_near_fragment_shape_def)
  have weight_affine:
    "comma_python_fragment_weight_affine ?fragment =
      comma_python_chart_affine_weight 0
        (Comma_Chart_Weight 0 0
          (int (comma_python_fragment_literal_steps ?fragment)) 1)"
    using shape
    by (simp add: comma_python_fragment_weight_affine_def
        comma_python_affine_times_def comma_python_constant_affine_def
        comma_python_affine_add_def comma_python_chart_affine_weight_def
        comma_python_affine_normalize_def comma_python_affine_zero_def
        comma_python_near_fragment_shape_def Let_def)
  show "comma_python_near_fragment_shape (fragments ! i)"
    using shape by simp
  show "0 < comma_python_fragment_literal_steps (fragments ! i)"
    using steps by simp
  show "comma_python_fragment_leading (fragments ! i) = f"
    using leading by simp
  show "comma_python_fragment_entering_digit (fragments ! i) =
      comma_chart_value p (boundaries ! i) mod 10"
    using digit by simp
  show "1 \<le> h" using h_lower .
  show "h \<le> 540" using h_upper .
  show "(case boundaries ! Suc i of
        Comma_Near f' delta' t \<Rightarrow>
          f' = f \<and> delta' = delta \<and>
          comma_near_prefix
            (comma_python_fragment_literal_steps (fragments ! i)) f h t
      | Comma_Entry g delta' offset \<Rightarrow>
          comma_python_fragment_literal_steps (fragments ! i) = 1 \<and>
          comma_finite_step (p mod 924) (boundaries ! i) =
            Comma_Next (boundaries ! Suc i))"
    using right_shape by simp
  show "comma_python_fragment_displacement_at_scale
        (fragments ! i) (10 ^ p) =
      int (comma_chart_value p (boundaries ! Suc i)) -
        int (comma_chart_value p (boundaries ! i))"
    using displacement by simp
  show "\<And>S. comma_python_fragment_weight_at_scale
        (fragments ! i) S =
      int (comma_python_fragment_literal_steps (fragments ! i))"
    using weight_scale by simp
  show "comma_python_fragment_weight_affine (fragments ! i) =
      comma_python_chart_affine_weight 0
        (Comma_Chart_Weight 0 0
          (int (comma_python_fragment_literal_steps (fragments ! i))) 1)"
    using weight_affine by simp
qed

theorem comma_python_near_cut_partial_selection:
  fixes p i j :: nat
  assumes exponent: "5 \<le> p"
    and cuts: "comma_python_cut_boundaries p origin fragments boundaries"
    and index: "i < length fragments"
    and left: "boundaries ! i = Comma_Near f delta h"
    and remaining: "int j \<le>
      comma_python_fragment_weight_at_scale (fragments ! i) (10 ^ p)"
  obtains point where
    "int (comma_chart_value p point) =
      int (comma_chart_value p (boundaries ! i)) +
        comma_python_fragment_select (fragments ! i) (10 ^ p) j"
proof -
  let ?fragment = "fragments ! i"
  let ?left = "boundaries ! i"
  let ?right = "boundaries ! Suc i"
  have shape: "comma_python_near_fragment_shape ?fragment"
    and steps_positive: "0 < comma_python_fragment_literal_steps ?fragment"
    and leading: "comma_python_fragment_leading ?fragment = f"
    and entering_digit:
      "comma_python_fragment_entering_digit ?fragment =
        comma_chart_value p ?left mod 10"
    and h_bounds: "1 \<le> h" "h \<le> 540"
    and right_shape:
      "(case ?right of
          Comma_Near f' delta' t \<Rightarrow>
            f' = f \<and> delta' = delta \<and>
            comma_near_prefix
              (comma_python_fragment_literal_steps ?fragment) f h t
        | Comma_Entry g delta' offset \<Rightarrow>
          comma_python_fragment_literal_steps ?fragment = 1)"
    and displacement:
      "comma_python_fragment_displacement_at_scale ?fragment (10 ^ p) =
        int (comma_chart_value p ?right) - int (comma_chart_value p ?left)"
    and fragment_weight:
      "comma_python_fragment_weight_at_scale ?fragment (10 ^ p) =
        int (comma_python_fragment_literal_steps ?fragment)"
    using comma_python_near_cut_chunk_refinement[OF cuts index left] by blast
  have steps: "j \<le> comma_python_fragment_literal_steps ?fragment"
    using remaining fragment_weight by exact_mod_cast
  have f_range: "1 \<le> f" "f \<le> 9"
    using shape leading by (auto simp: comma_python_near_fragment_shape_def)
  have source_sector:
      "comma_sector f (p + delta) (comma_chart_value p ?left)"
    using comma_near_chart_checked_sector[OF f_range exponent h_bounds, of delta]
      left by simp
  have source_sum:
      "comma_chart_value p ?left + h = (f + 1) * 10 ^ (p + delta)"
    using comma_sector_headroom[OF source_sector] .
  have source_digit:
      "comma_chart_value p ?left mod 10 = (10 - h mod 10) mod 10"
    by (rule comma_near_chart_digit[OF source_sum]) (use exponent in simp)
  show thesis
  proof (cases ?right)
    case (Comma_Near f' delta' t)
    have same: "f' = f" "delta' = delta"
      and path: "comma_near_prefix
        (comma_python_fragment_literal_steps ?fragment) f h t"
      using right_shape Comma_Near by auto
    obtain u where partial_path: "comma_near_prefix j f h u"
      using comma_python_near_prefix_initial[OF path steps] by blast
    have exact_full:
        "h = t + comma_period_displacement f
          (comma_python_fragment_entering_digit ?fragment)
          (comma_python_fragment_literal_steps ?fragment)"
    proof (rule comma_python_near_prefix_displacement_exact)
      show "1 \<le> f" "f \<le> 9" using f_range by simp_all
      show "1 \<le> h" "h \<le> 540" using h_bounds by simp_all
      show "comma_python_fragment_entering_digit ?fragment =
          (10 - h mod 10) mod 10"
        using source_digit entering_digit by simp
      show "comma_near_prefix
          (comma_python_fragment_literal_steps ?fragment) f h t"
        using path .
    qed
    have exact_partial:
        "h = u + comma_period_displacement f
          (comma_python_fragment_entering_digit ?fragment) j"
    proof (rule comma_python_near_prefix_displacement_exact)
      show "1 \<le> f" "f \<le> 9" using f_range by simp_all
      show "1 \<le> h" "h \<le> 540" using h_bounds by simp_all
      show "comma_python_fragment_entering_digit ?fragment =
          (10 - h mod 10) mod 10"
        using source_digit entering_digit by simp
      show "comma_near_prefix j f h u" using partial_path .
    qed
    have t_bounds: "1 \<le> t" "t \<le> 540"
      by (rule comma_python_near_prefix_headroom_bounds
        [OF f_range h_bounds path])
    have target_sector:
        "comma_sector f (p + delta) (comma_chart_value p ?right)"
      using comma_near_chart_checked_sector[OF f_range exponent t_bounds, of delta]
        Comma_Near same by simp
    have target_sum:
        "comma_chart_value p ?right + t = (f + 1) * 10 ^ (p + delta)"
      using comma_sector_headroom[OF target_sector] .
    have endpoint:
        "comma_chart_value p ?right =
          comma_chart_value p ?left +
            comma_period_displacement f
              (comma_python_fragment_entering_digit ?fragment)
              (comma_python_fragment_literal_steps ?fragment)"
      using source_sum target_sum exact_full same by arith
    have increment:
        "comma_python_fragment_literal_increment ?fragment =
          comma_period_displacement f
            (comma_python_fragment_entering_digit ?fragment)
            (comma_python_fragment_literal_steps ?fragment)"
    proof -
      have displacement_value:
          "comma_python_fragment_displacement_at_scale ?fragment (10 ^ p) =
            int (comma_python_fragment_literal_increment ?fragment)"
        using shape by (simp add: comma_python_fragment_displacement_at_scale_def
            comma_python_near_fragment_shape_def
            comma_python_affine_evaluate_def comma_python_affine_zero_def)
      show ?thesis using displacement endpoint displacement_value
        by (simp add: same; linarith)
    qed
    have selected:
        "comma_python_fragment_select ?fragment (10 ^ p) j =
          int (comma_period_displacement f
            (comma_python_fragment_entering_digit ?fragment) j)"
      by (rule comma_python_near_fragment_select[OF shape increment])
    have u_le_h:
        "u \<le> h"
      using exact_partial by arith
    have intermediate:
        "comma_chart_value p (Comma_Near f delta u) =
          comma_chart_value p ?left +
            comma_period_displacement f
              (comma_python_fragment_entering_digit ?fragment) j"
      using source_sum exact_partial u_le_h left
      by (simp add: comma_chart_value_def; arith)
    show thesis using selected intermediate
      by (rule that[where point="Comma_Near f delta u"]) simp
  next
    case (Comma_Entry g delta' offset)
    have singleton:
        "comma_python_fragment_literal_steps ?fragment = 1"
      using right_shape Comma_Entry by simp
    show thesis
    proof (cases j)
      case "0"
      have selected:
          "comma_python_fragment_select ?fragment (10 ^ p) j = 0"
        using singleton "0" by (simp add: comma_python_fragment_select_def
            comma_period_displacement_def)
      show thesis using selected "0"
        by (rule that[where point=?left]) simp
    next
      case (Suc k)
      have j_one: "j = 1" using remaining singleton Suc by arith
      have displacement_value:
          "comma_python_fragment_displacement_at_scale ?fragment (10 ^ p) =
            int (comma_python_fragment_literal_increment ?fragment)"
        using shape by (simp add: comma_python_fragment_displacement_at_scale_def
            comma_python_near_fragment_shape_def
            comma_python_affine_evaluate_def comma_python_affine_zero_def)
      have selected:
          "comma_python_fragment_select ?fragment (10 ^ p) j =
            int (comma_python_fragment_literal_increment ?fragment)"
        using singleton j_one
        by (simp add: comma_python_fragment_select_def displacement_value)
      show thesis using displacement selected
        by (rule that[where point=?right]) simp
    qed
  qed
qed

lemma comma_python_writer_edge_event_count:
  assumes edge: "comma_python_writer_edge p source successor weight pending
      emitted pending'"
  shows "sum_list (map comma_python_fragment_event_count emitted) +
      (case pending' of None \<Rightarrow> 0
       | Some fragment \<Rightarrow> comma_python_fragment_event_count fragment) =
    (case pending of None \<Rightarrow> 0
     | Some fragment \<Rightarrow> comma_python_fragment_event_count fragment) + 1"
  using edge
proof (induction rule: comma_python_writer_edge.induct)
  case (entry p f delta offset headroom weight pending)
  then show ?case
    by (cases pending)
      (simp_all add: comma_python_fragment_event_count_def
        comma_python_entry_sector_fragment_def comma_python_flush_near_def
        Let_def)
next
  case (near_start p f delta headroom next_headroom weight increment)
  then show ?case
    by (simp add: comma_python_fragment_event_count_def
        comma_python_literal_fragment_def)
next
  case (near_merge pending_fragment p f delta headroom next_headroom weight
      increment)
  then show ?case
    by (simp add: comma_python_fragment_event_count_def
        comma_python_literal_fragment_def comma_python_merge_near_fragments_def
        comma_python_near_fragments_compatible_def)
next
  case (near_cross p f delta headroom g next_delta offset weight pending
      increment)
  then show ?case
    by (cases pending)
      (simp_all add: comma_python_fragment_event_count_def
        comma_python_literal_fragment_def comma_python_flush_near_def)
qed

lemma comma_python_writer_run_event_count:
  assumes run:
    "comma_python_writer_run p source pending events outcome terminal fragments"
  shows "comma_python_fragment_event_cut fragments (length fragments) =
    length events + (case pending of None \<Rightarrow> 0
      | Some fragment \<Rightarrow> comma_python_fragment_event_count fragment)"
  using run
proof (induction rule: comma_python_writer_run.induct)
  case (fork p source a delta pending fragments)
  then show ?case
    by (cases pending)
      (simp_all add: comma_python_fragment_event_cut_def
        comma_python_fragment_event_count_def comma_python_flush_near_def)
next
  case (landmine p source delta pending fragments)
  then show ?case
    by (cases pending)
      (simp_all add: comma_python_fragment_event_cut_def
        comma_python_fragment_event_count_def comma_python_flush_near_def)
next
  case (advance p source successor weight pending emitted pending' events
      outcome terminal tail_fragments)
  have edge_count:
    "sum_list (map comma_python_fragment_event_count emitted) +
        (case pending' of None \<Rightarrow> 0
         | Some fragment \<Rightarrow> comma_python_fragment_event_count fragment) =
      (case pending of None \<Rightarrow> 0
       | Some fragment \<Rightarrow> comma_python_fragment_event_count fragment) + 1"
    by (rule comma_python_writer_edge_event_count[OF advance.hyps(2)])
  show ?case using advance.IH edge_count
    by (simp add: comma_python_fragment_event_cut_def sum_list_append algebra_simps)
qed

lemma comma_python_event_weight_prefix_nonnegative:
  "0 \<le> comma_python_event_weight_prefix p events k"
  unfolding comma_python_event_weight_prefix_def
  by (rule comma_python_sum_list_map_nonnegative) auto

theorem comma_python_actual_writer_point_at_prefix_cut:
  fixes p target :: nat
  assumes exponent: "5 \<le> p"
    and walk:
      "comma_python_first_terminal_walk p source events outcome terminal"
    and admitted: "comma_round_admitted source"
    and requested: "0 < target"
      "int target < comma_python_event_weight_prefix p events (length events)"
  obtains fragments boundaries weights prefixes i where
    run: "comma_python_writer_run p source None events outcome terminal fragments"
    and aligned: "comma_python_cut_boundaries p source fragments boundaries"
    and guards: "\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    and weight_array:
      "weights = comma_python_published_weights
        (comma_python_publish_fragments fragments)"
    and prefix_array:
      "prefixes = map (\<lambda>w.
        nat (comma_python_affine_evaluate w (10 ^ p))) weights"
    and array_guards:
      "\<forall>j\<le>length fragments.
        0 < comma_python_affine_denominator (weights ! j) \<and>
        comma_python_affine_divides (weights ! j) (10 ^ p)"
    and index: "i < length fragments"
    and adjacent:
      "prefixes ! Suc i = prefixes ! i +
        nat (comma_python_fragment_weight_at_scale (fragments ! i) (10 ^ p))"
    and event_cut_adjacent:
      "comma_python_fragment_event_cut fragments (Suc i) =
        comma_python_fragment_event_cut fragments i +
          comma_python_fragment_event_count (fragments ! i)"
    and search:
      "comma_prefix_lower_bound (length prefixes - 2) prefixes target
        1 (length prefixes - 1) = Suc i"
    and before: "prefixes ! i < target"
    and after: "target \<le> prefixes ! Suc i"
    and before_event:
      "int (prefixes ! i) = comma_python_event_weight_prefix p events
        (comma_python_fragment_event_cut fragments i)"
    and after_event:
      "int (prefixes ! Suc i) = comma_python_event_weight_prefix p events
        (comma_python_fragment_event_cut fragments (Suc i))"
    and before_value:
      "int (comma_chart_value p (boundaries ! i)) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events
            (comma_python_fragment_event_cut fragments i)))"
    and after_value:
      "int (comma_chart_value p (boundaries ! Suc i)) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events
            (comma_python_fragment_event_cut fragments (Suc i)))"
proof -
  obtain fragments boundaries where run:
      "comma_python_writer_run p source None events outcome terminal fragments"
    and aligned:
      "comma_python_cut_boundaries p source fragments boundaries"
    and guards: "\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    and weight_prefix:
      "\<forall>j\<le>length fragments.
        comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! j) (10 ^ p) =
        comma_python_event_weight_prefix p events
          (comma_python_fragment_event_cut fragments j)"
    and boundary_value:
      "\<forall>j\<le>length fragments.
        int (comma_chart_value p (boundaries ! j)) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events
            (comma_python_fragment_event_cut fragments j)))"
    using comma_python_actual_writer_event_weight_prefix_cuts
      [OF exponent walk admitted] by blast
  let ?weights = "comma_python_published_weights
    (comma_python_publish_fragments fragments)"
  let ?prefixes = "map (\<lambda>w.
    nat (comma_python_affine_evaluate w (10 ^ p))) ?weights"
  have weights_length: "length ?weights = Suc (length fragments)"
    by (simp add: comma_python_publish_fragments_def
        comma_python_affine_prefix_scan_length)
  have prefixes_length: "length ?prefixes = Suc (length fragments)"
    using weights_length by simp
  have eval_sum:
      "\<forall>j\<le>length fragments.
        comma_python_affine_evaluate (?weights ! j) (10 ^ p) =
        sum_list (map (\<lambda>g.
          comma_python_fragment_weight_at_scale g (10 ^ p))
          (take j fragments))"
  proof (intro allI impI)
    fix j assume j: "j \<le> length fragments"
    show "comma_python_affine_evaluate (?weights ! j) (10 ^ p) =
        sum_list (map (\<lambda>g.
          comma_python_fragment_weight_at_scale g (10 ^ p))
          (take j fragments))"
      by (rule comma_python_published_prefixes_at_scale(1)[OF guards j])
  qed
  have weight_array_guards:
      "\<forall>j\<le>length fragments.
        0 < comma_python_affine_denominator (?weights ! j) \<and>
        comma_python_affine_divides (?weights ! j) (10 ^ p)"
  proof (intro allI impI)
    fix j assume j: "j \<le> length fragments"
    have entries:
        "\<forall>x\<in>set (map comma_python_fragment_weight_affine
            (take j fragments)).
          0 < comma_python_affine_denominator x \<and>
          comma_python_affine_divides x (10 ^ p) \<and>
          0 \<le> comma_python_affine_evaluate x (10 ^ p)"
      using guards by (auto simp: comma_python_fragment_scale_guard_def)
    have zero_positive:
      "0 < comma_python_affine_denominator comma_python_affine_zero"
      by simp
    have zero_exact:
      "comma_python_affine_divides comma_python_affine_zero (10 ^ p)"
      by (simp add: comma_python_affine_divides_def
          comma_python_affine_zero_def comma_python_affine_normalize_def Let_def)
    have zero_nonnegative:
      "0 \<le> comma_python_affine_evaluate comma_python_affine_zero (10 ^ p)"
      by simp
    note folded = comma_python_affine_fold_scale_guard
      [OF zero_positive zero_exact zero_nonnegative entries]
    have folded_positive:
      "0 < comma_python_affine_denominator
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_weight_affine (take j fragments)))"
      by (rule folded(1))
    have folded_exact:
      "comma_python_affine_divides
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_weight_affine (take j fragments)))
          (10 ^ p)"
      by (rule folded(2))
    have nth:
      "?weights ! j =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_weight_affine (take j fragments))"
      by (rule comma_python_publish_fragments_nth(1)[OF j])
    show "0 < comma_python_affine_denominator (?weights ! j) \<and>
        comma_python_affine_divides (?weights ! j) (10 ^ p)"
      using folded_positive folded_exact nth by simp
  qed
  have prefix_event:
      "\<And>j. j \<le> length fragments \<Longrightarrow>
        int (?prefixes ! j) = comma_python_event_weight_prefix p events
          (comma_python_fragment_event_cut fragments j)"
  proof -
    fix j assume j: "j \<le> length fragments"
    have event_nonnegative:
      "0 \<le> comma_python_event_weight_prefix p events
        (comma_python_fragment_event_cut fragments j)"
      by (rule comma_python_event_weight_prefix_nonnegative)
    have eval: "comma_python_affine_evaluate (?weights ! j) (10 ^ p) =
        comma_python_event_weight_prefix p events
          (comma_python_fragment_event_cut fragments j)"
      using weight_prefix j by blast
    show "int (?prefixes ! j) = comma_python_event_weight_prefix p events
        (comma_python_fragment_event_cut fragments j)"
      using eval event_nonnegative j
      by (simp add: prefixes_length)
  qed
  have fragment_weights_nonnegative:
      "\<forall>g\<in>set fragments.
        0 \<le> comma_python_fragment_weight_at_scale g (10 ^ p)"
    using guards by (auto simp: comma_python_fragment_scale_guard_def)
  have eval_nonnegative:
      "\<forall>j\<le>length fragments.
        0 \<le> comma_python_affine_evaluate (?weights ! j) (10 ^ p)"
  proof (intro allI impI)
    fix j assume j: "j \<le> length fragments"
    have terms_nonnegative:
        "\<forall>g\<in>set (take j fragments).
          0 \<le> comma_python_fragment_weight_at_scale g (10 ^ p)"
      using fragment_weights_nonnegative by auto
    have sum_nonnegative:
        "0 \<le> sum_list (map
          (\<lambda>g. comma_python_fragment_weight_at_scale g (10 ^ p))
          (take j fragments))"
      by (rule comma_python_sum_list_map_nonnegative[OF terms_nonnegative])
    show "0 \<le> comma_python_affine_evaluate (?weights ! j) (10 ^ p)"
      using eval_sum j sum_nonnegative by simp
  qed
  have prefixes_monotone:
      "\<And>i j. i \<le> j \<Longrightarrow> j \<le> length fragments \<Longrightarrow>
        ?prefixes ! i \<le> ?prefixes ! j"
  proof -
    fix i j assume ij: "i \<le> j" and j: "j \<le> length fragments"
    have i: "i \<le> length fragments" using ij j by arith
    have sums: "comma_python_affine_evaluate (?weights ! i) (10 ^ p) =
        sum_list (map (\<lambda>g. comma_python_fragment_weight_at_scale g (10 ^ p))
          (take i fragments))"
      "comma_python_affine_evaluate (?weights ! j) (10 ^ p) =
        sum_list (map (\<lambda>g. comma_python_fragment_weight_at_scale g (10 ^ p))
          (take j fragments))"
      using eval_sum i j by simp_all
    have sum_order:
      "sum_list (map (\<lambda>g. comma_python_fragment_weight_at_scale g (10 ^ p))
          (take i fragments)) \<le>
       sum_list (map (\<lambda>g. comma_python_fragment_weight_at_scale g (10 ^ p))
          (take j fragments))"
      by (rule comma_python_sum_take_nonnegative_mono[OF ij
        fragment_weights_nonnegative])
    have eval_order:
      "comma_python_affine_evaluate (?weights ! i) (10 ^ p) \<le>
        comma_python_affine_evaluate (?weights ! j) (10 ^ p)"
      using sums sum_order by linarith
    have nat_order:
      "nat (comma_python_affine_evaluate (?weights ! i) (10 ^ p)) \<le>
        nat (comma_python_affine_evaluate (?weights ! j) (10 ^ p))"
      by (rule nat_mono[OF eval_order])
    show "?prefixes ! i \<le> ?prefixes ! j"
      using nat_order i j by simp
  qed
  have count:
    "comma_python_fragment_event_cut fragments (length fragments) =
      length events"
    using comma_python_writer_run_event_count[OF run] by simp
  have final_eval:
    "comma_python_affine_evaluate (?weights ! length fragments) (10 ^ p) =
      comma_python_event_weight_prefix p events (length events)"
    using weight_prefix count by simp
  have final_nonnegative:
    "0 \<le> comma_python_affine_evaluate
      (?weights ! length fragments) (10 ^ p)"
    using final_eval comma_python_event_weight_prefix_nonnegative by blast
  have final_prefix:
    "int (?prefixes ! length fragments) =
      comma_python_event_weight_prefix p events (length events)"
    using final_eval final_nonnegative by simp
  have target_before_last:
    "target < ?prefixes ! length fragments"
  proof -
    have "int target < int (?prefixes ! length fragments)"
      using requested(2) final_prefix by simp
    then show ?thesis by exact_mod_cast
  qed
  have initial: "?prefixes ! 0 = 0"
    by (simp add: prefixes_length comma_python_publish_fragments_def
        comma_python_affine_prefix_scan.simps comma_python_affine_zero_def
        comma_python_affine_evaluate_def)
  have nonempty: "fragments \<noteq> []"
  proof
    assume empty: "fragments = []"
    then have "?prefixes ! length fragments = 0" using initial by simp
    then show False using target_before_last requested(1) by simp
  qed
  have search_length: "1 < length ?prefixes"
    using prefixes_length nonempty by (cases fragments) auto
  have final: "target \<le> ?prefixes ! (length ?prefixes - 1)"
    using target_before_last prefixes_length by simp
  have monotone: "\<And>i j. 1 \<le> i \<Longrightarrow> i \<le> j \<Longrightarrow>
      j < length ?prefixes \<Longrightarrow> ?prefixes ! i \<le> ?prefixes ! j"
  proof -
    fix i j assume one: "1 \<le> i" and ij: "i \<le> j"
      and j: "j < length ?prefixes"
    have j_bound: "j \<le> length fragments"
      using j prefixes_length by arith
    show "?prefixes ! i \<le> ?prefixes ! j"
      by (rule prefixes_monotone[OF ij j_bound])
  qed
  let ?first = "Min {j. 1 \<le> j \<and> j < length ?prefixes \<and>
    target \<le> ?prefixes ! j}"
  have first_eq: "?first = Min {j. 1 \<le> j \<and>
      j < length ?prefixes \<and> target \<le> ?prefixes ! j}"
    by simp
  have search_facts:
    "comma_prefix_lower_bound (length ?prefixes - 2) ?prefixes target
      1 (length ?prefixes - 1) = ?first"
    "1 \<le> ?first"
    "?first < length ?prefixes"
    "target \<le> ?prefixes ! ?first"
    "?prefixes ! (?first - 1) < target"
    using comma_prefix_search_first_crossing
      [OF search_length requested(1) initial final monotone]
      first_eq by (simp_all only: first_eq)
  let ?i = "?first - 1"
  have i_bound: "?i < length fragments"
    using search_facts(2,3) prefixes_length by arith
  have after_bound: "Suc ?i \<le> length fragments"
    using search_facts(2,3) prefixes_length by arith
  have event_cut_adjacent:
      "comma_python_fragment_event_cut fragments (Suc ?i) =
        comma_python_fragment_event_cut fragments ?i +
          comma_python_fragment_event_count (fragments ! ?i)"
    using i_bound
    by (simp add: comma_python_fragment_event_cut_def
        take_Suc_conv_app_nth sum_list_append)
  have prefix_sum_adjacent:
      "sum_list (map (\<lambda>g. comma_python_fragment_weight_at_scale g (10 ^ p))
          (take (Suc ?i) fragments) =
       sum_list (map (\<lambda>g. comma_python_fragment_weight_at_scale g (10 ^ p))
          (take ?i fragments)) +
         comma_python_fragment_weight_at_scale (fragments ! ?i) (10 ^ p)"
    using i_bound by (simp add: take_Suc_conv_app_nth sum_list_append)
  have eval_adjacent:
      "comma_python_affine_evaluate (?weights ! Suc ?i) (10 ^ p) =
        comma_python_affine_evaluate (?weights ! ?i) (10 ^ p) +
          comma_python_fragment_weight_at_scale (fragments ! ?i) (10 ^ p)"
    using eval_sum i_bound after_bound prefix_sum_adjacent by simp
  have prefix_adjacent:
      "?prefixes ! Suc ?i = ?prefixes ! ?i +
        nat (comma_python_fragment_weight_at_scale (fragments ! ?i) (10 ^ p))"
    using eval_adjacent eval_nonnegative i_bound after_bound
      fragment_weights_nonnegative
    by (simp add: prefixes_length)
  have before_event:
    "int (?prefixes ! ?i) = comma_python_event_weight_prefix p events
      (comma_python_fragment_event_cut fragments ?i)"
    by (rule prefix_event[OF i_bound])
  have after_event:
    "int (?prefixes ! Suc ?i) = comma_python_event_weight_prefix p events
      (comma_python_fragment_event_cut fragments (Suc ?i))"
    by (rule prefix_event[OF after_bound])
  have before_value:
    "int (comma_chart_value p (boundaries ! ?i)) =
      int (comma_chart_value p
        (comma_python_event_prefix_endpoint source events
          (comma_python_fragment_event_cut fragments ?i)))"
    using boundary_value i_bound by blast
  have after_value:
    "int (comma_chart_value p (boundaries ! Suc ?i)) =
      int (comma_chart_value p
        (comma_python_event_prefix_endpoint source events
          (comma_python_fragment_event_cut fragments (Suc ?i)))"
    using boundary_value after_bound by blast
  show thesis
    using run aligned guards weight_array_guards prefix_adjacent
      event_cut_adjacent before_event after_event before_value after_value
      i_bound search_facts(1,2) search_facts(4,5)
    by (rule that[where fragments=fragments and boundaries=boundaries
        and weights="?weights" and prefixes="?prefixes" and i="?i"])
      (simp_all add: prefixes_length)
qed

lemma comma_python_cut_displacement_prefix:
  fixes p i :: nat
  assumes cuts:
      "comma_python_cut_boundaries p origin fragments boundaries"
    and index: "i \<le> length fragments"
  shows "sum_list (map (\<lambda>fragment.
      comma_python_fragment_displacement_at_scale fragment (10 ^ p))
      (take i fragments)) =
    int (comma_chart_value p (boundaries ! i)) -
      int (comma_chart_value p (boundaries ! 0))"
proof -
  have start: "boundaries ! 0 = origin"
    by (rule comma_python_cut_boundaries_start[OF cuts])
  have edge: "\<And>j. j < length fragments \<Longrightarrow>
      comma_python_fragment_displacement_at_scale (fragments ! j) (10 ^ p) =
        int (comma_chart_value p (boundaries ! Suc j)) -
          int (comma_chart_value p (boundaries ! j))"
    using cuts by (auto simp: comma_python_cut_boundaries_def)
  have telescope: "\<And>j. j \<le> length fragments \<Longrightarrow>
      sum_list (map (\<lambda>fragment.
        comma_python_fragment_displacement_at_scale fragment (10 ^ p))
        (take j fragments)) =
      int (comma_chart_value p (boundaries ! j)) -
        int (comma_chart_value p (boundaries ! 0))"
  proof -
    fix j
    assume j_bound: "j \<le> length fragments"
    show "sum_list (map (\<lambda>fragment.
        comma_python_fragment_displacement_at_scale fragment (10 ^ p))
        (take j fragments)) =
      int (comma_chart_value p (boundaries ! j)) -
        int (comma_chart_value p (boundaries ! 0))"
      using j_bound
    proof (induction j)
      case 0
      then show ?case by simp
    next
      case (Suc j)
      have j_less: "j < length fragments" using Suc.prems by arith
      have smaller_bound: "j \<le> length fragments" using j_less by simp
      have previous:
        "sum_list (map (\<lambda>fragment.
          comma_python_fragment_displacement_at_scale fragment (10 ^ p))
          (take j fragments)) =
         int (comma_chart_value p (boundaries ! j)) -
           int (comma_chart_value p (boundaries ! 0))"
        by (rule Suc.IH[OF smaller_bound])
      have edge_j:
        "comma_python_fragment_displacement_at_scale (fragments ! j) (10 ^ p) =
          int (comma_chart_value p (boundaries ! Suc j)) -
            int (comma_chart_value p (boundaries ! j))"
        by (rule edge[OF j_less])
      have sum_step:
        "sum_list (map (\<lambda>fragment.
          comma_python_fragment_displacement_at_scale fragment (10 ^ p))
          (take (Suc j) fragments)) =
         sum_list (map (\<lambda>fragment.
          comma_python_fragment_displacement_at_scale fragment (10 ^ p))
          (take j fragments)) +
         comma_python_fragment_displacement_at_scale (fragments ! j) (10 ^ p)"
        using j_less by (simp add: take_Suc_conv_app_nth sum_list_append)
      show ?case using previous edge_j sum_step
        by (simp add: algebra_simps)
    qed
  qed
  show ?thesis using telescope[OF index] .
qed

theorem comma_python_actual_writer_published_displacement_prefixes:
  fixes p :: nat
  assumes exponent: "5 \<le> p"
    and walk:
      "comma_python_first_terminal_walk p source events outcome terminal"
    and admitted: "comma_round_admitted source"
  obtains fragments boundaries where
    run: "comma_python_writer_run p source None events outcome terminal fragments"
    and aligned:
      "comma_python_cut_boundaries p source fragments boundaries"
    and guards: "\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    and displacement_array_guards:
      "\<forall>i\<le>length fragments.
        0 < comma_python_affine_denominator
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) \<and>
        comma_python_affine_divides
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p)"
    and published_displacement_at_cut:
      "\<forall>i\<le>length fragments.
        comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events
            (comma_python_fragment_event_cut fragments i))) -
          int (comma_chart_value p source)"
proof -
  obtain fragments boundaries where run:
      "comma_python_writer_run p source None events outcome terminal fragments"
    and aligned:
      "comma_python_cut_boundaries p source fragments boundaries"
    and guards: "\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    and actual_boundary_value:
      "\<forall>i\<le>length fragments.
        int (comma_chart_value p (boundaries ! i)) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events
            (comma_python_fragment_event_cut fragments i)))"
    using comma_python_actual_writer_event_weight_prefix_cuts
      [OF exponent walk admitted] by blast
  have array_guards:
      "\<forall>i\<le>length fragments.
        0 < comma_python_affine_denominator
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) \<and>
        comma_python_affine_divides
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p)"
  proof (intro allI impI)
    fix i assume index: "i \<le> length fragments"
    have entries:
        "\<forall>x\<in>set (map comma_python_fragment_displacement_affine
            (take i fragments)).
          0 < comma_python_affine_denominator x \<and>
          comma_python_affine_divides x (10 ^ p) \<and>
          0 \<le> comma_python_affine_evaluate x (10 ^ p)"
      using guards by (auto simp: comma_python_fragment_scale_guard_def)
    have zero_positive:
      "0 < comma_python_affine_denominator comma_python_affine_zero"
      by simp
    have zero_exact:
      "comma_python_affine_divides comma_python_affine_zero (10 ^ p)"
      by (simp add: comma_python_affine_divides_def
          comma_python_affine_zero_def comma_python_affine_normalize_def Let_def)
    have zero_nonnegative:
      "0 \<le> comma_python_affine_evaluate comma_python_affine_zero (10 ^ p)"
      by simp
    note folded = comma_python_affine_fold_scale_guard
      [OF zero_positive zero_exact zero_nonnegative entries]
    have nth:
      "comma_python_published_displacements
        (comma_python_publish_fragments fragments) ! i =
       foldl comma_python_affine_add comma_python_affine_zero
         (map comma_python_fragment_displacement_affine (take i fragments))"
      by (rule comma_python_publish_fragments_nth(2)[OF index])
    show "0 < comma_python_affine_denominator
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) \<and>
        comma_python_affine_divides
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p)"
      using folded(1,2) nth by simp
  qed
  have displacement_values:
      "\<forall>i\<le>length fragments.
        comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events
            (comma_python_fragment_event_cut fragments i))) -
          int (comma_chart_value p source)"
  proof (intro allI impI)
    fix i assume index: "i \<le> length fragments"
    have published:
      "comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
       sum_list (map (\<lambda>fragment.
          comma_python_fragment_displacement_at_scale fragment (10 ^ p))
        (take i fragments))"
      by (rule comma_python_published_prefixes_at_scale(2)[OF guards index])
    have telescope:
      "sum_list (map (\<lambda>fragment.
          comma_python_fragment_displacement_at_scale fragment (10 ^ p))
        (take i fragments)) =
       int (comma_chart_value p (boundaries ! i)) -
         int (comma_chart_value p (boundaries ! 0))"
      by (rule comma_python_cut_displacement_prefix[OF aligned index])
    have start: "boundaries ! 0 = source"
      by (rule comma_python_cut_boundaries_start[OF aligned])
    have event_value:
      "int (comma_chart_value p (boundaries ! i)) =
       int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events
            (comma_python_fragment_event_cut fragments i)))"
      using actual_boundary_value index by blast
    show "comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        int (comma_chart_value p
          (comma_python_event_prefix_endpoint source events
            (comma_python_fragment_event_cut fragments i))) -
          int (comma_chart_value p source)"
      using published telescope event_value start by simp
  qed
  show thesis using run aligned guards array_guards displacement_values
    by (rule that) blast
qed

lemmas comma_python_producer_partial_selection_oracle_audit_bundle =
  comma_python_near_cut_chunk_refinement
  comma_python_near_cut_partial_selection
  comma_python_writer_edge_event_count
  comma_python_writer_run_event_count
  comma_python_event_weight_prefix_nonnegative
  comma_python_actual_writer_point_at_prefix_cut
  comma_python_cut_displacement_prefix
  comma_python_actual_writer_published_displacement_prefixes
ML \<open>val _ = if null (Thm_Deps.all_oracles
  @{thms comma_python_producer_partial_selection_oracle_audit_bundle}) then ()
  else error "Comma_Semantic_Producer_Partial_Selection local oracle audit failed"\<close>

end
