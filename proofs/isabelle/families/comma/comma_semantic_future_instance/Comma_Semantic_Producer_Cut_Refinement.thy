theory Comma_Semantic_Producer_Cut_Refinement
  imports Comma_Semantic_Producer_Prefix_Refinement
    Comma_Near_Period.Comma_Near_Period
begin

text \<open>The pending Near record is tied to the last published cut.  This
is the invariant needed to interpret every displacement prefix as an
intermediate chart source: a pending Near run starts at that cut and its
literal displacement ends at the current chart position.\<close>

lemma comma_python_near_prefix_displacement_exact:
  fixes n f h t d :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and initial: "1 \<le> h" "h \<le> 540"
    and digit: "d = (10 - h mod 10) mod 10"
    and path: "comma_near_prefix n f h t"
  shows "h = t + comma_period_displacement f d n"
  by (rule comma_near_prefix_displacement_refines
      [OF f(1) f(2) initial(1) initial(2) digit path])

definition comma_python_fragment_near_cut ::
  "nat \<Rightarrow> comma_python_sector_fragment \<Rightarrow>
    comma_finite_position \<Rightarrow> comma_finite_position \<Rightarrow> bool"
where
  "comma_python_fragment_near_cut p fragment left right \<longleftrightarrow>
    (case left of
      Comma_Entry g delta offset \<Rightarrow> True
    | Comma_Near f delta h \<Rightarrow>
        comma_python_near_fragment_shape fragment \<and>
          0 < comma_python_fragment_literal_steps fragment \<and>
          1 \<le> h \<and> h \<le> 540 \<and>
          comma_python_fragment_leading fragment = f \<and>
          comma_python_fragment_entering_digit fragment =
            comma_chart_value p left mod 10 \<and>
          (case right of
            Comma_Near f' delta' t \<Rightarrow>
              f' = f \<and> delta' = delta \<and>
              comma_near_prefix
                (comma_python_fragment_literal_steps fragment) f h t
          | Comma_Entry g delta' offset \<Rightarrow>
              comma_python_fragment_literal_steps fragment = 1 \<and>
              comma_finite_step (p mod 924) left = Comma_Next right)))"

lemma comma_python_near_record_prefix:
  assumes record: "comma_python_fragment_record_matches p
      (Comma_Near f delta h) (Comma_Near f delta t) weight fragment"
  shows "comma_near_prefix 1 f h t"
proof -
  have step:
    "comma_weighted_step (p mod 924) (Comma_Near f delta h) =
      Comma_WNext (Comma_Near f delta t) weight"
    using record by (simp add: comma_python_fragment_record_matches_def)
  have finite:
    "comma_finite_step (p mod 924) (Comma_Near f delta h) =
      Comma_Next (Comma_Near f delta t)"
    using step by (simp add: comma_finite_step_def)
  have transport:
    "comma_finite_step (p mod 924) (Comma_Near f delta h) =
      comma_shift_move delta
        (comma_finite_step 0 (Comma_Near f 0 h))"
    by (rule comma_near_step_delta_transport[of "p mod 924" f 0 delta h 0])
  have unshifted:
    "comma_finite_step 0 (Comma_Near f 0 h) =
      Comma_Next (Comma_Near f 0 t)"
    using finite transport
    by (cases "comma_finite_step 0 (Comma_Near f 0 h)")
      (auto simp: comma_shift_move.simps
        split: comma_finite_move.splits comma_finite_position.splits)
  show ?thesis using unshifted by simp
qed

lemma comma_python_near_prefix_initial:
  assumes path: "comma_near_prefix n f h t" and index: "j \<le> n"
  obtains u where "comma_near_prefix j f h u"
  using path index
proof (induction j arbitrary: n h t)
  case "0"
  show thesis by (rule that[where u=h]) simp
next
  case (Suc j)
  have positive: "0 < n" using Suc.prems by auto
  then obtain m where n: "n = Suc m" by (cases n) auto
  obtain next_h where first:
      "comma_finite_step 0 (Comma_Near f 0 h) =
        Comma_Next (Comma_Near f 0 next_h)"
    and tail: "comma_near_prefix m f next_h t"
    using Suc.prems n by auto
  have j_bound: "j \<le> m" using Suc.prems n by arith
  obtain u where prefix: "comma_near_prefix j f next_h u"
    using Suc.IH[OF tail j_bound] by blast
  have whole_prefix: "comma_near_prefix (Suc j) f h u"
    using first prefix by auto
  show thesis by (rule that[OF whole_prefix])
qed

lemma comma_python_near_prefix_headroom_bounds:
  assumes f: "1 \<le> f" "f \<le> 9"
    and initial: "1 \<le> h" "h \<le> 540"
    and path: "comma_near_prefix n f h t"
  shows "1 \<le> t" "t \<le> 540"
  using path f initial
proof (induction n arbitrary: h)
  case "0"
  then show "1 \<le> t" "t \<le> 540" by simp_all
next
  case (Suc n)
  then obtain j where step:
      "comma_finite_step 0 (Comma_Near f 0 h) =
        Comma_Next (Comma_Near f 0 j)"
    and tail: "comma_near_prefix n f j t"
    by auto
  let ?d = "(10 - h mod 10) mod 10"
  have relation:
      "10 * ?d + f + (if f < 9 then 1 else 0) < h"
      "j = h - (10 * ?d + f)"
    using step f initial
    by (auto simp: comma_near_internal_iff[OF f(1) f(2) initial(1) initial(2)])
  have j_positive: "1 \<le> j"
    using relation f(1) by (cases "f < 9") arith+
  have j_upper: "j \<le> 540" using relation initial(2) by arith
  have tail_bounds: "1 \<le> t" "t \<le> 540"
    by (rule Suc.IH[OF f(1) f(2) j_positive j_upper tail])
  show "1 \<le> t" "t \<le> 540" using tail_bounds by simp_all
qed

definition comma_python_writer_boundary_link ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_sector_fragment option \<Rightarrow>
    comma_finite_position \<Rightarrow> bool" where
  "comma_python_writer_boundary_link p position pending boundary \<longleftrightarrow>
    (case pending of None \<Rightarrow> position = boundary
     | Some fragment \<Rightarrow>
        (case (position, boundary) of
          (Comma_Near f delta h, Comma_Near f' delta' h') \<Rightarrow>
            comma_python_near_fragment_shape fragment \<and>
            1 \<le> h' \<and> h' \<le> 540 \<and>
            comma_python_fragment_leading fragment = f \<and>
            comma_python_fragment_entering_digit fragment =
              comma_chart_value p boundary mod 10 \<and>
            f = f' \<and> delta = delta' \<and>
            comma_near_prefix
              (comma_python_fragment_literal_steps fragment) f h' h \<and>
            comma_python_fragment_displacement_at_scale fragment (10 ^ p) =
              int (comma_chart_value p position) -
                int (comma_chart_value p boundary)
        | _ \<Rightarrow> False))"

definition comma_python_cut_boundaries ::
  "nat \<Rightarrow> comma_finite_position \<Rightarrow>
    comma_python_sector_fragment list \<Rightarrow>
    comma_finite_position list \<Rightarrow> bool" where
  "comma_python_cut_boundaries p origin fragments boundaries \<longleftrightarrow>
    length boundaries = Suc (length fragments) \<and>
    boundaries ! 0 = origin \<and>
    (\<forall>i<length fragments.
      comma_python_fragment_displacement_at_scale (fragments ! i) (10 ^ p) =
        int (comma_chart_value p (boundaries ! Suc i)) -
          int (comma_chart_value p (boundaries ! i))) \<and>
    (\<forall>i<length fragments.
      comma_python_fragment_near_cut p (fragments ! i)
        (boundaries ! i) (boundaries ! Suc i))"

lemma comma_python_cut_boundaries_length:
  assumes "comma_python_cut_boundaries p origin fragments boundaries"
  shows "length boundaries = Suc (length fragments)"
  using assms by (simp add: comma_python_cut_boundaries_def)

lemma comma_python_cut_boundaries_start:
  assumes "comma_python_cut_boundaries p origin fragments boundaries"
  shows "boundaries ! 0 = origin"
  using assms by (simp add: comma_python_cut_boundaries_def)

lemma comma_python_cut_boundaries_append:
  assumes left: "comma_python_cut_boundaries p origin left left_bounds"
    and right:
      "comma_python_cut_boundaries p (last left_bounds) right right_bounds"
  shows "comma_python_cut_boundaries p origin (left @ right)
    (left_bounds @ tl right_bounds)"
proof -
  have left_length:
    "length left_bounds = Suc (length left)"
    using left by (rule comma_python_cut_boundaries_length)
  have right_length:
    "length right_bounds = Suc (length right)"
    using right by (rule comma_python_cut_boundaries_length)
  have right_start: "right_bounds ! 0 = last left_bounds"
    using comma_python_cut_boundaries_start[OF right] .
  have left_nonempty: "left_bounds \<noteq> []"
    using left_length by (cases left_bounds) auto
  have right_nonempty: "right_bounds \<noteq> []"
    using right_length by (cases right_bounds) auto
  have length:
    "length (left_bounds @ tl right_bounds) = Suc (length (left @ right))"
    using left_length right_length right_nonempty by simp
  have start: "(left_bounds @ tl right_bounds) ! 0 = origin"
    using left comma_python_cut_boundaries_start[OF left] left_nonempty
    by (simp add: comma_python_cut_boundaries_def)
  have edges:
    "\<forall>i<length (left @ right).
      comma_python_fragment_displacement_at_scale ((left @ right) ! i) (10 ^ p) =
        int (comma_chart_value p ((left_bounds @ tl right_bounds) ! Suc i)) -
          int (comma_chart_value p ((left_bounds @ tl right_bounds) ! i))"
  proof (intro allI impI)
    fix i assume i: "i < length (left @ right)"
    show "comma_python_fragment_displacement_at_scale ((left @ right) ! i) (10 ^ p) =
        int (comma_chart_value p ((left_bounds @ tl right_bounds) ! Suc i)) -
          int (comma_chart_value p ((left_bounds @ tl right_bounds) ! i))"
    proof (cases "i < length left")
      case True
      have edge:
        "comma_python_fragment_displacement_at_scale (left ! i) (10 ^ p) =
          int (comma_chart_value p (left_bounds ! Suc i)) -
            int (comma_chart_value p (left_bounds ! i))"
        using left True by (auto simp: comma_python_cut_boundaries_def)
      show ?thesis using edge True left_length by simp
    next
      case False
      then obtain j where j: "i = length left + j" by arith
      have j_bound: "j < length right" using i False j by simp
      have edge:
        "comma_python_fragment_displacement_at_scale (right ! j) (10 ^ p) =
          int (comma_chart_value p (right_bounds ! Suc j)) -
            int (comma_chart_value p (right_bounds ! j))"
        using right j_bound by (auto simp: comma_python_cut_boundaries_def)
      have start_equal: "right_bounds ! 0 = left_bounds ! length left"
        using right_start left_length left_nonempty by simp
      show ?thesis using edge j start_equal left_length right_length
        by (cases j) (simp_all add: nth_append)
    qed
  qed
  have paths:
    "\<forall>i<length (left @ right).
      comma_python_fragment_near_cut p ((left @ right) ! i)
        ((left_bounds @ tl right_bounds) ! i)
        ((left_bounds @ tl right_bounds) ! Suc i)"
  proof (intro allI impI)
    fix i assume i: "i < length (left @ right)"
    show "comma_python_fragment_near_cut p ((left @ right) ! i)
        ((left_bounds @ tl right_bounds) ! i)
        ((left_bounds @ tl right_bounds) ! Suc i)"
    proof (cases "i < length left")
      case True
      have path_left:
        "comma_python_fragment_near_cut p (left ! i)
          (left_bounds ! i) (left_bounds ! Suc i)"
        using left True by (auto simp: comma_python_cut_boundaries_def)
      show ?thesis using path_left True left_length by simp
    next
      case False
      then obtain j where j: "i = length left + j" by arith
      have j_bound: "j < length right" using i False j by simp
      have path_right:
        "comma_python_fragment_near_cut p (right ! j)
          (right_bounds ! j) (right_bounds ! Suc j)"
        using right j_bound by (auto simp: comma_python_cut_boundaries_def)
      have start_equal: "right_bounds ! 0 = left_bounds ! length left"
        using right_start left_length left_nonempty by simp
      show ?thesis using path_right j start_equal left_length right_length
        by (cases j) (simp_all add: nth_append)
    qed
  qed
  show ?thesis using length start edges paths
    by (simp add: comma_python_cut_boundaries_def)
qed

lemma comma_python_cut_boundaries_telescope:
  assumes cuts: "comma_python_cut_boundaries p origin fragments boundaries"
    and index: "i \<le> length fragments"
  shows "sum_list (map (\<lambda>g.
      comma_python_fragment_displacement_at_scale g (10 ^ p))
      (take i fragments)) =
    int (comma_chart_value p (boundaries ! i)) -
      int (comma_chart_value p origin)"
  using index
proof (induction i)
  case "0"
  have start: "boundaries ! 0 = origin"
    by (rule comma_python_cut_boundaries_start[OF cuts])
  then show ?case by simp
next
  case (Suc i)
  have previous: "i \<le> length fragments"
    using Suc.prems by simp
  have edge: "i < length fragments"
    using Suc.prems by simp
  have prefix:
    "sum_list (map (\<lambda>g.
        comma_python_fragment_displacement_at_scale g (10 ^ p))
        (take i fragments)) =
      int (comma_chart_value p (boundaries ! i)) -
        int (comma_chart_value p origin)"
    by (rule Suc.IH[OF previous])
  have adjacent:
    "comma_python_fragment_displacement_at_scale (fragments ! i) (10 ^ p) =
      int (comma_chart_value p (boundaries ! Suc i)) -
        int (comma_chart_value p (boundaries ! i))"
    using cuts edge by (auto simp: comma_python_cut_boundaries_def)
  show ?case using prefix adjacent Suc.prems
    by (simp add: take_Suc_conv_app_nth sum_list_append algebra_simps)
qed

lemma comma_python_writer_edge_boundary_cuts:
  assumes exponent: "5 \<le> p"
    and admitted: "comma_round_admitted source"
    and phase: "comma_python_pending_phase p source pending"
    and link: "comma_python_writer_boundary_link p source pending boundary"
    and edge: "comma_python_writer_edge p source successor weight pending
      emitted pending'"
  obtains boundary' where
    next_link:
      "comma_python_writer_boundary_link p successor pending' boundary'"
    and cuts:
      "comma_python_cut_boundaries p boundary emitted local_bounds"
    and end: "boundary' = last local_bounds"
proof -
  show thesis
    using edge exponent admitted phase link
  proof (induction rule: comma_python_writer_edge.induct)
    case (entry p f delta offset headroom weight pending)
    let ?source = "Comma_Entry f delta offset"
    let ?successor = "Comma_Near f delta headroom"
    let ?fragment = "comma_python_entry_sector_fragment f delta offset headroom"
    have pending_none: "pending = None"
      using entry.prems(3) by (cases pending)
        (auto simp: comma_python_pending_phase_def)
    have boundary_source: "boundary = ?source"
      using entry.prems(4) pending_none by (simp add:
        comma_python_writer_boundary_link_def)
    have displacement:
      "comma_python_fragment_displacement_at_scale ?fragment (10 ^ p) =
        int (comma_chart_value p ?successor) -
          int (comma_chart_value p ?source)"
      using entry.hyps(1) by (simp add: comma_python_fragment_record_matches_def)
    have cuts:
      "comma_python_cut_boundaries p boundary [?fragment]
        [boundary, ?successor]"
      using displacement boundary_source
      by (simp add: comma_python_cut_boundaries_def)
    have link':
      "comma_python_writer_boundary_link p ?successor None ?successor"
      by (simp add: comma_python_writer_boundary_link_def)
    show thesis
      by (rule entry.prems(5)[where boundary'="?successor"
            and local_bounds="[boundary, ?successor]"])
        (use cuts link' in simp_all)
  next
    case (near_start p f delta headroom next_headroom weight increment)
    let ?source = "Comma_Near f delta headroom"
    let ?successor = "Comma_Near f delta next_headroom"
    let ?fragment = "comma_python_literal_fragment f
      (comma_chart_value p ?source mod 10) 1 increment"
    have boundary_source: "boundary = ?source"
      using near_start.prems(4) by (simp add:
        comma_python_writer_boundary_link_def)
    have displacement:
      "comma_python_fragment_displacement_at_scale ?fragment (10 ^ p) =
        int (comma_chart_value p ?successor) - int (comma_chart_value p ?source)"
      using near_start.hyps(1)
      by (simp add: comma_python_fragment_record_matches_def)
    have f_range: "1 \<le> f" "f \<le> 9"
      using near_start.prems(2) by simp_all
    have fragment_shape: "comma_python_near_fragment_shape ?fragment"
      by (rule comma_python_literal_fragment_near_shape[OF f_range, of
        "comma_chart_value p ?source mod 10" 1 increment])
    have fragment_digit:
      "comma_python_fragment_entering_digit ?fragment =
        comma_chart_value p boundary mod 10"
      using boundary_source by simp
    have near_path:
      "comma_near_prefix 1 f headroom next_headroom"
      by (rule comma_python_near_record_prefix[OF near_start.hyps(1)])
    have next_link:
      "comma_python_writer_boundary_link p ?successor (Some ?fragment) boundary"
      using displacement boundary_source fragment_shape fragment_digit near_path
      by (simp add: comma_python_writer_boundary_link_def
          fragment_shape)
    have cuts: "comma_python_cut_boundaries p boundary [] [boundary]"
      by (simp add: comma_python_cut_boundaries_def)
    show thesis
      by (rule near_start.prems(5)[where boundary'=boundary
            and local_bounds="[boundary]"])
        (use cuts next_link in simp_all add:
          comma_python_writer_boundary_link_def)
  next
    case (near_merge pending_fragment p f delta headroom next_headroom weight
        increment)
    let ?source = "Comma_Near f delta headroom"
    let ?successor = "Comma_Near f delta next_headroom"
    let ?literal = "comma_python_literal_fragment f
      (comma_chart_value p ?source mod 10) 1 increment"
    have f_range: "1 \<le> f" "f \<le> 9"
      using near_merge.prems(2) by simp_all
    let ?merged = "comma_python_merge_near_fragments pending_fragment ?literal"
    obtain f' delta' h' where boundary_shape:
        "boundary = Comma_Near f' delta' h'"
      using near_merge.prems(4)
      by (cases boundary)
        (auto simp: comma_python_writer_boundary_link_def)
    have boundary_phase: "f = f'" "delta = delta'"
      using near_merge.prems(4) boundary_shape
      by (simp_all add: comma_python_writer_boundary_link_def)
    have pending_displacement:
      "comma_python_fragment_displacement_at_scale pending_fragment (10 ^ p) =
        int (comma_chart_value p ?source) - int (comma_chart_value p boundary)"
      using near_merge.prems(4) boundary_shape
      by (simp add: comma_python_writer_boundary_link_def)
    have pending_path:
      "comma_near_prefix
        (comma_python_fragment_literal_steps pending_fragment) f h' headroom"
      using near_merge.prems(4) boundary_shape
      by (simp add: comma_python_writer_boundary_link_def)
    have pending_digit:
      "comma_python_fragment_entering_digit pending_fragment =
        comma_chart_value p boundary mod 10"
      using near_merge.prems(4) boundary_shape
      by (simp add: comma_python_writer_boundary_link_def)
    have literal_path:
      "comma_near_prefix 1 f headroom next_headroom"
      by (rule comma_python_near_record_prefix[OF near_merge.hyps(2)])
    have literal_displacement:
      "comma_python_fragment_displacement_at_scale ?literal (10 ^ p) =
        int (comma_chart_value p ?successor) - int (comma_chart_value p ?source)"
      using near_merge.hyps(2)
      by (simp add: comma_python_fragment_record_matches_def)
    have merged_displacement:
      "comma_python_fragment_displacement_at_scale ?merged (10 ^ p) =
        int (comma_chart_value p ?successor) - int (comma_chart_value p boundary)"
      using comma_python_merge_near_preserves_displacement
        [OF near_merge.hyps(1), of "10 ^ p"]
        pending_displacement literal_displacement by linarith
    have merged_shape: "comma_python_near_fragment_shape ?merged"
      by (rule comma_python_merge_near_shape[OF near_merge.hyps(1)])
    have pending_leading:
      "comma_python_fragment_leading pending_fragment = f"
      using near_merge.prems(4)
      by (simp add: comma_python_writer_boundary_link_def)
    have merged_fields:
      "comma_python_fragment_leading ?merged = f"
      using comma_python_merge_near_fields(1)[OF near_merge.hyps(1)]
        pending_leading by simp
    have merged_digit:
      "comma_python_fragment_entering_digit ?merged =
        comma_chart_value p boundary mod 10"
      using comma_python_merge_near_fields(2)[OF near_merge.hyps(1)]
        pending_digit by simp
    have merged_path:
      "comma_near_prefix
        (comma_python_fragment_literal_steps ?merged) f h' next_headroom"
    proof -
      have appended:
        "comma_near_prefix
          (comma_python_fragment_literal_steps pending_fragment + 1)
          f h' next_headroom"
        by (rule comma_near_prefix_append[OF pending_path literal_path])
      show ?thesis using appended near_merge.hyps(1)
        by (simp add: comma_python_merge_near_fragments_def
            comma_python_near_fragments_compatible_def)
    qed
    have next_link:
      "comma_python_writer_boundary_link p ?successor (Some ?merged) boundary"
      using merged_shape merged_fields merged_digit merged_path
        merged_displacement boundary_shape
        boundary_phase
      by (simp add: comma_python_writer_boundary_link_def)
    have cuts: "comma_python_cut_boundaries p boundary [] [boundary]"
      by (simp add: comma_python_cut_boundaries_def)
    show thesis
      by (rule near_merge.prems(5)[where boundary'=boundary
            and local_bounds="[boundary]"])
        (use cuts next_link in simp_all add:
          comma_python_writer_boundary_link_def)
  next
    case (near_cross p f delta headroom g next_delta offset weight pending
        increment)
    let ?source = "Comma_Near f delta headroom"
    let ?successor = "Comma_Entry g next_delta offset"
    let ?literal = "comma_python_literal_fragment f
      (comma_chart_value p ?source mod 10) 1 increment"
    have f_range: "1 \<le> f" "f \<le> 9"
      using near_cross.prems(2) by simp_all
    have displacement:
      "comma_python_fragment_displacement_at_scale ?literal (10 ^ p) =
        int (comma_chart_value p ?successor) - int (comma_chart_value p ?source)"
      using near_cross.hyps(1)
      by (simp add: comma_python_fragment_record_matches_def)
    have current_finite:
      "comma_finite_step (p mod 924) ?source = Comma_Next ?successor"
      using near_cross.hyps(1)
      by (simp add: comma_finite_step_def
          comma_python_fragment_record_matches_def)
    show thesis
    proof (cases pending)
      case None
      have boundary_source: "boundary = ?source"
        using near_cross.prems(4) None
        by (simp add: comma_python_writer_boundary_link_def)
      have cuts:
        "comma_python_cut_boundaries p boundary [?literal]
          [boundary, ?successor]"
        using displacement boundary_source current_finite
        by (simp add: comma_python_cut_boundaries_def
            comma_python_fragment_near_cut_def
            comma_python_literal_fragment_near_shape f_range)
      have next_link:
        "comma_python_writer_boundary_link p ?successor None ?successor"
        by (simp add: comma_python_writer_boundary_link_def)
      show thesis
        by (rule near_cross.prems(5)[where boundary'="?successor"
              and local_bounds="[boundary, ?successor]"])
          (use cuts next_link in simp_all)
    next
      case (Some pending_fragment)
      obtain f' delta' h' where boundary_shape:
        "boundary = Comma_Near f' delta' h'"
        and pending_displacement:
        "comma_python_fragment_displacement_at_scale pending_fragment (10 ^ p) =
          int (comma_chart_value p ?source) - int (comma_chart_value p boundary)"
        using near_cross.prems(4) Some by (cases boundary)
          (auto simp: comma_python_writer_boundary_link_def
            split: comma_finite_position.splits)
      let ?bounds = "[boundary, ?source, ?successor]"
      have cuts:
        "comma_python_cut_boundaries p boundary
          [pending_fragment, ?literal] ?bounds"
        using pending_displacement displacement boundary_shape current_finite
          near_cross.prems(4) Some
        by (simp add: comma_python_cut_boundaries_def
            comma_python_fragment_near_cut_def
            comma_python_literal_fragment_near_shape
            comma_python_writer_boundary_link_def f_range)
      have next_link:
        "comma_python_writer_boundary_link p ?successor None ?successor"
        by (simp add: comma_python_writer_boundary_link_def)
      show thesis
        by (rule near_cross.prems(5)[where boundary'="?successor"
              and local_bounds=?bounds])
          (use cuts next_link in simp_all)
    qed
  qed
qed

theorem comma_python_first_terminal_walk_writer_cut_boundaries:
  fixes p source pending boundary events outcome terminal
  assumes exponent: "5 \<le> p"
    and walk: "comma_python_first_terminal_walk p source events outcome terminal"
    and admitted: "comma_round_admitted source"
    and phase: "comma_python_pending_phase p source pending"
    and link: "comma_python_writer_boundary_link p source pending boundary"
  obtains fragments boundaries where
    run: "comma_python_writer_run p source pending events outcome terminal fragments"
    and aligned:
      "comma_python_cut_boundaries p boundary fragments boundaries"
    and guards:
      "\<forall>g\<in>set fragments.
        comma_python_fragment_scale_guard g (10 ^ p)"
proof -
  show thesis
    using walk exponent admitted phase link
  proof (induction arbitrary: pending boundary
      rule: comma_python_first_terminal_walk.induct)
    case (fork p source a delta)
    let ?fragments = "comma_python_flush_near pending"
    show thesis
    proof (cases pending)
      case None
      have boundary_source: "boundary = source"
        using fork.prems(4) None
        by (simp add: comma_python_writer_boundary_link_def)
      have run:
        "comma_python_writer_run p source None [] (Comma_Fork_At a delta)
          source []"
        using fork.hyps(1) by (rule comma_python_writer_run.fork) simp
      have aligned: "comma_python_cut_boundaries p boundary [] [boundary]"
        by (simp add: comma_python_cut_boundaries_def)
      have guards: "\<forall>g\<in>set ([] :: comma_python_sector_fragment list).
          comma_python_fragment_scale_guard g (10 ^ p)"
        by simp
      show thesis using run aligned guards
        by (rule fork.prems(5)[where fragments="[]" and boundaries="[boundary]"])
          simp_all
    next
      case (Some fragment)
      have displacement:
        "comma_python_fragment_displacement_at_scale fragment (10 ^ p) =
          int (comma_chart_value p source) - int (comma_chart_value p boundary)"
        using fork.prems(4) Some by (auto simp:
          comma_python_writer_boundary_link_def split: comma_finite_position.splits)
      have run:
        "comma_python_writer_run p source (Some fragment) []
          (Comma_Fork_At a delta) source [fragment]"
        using fork.hyps(1) by (rule comma_python_writer_run.fork) simp
      have aligned:
        "comma_python_cut_boundaries p boundary [fragment] [boundary, source]"
        using displacement fork.prems(4) Some
        by (simp add: comma_python_cut_boundaries_def
            comma_python_fragment_near_cut_def
            comma_python_writer_boundary_link_def)
      have guards:
        "\<forall>g\<in>set [fragment]. comma_python_fragment_scale_guard g (10 ^ p)"
        by (rule comma_python_pending_flush_scale_guards[OF fork.prems(3)])
          (simp add: Some comma_python_flush_near_def)
      show thesis using run aligned guards
        by (rule fork.prems(5)[where fragments="[fragment]"
              and boundaries="[boundary, source]"])
          simp_all
    qed
  next
    case (landmine p source delta)
    let ?fragments = "comma_python_flush_near pending"
    show thesis
    proof (cases pending)
      case None
      have run:
        "comma_python_writer_run p source None [] (Comma_Landmine_At delta)
          source []"
        using landmine.hyps(1) by (rule comma_python_writer_run.landmine) simp
      have aligned: "comma_python_cut_boundaries p boundary [] [boundary]"
        using landmine.prems(4) None
        by (simp add: comma_python_writer_boundary_link_def
            comma_python_cut_boundaries_def)
      have guards: "\<forall>g\<in>set ([] :: comma_python_sector_fragment list).
          comma_python_fragment_scale_guard g (10 ^ p)"
        by simp
      show thesis using run aligned guards
        by (rule landmine.prems(5)[where fragments="[]" and boundaries="[boundary]"])
          simp_all
    next
      case (Some fragment)
      have displacement:
        "comma_python_fragment_displacement_at_scale fragment (10 ^ p) =
          int (comma_chart_value p source) - int (comma_chart_value p boundary)"
        using landmine.prems(4) Some by (auto simp:
          comma_python_writer_boundary_link_def split: comma_finite_position.splits)
      have run:
        "comma_python_writer_run p source (Some fragment) []
          (Comma_Landmine_At delta) source [fragment]"
        using landmine.hyps(1) by (rule comma_python_writer_run.landmine) simp
      have aligned:
        "comma_python_cut_boundaries p boundary [fragment] [boundary, source]"
        using displacement landmine.prems(4) Some
        by (simp add: comma_python_cut_boundaries_def
            comma_python_fragment_near_cut_def
            comma_python_writer_boundary_link_def)
      have guards:
        "\<forall>g\<in>set [fragment]. comma_python_fragment_scale_guard g (10 ^ p)"
        by (rule comma_python_pending_flush_scale_guards[OF landmine.prems(3)])
          (simp add: Some comma_python_flush_near_def)
      show thesis using run aligned guards
        by (rule landmine.prems(5)[where fragments="[fragment]"
              and boundaries="[boundary, source]"])
          simp_all
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
        [OF advance.prems(1) advance.prems(2) advance.prems(3) advance.hyps(1)]
      by blast
    obtain next_boundary local_bounds where local_link:
        "comma_python_writer_boundary_link p successor next_pending next_boundary"
      and local_cuts:
        "comma_python_cut_boundaries p boundary emitted local_bounds"
      and next_eq: "next_boundary = last local_bounds"
      using comma_python_writer_edge_boundary_cuts
        [OF advance.prems(1) advance.prems(2) advance.prems(3)
          advance.prems(4) edge] by blast
    obtain tail_fragments tail_bounds where tail_run:
        "comma_python_writer_run p successor next_pending events outcome terminal
          tail_fragments"
      and tail_aligned:
        "comma_python_cut_boundaries p next_boundary tail_fragments tail_bounds"
      and tail_guards:
        "\<forall>g\<in>set tail_fragments.
          comma_python_fragment_scale_guard g (10 ^ p)"
      using advance.IH[OF advance.prems(1) successor_admitted next_phase local_link]
      by blast
    have emitted_guards:
      "\<forall>g\<in>set emitted.
        comma_python_fragment_scale_guard g (10 ^ p)"
      by (rule comma_python_writer_edge_emitted_scale_guards
        [OF advance.prems(1) advance.prems(2) advance.prems(3) edge])
    have run:
      "comma_python_writer_run p source pending
        (Comma_Python_Advance source successor weight # events)
        outcome terminal (emitted @ tail_fragments)"
      by (rule comma_python_writer_run.advance
        [OF advance.hyps(1) edge tail_run])
    have tail_aligned':
      "comma_python_cut_boundaries p (last local_bounds) tail_fragments tail_bounds"
      using tail_aligned next_eq by simp
    have aligned:
      "comma_python_cut_boundaries p boundary (emitted @ tail_fragments)
        (local_bounds @ tl tail_bounds)"
      by (rule comma_python_cut_boundaries_append[OF local_cuts tail_aligned'])
    have guards:
      "\<forall>g\<in>set (emitted @ tail_fragments).
        comma_python_fragment_scale_guard g (10 ^ p)"
      using emitted_guards tail_guards by auto
    show thesis using run aligned guards
      by (rule advance.prems(5)[where fragments="emitted @ tail_fragments"
            and boundaries="local_bounds @ tl tail_bounds"])
        simp_all
  qed
qed

theorem comma_python_actual_writer_prefix_sources:
  fixes p :: nat
  assumes exponent: "5 \<le> p"
    and walk: "comma_python_first_terminal_walk p source events outcome terminal"
    and admitted: "comma_round_admitted source"
  obtains fragments boundaries where
    run: "comma_python_writer_run p source None events outcome terminal fragments"
    and aligned:
      "comma_python_cut_boundaries p source fragments boundaries"
    and prefix_source:
      "\<forall>i\<le>length fragments.
        comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
          int (comma_chart_value p (boundaries ! i)) -
            int (comma_chart_value p source)"
    and prefix_weight:
      "\<forall>i\<le>length fragments.
        comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        sum_list (map (\<lambda>g.
          comma_python_fragment_weight_at_scale g (10 ^ p))
          (take i fragments))"
proof -
  have phase: "comma_python_pending_phase p source None"
    by (simp add: comma_python_pending_phase_def)
  have link: "comma_python_writer_boundary_link p source None source"
    by (simp add: comma_python_writer_boundary_link_def)
  obtain fragments boundaries where run:
      "comma_python_writer_run p source None events outcome terminal fragments"
    and aligned: "comma_python_cut_boundaries p source fragments boundaries"
    and guards: "\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    using comma_python_first_terminal_walk_writer_cut_boundaries
      [OF exponent walk admitted phase link] by blast
  have prefix_source:
    "\<forall>i\<le>length fragments.
      comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        int (comma_chart_value p (boundaries ! i)) -
          int (comma_chart_value p source)"
  proof (intro allI impI)
    fix i assume index: "i \<le> length fragments"
    have published:
      "comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        sum_list (map (\<lambda>g.
          comma_python_fragment_displacement_at_scale g (10 ^ p))
          (take i fragments))"
      by (rule comma_python_published_prefixes_at_scale(2)
        [OF guards index])
    have telescope:
      "sum_list (map (\<lambda>g.
          comma_python_fragment_displacement_at_scale g (10 ^ p))
          (take i fragments)) =
        int (comma_chart_value p (boundaries ! i)) -
          int (comma_chart_value p source)"
      by (rule comma_python_cut_boundaries_telescope[OF aligned index])
    show "comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        int (comma_chart_value p (boundaries ! i)) -
          int (comma_chart_value p source)"
    using published telescope by simp
  qed
  have prefix_weight:
    "\<forall>i\<le>length fragments.
      comma_python_affine_evaluate
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
      sum_list (map (\<lambda>g.
        comma_python_fragment_weight_at_scale g (10 ^ p))
        (take i fragments))"
  proof (intro allI impI)
    fix i assume index: "i \<le> length fragments"
    show "comma_python_affine_evaluate
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
      sum_list (map (\<lambda>g.
        comma_python_fragment_weight_at_scale g (10 ^ p))
        (take i fragments))"
      by (rule comma_python_published_prefixes_at_scale(1)
        [OF guards index])
  qed
  show thesis using run aligned prefix_source prefix_weight by (rule that)
qed

lemma comma_python_published_point_base_is_cut_source:
  assumes prefix_source:
      "comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        int (comma_chart_value p (boundaries ! i)) -
          int (comma_chart_value p source)"
    and nonnegative:
      "0 \<le> comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p)"
  shows "int (comma_chart_value p source +
      nat (comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p))) =
    int (comma_chart_value p (boundaries ! i))"
proof -
  have natural_value:
    "int (nat (comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p))) =
      comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p)"
    using nonnegative by simp
  show ?thesis using prefix_source natural_value by simp
qed

lemmas comma_python_producer_cut_refinement_oracle_audit_bundle =
  comma_python_cut_boundaries_append
  comma_python_cut_boundaries_telescope
  comma_python_writer_edge_boundary_cuts
  comma_python_first_terminal_walk_writer_cut_boundaries
  comma_python_actual_writer_prefix_sources
  comma_python_published_point_base_is_cut_source
ML \<open>val _ = if null (Thm_Deps.all_oracles
  @{thms comma_python_producer_cut_refinement_oracle_audit_bundle}) then ()
  else error "Comma_Semantic_Producer_Cut_Refinement local oracle audit failed"\<close>

end
