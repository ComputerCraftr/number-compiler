theory Comma_Semantic_Producer_Prefix_Refinement
  imports Comma_Semantic_Producer_Trace_Bridge
begin

text \<open>This owner derives the published prefix guards from the actual
first-terminal writer.  Entry fragments use the checked exact cycle quotient;
Near fragments use their record shape and natural literal fields.  These
guards then compose through the same normalized affine addition used by the
runtime prefix arrays.\<close>

definition comma_python_fragment_scale_guard ::
  "comma_python_sector_fragment \<Rightarrow> nat \<Rightarrow> bool" where
  "comma_python_fragment_scale_guard g S \<longleftrightarrow>
    0 < comma_python_affine_denominator
      (comma_python_fragment_weight_affine g) \<and>
    comma_python_affine_divides (comma_python_fragment_weight_affine g) S \<and>
    comma_python_affine_evaluate (comma_python_fragment_weight_affine g) S =
      comma_python_fragment_weight_at_scale g S \<and>
    0 \<le> comma_python_fragment_weight_at_scale g S \<and>
    0 < comma_python_affine_denominator
      (comma_python_fragment_displacement_affine g) \<and>
    comma_python_affine_divides
      (comma_python_fragment_displacement_affine g) S \<and>
    comma_python_affine_evaluate
      (comma_python_fragment_displacement_affine g) S =
      comma_python_fragment_displacement_at_scale g S \<and>
    0 \<le> comma_python_fragment_displacement_at_scale g S"

definition comma_python_fragment_weight_at_exponent ::
  "nat \<Rightarrow> comma_python_sector_fragment \<Rightarrow> int" where
  "comma_python_fragment_weight_at_exponent p g =
    comma_python_fragment_weight_at_scale g (10 ^ p)"

definition comma_python_fragment_displacement_at_exponent ::
  "nat \<Rightarrow> comma_python_sector_fragment \<Rightarrow> int" where
  "comma_python_fragment_displacement_at_exponent p g =
    comma_python_fragment_displacement_at_scale g (10 ^ p)"

lemma comma_python_affine_times_exact_at_scale:
  fixes a :: comma_python_affine_weight and S n :: nat
  assumes positive: "0 < comma_python_affine_denominator a"
    and exact: "comma_python_affine_divides a S"
  shows "0 < comma_python_affine_denominator
      (comma_python_affine_times n a)"
    and "comma_python_affine_divides (comma_python_affine_times n a) S"
    and "comma_python_affine_evaluate (comma_python_affine_times n a) S =
      int n * comma_python_affine_evaluate a S"
proof -
  let ?D = "comma_python_affine_denominator a"
  let ?N = "comma_python_affine_scale a * int S +
    comma_python_affine_offset a"
  let ?A = "int n * comma_python_affine_scale a"
  let ?B = "int n * comma_python_affine_offset a"
  obtain k where numerator: "?N = int ?D * k"
    using exact by (auto simp: comma_python_affine_divides_def dvd_def)
  have raw_factor: "?A * int S + ?B = int ?D * (int n * k)"
    using numerator by (simp add: algebra_simps)
  have raw_exact: "int ?D dvd (?A * int S + ?B)"
    unfolding dvd_def using raw_factor by blast
  have normalized_positive:
    "0 < comma_python_affine_denominator
      (comma_python_affine_normalize ?A ?B ?D)"
    by (rule comma_python_affine_normalize_positive_denominator[OF positive])
  have normalized_exact:
    "int (comma_python_affine_denominator
        (comma_python_affine_normalize ?A ?B ?D)) dvd
      (comma_python_affine_scale (comma_python_affine_normalize ?A ?B ?D) *
        int S + comma_python_affine_offset
          (comma_python_affine_normalize ?A ?B ?D))"
    by (rule comma_python_affine_normalize_evaluate_exact(2)
      [OF positive raw_exact])
  have eval_a: "comma_python_affine_evaluate a S = k"
  proof -
    have integral: "comma_python_affine_evaluate a S * int ?D = ?N"
      by (rule comma_python_affine_evaluate_integral)
        (use exact in \<open>simp add: comma_python_affine_divides_def\<close>)
    have nonzero: "int ?D \<noteq> 0" using positive by simp
    show ?thesis using integral numerator nonzero
      by (metis mult_left_cancel mult.commute)
  qed
  have eval_raw:
    "(?A * int S + ?B) div int ?D = int n * k"
    using raw_factor positive by (simp add: div_mult_self4)
  have eval_normalized:
    "comma_python_affine_evaluate
        (comma_python_affine_normalize ?A ?B ?D) S = int n * k"
    using comma_python_affine_normalize_evaluate_exact(1)
      [OF positive raw_exact] eval_raw by simp
  show "0 < comma_python_affine_denominator
      (comma_python_affine_times n a)"
    using normalized_positive by (simp add: comma_python_affine_times_def)
  show "comma_python_affine_divides (comma_python_affine_times n a) S"
    using normalized_exact
    by (simp add: comma_python_affine_times_def comma_python_affine_divides_def)
  show "comma_python_affine_evaluate (comma_python_affine_times n a) S =
      int n * comma_python_affine_evaluate a S"
    using eval_normalized eval_a
    by (simp add: comma_python_affine_times_def)
qed

lemma comma_python_constant_affine_exact_at_scale:
  "0 < comma_python_affine_denominator (comma_python_constant_affine n)"
  "comma_python_affine_divides (comma_python_constant_affine n) S"
  "comma_python_affine_evaluate (comma_python_constant_affine n) S = int n"
  by (simp_all add: comma_python_constant_affine_def
      comma_python_affine_normalize_def comma_python_affine_divides_def
      comma_python_affine_evaluate_def Let_def)

lemma comma_python_near_fragment_scale_guard:
  assumes shape: "comma_python_near_fragment_shape g"
  shows "comma_python_fragment_scale_guard g S"
  using shape
  by (auto simp: comma_python_fragment_scale_guard_def
      comma_python_fragment_weight_affine_def
      comma_python_fragment_displacement_affine_def
      comma_python_affine_times_def comma_python_constant_affine_def
      comma_python_affine_add_def comma_python_affine_normalize_def
      comma_python_affine_zero_def comma_python_near_fragment_shape_def
      comma_python_fragment_weight_at_scale_def
      comma_python_fragment_displacement_at_scale_def
      comma_python_affine_divides_def comma_python_affine_evaluate_def Let_def)

lemma comma_python_literal_fragment_scale_guard:
  "comma_python_fragment_scale_guard
    (comma_python_literal_fragment f digit steps increment) S"
  by (simp add: comma_python_fragment_scale_guard_def
      comma_python_fragment_weight_affine_def
      comma_python_fragment_displacement_affine_def
      comma_python_affine_times_def comma_python_constant_affine_def
      comma_python_affine_add_def comma_python_affine_normalize_def
      comma_python_affine_zero_def comma_python_fragment_weight_at_scale_def
      comma_python_fragment_displacement_at_scale_def
      comma_python_affine_divides_def comma_python_affine_evaluate_def Let_def)

lemma comma_python_entry_fragment_scale_guard:
  fixes f p delta offset :: nat
  assumes f: "1 \<le> f" "f \<le> 9"
    and exponent: "5 \<le> p"
    and offset: "offset \<le> 98"
  defines "h \<equiv> comma_finite_headroom f (p mod 924) delta offset"
    and "P \<equiv> comma_finite_period f (offset mod 10)"
    and "L \<equiv> comma_cycle_length f"
    and "c \<equiv> (10 ^ (p + delta) - offset - h) div P"
    and "fragment \<equiv> comma_python_entry_sector_fragment f delta offset h"
  shows "comma_python_fragment_scale_guard fragment (10 ^ p)"
proof -
  note exact = comma_python_entry_fragment_refines_chart_move
    [OF f exponent offset, of delta]
  have cycle_positive:
    "0 < comma_python_affine_denominator
      (comma_python_fragment_complete_cycles fragment)"
    using exact(2) by (simp add: fragment_def)
  have cycle_divides:
    "comma_python_affine_divides
      (comma_python_fragment_complete_cycles fragment) (10 ^ p)"
    using exact(3) by (simp add: fragment_def)
  have cycle_value:
    "comma_python_affine_evaluate
      (comma_python_fragment_complete_cycles fragment) (10 ^ p) = int c"
    using exact(4) by (simp add: fragment_def)
  have zero_positive:
    "0 < comma_python_affine_denominator (comma_python_constant_affine 0)"
    by (rule comma_python_constant_affine_exact_at_scale(1))
  have zero_divides:
    "comma_python_affine_divides (comma_python_constant_affine 0) (10 ^ p)"
    by (rule comma_python_constant_affine_exact_at_scale(2))
  have weight_time:
    "0 < comma_python_affine_denominator
        (comma_python_affine_times L
          (comma_python_fragment_complete_cycles fragment))"
    "comma_python_affine_divides
        (comma_python_affine_times L
          (comma_python_fragment_complete_cycles fragment)) (10 ^ p)"
    "comma_python_affine_evaluate
        (comma_python_affine_times L
          (comma_python_fragment_complete_cycles fragment)) (10 ^ p) =
      int L * int c"
    using comma_python_affine_times_exact_at_scale
      [OF cycle_positive cycle_divides, of L] cycle_value
    by simp_all
  have displacement_time:
    "0 < comma_python_affine_denominator
        (comma_python_affine_times P
          (comma_python_fragment_complete_cycles fragment))"
    "comma_python_affine_divides
        (comma_python_affine_times P
          (comma_python_fragment_complete_cycles fragment)) (10 ^ p)"
    "comma_python_affine_evaluate
        (comma_python_affine_times P
          (comma_python_fragment_complete_cycles fragment)) (10 ^ p) =
      int P * int c"
    using comma_python_affine_times_exact_at_scale
      [OF cycle_positive cycle_divides, of P] cycle_value
    by simp_all
  have weight_add_positive:
    "0 < comma_python_affine_denominator
      (comma_python_affine_add
        (comma_python_affine_times L
          (comma_python_fragment_complete_cycles fragment))
        (comma_python_constant_affine 0))"
    by (rule comma_python_affine_add_positive[OF weight_time(1) zero_positive])
  have displacement_add_positive:
    "0 < comma_python_affine_denominator
      (comma_python_affine_add
        (comma_python_affine_times P
          (comma_python_fragment_complete_cycles fragment))
        (comma_python_constant_affine 0))"
    by (rule comma_python_affine_add_positive
      [OF displacement_time(1) zero_positive])
  note weight_add = comma_python_affine_add_exact_at_scale
    [OF weight_time(1) zero_positive weight_time(2) zero_divides]
  note displacement_add = comma_python_affine_add_exact_at_scale
    [OF displacement_time(1) zero_positive displacement_time(2) zero_divides]
  have weight_value:
    "comma_python_affine_evaluate
      (comma_python_fragment_weight_affine fragment) (10 ^ p) =
      comma_python_fragment_weight_at_scale fragment (10 ^ p)"
    using weight_add(2) weight_time(3)
    by (simp add: comma_python_fragment_weight_affine_def fragment_def
        comma_python_entry_sector_fragment_def comma_python_constant_affine_def
        comma_python_affine_normalize_def comma_python_affine_evaluate_def Let_def)
  have displacement_value:
    "comma_python_affine_evaluate
      (comma_python_fragment_displacement_affine fragment) (10 ^ p) =
      comma_python_fragment_displacement_at_scale fragment (10 ^ p)"
    using displacement_add(2) displacement_time(3)
    by (simp add: comma_python_fragment_displacement_affine_def fragment_def
        comma_python_entry_sector_fragment_def comma_python_constant_affine_def
        comma_python_affine_normalize_def comma_python_affine_evaluate_def Let_def)
  have weight_nonnegative:
    "0 \<le> comma_python_fragment_weight_at_scale fragment (10 ^ p)"
    using cycle_value f
    by (simp add: comma_python_fragment_weight_at_scale_def fragment_def
        comma_python_entry_sector_fragment_def Let_def)
  have displacement_nonnegative:
    "0 \<le> comma_python_fragment_displacement_at_scale fragment (10 ^ p)"
    using cycle_value
    by (simp add: comma_python_fragment_displacement_at_scale_def fragment_def
        comma_python_entry_sector_fragment_def Let_def)
  show ?thesis
    using weight_add(1) displacement_add(1) weight_add_positive
      displacement_add_positive weight_value displacement_value
      weight_nonnegative displacement_nonnegative
    by (simp add: comma_python_fragment_scale_guard_def
        comma_python_fragment_weight_affine_def
        comma_python_fragment_displacement_affine_def fragment_def
        comma_python_entry_sector_fragment_def comma_python_constant_affine_def
        comma_python_affine_normalize_def comma_python_affine_divides_def
        comma_python_affine_evaluate_def Let_def)
qed

lemma comma_python_pending_flush_scale_guards:
  assumes phase: "comma_python_pending_phase p position pending"
  shows "\<forall>g\<in>set (comma_python_flush_near pending).
    comma_python_fragment_scale_guard g S"
proof (cases pending)
  case None
  then show ?thesis by (simp add: comma_python_flush_near_def)
next
  case (Some fragment)
  have shape: "comma_python_near_fragment_shape fragment"
    using phase Some by (cases position)
      (auto simp: comma_python_pending_phase_def)
  then show ?thesis using Some
    by (simp add: comma_python_flush_near_def
        comma_python_near_fragment_scale_guard)
qed

lemma comma_python_writer_edge_emitted_scale_guards:
  assumes exponent: "5 \<le> p"
    and admitted: "comma_round_admitted source"
    and phase: "comma_python_pending_phase p source pending"
    and edge: "comma_python_writer_edge p source successor weight pending
      emitted pending'"
  shows "\<forall>g\<in>set emitted. comma_python_fragment_scale_guard g (10 ^ p)"
  using edge exponent admitted phase
proof (induction rule: comma_python_writer_edge.induct)
  case (entry p f delta offset headroom weight pending)
  have admitted': "comma_round_admitted (Comma_Entry f delta offset)"
    using entry.prems(2) by simp
  have f: "1 \<le> f" "f \<le> 9" and offset: "offset \<le> 98"
    using admitted' by simp_all
  let ?h = "comma_finite_headroom f (p mod 924) delta offset"
  let ?P = "comma_finite_period f (offset mod 10)"
  let ?L = "comma_cycle_length f"
  have expected:
    "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta ?h)
        (Comma_Chart_Weight ?L delta (- int (?L * (offset + ?h))) ?P)"
    using comma_entry_chart_exact_literal_path(7)[OF f entry.prems(1) offset,
        of delta] by simp
  have matched:
    "comma_weighted_step (p mod 924) (Comma_Entry f delta offset) =
      Comma_WNext (Comma_Near f delta headroom) weight"
    using entry.hyps(1)
    by (simp add: comma_python_fragment_record_matches_def)
  have headroom: "headroom = ?h"
    and weight: "weight =
      Comma_Chart_Weight ?L delta (- int (?L * (offset + ?h))) ?P"
    using matched expected by injection auto
  have entry_guard:
    "comma_python_fragment_scale_guard
      (comma_python_entry_sector_fragment f delta offset ?h) (10 ^ p)"
    by (rule comma_python_entry_fragment_scale_guard[OF f entry.prems(1)
      offset]; simp)
  have pending_empty: "pending = None"
    using entry.prems(3)
    by (cases pending) (auto simp: comma_python_pending_phase_def)
  show ?case using entry_guard headroom pending_empty
    by (simp add: comma_python_flush_near_def)
next
  case (near_start p f delta headroom next_headroom weight increment)
  then show ?case by simp
next
  case (near_merge p pending_fragment f delta headroom next_headroom weight
      increment)
  then show ?case by simp
next
  case (near_cross p f delta headroom g next_delta offset weight pending
      increment)
  have pending_guards:
    "\<forall>g\<in>set (comma_python_flush_near pending).
      comma_python_fragment_scale_guard g (10 ^ p)"
    by (rule comma_python_pending_flush_scale_guards[OF near_cross.prems(3)])
  have literal_guard:
    "comma_python_fragment_scale_guard
      (comma_python_literal_fragment f
        (comma_chart_value p (Comma_Near f delta headroom) mod 10)
        1 increment) (10 ^ p)"
    by (rule comma_python_literal_fragment_scale_guard)
  show ?case using pending_guards literal_guard
    by (simp add: set_append)
qed

lemma comma_python_affine_fold_scale_guard:
  fixes z :: comma_python_affine_weight
  assumes initial_positive: "0 < comma_python_affine_denominator z"
    and initial_exact: "comma_python_affine_divides z S"
    and initial_nonnegative: "0 \<le> comma_python_affine_evaluate z S"
    and entries: "\<forall>x\<in>set xs.
      0 < comma_python_affine_denominator x \<and>
      comma_python_affine_divides x S \<and>
      0 \<le> comma_python_affine_evaluate x S"
  shows "0 < comma_python_affine_denominator
      (foldl comma_python_affine_add z xs)"
    and "comma_python_affine_divides
      (foldl comma_python_affine_add z xs) S"
    and "comma_python_affine_evaluate
      (foldl comma_python_affine_add z xs) S =
        comma_python_affine_evaluate z S +
          sum_list (map (\<lambda>x. comma_python_affine_evaluate x S) xs)"
    and "0 \<le> comma_python_affine_evaluate
      (foldl comma_python_affine_add z xs) S"
  using initial_positive initial_exact initial_nonnegative entries
proof (induction xs arbitrary: z)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  have x_positive: "0 < comma_python_affine_denominator x"
    and x_exact: "comma_python_affine_divides x S"
    and x_nonnegative: "0 \<le> comma_python_affine_evaluate x S"
    using Cons.prems(4) by simp_all
  let ?z = "comma_python_affine_add z x"
  have z_positive: "0 < comma_python_affine_denominator ?z"
    by (rule comma_python_affine_add_positive[OF Cons.prems(1) x_positive])
  note z_exact = comma_python_affine_add_exact_at_scale
    [OF Cons.prems(1) x_positive Cons.prems(2) x_exact]
  have z_nonnegative: "0 \<le> comma_python_affine_evaluate ?z S"
    using z_exact(2) Cons.prems(3) x_nonnegative by simp
  have z_divides: "comma_python_affine_divides ?z S"
    using z_exact(1) by (simp add: comma_python_affine_divides_def)
  have rest:
    "0 < comma_python_affine_denominator (foldl comma_python_affine_add ?z xs)"
    "comma_python_affine_divides (foldl comma_python_affine_add ?z xs) S"
    "comma_python_affine_evaluate (foldl comma_python_affine_add ?z xs) S =
      comma_python_affine_evaluate ?z S +
        sum_list (map (\<lambda>x. comma_python_affine_evaluate x S) xs)"
    "0 \<le> comma_python_affine_evaluate
      (foldl comma_python_affine_add ?z xs) S"
    using Cons.IH[OF z_positive z_divides z_nonnegative] Cons.prems(4)
    by simp_all
  show ?case using rest z_exact(2) Cons.prems(3)
    by (simp_all add: sum_list_Cons)
qed

lemma comma_python_sum_list_map_nonnegative:
  fixes f :: "'a \<Rightarrow> int"
  assumes "\<forall>x\<in>set xs. 0 \<le> f x"
  shows "0 \<le> sum_list (map f xs)"
  using assms by (induction xs) auto

lemma comma_python_sum_take_nonnegative_mono:
  fixes f :: "'a \<Rightarrow> int"
  assumes indices: "i \<le> j"
    and values: "\<forall>x\<in>set xs. 0 \<le> f x"
  shows "sum_list (map f (take i xs)) \<le>
    sum_list (map f (take j xs))"
proof -
  have decomp:
    "take i (take j xs) @ drop i (take j xs) = take j xs"
    by (rule append_take_drop_id)
  have prefix: "take i (take j xs) = take i xs"
    using indices by simp
  have remainder_values:
    "\<forall>x\<in>set (drop i (take j xs)). 0 \<le> f x"
    using values by auto
  have remainder_nonnegative:
    "0 \<le> sum_list (map f (drop i (take j xs)))"
    by (rule comma_python_sum_list_map_nonnegative[OF remainder_values])
  have sum_decomp:
    "sum_list (map f (take j xs)) =
      sum_list (map f (take i xs)) +
        sum_list (map f (drop i (take j xs)))"
    using decomp prefix by (simp add: map_append sum_list_append)
  show ?thesis using sum_decomp remainder_nonnegative by linarith
qed

lemma comma_python_actual_writer_prefix_guards:
  fixes p :: nat
  assumes exponent: "5 \<le> p"
    and walk: "comma_python_first_terminal_walk p source events outcome terminal"
    and admitted: "comma_round_admitted source"
    and phase: "comma_python_pending_phase p source None"
  obtains fragments where
    run: "comma_python_writer_run p source None events outcome terminal fragments"
    and fragment_guards:
      "\<forall>g\<in>set fragments.
        comma_python_fragment_scale_guard g (10 ^ p)"
    and weight_array_length:
      "length (comma_python_published_weights
        (comma_python_publish_fragments fragments)) = Suc (length fragments)"
    and displacement_array_length:
      "length (comma_python_published_displacements
        (comma_python_publish_fragments fragments)) = Suc (length fragments)"
    and weight_array_fold:
      "\<forall>i\<le>length fragments.
        comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_weight_affine (take i fragments))"
    and displacement_array_fold:
      "\<forall>i\<le>length fragments.
        comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_displacement_affine (take i fragments))"
    and weight_prefixes:
      "\<forall>i\<le>length fragments.
        0 < comma_python_affine_denominator
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) \<and>
        comma_python_affine_divides
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
        0 \<le> comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
        comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
          sum_list (map (comma_python_fragment_weight_at_exponent p)
            (take i fragments))"
    and displacement_prefixes:
      "\<forall>i\<le>length fragments.
        0 < comma_python_affine_denominator
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) \<and>
        comma_python_affine_divides
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
        0 \<le> comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
        comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
          sum_list (map (comma_python_fragment_displacement_at_exponent p)
            (take i fragments))"
    and monotone_weights:
      "\<forall>i j. i \<le> j \<longrightarrow> j \<le> length fragments \<longrightarrow>
        nat (comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p)) \<le>
        nat (comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! j) (10 ^ p))"
    and monotone_displacements:
      "\<forall>i j. i \<le> j \<longrightarrow> j \<le> length fragments \<longrightarrow>
        nat (comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p)) \<le>
        nat (comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! j) (10 ^ p))"
proof -
  have general:
    "comma_python_pending_phase p source pending \<Longrightarrow>
      (\<exists>fragments.
        comma_python_writer_run p source pending events outcome terminal fragments \<and>
        (\<forall>g\<in>set fragments.
          comma_python_fragment_scale_guard g (10 ^ p)))"
    using walk exponent admitted
  proof (induction arbitrary: pending
      rule: comma_python_first_terminal_walk.induct)
    case (fork p source a delta)
    show ?case
    proof
      assume phase: "comma_python_pending_phase p source pending"
      have run:
        "comma_python_writer_run p source pending []
          (Comma_Fork_At a delta) source (comma_python_flush_near pending)"
        by (rule comma_python_writer_run.fork[OF fork.hyps(1)]) simp
      have guards:
        "\<forall>g\<in>set (comma_python_flush_near pending).
          comma_python_fragment_scale_guard g (10 ^ p)"
        by (rule comma_python_pending_flush_scale_guards[OF phase])
      show "\<exists>fragments.
          comma_python_writer_run p source pending []
            (Comma_Fork_At a delta) source fragments \<and>
          (\<forall>g\<in>set fragments.
            comma_python_fragment_scale_guard g (10 ^ p))"
        using run guards by blast
    qed
  next
    case (landmine p source delta)
    show ?case
    proof
      assume phase: "comma_python_pending_phase p source pending"
      have run:
        "comma_python_writer_run p source pending []
          (Comma_Landmine_At delta) source (comma_python_flush_near pending)"
        by (rule comma_python_writer_run.landmine[OF landmine.hyps(1)]) simp
      have guards:
        "\<forall>g\<in>set (comma_python_flush_near pending).
          comma_python_fragment_scale_guard g (10 ^ p)"
        by (rule comma_python_pending_flush_scale_guards[OF phase])
      show "\<exists>fragments.
          comma_python_writer_run p source pending []
            (Comma_Landmine_At delta) source fragments \<and>
          (\<forall>g\<in>set fragments.
            comma_python_fragment_scale_guard g (10 ^ p))"
        using run guards by blast
    qed
  next
    case (advance p source successor weight events outcome terminal)
    show ?case
    proof
      assume phase: "comma_python_pending_phase p source pending"
      have finite_next:
        "comma_finite_step (p mod 924) source = Comma_Next successor"
        using advance.hyps(1) by (simp add: comma_finite_step_def)
      have successor_admitted: "comma_round_admitted successor"
        by (rule comma_round_next_admitted[OF advance.prems(2) finite_next])
      obtain emitted pending' where edge:
          "comma_python_writer_edge p source successor weight pending emitted pending'"
        and next_phase: "comma_python_pending_phase p successor pending'"
        using comma_python_writer_edge_exists
          [OF advance.prems(1) advance.prems(2) phase advance.hyps(1)]
        by blast
      obtain tail_fragments where tail_run:
          "comma_python_writer_run p successor pending' events outcome terminal
            tail_fragments"
        and tail_guards: "\<forall>g\<in>set tail_fragments.
          comma_python_fragment_scale_guard g (10 ^ p)"
        using advance.IH[OF advance.prems(1) successor_admitted next_phase]
        by blast
      have emitted_guards:
        "\<forall>g\<in>set emitted.
          comma_python_fragment_scale_guard g (10 ^ p)"
        by (rule comma_python_writer_edge_emitted_scale_guards
          [OF advance.prems(1) advance.prems(2) phase edge])
      have run:
        "comma_python_writer_run p source pending
          (Comma_Python_Advance source successor weight # events)
          outcome terminal (emitted @ tail_fragments)"
        by (rule comma_python_writer_run.advance
          [OF advance.hyps(1) edge tail_run])
      show "\<exists>fragments.
          comma_python_writer_run p source pending
            (Comma_Python_Advance source successor weight # events)
            outcome terminal fragments \<and>
          (\<forall>g\<in>set fragments.
            comma_python_fragment_scale_guard g (10 ^ p))"
        using run emitted_guards tail_guards by auto
    qed
  qed
  have actual:
    "\<exists>fragments.
      comma_python_writer_run p source None events outcome terminal fragments \<and>
      (\<forall>g\<in>set fragments.
        comma_python_fragment_scale_guard g (10 ^ p))"
    using general phase by blast
  obtain fragments where run:
      "comma_python_writer_run p source None events outcome terminal fragments"
    and guards: "\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    using actual by blast
  have weight_array_length:
    "length (comma_python_published_weights
      (comma_python_publish_fragments fragments)) = Suc (length fragments)"
    and displacement_array_length:
    "length (comma_python_published_displacements
      (comma_python_publish_fragments fragments)) = Suc (length fragments)"
    by (simp_all add: comma_python_publish_fragments_lengths)
  have weight_array_fold:
    "\<forall>i\<le>length fragments.
      comma_python_published_weights
        (comma_python_publish_fragments fragments) ! i =
      foldl comma_python_affine_add comma_python_affine_zero
        (map comma_python_fragment_weight_affine (take i fragments))"
  proof (intro allI impI)
    fix i assume index: "i \<le> length fragments"
    show "comma_python_published_weights
        (comma_python_publish_fragments fragments) ! i =
      foldl comma_python_affine_add comma_python_affine_zero
        (map comma_python_fragment_weight_affine (take i fragments))"
      by (rule comma_python_publish_fragments_nth(1)[OF index])
  qed
  have displacement_array_fold:
    "\<forall>i\<le>length fragments.
      comma_python_published_displacements
        (comma_python_publish_fragments fragments) ! i =
      foldl comma_python_affine_add comma_python_affine_zero
        (map comma_python_fragment_displacement_affine (take i fragments))"
  proof (intro allI impI)
    fix i assume index: "i \<le> length fragments"
    show "comma_python_published_displacements
        (comma_python_publish_fragments fragments) ! i =
      foldl comma_python_affine_add comma_python_affine_zero
        (map comma_python_fragment_displacement_affine (take i fragments))"
      by (rule comma_python_publish_fragments_nth(2)[OF index])
  qed
  have weight_prefixes:
    "\<forall>i\<le>length fragments.
      0 < comma_python_affine_denominator
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) \<and>
      comma_python_affine_divides
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
      0 \<le> comma_python_affine_evaluate
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
      comma_python_affine_evaluate
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        sum_list (map (comma_python_fragment_weight_at_exponent p)
          (take i fragments))"
  proof (intro allI impI)
    fix i assume i: "i \<le> length fragments"
    have entry_guards:
      "\<forall>x\<in>set (map comma_python_fragment_weight_affine
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
    have fold_guard:
      "0 < comma_python_affine_denominator
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_weight_affine (take i fragments)))"
        "comma_python_affine_divides
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_weight_affine (take i fragments)))
          (10 ^ p)"
        "0 \<le> comma_python_affine_evaluate
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_weight_affine (take i fragments)))
          (10 ^ p)"
        "comma_python_affine_evaluate
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_weight_affine (take i fragments)))
          (10 ^ p) =
          sum_list (map (\<lambda>g. comma_python_affine_evaluate
            (comma_python_fragment_weight_affine g) (10 ^ p))
            (take i fragments))"
      by (rule comma_python_affine_fold_scale_guard
        [OF zero_positive zero_exact zero_nonnegative entry_guards])
    have nth:
      "comma_python_published_weights
        (comma_python_publish_fragments fragments) ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_weight_affine (take i fragments))"
      by (rule comma_python_publish_fragments_nth(1)[OF i])
    have values:
      "map (\<lambda>g. comma_python_affine_evaluate
          (comma_python_fragment_weight_affine g) (10 ^ p)) (take i fragments) =
        map (comma_python_fragment_weight_at_exponent p) (take i fragments)"
      using guards by (induction "take i fragments")
        (auto simp: comma_python_fragment_scale_guard_def
          comma_python_fragment_weight_at_exponent_def)
    show "0 < comma_python_affine_denominator
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) \<and>
        comma_python_affine_divides
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
        0 \<le> comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
        comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
          sum_list (map (comma_python_fragment_weight_at_exponent p)
            (take i fragments))"
      using fold_guard nth values
      by (simp add: comma_python_fragment_weight_at_exponent_def)
  qed
  have displacement_prefixes:
    "\<forall>i\<le>length fragments.
      0 < comma_python_affine_denominator
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) \<and>
      comma_python_affine_divides
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
      0 \<le> comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
      comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        sum_list (map (comma_python_fragment_displacement_at_exponent p)
          (take i fragments))"
  proof (intro allI impI)
    fix i assume i: "i \<le> length fragments"
    have entry_guards:
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
    have fold_guard:
      "0 < comma_python_affine_denominator
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_displacement_affine (take i fragments)))"
        "comma_python_affine_divides
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_displacement_affine (take i fragments)))
          (10 ^ p)"
        "0 \<le> comma_python_affine_evaluate
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_displacement_affine (take i fragments)))
          (10 ^ p)"
        "comma_python_affine_evaluate
          (foldl comma_python_affine_add comma_python_affine_zero
            (map comma_python_fragment_displacement_affine (take i fragments)))
          (10 ^ p) =
          sum_list (map (\<lambda>g. comma_python_affine_evaluate
            (comma_python_fragment_displacement_affine g) (10 ^ p))
            (take i fragments))"
      by (rule comma_python_affine_fold_scale_guard
        [OF zero_positive zero_exact zero_nonnegative entry_guards])
    have nth:
      "comma_python_published_displacements
        (comma_python_publish_fragments fragments) ! i =
        foldl comma_python_affine_add comma_python_affine_zero
          (map comma_python_fragment_displacement_affine (take i fragments))"
      by (rule comma_python_publish_fragments_nth(2)[OF i])
    have values:
      "map (\<lambda>g. comma_python_affine_evaluate
          (comma_python_fragment_displacement_affine g) (10 ^ p))
          (take i fragments) =
        map (comma_python_fragment_displacement_at_exponent p)
          (take i fragments)"
      using guards by (induction "take i fragments")
        (auto simp: comma_python_fragment_scale_guard_def
          comma_python_fragment_displacement_at_exponent_def)
    show "0 < comma_python_affine_denominator
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) \<and>
        comma_python_affine_divides
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
        0 \<le> comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) \<and>
        comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
          sum_list (map (comma_python_fragment_displacement_at_exponent p)
            (take i fragments))"
      using fold_guard nth values
      by (simp add: comma_python_fragment_displacement_at_exponent_def)
  qed
  have monotone_weights:
    "\<forall>i j. i \<le> j \<longrightarrow> j \<le> length fragments \<longrightarrow>
      nat (comma_python_affine_evaluate
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! i) (10 ^ p)) \<le>
      nat (comma_python_affine_evaluate
        (comma_python_published_weights
          (comma_python_publish_fragments fragments) ! j) (10 ^ p))"
  proof (intro allI impI)
    fix i j assume ij: "i \<le> j" and j: "j \<le> length fragments"
    have i: "i \<le> length fragments" using ij j by arith
    have sums:
      "comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        sum_list (map (comma_python_fragment_weight_at_exponent p)
          (take i fragments))"
      "comma_python_affine_evaluate
          (comma_python_published_weights
            (comma_python_publish_fragments fragments) ! j) (10 ^ p) =
        sum_list (map (comma_python_fragment_weight_at_exponent p)
          (take j fragments))"
      using weight_prefixes i j by simp_all
    have values: "\<forall>g\<in>set fragments.
      0 \<le> comma_python_fragment_weight_at_exponent p g"
      using guards by (auto simp: comma_python_fragment_scale_guard_def
        comma_python_fragment_weight_at_exponent_def)
    have order:
      "sum_list (map (comma_python_fragment_weight_at_exponent p)
        (take i fragments)) \<le>
       sum_list (map (comma_python_fragment_weight_at_exponent p)
        (take j fragments))"
      by (rule comma_python_sum_take_nonnegative_mono[OF ij values])
    have nat_order:
      "nat (sum_list (map (comma_python_fragment_weight_at_exponent p)
          (take i fragments))) \<le>
       nat (sum_list (map (comma_python_fragment_weight_at_exponent p)
          (take j fragments)))"
      by (rule nat_mono[OF order])
    show ?case using sums nat_order by simp
  qed
  have monotone_displacements:
    "\<forall>i j. i \<le> j \<longrightarrow> j \<le> length fragments \<longrightarrow>
      nat (comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! i) (10 ^ p)) \<le>
      nat (comma_python_affine_evaluate
        (comma_python_published_displacements
          (comma_python_publish_fragments fragments) ! j) (10 ^ p))"
  proof (intro allI impI)
    fix i j assume ij: "i \<le> j" and j: "j \<le> length fragments"
    have i: "i \<le> length fragments" using ij j by arith
    have sums:
      "comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
        sum_list (map (comma_python_fragment_displacement_at_exponent p)
          (take i fragments))"
      "comma_python_affine_evaluate
          (comma_python_published_displacements
            (comma_python_publish_fragments fragments) ! j) (10 ^ p) =
        sum_list (map (comma_python_fragment_displacement_at_exponent p)
          (take j fragments))"
      using displacement_prefixes i j by simp_all
    have values: "\<forall>g\<in>set fragments.
      0 \<le> comma_python_fragment_displacement_at_exponent p g"
      using guards by (auto simp: comma_python_fragment_scale_guard_def
        comma_python_fragment_displacement_at_exponent_def)
    have order:
      "sum_list (map (comma_python_fragment_displacement_at_exponent p)
        (take i fragments)) \<le>
       sum_list (map (comma_python_fragment_displacement_at_exponent p)
        (take j fragments))"
      by (rule comma_python_sum_take_nonnegative_mono[OF ij values])
    have nat_order:
      "nat (sum_list (map (comma_python_fragment_displacement_at_exponent p)
          (take i fragments))) \<le>
       nat (sum_list (map (comma_python_fragment_displacement_at_exponent p)
          (take j fragments)))"
      by (rule nat_mono[OF order])
    show ?case using sums nat_order by simp
  qed
  show thesis
    using run guards weight_prefixes displacement_prefixes
      weight_array_length displacement_array_length weight_array_fold
      displacement_array_fold monotone_weights monotone_displacements
    by (rule that)
qed

lemma comma_python_published_prefixes_at_scale:
  assumes guards: "\<forall>g\<in>set fragments.
      comma_python_fragment_scale_guard g (10 ^ p)"
    and index: "i \<le> length fragments"
  shows "comma_python_affine_evaluate
      (comma_python_published_weights
        (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
    sum_list (map (\<lambda>g.
      comma_python_fragment_weight_at_scale g (10 ^ p))
      (take i fragments))"
    and "comma_python_affine_evaluate
      (comma_python_published_displacements
        (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
    sum_list (map (\<lambda>g.
      comma_python_fragment_displacement_at_scale g (10 ^ p))
      (take i fragments))"
proof -
  have weight_facts:
    "\<forall>x\<in>set (map comma_python_fragment_weight_affine
        (take i fragments)).
      0 < comma_python_affine_denominator x \<and>
      comma_python_affine_divides x (10 ^ p) \<and>
      0 \<le> comma_python_affine_evaluate x (10 ^ p)"
    using guards by (auto simp: comma_python_fragment_scale_guard_def)
  have displacement_affine_facts:
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
    by (simp add: comma_python_affine_divides_def comma_python_affine_zero_def
        comma_python_affine_normalize_def Let_def)
  have zero_nonnegative:
    "0 \<le> comma_python_affine_evaluate comma_python_affine_zero (10 ^ p)"
    by simp
  note weight_fold = comma_python_affine_fold_scale_guard
    [OF zero_positive zero_exact zero_nonnegative weight_facts]
  note displacement_fold = comma_python_affine_fold_scale_guard
    [OF zero_positive zero_exact zero_nonnegative displacement_affine_facts]
  have published_weight:
    "comma_python_published_weights
      (comma_python_publish_fragments fragments) ! i =
     foldl comma_python_affine_add comma_python_affine_zero
       (map comma_python_fragment_weight_affine (take i fragments))"
    by (rule comma_python_publish_fragments_nth(1)[OF index])
  have published_displacement:
    "comma_python_published_displacements
      (comma_python_publish_fragments fragments) ! i =
     foldl comma_python_affine_add comma_python_affine_zero
       (map comma_python_fragment_displacement_affine (take i fragments))"
    by (rule comma_python_publish_fragments_nth(2)[OF index])
  have weight_values:
    "map (\<lambda>g. comma_python_affine_evaluate
        (comma_python_fragment_weight_affine g) (10 ^ p))
        (take i fragments) =
      map (\<lambda>g. comma_python_fragment_weight_at_scale g (10 ^ p))
        (take i fragments)"
    using guards by (induction "take i fragments")
      (auto simp: comma_python_fragment_scale_guard_def)
  have displacement_values:
    "map (\<lambda>g. comma_python_affine_evaluate
        (comma_python_fragment_displacement_affine g) (10 ^ p))
        (take i fragments) =
      map (\<lambda>g. comma_python_fragment_displacement_at_scale g (10 ^ p))
        (take i fragments)"
    using guards by (induction "take i fragments")
      (auto simp: comma_python_fragment_scale_guard_def)
  show "comma_python_affine_evaluate
      (comma_python_published_weights
        (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
    sum_list (map (\<lambda>g.
      comma_python_fragment_weight_at_scale g (10 ^ p))
      (take i fragments))"
    using weight_fold(3) published_weight weight_values by simp
  show "comma_python_affine_evaluate
      (comma_python_published_displacements
        (comma_python_publish_fragments fragments) ! i) (10 ^ p) =
    sum_list (map (\<lambda>g.
      comma_python_fragment_displacement_at_scale g (10 ^ p))
      (take i fragments))"
    using displacement_fold(3) published_displacement displacement_values by simp
qed

lemmas comma_python_producer_prefix_refinement_oracle_audit_bundle =
  comma_python_affine_times_exact_at_scale
  comma_python_near_fragment_scale_guard
  comma_python_entry_fragment_scale_guard
  comma_python_writer_edge_emitted_scale_guards
  comma_python_affine_fold_scale_guard
  comma_python_published_prefixes_at_scale
  comma_python_actual_writer_prefix_guards
ML \<open>val _ = if null (Thm_Deps.all_oracles
  @{thms comma_python_producer_prefix_refinement_oracle_audit_bundle}) then ()
  else error "Comma_Semantic_Producer_Prefix_Refinement local oracle audit failed"\<close>

end
